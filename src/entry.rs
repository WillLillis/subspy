//! Subspy CLI entry point.
//!
//! [`subspy_entry`] is what the `subspy` binary's main runs, and what the
//! `subspy-git` shim hands off to when it sees the [`INTERNAL_FLAG`]
//! sentinel that `spawn_daemon` prepends. That sentinel route lets
//! `spawn_daemon` use `current_exe()` without caring whether it resolves
//! to `subspy` or the shim. Whichever binary is running can serve the
//! daemon role.

use std::{ffi::OsString, io, process::ExitCode};

use clap::{Command, FromArgMatches as _, Subcommand as _};
use etcetera::BaseStrategy as _;
use flexi_logger::{FileSpec, Logger, WriteMode};
use log::{error, info};

use crate::{
    cli::{Commands, LogLevel, RunResult},
    git::configure_git2,
    paint::{Paint, RED},
};

/// Internal-only argv marker, prepended by `spawn_daemon` so the receiving
/// process knows to run subspy's CLI regardless of which binary it is.
pub const INTERNAL_FLAG: &str = "--subspy-internal";

/// Runs the subspy CLI with the given argv, printing errors and returning
/// the appropriate process exit code.
///
/// Silently drops a leading [`INTERNAL_FLAG`] (immediately after the
/// program name) if present, so daemon-spawned invocations are accepted
/// without making the flag a public part of the CLI surface.
pub fn subspy_entry<I, T>(args: I) -> ExitCode
where
    I: IntoIterator<Item = T>,
    T: Into<OsString>,
{
    match subspy_dispatch(strip_internal_flag(args)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            if !err.to_string().is_empty() {
                eprintln!("{}: {err}", Paint::new(RED, "Error"));
            }
            ExitCode::FAILURE
        }
    }
}

/// Drops a leading [`INTERNAL_FLAG`] immediately after the program name, if
/// present.
fn strip_internal_flag<I, T>(args: I) -> impl Iterator<Item = OsString>
where
    I: IntoIterator<Item = T>,
    T: Into<OsString>,
{
    let mut iter = args.into_iter().map(Into::into);
    let program = iter.next();
    let mut iter = iter.peekable();
    if iter.peek().is_some_and(|arg| arg == INTERNAL_FLAG) {
        iter.next();
    }
    program.into_iter().chain(iter)
}

fn subspy_dispatch<I>(args: I) -> RunResult<()>
where
    I: IntoIterator<Item = OsString>,
{
    // First git2 call in the process triggers libgit2's one-time
    // global initialization (~80-200K cycles). configure_git2 itself
    // is ~430 cycles; the rest is init overhead that would otherwise
    // be paid on the first Repository::open call.
    configure_git2();
    let cli = Command::new("subspy")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .disable_help_subcommand(true)
        .disable_colored_help(false)
        .after_help("Use `subspy <COMMAND> --help` for more information on a subcommand.");
    let cli = Commands::augment_subcommands(cli);

    let command = Commands::from_arg_matches(&cli.get_matches_from(args))?;
    setup_logging(&command);

    match command {
        Commands::Start(watch_options) => {
            let result = watch_options.run();
            if let Err(ref err) = result {
                error!("Fatal: {err}");
            }
            log::logger().flush();
            result
        }
        Commands::Status(status_options) => {
            let mut out = io::BufWriter::with_capacity(64 * 1024, io::stdout().lock());
            status_options.run(&mut out)
        }
        Commands::Stop(shutdown_options) => shutdown_options.run(),
        Commands::Reindex(reindex_options) => reindex_options.run(),
        Commands::Debug(debug_options) => debug_options.run(),
        Commands::List(list_options) => list_options.run(),
        Commands::Prompt(prompt_options) => prompt_options.run(),
    }
}

/// Sets up logging and, for the watch server, the panic hook. The watch
/// server logs to a file in the cache dir (default `info`); client commands
/// log to stderr (default `warn`).
///
/// Logging is best-effort: a setup failure is swallowed and the command runs
/// unlogged rather than aborting. This matters most for the daemon, which is
/// spawned detached with a null stderr -- propagating the error would kill the
/// auto-spawned server silently and break the client that spawned it.
fn setup_logging(command: &Commands) {
    if let Commands::Start(start) = command {
        if let Ok(base) = etcetera::choose_base_strategy() {
            let mut log_file_dir = base.cache_dir();
            log_file_dir.push("subspy");
            let _ = Logger::with(start.log_level.unwrap_or(LogLevel::Info))
                .log_to_file(FileSpec::default().directory(log_file_dir))
                .write_mode(WriteMode::BufferAndFlush)
                .start();
        }

        let default_panic_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            error!("Panic: {info}");
            log::logger().flush();
            default_panic_hook(info);
        }));

        info!("Invoked with command: {command:#?}");
    } else {
        let _ = Logger::with(LogLevel::Warn).log_to_stderr().start();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strip(args: &[&str]) -> Vec<OsString> {
        strip_internal_flag(args.iter().map(OsString::from)).collect()
    }

    fn os(args: &[&str]) -> Vec<OsString> {
        args.iter().map(OsString::from).collect()
    }

    #[test]
    fn strips_leading_sentinel() {
        assert_eq!(
            strip(&["subspy", INTERNAL_FLAG, "start", "/path"]),
            os(&["subspy", "start", "/path"]),
        );
    }

    #[test]
    fn passes_through_when_sentinel_absent() {
        assert_eq!(
            strip(&["subspy", "start", "/path"]),
            os(&["subspy", "start", "/path"]),
        );
    }

    #[test]
    fn only_strips_in_leading_position() {
        // Anywhere other than immediately after the program name, the
        // sentinel is left alone for clap to reject.
        assert_eq!(
            strip(&["subspy", "start", INTERNAL_FLAG, "/path"]),
            os(&["subspy", "start", INTERNAL_FLAG, "/path"]),
        );
    }
}
