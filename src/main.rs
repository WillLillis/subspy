//! CLI entry point and subcommand dispatch.

use std::process;

use anstyle::AnsiColor;
use clap::{Command, FromArgMatches as _, Subcommand as _};
use etcetera::BaseStrategy as _;
use flexi_logger::{FileSpec, Logger, WriteMode};
use log::{error, info};

use subspy::{
    cli::{Commands, LogLevel, RunResult},
    git::configure_git2,
    paint,
};

pub fn main() {
    if let Err(err) = run() {
        if !err.to_string().is_empty() {
            eprintln!("{}: {err}", paint(Some(AnsiColor::Red), "Error"));
        }
        process::exit(1);
    }
}

/// Sets up logging, panic hooks, and flush behavior. Returns `true` if the
/// command is the watch server (i.e. logs should be flushed on exit).
fn setup_logging(command: &Commands) -> RunResult<bool> {
    let is_watcher = matches!(command, Commands::Start(_));

    if is_watcher {
        let mut log_file_dir = etcetera::choose_base_strategy()?.cache_dir();
        log_file_dir.push("subspy");
        Logger::with(command.log_level().unwrap_or(LogLevel::Info))
            .log_to_file(FileSpec::default().directory(log_file_dir))
            .write_mode(WriteMode::BufferAndFlush)
            .start()
            .unwrap();

        let default_panic_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            error!("Panic: {info}");
            log::logger().flush();
            default_panic_hook(info);
        }));

        info!("Invoked with command: {command:#?}");
    } else {
        Logger::with(command.log_level().unwrap_or(LogLevel::Warn))
            .log_to_stderr()
            .start()
            .unwrap();
    }

    Ok(is_watcher)
}

fn run() -> RunResult<()> {
    // This is the first git2 call in the process, so it triggers libgit2's
    // one-time global initialization (~80-200K cycles). The configure_git2
    // function itself is ~430 cycles; the rest is the init overhead that
    // would otherwise be paid on the first Repository::open call.
    configure_git2();
    let cli = Command::new("subspy")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .disable_help_subcommand(true)
        .disable_colored_help(false)
        .after_help("Use `subspy <COMMAND> --help` for more information on a subcommand.");
    let cli = Commands::augment_subcommands(cli);

    let command = Commands::from_arg_matches(&cli.get_matches())?;
    let is_watcher = setup_logging(&command)?;

    let result = match command {
        Commands::Start(watch_options) => watch_options.run(),
        Commands::Status(status_options) => status_options.run(),
        Commands::Stop(shutdown_options) => shutdown_options.run(),
        Commands::Reindex(reindex_options) => reindex_options.run(),
        Commands::Debug(debug_options) => debug_options.run(),
        Commands::List(list_options) => list_options.run(),
        Commands::Prompt(prompt_options) => prompt_options.run(),
    };

    if is_watcher {
        if let Err(ref err) = result {
            error!("Fatal: {err}");
        }
        log::logger().flush();
    }

    result
}
