use std::{
    env::current_dir,
    io,
    path::{Path, PathBuf},
    process,
};

use anstyle::{AnsiColor, Color, Style};
use clap::{Args, Command, FromArgMatches as _, Subcommand, ValueEnum};
use etcetera::{BaseStrategy, HomeDirError};
use flexi_logger::{Cleanup, Criterion, FileSpec, Logger, Naming, WriteMode};
use log::{error, info};
use thiserror::Error;

use subspy::{
    DOT_GIT, DOT_GITMODULES, RepoKind,
    connection::{client::request_reindex, watch_server::watch},
    reindex::ReindexError,
    shutdown::{ShutdownError, shutdown},
    status::{StatusError, status},
    watch::{WatchError, WatchResult},
};

#[derive(Subcommand, Debug)]
enum Commands {
    /// Reindex a watch server
    Reindex(Reindex),
    /// Shutdown a watch server
    Shutdown(Shutdown),
    /// Display the status of a watched git project
    Status(Status),
    /// Start a watch server on a git project
    Watch(Watch),
}

impl Commands {
    const fn log_level(&self) -> Option<LogLevel> {
        match self {
            Self::Reindex(cmd) => cmd.log_level,
            Self::Shutdown(cmd) => cmd.log_level,
            Self::Status(cmd) => cmd.log_level,
            Self::Watch(cmd) => cmd.log_level,
        }
    }
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["r", "re"])]
struct Reindex {
    /// The directory whose watcher should reindex
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["s", "st"])]
struct Status {
    /// The directory to query `git status` for
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["sh", "stop"])]
struct Shutdown {
    /// The directory to shutdown a watcher for
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["w", "wa"])]
struct Watch {
    /// The directory containing the repository's `.gitmodules` file
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// Launch the watch server as a background process
    #[arg(short, long)]
    pub daemon: bool,
    /// The log level to use for the watch server
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
}

pub type RunResult<T> = Result<T, RunError>;

#[derive(Error, Debug)]
pub enum RunError {
    #[error(transparent)]
    Status(#[from] StatusError),
    #[error(transparent)]
    Watch(#[from] WatchError),
    #[error("Invalid path {}: {error}", path.display())]
    ProjectPath {
        path: PathBuf,
        error: std::io::Error,
    },
    #[error(transparent)]
    Reindex(#[from] ReindexError),
    #[error(transparent)]
    Shutdown(#[from] ShutdownError),
    #[error("Unable to determine home directory: {0}")]
    Home(#[from] HomeDirError),
    #[error(transparent)]
    Clap(#[from] clap::Error),
}

impl RunError {
    /// Returns `RunError::ProjectPath`, indicating `path` does not point to a non-recursive (not
    /// a submodule of a submodule) git repository with submodules.
    fn server_path(path: PathBuf) -> Self {
        Self::ProjectPath {
            path,
            error: io::Error::other(
                "Path must be inside a non-recursive git repository with a .gitmodules file",
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum LogLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

impl From<LogLevel> for flexi_logger::LogSpecification {
    fn from(level: LogLevel) -> Self {
        match level {
            LogLevel::Error => Self::error(),
            LogLevel::Warn => Self::warn(),
            LogLevel::Info => Self::info(),
            LogLevel::Debug => Self::debug(),
            LogLevel::Trace => Self::trace(),
        }
    }
}

impl std::fmt::Display for LogLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Error => "error",
                Self::Warn => "warn",
                Self::Info => "info",
                Self::Debug => "debug",
                Self::Trace => "trace",
            }
        )
    }
}

impl Reindex {
    fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        if repo_kind != RepoKind::WithSubmodules {
            return Err(RunError::server_path(true_path));
        }
        Ok(request_reindex(true_path.as_path())?)
    }
}

impl Shutdown {
    fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        if repo_kind != RepoKind::WithSubmodules {
            return Err(RunError::server_path(true_path));
        }
        Ok(shutdown(true_path.as_path())?)
    }
}

impl Status {
    fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        Ok(status(true_path.as_path(), repo_kind)?)
    }
}

impl Watch {
    fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        if repo_kind != RepoKind::WithSubmodules {
            return Err(RunError::server_path(true_path));
        }

        if self.daemon {
            Ok(Self::spawn_daemon(&true_path, self.log_level)?)
        } else {
            Ok(watch(true_path.as_path())?)
        }
    }

    /// Spawns the watch server as a fully detached background process.
    fn spawn_daemon(path: &Path, log_level: Option<LogLevel>) -> WatchResult<()> {
        let log_level = log_level.map(|l| l.to_string());
        let exe = std::env::current_exe()?;
        let mut cmd = process::Command::new(exe);
        cmd.arg("watch")
            .arg(path)
            .stdin(process::Stdio::null())
            .stdout(process::Stdio::null())
            .stderr(process::Stdio::null());
        if let Some(log_level) = log_level {
            cmd.args(["--log-level", &log_level]);
        }

        #[cfg(target_os = "windows")]
        {
            use std::os::windows::process::CommandExt as _;
            // https://learn.microsoft.com/en-us/windows/win32/procthread/process-creation-flags#flags
            // The new process does not inherit its parent's console
            const DETACHED_PROCESS: u32 = 0x0000_0008;
            // The new process is the root process of a new process group...If this flag is specified,
            // CTRL+C signals will be disabled for all processes within the new process group.
            const CREATE_NEW_PROCESS_GROUP: u32 = 0x0000_0200;
            cmd.creation_flags(DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP);
        }

        cmd.spawn()?;
        Ok(())
    }
}

/// Uses `path` if present or uses the current working directory. Ensures the resolved path
/// is a git repository or a child of one.
///
/// If found, returns the path to the repository and the kind of repository.
fn get_project_path(path: Option<PathBuf>) -> RunResult<(PathBuf, RepoKind)> {
    let path = path.unwrap_or_else(|| current_dir().unwrap());
    let true_path = dunce::canonicalize(&path).map_err(|error| RunError::ProjectPath {
        path: path.clone(),
        error,
    })?;

    let mut current_path = true_path.as_path();
    loop {
        let dot_git_path = current_path.join(DOT_GIT);
        if dot_git_path.exists() {
            if dot_git_path.is_file() {
                return Ok((current_path.to_path_buf(), RepoKind::Submodule));
            }
            let dot_gitmodules_path = current_path.join(DOT_GITMODULES);
            let has_gitmodules = dot_gitmodules_path.exists() && dot_gitmodules_path.is_file();
            let repo_kind = if has_gitmodules {
                RepoKind::WithSubmodules
            } else {
                RepoKind::Normal
            };
            return Ok((current_path.to_path_buf(), repo_kind));
        }
        current_path = match current_path.parent() {
            Some(p) => p,
            None => Err(RunError::ProjectPath {
                #[allow(clippy::redundant_clone)] // false positive
                path: path.clone(),
                error: io::Error::other("Path must be inside a git repository"),
            })?,
        }
    }
}

fn paint(color: Option<impl Into<Color>>, text: &str) -> String {
    let style = Style::new().fg_color(color.map(Into::into));
    format!("{style}{text}{style:#}")
}

pub fn main() {
    if let Err(err) = run() {
        error!("Fatal: {err}");
        if !err.to_string().is_empty() {
            eprintln!("{}: {err}", paint(Some(AnsiColor::Red), "Error"));
        }
        std::process::exit(1);
    }
}

fn run() -> RunResult<()> {
    let cli = Command::new("subspy")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .disable_help_subcommand(true)
        .disable_colored_help(false);
    let cli = Commands::augment_subcommands(cli);

    let command = Commands::from_arg_matches(&cli.get_matches())?;

    let mut log_file_dir = etcetera::choose_base_strategy()?.cache_dir();
    log_file_dir.push("subspy");

    Logger::with(command.log_level().unwrap_or(LogLevel::Info))
        .log_to_file(FileSpec::default().directory(log_file_dir))
        .rotate(
            Criterion::Size(10 * 1024 * 1024),
            Naming::Numbers,
            Cleanup::KeepLogFiles(5),
        )
        .write_mode(WriteMode::BufferAndFlush)
        .start()
        .unwrap();

    let default_panic_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        error!("Panic: {info}");
        default_panic_hook(info);
    }));
    info!("Invoked with command: {command:#?}");

    match command {
        Commands::Watch(watch_options) => watch_options.run()?,
        Commands::Status(status_options) => status_options.run()?,
        Commands::Shutdown(shutdown_options) => shutdown_options.run()?,
        Commands::Reindex(reindex_options) => reindex_options.run()?,
    }

    Ok(())
}
