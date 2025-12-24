use std::{env::current_dir, io, path::PathBuf};

use anstyle::{AnsiColor, Color, Style};
use clap::{Args, Command, FromArgMatches as _, Subcommand};
use etcetera::{BaseStrategy, HomeDirError};
use flexi_logger::{Cleanup, Criterion, FileSpec, Logger, Naming, WriteMode};
use thiserror::Error;

use subspy::{
    connection::watch_server::watch,
    status::{StatusError, status},
    watch::WatchError,
};

// TODO: Re-index, shutdown/stop commands

#[derive(Subcommand)]
enum Commands {
    /// Start a watch on a git project
    Watch(Watch),
    /// Display the status of a watched git project
    Status(Status),
}

#[derive(Args)]
struct Watch {
    /// The directory containing the repository's `.gitmodules` file
    #[arg(short, long)]
    pub dir: Option<PathBuf>,
}

#[derive(Args)]
struct Status {
    /// The directory to query `git status` for
    #[arg(short, long)]
    pub dir: Option<PathBuf>,
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
    #[error("Unable to determine home directory: {0}")]
    Home(#[from] HomeDirError),
    #[error(transparent)]
    Clap(#[from] clap::Error),
}

impl Watch {
    fn run(self) -> RunResult<()> {
        let true_path = get_project_path(self.dir)?;
        Ok(watch(true_path.as_path())?)
    }
}

impl Status {
    fn run(self) -> RunResult<()> {
        let true_path = get_project_path(self.dir)?;
        Ok(status(true_path.as_path())?)
    }
}

/// Uses `path` if present or uses the current working directory. Ensures the resolved path
/// is a directory and contains a `.gitmodules` file.
fn get_project_path(path: Option<PathBuf>) -> RunResult<PathBuf> {
    let path = path.unwrap_or_else(|| current_dir().unwrap());
    let true_path =
        dunce::canonicalize(&path).map_err(|error| RunError::ProjectPath { path, error })?;
    let mut gitmodules_path = true_path.clone();
    gitmodules_path.push(".gitmodules");
    if !true_path.is_dir() || !gitmodules_path.exists() {
        Err(RunError::ProjectPath {
            #[allow(clippy::redundant_clone)] // false positive
            path: true_path.clone(),
            error: io::Error::other("Path must be a directory containing `.gitmodules` file"),
        })?;
    }

    Ok(true_path)
}

fn paint(color: Option<impl Into<Color>>, text: &str) -> String {
    let style = Style::new().fg_color(color.map(Into::into));
    format!("{style}{text}{style:#}")
}

pub fn main() {
    let result = run();
    if let Err(err) = &result {
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

    Logger::try_with_env_or_str("info")
        .unwrap()
        .log_to_file(FileSpec::default().directory(log_file_dir))
        .rotate(
            Criterion::Size(10 * 1024 * 1024),
            Naming::Numbers,
            Cleanup::KeepLogFiles(5),
        )
        .write_mode(WriteMode::BufferAndFlush)
        .start()
        .unwrap();

    match command {
        Commands::Watch(watch_options) => watch_options.run()?,
        Commands::Status(status_options) => status_options.run()?,
    }

    Ok(())
}
