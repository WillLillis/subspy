//! CLI argument definitions, subcommand dispatch, error types, and
//! repository path resolution.

use std::{env::current_dir, io, io::IsTerminal as _, path::PathBuf, time::Duration};

use clap::{Args, Subcommand, ValueEnum};
use thiserror::Error;

use crate::{
    DOT_GIT, DOT_GITMODULES, RepoKind,
    connection::watch_server::watch,
    debug::{DebugError, debug},
    list::{ListError, list},
    prompt::{PromptError, prompt},
    reindex::{ReindexError, reindex},
    shutdown::{ShutdownError, shutdown},
    status::{StatusError, status},
    watch::{WatchError, spawn_daemon},
};

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// Start a watch server on a git project
    Start(Start),
    /// Display the status of a watched git project
    Status(Status),
    /// Shutdown a watch server
    Stop(Stop),
    /// Reindex a watch server
    Reindex(Reindex),
    /// Dump the internal state of the watch server
    Debug(DebugDump),
    /// List submodule metadata
    List(List),
    /// Submodule status summary for shell prompt integration
    Prompt(Prompt),
}

impl Commands {
    #[must_use]
    pub const fn log_level(&self) -> Option<LogLevel> {
        match self {
            Self::Reindex(cmd) => cmd.log_level,
            Self::Stop(cmd) => cmd.log_level,
            Self::Status(cmd) => cmd.log_level,
            Self::Start(cmd) => cmd.log_level,
            Self::Debug(cmd) => cmd.log_level,
            Self::List(cmd) => cmd.log_level,
            Self::Prompt(cmd) => cmd.log_level,
        }
    }
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["re", "r"])]
pub struct Reindex {
    /// The directory whose watcher should reindex
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
    /// Replace all filesystem watchers during the reindex
    #[arg(short = 'w', long)]
    pub replace_watchers: bool,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["st", "s"])]
pub struct Status {
    /// The directory to query `git status` for
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
    /// Skip the watch server and compute status locally via libgit2
    #[arg(long)]
    pub no_server: bool,
}

#[derive(Args, Debug)]
pub struct Stop {
    /// The directory to shutdown a watcher for
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["dbg", "d"])]
pub struct DebugDump {
    /// The directory whose watcher state to dump
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["ls", "l"])]
pub struct List {
    /// The directory to list submodule info for
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
    #[expect(
        clippy::doc_markdown,
        reason = "placeholder names render in clap help text"
    )]
    #[allow(rustdoc::broken_intra_doc_links)]
    /// Custom format string with {placeholder} substitution.
    ///
    /// Available placeholders:
    ///   {name}        - submodule name (from .gitmodules [submodule "name"])
    ///   {path}        - submodule path (relative to repo root)
    ///   {commit}      - committed OID in the parent repo (short, 7 chars)
    ///   {commit_long} - committed OID (full 40 chars)
    ///   {head}        - current HEAD OID in the submodule workdir (short)
    ///   {head_long}   - current HEAD OID in the submodule workdir (full)
    ///   {branch}      - tracking branch from .gitmodules (if set)
    ///   {head_branch} - checked-out branch in the submodule workdir (empty if detached)
    ///   {status}      - submodule status (e.g. "modified content, new commits")
    ///
    /// Extra text inside braces is preserved and padded as a unit, e.g.
    /// {[name]} outputs [value] with alignment applied to the whole [value].
    /// Escape sequences: \n, \r, \t, \\, \{, \}.
    #[arg(short, long, verbatim_doc_comment)]
    pub format: Option<String>,
    /// Omit the header row
    #[arg(long)]
    pub no_header: bool,
    /// Skip the watch server and compute all fields locally via libgit2
    #[arg(long)]
    pub no_server: bool,
}

#[derive(Args, Debug)]
pub struct Prompt {
    /// The directory to query submodule status for
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// The log level to use for the requesting client
    #[arg(short, long)]
    pub log_level: Option<LogLevel>,
    /// Skip the watch server and compute status locally via libgit2
    #[arg(long)]
    pub no_server: bool,
    #[expect(
        clippy::doc_markdown,
        reason = "placeholder names render in clap help text"
    )]
    /// Format string with {placeholder} substitution.
    ///
    /// Available placeholders:
    ///   {dirty}       - submodules with modified or untracked content
    ///   {staged}      - submodules staged in the parent index
    ///   {new_commits} - submodules whose HEAD differs from the parent gitlink
    ///   {clean}       - submodules with no changes
    ///   {total}       - total number of submodules
    ///
    /// Default format: "{dirty} {staged} {new_commits} {clean} {total}"
    /// Escape sequences: \n, \r, \t, \\, \{, \}.
    #[arg(short, long, verbatim_doc_comment)]
    pub format: Option<String>,
    /// Timeout in milliseconds for the server response. Produces no output
    /// if exceeded.
    #[arg(short, long, default_value_t = 500)]
    pub timeout_ms: u64,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["watch", "w"])]
pub struct Start {
    /// The directory containing the repository's `.gitmodules` file
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
    /// Don't launch the server as a background process
    #[arg(short, long)]
    pub foreground: bool,
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
    #[error(transparent)]
    Debug(#[from] DebugError),
    #[error(transparent)]
    List(#[from] ListError),
    #[error(transparent)]
    Prompt(#[from] PromptError),
    #[error("Unable to determine home directory: {0}")]
    Home(#[from] etcetera::HomeDirError),
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
pub enum LogLevel {
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

impl DebugDump {
    /// Resolves the project path and executes the `debug` subcommand.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        if repo_kind != RepoKind::WithSubmodules {
            return Err(RunError::server_path(true_path));
        }
        Ok(debug(true_path.as_path())?)
    }
}

impl Reindex {
    /// Resolves the project path and executes the `reindex` subcommand.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        if repo_kind != RepoKind::WithSubmodules {
            return Err(RunError::server_path(true_path));
        }
        let display_progress = std::io::stderr().is_terminal();
        Ok(reindex(
            true_path.as_path(),
            self.replace_watchers,
            display_progress,
        )?)
    }
}

impl Stop {
    /// Resolves the project path and executes the `stop` subcommand.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        if repo_kind != RepoKind::WithSubmodules {
            return Err(RunError::server_path(true_path));
        }
        Ok(shutdown(true_path.as_path())?)
    }
}

impl Status {
    /// Resolves the project path and executes the `status` subcommand.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        let display_progress = std::io::stderr().is_terminal();
        let use_server = !self.no_server && repo_kind == RepoKind::WithSubmodules;
        Ok(status(
            true_path.as_path(),
            repo_kind,
            display_progress,
            use_server,
        )?)
    }
}

impl Prompt {
    /// Resolves the project path and executes the `prompt` subcommand.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        if repo_kind != RepoKind::WithSubmodules {
            return Ok(());
        }
        let timeout = Duration::from_millis(self.timeout_ms);
        prompt(
            true_path.as_path(),
            !self.no_server,
            self.format.as_deref(),
            timeout,
        )?;
        Ok(())
    }
}

impl List {
    /// Resolves the project path and executes the `list` subcommand.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        let no_server = self.no_server || repo_kind != RepoKind::WithSubmodules;
        Ok(list(
            true_path.as_path(),
            self.format.as_deref(),
            !self.no_header,
            no_server,
        )?)
    }
}

impl Start {
    /// Resolves the project path and executes the `start` subcommand.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self) -> RunResult<()> {
        let (true_path, repo_kind) = get_project_path(self.dir)?;
        if repo_kind != RepoKind::WithSubmodules {
            return Err(RunError::server_path(true_path));
        }

        if self.foreground {
            Ok(watch(true_path.as_path(), std::io::stderr().is_terminal())?)
        } else {
            let level_str = self.log_level.map(|l| l.to_string());
            spawn_daemon(&true_path, level_str.as_deref()).map_err(WatchError::from)?;
            Ok(())
        }
    }
}

/// Uses `path` if present or uses the current working directory. Ensures the resolved path
/// is a git repository or a child of one.
///
/// If found, returns the path to the repository and the kind of repository.
///
/// # Errors
///
/// Returns `Err` if the current working directory cannot be resolved (when
/// `path` is `None`), the path cannot be canonicalized, or no git repository
/// is found in the path or any of its ancestors.
pub fn get_project_path(path: Option<PathBuf>) -> RunResult<(PathBuf, RepoKind)> {
    let path = match path {
        Some(p) => p,
        None => current_dir().map_err(|error| RunError::ProjectPath {
            path: PathBuf::from("."),
            error,
        })?,
    };
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
            let has_gitmodules = dot_gitmodules_path.is_file();
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

#[cfg(test)]
mod tests {
    // NOTE: Some tests assume `TempDir` creates directories outside any git
    // repository (typically under /tmp). If the CI runner's temp directory is
    // inside a git checkout, ancestry-based tests may produce false positives.
    use super::*;
    use tempfile::TempDir;

    fn setup_git_dir(path: &std::path::Path) {
        std::fs::create_dir_all(path.join(".git")).unwrap();
    }

    fn setup_gitmodules(path: &std::path::Path) {
        std::fs::File::create(path.join(".gitmodules")).unwrap();
    }

    fn setup_git_file(path: &std::path::Path) {
        std::fs::File::create(path.join(".git")).unwrap();
    }

    #[test]
    fn repo_with_submodules() {
        let tmp = TempDir::new().unwrap();
        setup_git_dir(tmp.path());
        setup_gitmodules(tmp.path());

        let (path, kind) = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(path, dunce::canonicalize(tmp.path()).unwrap());
        assert_eq!(kind, RepoKind::WithSubmodules);
    }

    #[test]
    fn normal_repo() {
        let tmp = TempDir::new().unwrap();
        setup_git_dir(tmp.path());

        let (path, kind) = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(path, dunce::canonicalize(tmp.path()).unwrap());
        assert_eq!(kind, RepoKind::Normal);
    }

    #[test]
    fn submodule_detected_by_git_file() {
        let tmp = TempDir::new().unwrap();
        setup_git_file(tmp.path());

        let (path, kind) = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(path, dunce::canonicalize(tmp.path()).unwrap());
        assert_eq!(kind, RepoKind::Submodule);
    }

    #[test]
    fn child_dir_traverses_to_parent_repo() {
        let tmp = TempDir::new().unwrap();
        setup_git_dir(tmp.path());
        setup_gitmodules(tmp.path());

        let child = tmp.path().join("some").join("nested").join("dir");
        std::fs::create_dir_all(&child).unwrap();

        let (path, kind) = get_project_path(Some(child)).unwrap();
        assert_eq!(path, dunce::canonicalize(tmp.path()).unwrap());
        assert_eq!(kind, RepoKind::WithSubmodules);
    }

    #[test]
    fn nonexistent_path_errors() {
        let result = get_project_path(Some(PathBuf::from("/nonexistent/path/xyz")));
        assert!(result.is_err());
    }

    #[test]
    fn no_git_repo_in_ancestry_errors() {
        let tmp = TempDir::new().unwrap();
        // Empty directory, no .git anywhere
        let result = get_project_path(Some(tmp.path().to_path_buf()));
        assert!(result.is_err());
    }

    #[test]
    fn nested_submodule_with_own_submodules() {
        // .git file takes precedence over .gitmodules presence.
        let tmp = TempDir::new().unwrap();
        setup_git_file(tmp.path());
        setup_gitmodules(tmp.path());

        let (_, kind) = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(kind, RepoKind::Submodule);
    }

    #[test]
    fn gitmodules_as_directory_ignored() {
        let tmp = TempDir::new().unwrap();
        setup_git_dir(tmp.path());
        // .gitmodules exists but is a directory, not a file
        std::fs::create_dir_all(tmp.path().join(".gitmodules")).unwrap();

        let (_, kind) = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(kind, RepoKind::Normal);
    }
}
