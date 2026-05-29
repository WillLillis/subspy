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
    status::{
        IgnoreSubmodules, IgnoredFiles, OutputFormat, OutputOpts, PorcelainVersion, StatusError,
        UntrackedFiles, status,
    },
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
#[expect(
    clippy::struct_excessive_bools,
    reason = "fields mirror independent git-status flags"
)]
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
    /// Use porcelain machine-readable format (version 1 or 2)
    #[arg(long, value_name = "VERSION", default_missing_value = "1", num_args = 0..=1, conflicts_with = "short")]
    pub porcelain: Option<PorcelainVersion>,
    /// Use short format (`XY PATH`, colored)
    #[arg(short, long, conflicts_with = "porcelain")]
    pub short: bool,
    /// Terminate entries with NUL instead of newline
    #[arg(short = 'z')]
    pub null_terminate: bool,
    /// How to handle submodule changes in the output
    #[arg(
        long = "ignore-submodules",
        value_name = "WHEN",
        default_value = "none"
    )]
    pub ignore_submodules: IgnoreSubmodules,
    /// Show untracked files
    #[arg(
        long = "untracked-files",
        short = 'u',
        value_name = "MODE",
        default_missing_value = "normal",
        num_args = 0..=1
    )]
    pub untracked_files: Option<UntrackedFiles>,
    /// Show ignored files. Bare `--ignored` is `--ignored=traditional`.
    #[arg(
        long = "ignored",
        value_name = "MODE",
        default_missing_value = "traditional",
        num_args = 0..=1
    )]
    pub ignored: Option<IgnoredFiles>,
    /// Show branch and tracking info (short / porcelain modes;
    /// long format always shows branch info)
    #[arg(short = 'b', long)]
    pub branch: bool,
    /// Compute and display detailed ahead/behind upstream counts (default).
    #[arg(long = "ahead-behind", conflicts_with = "no_ahead_behind")]
    pub ahead_behind: bool,
    /// Skip the commit-graph walk and emit only the divergence
    /// relationship without specific counts.
    #[arg(long = "no-ahead-behind", conflicts_with = "ahead_behind")]
    pub no_ahead_behind: bool,
    /// Quote bytes `>= 0x80` in paths as octal escapes (git's default).
    /// Set to `false` to emit such bytes verbatim (matches
    /// `-c core.quotepath=false`).
    #[arg(long = "quote-path", default_value_t = true,
          action = clap::ArgAction::Set)]
    pub quote_path: bool,
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
        let repo_root = get_project_path(self.dir)?.require_with_submodules()?;
        Ok(debug(&repo_root)?)
    }
}

impl Reindex {
    /// Resolves the project path and executes the `reindex` subcommand.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self) -> RunResult<()> {
        let repo_root = get_project_path(self.dir)?.require_with_submodules()?;
        let display_progress = std::io::stderr().is_terminal();
        Ok(reindex(
            &repo_root,
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
        let repo_root = get_project_path(self.dir)?.require_with_submodules()?;
        Ok(shutdown(&repo_root)?)
    }
}

impl Status {
    /// Translates the mutually-exclusive `--short` / `--porcelain` flags
    /// to the internal `OutputFormat`. Clap rejects the
    /// `short && porcelain.is_some()` combination at parse time.
    const fn output_format(&self) -> OutputFormat {
        if self.short {
            OutputFormat::Short
        } else if let Some(v) = self.porcelain {
            OutputFormat::Porcelain(v)
        } else {
            OutputFormat::Long
        }
    }

    /// Resolves the project path and executes the `status` subcommand,
    /// writing output to `out`. CLI `main` passes a buffered stdout; the
    /// shim passes a `Vec<u8>` so it can discard partial output and fall
    /// back to real `git` if anything fails.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the project path is invalid or the operation fails.
    pub fn run(self, out: &mut impl io::Write) -> RunResult<()> {
        // `effective_cwd` is the canonicalized --dir argument (or the
        // process cwd if --dir was absent), reused as the baseline for
        // path-formatting in status output. Mirrors `git -C <path>`'s
        // semantics.
        let format = self.output_format();
        let project = get_project_path(self.dir)?;
        let display_progress = std::io::stderr().is_terminal();
        let use_server = !self.no_server
            && project.kind == RepoKind::WithSubmodules
            && self.ignore_submodules != IgnoreSubmodules::All;
        // Default is on; only the explicit `--no-ahead-behind` flips it off.
        // `--ahead-behind` is accepted for symmetry but is the default.
        let ahead_behind = !self.no_ahead_behind;
        Ok(status(
            &project,
            display_progress,
            use_server,
            OutputOpts {
                format,
                null_terminate: self.null_terminate,
                ignore_submodules: self.ignore_submodules,
                untracked_files: self.untracked_files.unwrap_or_default(),
                ignored_files: self.ignored.unwrap_or_default(),
                branch: self.branch,
                ahead_behind,
                quote_path: self.quote_path,
            },
            out,
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
        let project = get_project_path(self.dir)?;
        if project.kind != RepoKind::WithSubmodules {
            return Ok(());
        }
        let timeout = Duration::from_millis(self.timeout_ms);
        prompt(
            &project.repo_root,
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
        let project = get_project_path(self.dir)?;
        let no_server = self.no_server || project.kind != RepoKind::WithSubmodules;
        Ok(list(
            &project.repo_root,
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
        let repo_root = get_project_path(self.dir)?.require_with_submodules()?;

        if self.foreground {
            Ok(watch(&repo_root, std::io::stderr().is_terminal())?)
        } else {
            let level_str = self.log_level.map(|l| l.to_string());
            spawn_daemon(&repo_root, level_str.as_deref()).map_err(WatchError::from)?;
            Ok(())
        }
    }
}

/// Resolved project paths: the repo root, the canonical effective cwd
/// (the argument the caller provided or `current_dir()` if none), and
/// the kind of repository.
#[derive(Debug)]
pub struct ProjectPath {
    pub repo_root: PathBuf,
    pub effective_cwd: PathBuf,
    pub kind: RepoKind,
}

impl ProjectPath {
    /// Returns `repo_root` for top-level submodule projects, the only
    /// shape that admits a watch server.
    ///
    /// # Errors
    ///
    /// Returns `RunError::ProjectPath` when `kind` is not
    /// `RepoKind::WithSubmodules`.
    pub fn require_with_submodules(self) -> RunResult<PathBuf> {
        if self.kind == RepoKind::WithSubmodules {
            Ok(self.repo_root)
        } else {
            Err(RunError::server_path(self.repo_root))
        }
    }
}

/// Uses `path` if present or uses the current working directory. Ensures the resolved path
/// is a git repository or a child of one.
///
/// # Errors
///
/// Returns `Err` if the current working directory cannot be resolved (when
/// `path` is `None`), the path cannot be canonicalized, or no git repository
/// is found in the path or any of its ancestors.
pub fn get_project_path(path: Option<PathBuf>) -> RunResult<ProjectPath> {
    let path = match path {
        Some(p) => p,
        None => current_dir().map_err(|error| RunError::ProjectPath {
            path: PathBuf::from("."),
            error,
        })?,
    };
    let effective_cwd = dunce::canonicalize(&path).map_err(|error| RunError::ProjectPath {
        path: path.clone(),
        error,
    })?;

    let mut current_path = effective_cwd.as_path();
    loop {
        let dot_git_path = current_path.join(DOT_GIT);
        if dot_git_path.exists() {
            let kind = if dot_git_path.is_file() {
                RepoKind::Submodule
            } else if current_path.join(DOT_GITMODULES).is_file() {
                RepoKind::WithSubmodules
            } else {
                RepoKind::Normal
            };
            return Ok(ProjectPath {
                repo_root: current_path.to_path_buf(),
                effective_cwd,
                kind,
            });
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

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.repo_root, dunce::canonicalize(tmp.path()).unwrap());
        assert_eq!(project.kind, RepoKind::WithSubmodules);
    }

    #[test]
    fn normal_repo() {
        let tmp = TempDir::new().unwrap();
        setup_git_dir(tmp.path());

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.repo_root, dunce::canonicalize(tmp.path()).unwrap());
        assert_eq!(project.kind, RepoKind::Normal);
    }

    #[test]
    fn submodule_detected_by_git_file() {
        let tmp = TempDir::new().unwrap();
        setup_git_file(tmp.path());

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.repo_root, dunce::canonicalize(tmp.path()).unwrap());
        assert_eq!(project.kind, RepoKind::Submodule);
    }

    #[test]
    fn child_dir_traverses_to_parent_repo() {
        let tmp = TempDir::new().unwrap();
        setup_git_dir(tmp.path());
        setup_gitmodules(tmp.path());

        let child = tmp.path().join("some").join("nested").join("dir");
        std::fs::create_dir_all(&child).unwrap();

        let project = get_project_path(Some(child.clone())).unwrap();
        assert_eq!(project.repo_root, dunce::canonicalize(tmp.path()).unwrap());
        assert_eq!(project.effective_cwd, dunce::canonicalize(&child).unwrap());
        assert_eq!(project.kind, RepoKind::WithSubmodules);
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

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.kind, RepoKind::Submodule);
    }

    #[test]
    fn gitmodules_as_directory_ignored() {
        let tmp = TempDir::new().unwrap();
        setup_git_dir(tmp.path());
        // .gitmodules exists but is a directory, not a file
        std::fs::create_dir_all(tmp.path().join(".gitmodules")).unwrap();

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.kind, RepoKind::Normal);
    }
}
