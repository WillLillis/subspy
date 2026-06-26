//! CLI argument definitions, subcommand dispatch, error types, and
//! repository path resolution.

use std::{env::current_dir, io, io::IsTerminal as _, path::PathBuf, time::Duration};

use clap::{Args, Subcommand, ValueEnum};
use thiserror::Error;

use crate::{
    DOT_GIT, DOT_GITMODULES, RepoKind,
    connection::watch_server::watch,
    debug::{DebugError, debug},
    git::{gitlink_points_at_worktree, submodule_modules_subpath},
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

#[derive(Args, Debug)]
#[command(visible_aliases = ["re", "r"])]
pub struct Reindex {
    /// The directory whose watcher should reindex
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
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
    /// Show untracked files. Bare `-u` is `-u=all`, matching git (absent is `normal`).
    #[arg(
        long = "untracked-files",
        short = 'u',
        value_name = "MODE",
        default_missing_value = "all",
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
    /// Append stash-count info: long format gets a `Your stash currently
    /// has N entr...` line; porcelain v2 with `--branch` gets `# stash N`.
    #[arg(long = "show-stash")]
    pub show_stash: bool,
}

#[derive(Args, Debug)]
pub struct Stop {
    /// The directory to shutdown a watcher for
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["dbg", "d"])]
pub struct DebugDump {
    /// The directory whose watcher state to dump
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
}

#[derive(Args, Debug)]
#[command(visible_aliases = ["ls", "l"])]
pub struct List {
    /// The directory to list submodule info for
    #[arg(index = 1)]
    pub dir: Option<PathBuf>,
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
    #[error("A watch server needs .git to be a directory, but it's a gitlink to an external git directory ({})", _0.display())]
    Gitlink(PathBuf),
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
        } else if self.null_terminate {
            // Bare `-z` with no explicit format implies porcelain v1, matching
            // `git status -z` (NUL-delimited machine output, not the human
            // long format). The shim builds a `Status` and runs it through here
            // too, so this also fixes `git status -z` via `subspy-git`.
            OutputFormat::Porcelain(PorcelainVersion::V1)
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
            && project.kind.server_eligible()
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
                show_stash: self.show_stash,
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
        if !project.kind.has_submodules() {
            return Ok(());
        }
        let timeout = Duration::from_millis(self.timeout_ms);
        let use_server = !self.no_server && project.kind.server_eligible();
        prompt(
            &project.repo_root,
            use_server,
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
        let no_server = self.no_server || !project.kind.server_eligible();
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
    /// Returns `repo_root` for a repo that can host a watch server: a top-level
    /// superproject (`WithSubmodules`) or a linked worktree of one
    /// (`WorktreeWithSubmodules`).
    ///
    /// # Errors
    ///
    /// Returns a `RunError` describing why the repo can't host a server: a
    /// gitlink to an external git dir ([`RunError::Gitlink`]), or anything else
    /// that isn't a non-recursive repo with a `.gitmodules` file
    /// ([`RunError::ProjectPath`]) -- including a worktree with no submodules.
    pub fn require_with_submodules(self) -> RunResult<PathBuf> {
        if self.kind.server_eligible() {
            return Ok(self.repo_root);
        }
        Err(match self.kind {
            RepoKind::OtherGitlink | RepoKind::OtherGitlinkWithSubmodules => {
                RunError::Gitlink(self.repo_root)
            }
            // The server-eligible kinds (WithSubmodules, WorktreeWithSubmodules)
            // are handled by the guard above; everything else -- including a
            // worktree with no submodules -- has nothing for a server to watch.
            RepoKind::Normal
            | RepoKind::WithSubmodules
            | RepoKind::Submodule
            | RepoKind::SubmoduleWithSubmodules
            | RepoKind::Worktree
            | RepoKind::WorktreeWithSubmodules => RunError::server_path(self.repo_root),
        })
    }
}

/// Classifies a repo from its `.git` gitlink contents, whether a `.gitmodules`
/// file is present, and whether the gitlink resolves to a linked worktree.
fn classify_repo(
    git_file_contents: Option<&[u8]>,
    has_gitmodules: bool,
    is_linked_worktree: bool,
) -> RepoKind {
    let Some(contents) = git_file_contents else {
        // `.git` is a real directory.
        return if has_gitmodules {
            RepoKind::WithSubmodules
        } else {
            RepoKind::Normal
        };
    };
    // A linked worktree is confirmed structurally (its gitdir has a `commondir`
    // marker), so that verdict wins over any path shape. Otherwise only the
    // submodule location convention (`.git/modules/`) is a reliable byte-level
    // signal. Anything else is an external/unrecognized gitdir.
    let (plain, with_submodules) = if is_linked_worktree {
        (RepoKind::Worktree, RepoKind::WorktreeWithSubmodules)
    } else if submodule_modules_subpath(contents).is_some() {
        (RepoKind::Submodule, RepoKind::SubmoduleWithSubmodules)
    } else {
        (RepoKind::OtherGitlink, RepoKind::OtherGitlinkWithSubmodules)
    };
    if has_gitmodules {
        with_submodules
    } else {
        plain
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
            // A `.git` *file* is a gitlink (a submodule, a linked worktree, or
            // some other external git dir); read its `gitdir:` pointer so
            // `classify_repo` can tell them apart (`None` means `.git` is a real
            // directory).
            let git_file_contents = if dot_git_path.is_file() {
                let contents =
                    std::fs::read(&dot_git_path).map_err(|error| RunError::ProjectPath {
                        path: dot_git_path.clone(),
                        error,
                    })?;
                Some(contents)
            } else {
                None
            };
            // Confirm a linked worktree structurally (via the `commondir` marker
            // in its gitdir)
            let is_linked_worktree = git_file_contents
                .as_deref()
                .is_some_and(|bytes| gitlink_points_at_worktree(bytes, current_path));
            let has_gitmodules = current_path.join(DOT_GITMODULES).is_file();
            let kind = classify_repo(
                git_file_contents.as_deref(),
                has_gitmodules,
                is_linked_worktree,
            );
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
        // A submodule gitlink: a `.git` *file* pointing into the parent's
        // `.git/modules/`.
        std::fs::write(path.join(".git"), "gitdir: ../.git/modules/sub\n").unwrap();
    }

    /// Fabricates a linked-worktree gitlink at `path`: a `.git` *file* pointing
    /// at a gitdir that carries the `commondir` marker git writes for every
    /// linked worktree.
    fn setup_worktree_git_file(path: &std::path::Path) {
        let gitdir = path.join("wt-gitdir");
        std::fs::create_dir_all(&gitdir).unwrap();
        std::fs::write(gitdir.join("commondir"), "../..\n").unwrap();
        std::fs::write(path.join(".git"), format!("gitdir: {}\n", gitdir.display())).unwrap();
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
        // A submodule (`.git` file) that itself has submodules (`.gitmodules`)
        // is its own superproject for status purposes, but not server-eligible.
        let tmp = TempDir::new().unwrap();
        setup_git_file(tmp.path());
        setup_gitmodules(tmp.path());

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.kind, RepoKind::SubmoduleWithSubmodules);
        assert!(project.kind.has_submodules());
        assert!(!project.kind.server_eligible());
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

    #[test]
    fn linked_worktree_detected_via_commondir() {
        // End-to-end: a `.git` gitlink whose target carries the `commondir`
        // marker is classified as a worktree by the on-disk probe.
        let tmp = TempDir::new().unwrap();
        setup_worktree_git_file(tmp.path());

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.kind, RepoKind::Worktree);
    }

    #[test]
    fn linked_worktree_with_submodules_is_server_eligible() {
        let tmp = TempDir::new().unwrap();
        setup_worktree_git_file(tmp.path());
        setup_gitmodules(tmp.path());

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.kind, RepoKind::WorktreeWithSubmodules);
        assert!(project.kind.server_eligible());
    }

    #[test]
    fn separate_git_dir_that_looks_like_worktree_is_not_served() {
        // A gitlink whose target *looks* like a worktree path
        // (`.../.git/worktrees/...`) but lacks the `commondir` marker is an
        // external gitdir, not a worktree -- so even with a `.gitmodules` it must
        // not become the server-eligible `WorktreeWithSubmodules`.
        let tmp = TempDir::new().unwrap();
        let fake_gitdir = tmp
            .path()
            .join("other")
            .join(".git")
            .join("worktrees")
            .join("proj");
        // A plain directory, deliberately WITHOUT a `commondir` file.
        std::fs::create_dir_all(&fake_gitdir).unwrap();
        std::fs::write(
            tmp.path().join(".git"),
            format!("gitdir: {}\n", fake_gitdir.display()),
        )
        .unwrap();
        setup_gitmodules(tmp.path());

        let project = get_project_path(Some(tmp.path().to_path_buf())).unwrap();
        assert_eq!(project.kind, RepoKind::OtherGitlinkWithSubmodules);
        assert!(!project.kind.server_eligible());
    }

    #[test]
    fn classify_repo_maps_all_shapes() {
        // `.git` is a directory (never a worktree gitlink):
        assert_eq!(classify_repo(None, false, false), RepoKind::Normal);
        assert_eq!(classify_repo(None, true, false), RepoKind::WithSubmodules);
        // gitlink pointing at a submodule gitdir (not a linked worktree):
        let submod = Some(b"gitdir: ../.git/modules/sub\n".as_slice());
        assert_eq!(classify_repo(submod, false, false), RepoKind::Submodule);
        assert_eq!(
            classify_repo(submod, true, false),
            RepoKind::SubmoduleWithSubmodules
        );
        // gitlink the caller confirmed (via the `commondir` marker) is a linked
        // worktree -- the verdict comes from `is_linked_worktree`, not the path:
        let wt = Some(b"gitdir: /main/.git/worktrees/wt\n".as_slice());
        assert_eq!(classify_repo(wt, false, true), RepoKind::Worktree);
        assert_eq!(
            classify_repo(wt, true, true),
            RepoKind::WorktreeWithSubmodules
        );
    }

    #[test]
    fn classify_repo_submodule_nested_in_worktree_is_submodule() {
        // A submodule inside a worktree points at `.git/worktrees/<wt>/modules/<name>`.
        // Its gitdir is an ordinary main gitdir (no `commondir`), so
        // `is_linked_worktree` is false and the inner `modules` makes it a submodule.
        let nested = Some(b"gitdir: /main/.git/worktrees/wt/modules/sub\n".as_slice());
        assert_eq!(classify_repo(nested, false, false), RepoKind::Submodule);
        assert_eq!(
            classify_repo(nested, true, false),
            RepoKind::SubmoduleWithSubmodules
        );
    }

    #[test]
    fn classify_repo_multi_component_submodule_name() {
        // A submodule at path `libs/foo` has gitdir `.git/modules/libs/foo`, so the
        // classifying `modules` isn't the leaf's immediate parent.
        let sub = Some(b"gitdir: ../../.git/modules/libs/foo\n".as_slice());
        assert_eq!(classify_repo(sub, false, false), RepoKind::Submodule);
    }

    #[test]
    fn classify_repo_coincidental_worktrees_component_is_other() {
        // A `git init --separate-git-dir` into a path with a coincidental
        // `worktrees` component is not a submodule (no `.git/modules/`) and has no
        // `commondir` marker, so it is an external gitdir, not a worktree.
        let separate = Some(b"gitdir: /home/me/worktrees/myrepo\n".as_slice());
        assert_eq!(
            classify_repo(separate, false, false),
            RepoKind::OtherGitlink
        );
        assert_eq!(
            classify_repo(separate, true, false),
            RepoKind::OtherGitlinkWithSubmodules
        );
        // A submodule literally named `worktrees/foo` is still a submodule:
        let sub = Some(b"gitdir: ../.git/modules/worktrees/foo\n".as_slice());
        assert_eq!(classify_repo(sub, false, false), RepoKind::Submodule);
    }

    #[test]
    fn classify_repo_separate_git_dir_under_worktrees_is_not_a_worktree() {
        // A `--separate-git-dir` whose gitdir *literally* contains
        // `.git/worktrees/` as path components used to be misclassified as a
        // worktree by the old substring scan. Worktree status is now confirmed
        // structurally (the caller's `commondir` probe), so with that verdict
        // false the gitlink is correctly an external gitdir -- even with a
        // `.gitmodules`, which previously made the bogus worktree server-eligible.
        let looks_like_worktree =
            Some(b"gitdir: /srv/other/.git/worktrees/proj/sep.git\n".as_slice());
        assert_eq!(
            classify_repo(looks_like_worktree, false, false),
            RepoKind::OtherGitlink
        );
        assert_eq!(
            classify_repo(looks_like_worktree, true, false),
            RepoKind::OtherGitlinkWithSubmodules
        );
    }

    #[test]
    fn classify_repo_separate_git_dir_under_modules_is_cosmetically_submodule() {
        // The submodule side stays a location-convention heuristic -- there is no
        // on-disk marker for submodule-ness -- so a separate gitdir literally
        // under a `.git/modules/` path is still reported as a submodule. Harmless:
        // it only changes which error a server command prints, never eligibility.
        let looks_like_submodule =
            Some(b"gitdir: /srv/other/.git/modules/proj/sep.git\n".as_slice());
        assert_eq!(
            classify_repo(looks_like_submodule, false, false),
            RepoKind::Submodule
        );
        assert!(!RepoKind::Submodule.server_eligible());
    }

    #[test]
    fn classify_repo_unrecognized_gitlink_is_other() {
        // An empty/garbage gitlink, or one pointing at an external git dir, is
        // `OtherGitlink`.
        assert_eq!(
            classify_repo(Some(b""), false, false),
            RepoKind::OtherGitlink
        );
        assert_eq!(
            classify_repo(Some(b"garbage"), true, false),
            RepoKind::OtherGitlinkWithSubmodules
        );
        let external = Some(b"gitdir: /var/lib/git/myrepo.git\n".as_slice());
        assert_eq!(
            classify_repo(external, false, false),
            RepoKind::OtherGitlink
        );
    }

    #[test]
    fn worktree_with_submodules_is_server_eligible() {
        // A linked worktree of a superproject can host a watch server.
        let worktree = ProjectPath {
            repo_root: PathBuf::from("/wt"),
            effective_cwd: PathBuf::from("/wt"),
            kind: RepoKind::WorktreeWithSubmodules,
        };
        assert_eq!(
            worktree.require_with_submodules().unwrap(),
            PathBuf::from("/wt")
        );
    }

    #[test]
    fn server_commands_reject_gitlink_and_bare_worktree() {
        // start/stop/reindex/debug gate on `require_with_submodules`.
        // An external (`--separate-git-dir`) gitlink is not served.
        let external = ProjectPath {
            repo_root: PathBuf::from("/ext"),
            effective_cwd: PathBuf::from("/ext"),
            kind: RepoKind::OtherGitlinkWithSubmodules,
        };
        assert!(matches!(
            external.require_with_submodules(),
            Err(RunError::Gitlink(_))
        ));
        // A worktree with no submodules has nothing for a server to watch.
        let bare_worktree = ProjectPath {
            repo_root: PathBuf::from("/wt"),
            effective_cwd: PathBuf::from("/wt"),
            kind: RepoKind::Worktree,
        };
        assert!(matches!(
            bare_worktree.require_with_submodules(),
            Err(RunError::ProjectPath { .. })
        ));
    }
}
