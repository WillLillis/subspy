//! The `status` subcommand: displays submodule and working-tree status
//! in a format that mirrors `git status`.
//!
//! Output formats live in dedicated submodules:
//! - [`display`] for the long-format (default, human-readable) layout
//! - [`short`] for `git status -s` / `--short`
//! - [`porcelain_v1`] and [`porcelain_v2`] for the machine-readable formats
//!
//! Helper modules:
//! - [`xy_line`]: shared `XY PATH` writer for short + porcelain v1
//! - [`header`]: branch/upstream/operation-state header rendering (long format)
//! - [`conflict`]: shared conflict-index parsing
//! - [`submodule`]: submodule status computation and filtering

mod conflict;
mod display;
mod header;
mod porcelain_v1;
mod porcelain_v2;
mod quote;
mod relativize;
mod short;
mod submodule;
mod xy_line;

#[cfg(test)]
mod tests;

use clap::ValueEnum;
use git2::Repository;
use thiserror::Error;

use std::{borrow::Cow, io, path::Path};

use crate::{
    RepoKind, StatusSummary,
    cli::ProjectPath,
    connection::{
        IpcError,
        client::{recv_status_response, send_status_request},
    },
    watch::LockFileError,
};

pub use relativize::Relativizer;
pub use submodule::{SubmoduleChanges, SubmoduleRename, compute_local_statuses, submodule_changes};

pub type StatusResult<T> = Result<T, StatusError>;

#[derive(Error, Debug)]
pub enum StatusError {
    #[error(transparent)]
    Ipc(#[from] IpcError),
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error(transparent)]
    LockFile(#[from] LockFileError),
    #[error(transparent)]
    IO(#[from] io::Error),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum PorcelainVersion {
    #[value(name = "1", alias = "v1")]
    V1,
    #[value(name = "2", alias = "v2")]
    V2,
}

/// Which renderer to use for status output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputFormat {
    /// Default `git status` output (the long, human-readable layout).
    #[default]
    Long,
    /// `git status -s` / `--short` (terse `XY PATH` with colors).
    Short,
    /// `git status --porcelain[=v1|v2]` (stable machine-readable).
    Porcelain(PorcelainVersion),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum IgnoreSubmodules {
    #[default]
    #[value(name = "none")]
    None,
    #[value(name = "untracked")]
    Untracked,
    #[value(name = "dirty")]
    Dirty,
    #[value(name = "all")]
    All,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum UntrackedFiles {
    #[default]
    #[value(name = "normal")]
    Normal,
    #[value(name = "no")]
    No,
    #[value(name = "all")]
    All,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum IgnoredFiles {
    /// Don't show ignored entries (git's default when `--ignored` is absent).
    #[default]
    #[value(name = "no")]
    No,
    /// Show ignored files and directory names (git's default for bare
    /// `--ignored` or `--ignored=traditional`).
    #[value(name = "traditional")]
    Traditional,
    // git's `--ignored=matching` mode is intentionally absent: it shows
    // paths that directly match an ignore pattern, while libgit2's
    // `recurse_ignored_dirs(true)` enumerates contents of ignored
    // directories regardless of pattern. The two diverge on common
    // cases (e.g. a `dir/` gitignore line), so the shim forwards
    // `--ignored=matching` to real git, and the subspy CLI rejects it
    // rather than producing approximate output.
}

/// Output format and filtering options passed through from git-status-compatible flags.
#[derive(Debug, Clone, Copy)]
#[expect(clippy::struct_excessive_bools, reason = "matches git")]
pub struct OutputOpts {
    pub format: OutputFormat,
    pub null_terminate: bool,
    pub ignore_submodules: IgnoreSubmodules,
    pub untracked_files: UntrackedFiles,
    pub ignored_files: IgnoredFiles,
    pub branch: bool,
    /// Compute and display detailed upstream ahead/behind counts. When
    /// false, long format reports only divergence (no specific counts)
    /// and porcelain v2 emits `# branch.ab +? -?`.
    pub ahead_behind: bool,
    /// `core.quotepath` (default `true`). When `false`, bytes `>= 0x80`
    /// in paths are emitted verbatim instead of as octal escapes.
    pub quote_path: bool,
}

/// Porcelain-specific format flags (`-z`, `--branch`, `--ahead-behind`,
/// `core.quotepath`).
#[derive(Debug, Clone, Copy)]
#[expect(clippy::struct_excessive_bools, reason = "matches git")]
pub struct PorcelainOpts {
    pub null_terminate: bool,
    pub branch: bool,
    pub ahead_behind: bool,
    pub quote_path: bool,
}

/// The set of status entries to render.
pub struct StatusEntries<'a> {
    pub non_submod: &'a git2::Statuses<'a>,
    pub submodules: &'a [(String, StatusSummary)],
    pub deleted_submodules: &'a [String],
    pub renamed_submodules: &'a [SubmoduleRename],
}

/// Builds the `git2::StatusOptions` used by production and tests. Kept
/// in one place so the two stay in sync.
#[must_use]
pub fn build_status_options(opts: OutputOpts, repo_kind: RepoKind) -> git2::StatusOptions {
    let mut st_opts = git2::StatusOptions::new();
    match opts.untracked_files {
        UntrackedFiles::Normal => {
            st_opts
                .include_untracked(true)
                .recurse_untracked_dirs(false);
        }
        UntrackedFiles::All => {
            st_opts.include_untracked(true).recurse_untracked_dirs(true);
        }
        UntrackedFiles::No => {
            st_opts.include_untracked(false);
        }
    }
    match opts.ignored_files {
        IgnoredFiles::No => {
            st_opts.include_ignored(false);
        }
        IgnoredFiles::Traditional => {
            st_opts.include_ignored(true).recurse_ignored_dirs(false);
        }
    }
    // The repo was just opened, so the index is already fresh from disk.
    // Skip the redundant stat-cache refresh pass.
    st_opts.no_refresh(true);

    // Match git's default `diff.renames=true` so renames render as
    // `R old -> new` rather than separate `D old`/`A new` entries.
    st_opts
        .renames_head_to_index(true)
        .renames_index_to_workdir(true)
        .renames_from_rewrites(true);

    // Ignore submodules _only_ if we are the top level, in which case
    // submodule statuses are provided by the watch server or computed
    // locally outside `repo.statuses`.
    if repo_kind == RepoKind::WithSubmodules {
        st_opts.exclude_submodules(true);
    }
    st_opts
}

/// Opens the repository, runs the shared status-assembly pipeline, and
/// hands the result to `render`.
///
/// Pipeline: `git2::statuses`, `submodule_changes`, ignore-submodules
/// masking, rename-new filter, relativizer, `StatusEntries`. The
/// `submodule_statuses` closure is the caller's hook for supplying
/// submodule-level statuses -- production receives them over IPC,
/// tests fall back to `compute_local_statuses`.
///
/// # Errors
///
/// Propagates `StatusError` from the closures and from intermediate
/// libgit2 calls.
pub fn assemble_status<R>(
    project: &ProjectPath,
    opts: OutputOpts,
    submodule_statuses: impl FnOnce(&Repository) -> StatusResult<Vec<(String, StatusSummary)>>,
    render: impl FnOnce(&Repository, &StatusEntries<'_>, &Relativizer<'_>) -> StatusResult<R>,
) -> StatusResult<R> {
    let repo = Repository::open(&project.repo_root)?;
    let mut so = build_status_options(opts, project.kind);
    let non_submod = repo.statuses(Some(&mut so))?;

    let submod_changes = if opts.ignore_submodules == IgnoreSubmodules::All {
        SubmoduleChanges::default()
    } else {
        submodule_changes(&repo)?
    };

    let raw_submods = submodule_statuses(&repo)?;
    let mut submods = submodule::apply_ignore_submodules(raw_submods, opts.ignore_submodules);
    submodule::filter_rename_new_paths(&mut submods, &submod_changes.renamed);

    // Path-formatting policy by output mode:
    // - Porcelain v1: repo-root-relative regardless of cwd.
    // - Porcelain v2: cwd-relative without `-z`, repo-root-relative
    //   with `-z` (where paths are stable identifiers).
    // - Short and long: cwd-relative.
    let cwd_rel = cwd_relative_to_repo(&project.repo_root, &project.effective_cwd);
    let rel = relativize::Relativizer::new(&cwd_rel, opts.quote_path);

    let entries = StatusEntries {
        non_submod: &non_submod,
        submodules: &submods,
        deleted_submodules: &submod_changes.deleted,
        renamed_submodules: &submod_changes.renamed,
    };

    render(&repo, &entries, &rel)
}

/// Retrieves and displays the statuses for the repository described by
/// `project`. Paths in the output are reported relative to
/// [`ProjectPath::effective_cwd`], matching `git -C <path> status`.
///
/// # Errors
///
/// Returns `Err` if statuses cannot be retrieved from the repository or watch server
pub fn status(
    project: &ProjectPath,
    display_progress: bool,
    use_server: bool,
    opts: OutputOpts,
    out: &mut impl io::Write,
) -> StatusResult<()> {
    // Send IPC request early so the server starts processing while we
    // do local work.
    let mut conn = if use_server {
        Some(send_status_request(&project.repo_root)?)
    } else {
        None
    };

    let porcelain_opts = PorcelainOpts {
        null_terminate: opts.null_terminate,
        branch: opts.branch,
        ahead_behind: opts.ahead_behind,
        quote_path: opts.quote_path,
    };
    let format = opts.format;
    let ahead_behind = opts.ahead_behind;
    let ignore_submodules = opts.ignore_submodules;
    let kind = project.kind;

    assemble_status(
        project,
        opts,
        |repo| match conn {
            Some(ref mut c) => Ok(recv_status_response(c, display_progress)?.0),
            None if kind == RepoKind::WithSubmodules
                && ignore_submodules != IgnoreSubmodules::All =>
            {
                compute_local_statuses(&project.repo_root, repo)
            }
            None => Ok(Vec::new()),
        },
        |repo, entries, rel| {
            match format {
                OutputFormat::Long => {
                    display::display_status(out, repo, entries, rel, ahead_behind)?;
                }
                OutputFormat::Short => {
                    short::display_short(out, repo, entries, rel, porcelain_opts)?;
                }
                OutputFormat::Porcelain(PorcelainVersion::V1) => {
                    porcelain_v1::display_porcelain_v1(out, repo, entries, porcelain_opts)?;
                }
                OutputFormat::Porcelain(PorcelainVersion::V2) => {
                    porcelain_v2::display_porcelain_v2(out, repo, entries, rel, porcelain_opts)?;
                }
            }
            Ok(())
        },
    )
}

/// Returns `effective_cwd` expressed relative to `repo_root`, as a
/// forward-slash separated str suitable for [`relativize::Relativizer::new`].
///
/// Returns `Cow::Borrowed("")` when `effective_cwd == repo_root` or
/// when the prefix relationship can't be computed - both cases produce a
/// no-op `Relativizer`.
fn cwd_relative_to_repo<'a>(repo_root: &Path, effective_cwd: &'a Path) -> Cow<'a, str> {
    effective_cwd
        .strip_prefix(repo_root)
        .ok()
        .and_then(|p| p.to_str())
        .map_or(Cow::Borrowed(""), |s| {
            if cfg!(windows) && s.contains('\\') {
                Cow::Owned(s.replace('\\', "/"))
            } else {
                Cow::Borrowed(s)
            }
        })
}

/// Line terminator for porcelain output: NUL with `-z`, LF without.
const fn line_terminator(null_terminate: bool) -> &'static str {
    if null_terminate { "\0" } else { "\n" }
}

/// Returns the branch name HEAD points at, intended for the unborn-branch
/// case (empty repo, no commits) where `repo.head()` returned `Err` but
/// `HEAD` still points at some `refs/heads/<branch>`.
fn unborn_branch_name<'a>(head: &'a git2::Reference<'_>) -> Option<&'a str> {
    head.symbolic_target()
        .ok()
        .flatten()
        .map(|t| t.strip_prefix("refs/heads/").unwrap_or(t))
}

/// Resolves the configured upstream short name (e.g. `origin/master`) for
/// the branch whose full ref name is `local_ref_name`, without requiring
/// the remote-tracking ref to exist. Used to distinguish "no upstream
/// configured" from "configured but gone" once `Branch::upstream()` has
/// already failed.
fn configured_upstream_short_name(repo: &Repository, local_ref_name: &str) -> Option<String> {
    let buf = repo.branch_upstream_name(local_ref_name).ok()?;
    let full = buf.as_str().ok()?;
    Some(
        full.strip_prefix("refs/remotes/")
            .unwrap_or(full)
            .to_string(),
    )
}
