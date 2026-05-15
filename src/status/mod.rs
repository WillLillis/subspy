//! The `status` subcommand: displays submodule and working-tree status
//! in a format that mirrors `git status`.
//!
//! Output formats live in dedicated submodules:
//! - [`display`] for the long-format (default, human-readable) layout
//! - [`porcelain_v1`] and [`porcelain_v2`] for the machine-readable formats
//!
//! Helper modules:
//! - [`header`]: branch/upstream/operation-state header rendering
//! - [`conflict`]: shared conflict-index parsing for porcelain entries
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
mod long_tests;
#[cfg(test)]
mod porcelain_tests;
#[cfg(test)]
mod short_tests;
#[cfg(test)]
mod test_fixtures;

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

pub use submodule::{compute_local_statuses, deleted_submodule_paths};

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

/// Output format and filtering options passed through from git-status-compatible flags.
#[derive(Debug, Clone, Copy)]
pub struct OutputOpts {
    pub format: OutputFormat,
    pub null_terminate: bool,
    pub ignore_submodules: IgnoreSubmodules,
    pub untracked_files: UntrackedFiles,
    pub show_ignored: bool,
    pub branch: bool,
}

/// Porcelain-specific format flags (`-z` and `--branch`).
#[derive(Debug, Clone, Copy)]
pub struct PorcelainOpts {
    pub null_terminate: bool,
    pub branch: bool,
}

/// The set of status entries to render.
pub struct StatusEntries<'a> {
    pub non_submod: &'a git2::Statuses<'a>,
    pub submodules: &'a [(String, StatusSummary)],
    pub deleted_submodules: &'a [String],
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
) -> StatusResult<()> {
    let OutputOpts {
        format,
        null_terminate,
        ignore_submodules,
        untracked_files,
        show_ignored,
        branch,
    } = opts;
    // Send IPC request early so the server starts processing while we do local work.
    let mut conn = if use_server {
        Some(send_status_request(&project.repo_root)?)
    } else {
        None
    };

    let repo = Repository::open(&project.repo_root)?;

    let mut opts = git2::StatusOptions::new();
    match untracked_files {
        UntrackedFiles::Normal => {
            opts.include_untracked(true).recurse_untracked_dirs(false);
        }
        UntrackedFiles::All => {
            opts.include_untracked(true).recurse_untracked_dirs(true);
        }
        UntrackedFiles::No => {
            opts.include_untracked(false);
        }
    }
    // The repo was just opened, so the index is already fresh from disk.
    // Skip the redundant stat-cache refresh pass.
    opts.include_ignored(show_ignored).no_refresh(true);

    // Match git's default `diff.renames=true` so renames render as
    // `R old -> new` rather than separate `D old`/`A new` entries.
    opts.renames_head_to_index(true)
        .renames_index_to_workdir(true)
        .renames_from_rewrites(true);

    // Ignore submodules _only_ if we are the top level, in which case submodule statuses
    // are provided by the watch server or computed locally below.
    if project.kind == RepoKind::WithSubmodules {
        opts.exclude_submodules(true);
    }

    let non_submodule_statuses = repo.statuses(Some(&mut opts))?;
    let deleted_submodule_paths = if ignore_submodules == IgnoreSubmodules::All {
        Vec::new()
    } else {
        deleted_submodule_paths(&repo)?
    };

    let submodule_statuses = match conn {
        Some(ref mut c) => recv_status_response(c, display_progress)?.0,
        None if project.kind == RepoKind::WithSubmodules => {
            compute_local_statuses(&project.repo_root, &repo)?
        }
        None => Vec::new(),
    };
    let submodule_statuses =
        submodule::apply_ignore_submodules(submodule_statuses, ignore_submodules);

    // Path-formatting policy by output mode:
    // - Porcelain v1: repo-root-relative regardless of cwd.
    // - Porcelain v2: cwd-relative without `-z`, repo-root-relative
    //   with `-z` (where paths are stable identifiers).
    // - Short and long: cwd-relative.
    let cwd_rel = cwd_relative_to_repo(&project.repo_root, &project.effective_cwd);
    let rel = relativize::Relativizer::new(&cwd_rel);

    let entries = StatusEntries {
        non_submod: &non_submodule_statuses,
        submodules: &submodule_statuses,
        deleted_submodules: &deleted_submodule_paths,
    };
    let porcelain_opts = PorcelainOpts {
        null_terminate,
        branch,
    };

    let mut out = io::BufWriter::with_capacity(64 * 1024, io::stdout().lock());
    match format {
        OutputFormat::Long => display::display_status(&mut out, &repo, &entries, &rel)?,
        OutputFormat::Short => {
            short::display_short(&mut out, &repo, &entries, &rel, porcelain_opts)?;
        }
        OutputFormat::Porcelain(PorcelainVersion::V1) => {
            porcelain_v1::display_porcelain_v1(&mut out, &repo, &entries, porcelain_opts)?;
        }
        OutputFormat::Porcelain(PorcelainVersion::V2) => {
            porcelain_v2::display_porcelain_v2(&mut out, &repo, &entries, &rel, porcelain_opts)?;
        }
    }

    Ok(())
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
        .map(|t| t.strip_prefix("refs/heads/").unwrap_or(t))
}
