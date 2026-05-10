//! The `status` subcommand: displays submodule and working-tree status
//! in a format that mirrors `git status`.
//!
//! Output formats live in dedicated submodules:
//! - [`display`] for the human-readable layout
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
mod submodule;

#[cfg(test)]
mod porcelain_tests;

use clap::ValueEnum;
use git2::Repository;
use thiserror::Error;

use std::{io, path::Path};

use crate::{
    RepoKind,
    connection::{
        IpcError,
        client::{recv_status_response, send_status_request},
    },
    watch::LockFileError,
};

pub use submodule::{compute_local_statuses, deleted_submodule_paths};

/// Line terminator for porcelain output: NUL with `-z`, LF without.
const fn line_terminator(null_terminate: bool) -> &'static str {
    if null_terminate { "\0" } else { "\n" }
}

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
    pub porcelain: Option<PorcelainVersion>,
    pub null_terminate: bool,
    pub ignore_submodules: IgnoreSubmodules,
    pub untracked_files: UntrackedFiles,
    pub show_ignored: bool,
    pub branch: bool,
}

/// Retrieves and displays the statuses for the repository at `path`.
///
/// # Errors
///
/// Returns `Err` if statuses cannot be retrieved from the repository or watch server
pub fn status(
    root_path: &Path,
    repo_kind: RepoKind,
    display_progress: bool,
    use_server: bool,
    opts: OutputOpts,
) -> StatusResult<()> {
    let OutputOpts {
        porcelain,
        null_terminate,
        ignore_submodules,
        untracked_files,
        show_ignored,
        branch,
    } = opts;
    // Send IPC request early so the server starts processing while we do local work.
    let mut conn = if use_server {
        Some(send_status_request(root_path)?)
    } else {
        None
    };

    let repo = Repository::open(root_path)?;

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
    if repo_kind == RepoKind::WithSubmodules {
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
        None if repo_kind == RepoKind::WithSubmodules => compute_local_statuses(root_path, &repo)?,
        None => Vec::new(),
    };
    let submodule_statuses =
        submodule::apply_ignore_submodules(submodule_statuses, ignore_submodules);

    let mut out = io::BufWriter::with_capacity(64 * 1024, io::stdout().lock());
    match porcelain {
        Some(PorcelainVersion::V1) => porcelain_v1::display_porcelain_v1(
            &mut out,
            &repo,
            &non_submodule_statuses,
            &submodule_statuses,
            &deleted_submodule_paths,
            null_terminate,
            branch,
        )?,
        Some(PorcelainVersion::V2) => porcelain_v2::display_porcelain_v2(
            &mut out,
            &repo,
            &non_submodule_statuses,
            &submodule_statuses,
            &deleted_submodule_paths,
            null_terminate,
            branch,
        )?,
        // `branch` only governs porcelain output; non-porcelain mode always
        // shows branch info as part of the human-readable header, matching git.
        None => display::display_status(
            &mut out,
            &repo,
            &non_submodule_statuses,
            &submodule_statuses,
            &deleted_submodule_paths,
        )?,
    }

    Ok(())
}
