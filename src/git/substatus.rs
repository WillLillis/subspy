//! Submodule status computed without libgit2's submodule API.
//!
//! `Repository::submodule_status` resolves submodule configuration from the
//! worktree `.gitmodules` on every call, so a conflicted or otherwise
//! unparsable file fails every read even though no status fact lives in that
//! file.

use std::path::Path;

use git2::{FileMode, Repository, RepositoryOpenFlags, StatusOptions};
use thiserror::Error;

use crate::StatusSummary;

/// Failure of a submodule status computation.
#[derive(Error, Debug)]
pub enum SubstatusError {
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error("cannot compute submodule status for a bare repository")]
    BareRepository,
}

/// Sub-repository status flags that count as modified content
const MODIFIED_FLAGS: git2::Status = git2::Status::INDEX_NEW
    .union(git2::Status::INDEX_MODIFIED)
    .union(git2::Status::INDEX_DELETED)
    .union(git2::Status::INDEX_RENAMED)
    .union(git2::Status::INDEX_TYPECHANGE)
    .union(git2::Status::WT_MODIFIED)
    .union(git2::Status::WT_DELETED)
    .union(git2::Status::WT_RENAMED)
    .union(git2::Status::WT_TYPECHANGE)
    .union(git2::Status::CONFLICTED);

/// The unique root-relative paths recorded as gitlinks in `repo`'s index,
/// in index (path-sorted) order. This is the set of paths a submodule
/// status row can exist for.
///
/// Conflicted entries count through their stages, deduplicated. Staged deletions
/// (gitlinks only in HEAD) are deliberately absent, they are handled at display
/// time by `deleted_submodule_paths`.
///
/// # Errors
///
/// Returns `git2::Error` if the index cannot be read.
pub fn gitlink_paths(repo: &Repository) -> Result<Vec<String>, git2::Error> {
    let gitlink_mode = u32::from(FileMode::Commit);
    let index = repo.index()?;
    let mut paths: Vec<String> = Vec::new();
    for entry in index.iter() {
        if entry.mode != gitlink_mode {
            continue;
        }
        let Ok(path) = std::str::from_utf8(&entry.path) else {
            continue;
        };
        // Conflict stages repeat a path consecutively (the index is
        // path-sorted), so adjacent deduplication suffices.
        if paths.last().map(String::as_str) != Some(path) {
            paths.push(path.to_owned());
        }
    }

    Ok(paths)
}

/// Computes the [`StatusSummary`] for the submodule at root-relative `rel`.
///
/// Reads the superproject through `repo` (index and HEAD gitlinks) and the
/// submodule through its own repository (HEAD and a status walk), which
/// resolves only the submodule's own configuration.
///
/// An unmerged gitlink compares against its stage-2 (ours) entry, the
/// commit the worktree is based on. The conflict machinery owns those rows
/// at display time and computes the commit-changed flag itself, so only the
/// workdir-content bits of this value are consumed there.
///
/// # Errors
///
/// Returns [`SubstatusError::Git`] if the superproject index cannot be read or
/// the submodule's status walk fails, and [`SubstatusError::BareRepository`] when
/// `repo` has no worktree.
pub fn submodule_status(repo: &Repository, rel: &str) -> Result<StatusSummary, SubstatusError> {
    let commit_file_mode = u32::from(FileMode::Commit);

    let mut summary = StatusSummary::clean();
    let rel_path = Path::new(rel);

    let index = repo.index()?;
    let index_gitlink = index
        .get_path(rel_path, 0)
        .filter(|e| e.mode == commit_file_mode)
        .map(|e| e.id)
        .or_else(|| match conflicted_ours_gitlink(&index, rel) {
            Ok(oid) => oid,
            Err(error) => {
                log::warn!("failed to read stage-2 gitlink for submodule {rel:?}: {error}");
                None
            }
        });

    // Bind the tree so its entry can be inspected before it drops.
    let head_tree = head_tree(repo);
    let head_gitlink = head_tree
        .as_ref()
        .and_then(|t| t.get_path(rel_path).ok())
        .filter(|e| e.filemode() == i32::from(FileMode::Commit))
        .map(|e| e.id());

    match (head_gitlink, index_gitlink) {
        (None, Some(_)) => summary |= StatusSummary::STAGED_NEW,
        (Some(h), Some(i)) if h != i => summary |= StatusSummary::STAGED,
        _ => {}
    }

    let Some(workdir) = repo.workdir() else {
        return Err(SubstatusError::BareRepository);
    };
    let sub_workdir = workdir.join(rel_path);
    if !sub_workdir.is_dir() {
        return Ok(summary | StatusSummary::DELETED_WORKDIR);
    }

    // NO_SEARCH keeps an uninitialized (empty or repo-less) workdir from
    // resolving upward to the superproject itself. Failing to open is the
    // uninitialized state.
    let Ok(sub) = Repository::open_ext(
        &sub_workdir,
        RepositoryOpenFlags::NO_SEARCH,
        &[] as &[&std::ffi::OsStr],
    ) else {
        return Ok(summary);
    };

    // NEW_COMMITS: the submodule's checked-out HEAD differs from the gitlink
    // recorded in the superproject index.
    if let Some(recorded) = index_gitlink {
        match sub.head() {
            Ok(head) => match head.peel_to_commit() {
                Ok(commit) if commit.id() != recorded => summary |= StatusSummary::NEW_COMMITS,
                Ok(_) => {}
                Err(e) => log::warn!("failed to peel HEAD for submodule {rel:?} to a commit: {e}"),
            },
            Err(e) if e.code() == git2::ErrorCode::UnbornBranch => {}
            Err(e) => log::warn!("failed to read HEAD for submodule {rel:?}: {e}"),
        }
    }

    let mut opts = StatusOptions::new();
    opts.include_untracked(true)
        .recurse_untracked_dirs(false)
        .include_ignored(false);
    for entry in sub.statuses(Some(&mut opts))?.iter() {
        let status = entry.status();
        if status.intersects(MODIFIED_FLAGS) {
            summary |= StatusSummary::MODIFIED_CONTENT;
        }
        if status.intersects(git2::Status::WT_NEW) {
            summary |= StatusSummary::UNTRACKED_CONTENT;
        }
        if summary.contains(StatusSummary::MODIFIED_CONTENT | StatusSummary::UNTRACKED_CONTENT) {
            break;
        }
    }

    Ok(summary)
}

/// The stage-2 (ours) gitlink OID for `rel` when its index entry is
/// unmerged, found through the index's conflict records.
fn conflicted_ours_gitlink(
    index: &git2::Index,
    rel: &str,
) -> Result<Option<git2::Oid>, git2::Error> {
    if !index.has_conflicts() {
        return Ok(None);
    }
    for conflict in index.conflicts()? {
        let conflict = conflict?;
        let Some(ours) = conflict.our else { continue };
        if ours.path == rel.as_bytes() && ours.mode == u32::from(FileMode::Commit) {
            return Ok(Some(ours.id));
        }
    }

    Ok(None)
}

fn head_tree(repo: &Repository) -> Option<git2::Tree<'_>> {
    match repo.head() {
        Ok(head) => match head.peel_to_tree() {
            Ok(tree) => Some(tree),
            Err(error) => {
                log::warn!("failed to peel HEAD to a tree: {error}");
                None
            }
        },
        Err(error) if error.code() == git2::ErrorCode::UnbornBranch => None,
        Err(error) => {
            log::warn!("failed to read superproject HEAD: {error}");
            None
        }
    }
}
