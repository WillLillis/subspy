//! `SKIP_WORKTREE` index entries (sparse checkout, `git update-index
//! --skip-worktree`).
//!
//! libgit2 honors the flag when the file is present, reporting `CURRENT` for a
//! modified skip-worktree file just as git does. It does not honor it when the
//! file is absent, still reporting `WT_DELETED` where git reports nothing.
//! That is the state a sparse checkout leaves for every excluded path.
//!
//! Only the deletion bit is cleared: a skip-worktree entry can still carry a
//! real staged change, which git prints as `M `, not `MD`.

use git2::{IndexEntryExtendedFlag, Repository};
use rustc_hash::FxHashSet;

/// Whether `entry` carries `SKIP_WORKTREE`. Also used by the long format's
/// sparse-checkout header, which reports how many entries are flagged.
pub fn is_skip_worktree(entry: &git2::IndexEntry) -> bool {
    IndexEntryExtendedFlag::from_bits_truncate(entry.flags_extended).is_skip_worktree()
}

/// Byte paths of every index entry flagged `SKIP_WORKTREE`. An unreadable
/// index yields an empty set, leaving statuses untouched.
pub fn skip_worktree_paths(repo: &Repository) -> FxHashSet<Vec<u8>> {
    let Ok(index) = repo.index() else {
        return FxHashSet::default();
    };
    index
        .iter()
        .filter(is_skip_worktree)
        .map(|entry| entry.path)
        .collect()
}

/// Clears `WT_DELETED` from `st` when `path` is sparse-excluded.
pub(super) fn mask(
    st: git2::Status,
    path: &[u8],
    skip_worktree: &FxHashSet<Vec<u8>>,
) -> git2::Status {
    if skip_worktree.is_empty()
        || !st.contains(git2::Status::WT_DELETED)
        || !skip_worktree.contains(path)
    {
        return st;
    }
    st.difference(git2::Status::WT_DELETED)
}
