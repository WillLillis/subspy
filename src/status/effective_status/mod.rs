//! Where libgit2's `Status` disagrees with git's, and how to reconcile it.
//!
//! libgit2 models some index state loosely and reports rows git suppresses
//! outright. Each such divergence lives in one file here, behind a single
//! [`effective_status`] entry point.
//!
//! Invariant: once a row's status has been through [`effective_status`],
//! nothing reads `entry.status()` for that row again.
//! [`super::tracked::TrackedRow::Entry`] carries the corrected status so
//! renderers cannot reach past it.

mod case_collision;
mod skip_worktree;

use rustc_hash::FxHashSet;

pub(super) use case_collision::phantom_deletes;
pub(super) use skip_worktree::skip_worktree_paths;

/// Where libgit2's answer needs correcting for this status request.
#[derive(Debug, Default)]
pub struct Corrections {
    pub phantom_deletes: FxHashSet<Vec<u8>>,
    pub skip_worktree: FxHashSet<Vec<u8>>,
}

impl Corrections {
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.phantom_deletes.is_empty() && self.skip_worktree.is_empty()
    }
}

/// git's view of the entry libgit2 reported as `st` at `path`. `None` when git
/// renders no row for the path.
pub(super) fn effective_status(
    st: git2::Status,
    path: &[u8],
    corrections: &Corrections,
) -> Option<git2::Status> {
    if corrections.is_empty() {
        return Some(st);
    }
    if corrections.phantom_deletes.contains(path) {
        return None;
    }
    let st = skip_worktree::mask(st, path, &corrections.skip_worktree);
    (st != git2::Status::CURRENT).then_some(st)
}
