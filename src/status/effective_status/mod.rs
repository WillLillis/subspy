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
mod intent_to_add;
mod skip_worktree;

use rustc_hash::FxHashSet;

pub(super) use skip_worktree::is_skip_worktree;

/// Where libgit2's answer needs correcting for this status request.
#[derive(Debug, Default)]
pub struct Corrections {
    pub phantom_deletes: FxHashSet<Vec<u8>>,
    pub skip_worktree: FxHashSet<Vec<u8>>,
    /// Rebuilt as synthetic rows rather than corrected in place, so
    /// [`effective_status`] leaves these alone.
    pub intent_to_add: FxHashSet<Vec<u8>>,
}

impl Corrections {
    /// Scans only for the corrections the reported statuses make reachable.
    /// The delete-clearing ones need a `WT_DELETED`, and libgit2 always reports
    /// an intent-to-add entry as a staged add, so an index scan is skipped
    /// entirely unless the corresponding bit appears.
    pub(super) fn detect(
        repo: &git2::Repository,
        non_submod: &git2::Statuses<'_>,
        case: super::CaseSensitivity,
    ) -> Self {
        let (mut worktree_delete, mut index_new) = (false, false);
        for entry in non_submod.iter() {
            let st = entry.status();
            worktree_delete |= st.contains(git2::Status::WT_DELETED);
            index_new |= st.contains(git2::Status::INDEX_NEW);
        }
        Self {
            phantom_deletes: if worktree_delete {
                case_collision::phantom_deletes(non_submod, case)
            } else {
                FxHashSet::default()
            },
            skip_worktree: if worktree_delete {
                skip_worktree::skip_worktree_paths(repo)
            } else {
                FxHashSet::default()
            },
            intent_to_add: if index_new {
                intent_to_add::intent_to_add_paths(repo)
            } else {
                FxHashSet::default()
            },
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.phantom_deletes.is_empty()
            && self.skip_worktree.is_empty()
            && self.intent_to_add.is_empty()
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
