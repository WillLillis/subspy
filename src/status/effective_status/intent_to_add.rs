//! `INTENT_TO_ADD` index entries (`git add -N`).
//!
//! An intent-to-add entry is a normal index entry, mode 100644 pointing at the
//! empty blob, flagged `INTENT_TO_ADD`. Git hides it from the HEAD-to-index
//! diff, so the path reads as added in the worktree with nothing staged. Once
//! the file is gone git stops hiding it and reports a plain deletion against
//! the entry instead.
//!
//! libgit2 preserves the flag but never acts on it, reporting a staged add
//! plus a worktree modification. The resulting rows use `XY` combinations no
//! `git2::Status` can express (`.A`), so they are rebuilt as synthetic rows
//! rather than corrected in place.

use git2::{IndexEntryExtendedFlag, Repository};
use rustc_hash::FxHashSet;

/// Byte paths of every index entry flagged `INTENT_TO_ADD`. An unreadable
/// index yields an empty set, leaving statuses untouched.
pub fn intent_to_add_paths(repo: &Repository) -> FxHashSet<Vec<u8>> {
    let Ok(index) = repo.index() else {
        return FxHashSet::default();
    };
    index
        .iter()
        .filter(|entry| {
            IndexEntryExtendedFlag::from_bits_truncate(entry.flags_extended).is_intent_to_add()
        })
        .map(|entry| entry.path)
        .collect()
}
