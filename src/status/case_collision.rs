//! Detects libgit2's case-collision phantom deletes so subspy can drop them,
//! matching git.
//!
//! On a case-insensitive filesystem (`core.ignorecase`), two index entries that
//! differ only in case (e.g. `Foo.txt` and `foo.txt`, committed on a
//! case-sensitive FS) collapse to one working file on checkout. libgit2's diff
//! pairs that file with one entry and reports the other as a spurious
//! `WT_DELETED`; git instead collapses the pair to a single status line. We
//! suppress the phantom: a worktree-delete whose case-folded path also belongs
//! to a present (non-deleted) entry.

use rustc_hash::FxHashSet;

/// Byte paths of the phantom deletes in `non_submod`. Returns empty after a
/// single scan when nothing is worktree-deleted, so the common case allocates
/// nothing. Callers gate this on `core.ignorecase`; a case-sensitive FS cannot
/// produce a collision.
pub(super) fn phantom_deletes(non_submod: &git2::Statuses<'_>) -> FxHashSet<Vec<u8>> {
    if !non_submod
        .iter()
        .any(|e| e.status().contains(git2::Status::WT_DELETED))
    {
        return FxHashSet::default();
    }
    // `path_bytes()` borrows the (temporary) entry, so materialize owned paths
    // before the case-folded comparison.
    let entries: Vec<(Vec<u8>, bool)> = non_submod
        .iter()
        .map(|e| {
            (
                e.path_bytes().to_vec(),
                e.status().contains(git2::Status::WT_DELETED),
            )
        })
        .collect();
    phantom_deletes_from(&entries)
}

/// Pure core: given `(path, is_worktree_delete)` for each tracked entry, returns
/// the delete paths whose case-folded name also belongs to a present entry.
///
/// Case-folding is ASCII, matching the common Windows/macOS collision; full
/// Unicode case-folding is not attempted.
fn phantom_deletes_from(entries: &[(Vec<u8>, bool)]) -> FxHashSet<Vec<u8>> {
    let present: FxHashSet<Vec<u8>> = entries
        .iter()
        .filter(|(_, deleted)| !deleted)
        .map(|(path, _)| path.to_ascii_lowercase())
        .collect();
    entries
        .iter()
        .filter(|(_, deleted)| *deleted)
        .filter(|(path, _)| present.contains(&path.to_ascii_lowercase()))
        .map(|(path, _)| path.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::phantom_deletes_from;

    fn entry(path: &str, deleted: bool) -> (Vec<u8>, bool) {
        (path.as_bytes().to_vec(), deleted)
    }

    #[test]
    fn drops_delete_with_present_case_sibling() {
        // Foo.txt survives checkout (reported modified); foo.txt is the phantom.
        let phantom = phantom_deletes_from(&[entry("foo.txt", true), entry("Foo.txt", false)]);
        assert_eq!(phantom.len(), 1);
        assert!(phantom.contains(b"foo.txt".as_slice()));
    }

    #[test]
    fn keeps_real_delete_without_sibling() {
        let phantom = phantom_deletes_from(&[entry("gone.txt", true), entry("other.txt", false)]);
        assert!(phantom.is_empty());
    }

    #[test]
    fn keeps_both_when_both_deleted() {
        // The file is genuinely gone under both cases; neither is phantom.
        let phantom = phantom_deletes_from(&[entry("foo.txt", true), entry("Foo.txt", true)]);
        assert!(phantom.is_empty());
    }
}
