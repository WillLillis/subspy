//! Case-collision phantom deletes on a `core.ignorecase` filesystem.
//!
//! Two index entries differing only in case (e.g. `Foo.txt` and `foo.txt`,
//! committed on a case-sensitive filesystem) collapse to one working file on
//! checkout. libgit2 pairs that file with one entry and reports the other as a
//! spurious `WT_DELETED`. Git collapses the collision to a single line, so the
//! phantom row is dropped whole and the surviving sibling renders instead.

use rustc_hash::FxHashSet;

use crate::status::case::CaseSensitivity;

/// Byte paths of the phantom deletes in `non_submod`. A case-sensitive
/// filesystem cannot produce a collision, so `case` short-circuits before the
/// scan. Otherwise a single pass returns empty unless something is
/// worktree-deleted, so the common case allocates nothing.
pub fn phantom_deletes(
    non_submod: &git2::Statuses<'_>,
    case: CaseSensitivity,
) -> FxHashSet<Vec<u8>> {
    if !case.folds()
        || !non_submod
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
    phantom_deletes_from(&entries, case)
}

/// Pure core: given `(path, is_worktree_delete)` for each tracked entry, returns
/// the delete paths whose case-folded name also belongs to a present entry.
fn phantom_deletes_from(entries: &[(Vec<u8>, bool)], case: CaseSensitivity) -> FxHashSet<Vec<u8>> {
    let present: FxHashSet<Vec<u8>> = entries
        .iter()
        .filter(|(_, deleted)| !deleted)
        .map(|(path, _)| case.fold_key(path).into_owned())
        .collect();
    entries
        .iter()
        .filter(|(_, deleted)| *deleted)
        .filter(|(path, _)| present.contains(&*case.fold_key(path)))
        .map(|(path, _)| path.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;

    fn entry(path: &str, deleted: bool) -> (Vec<u8>, bool) {
        (path.as_bytes().to_vec(), deleted)
    }

    /// Collisions only arise on a case-insensitive filesystem, which is how
    /// production always reaches `phantom_deletes_from`.
    fn phantoms(entries: &[(Vec<u8>, bool)]) -> FxHashSet<Vec<u8>> {
        phantom_deletes_from(entries, CaseSensitivity::Insensitive)
    }

    #[test]
    fn drops_delete_with_present_case_sibling() {
        // Foo.txt survives checkout (reported modified); foo.txt is the phantom.
        let phantom = phantoms(&[entry("foo.txt", true), entry("Foo.txt", false)]);
        assert_eq!(phantom.len(), 1);
        assert!(phantom.contains(b"foo.txt".as_slice()));
    }

    #[test]
    fn keeps_real_delete_without_sibling() {
        let phantom = phantoms(&[entry("gone.txt", true), entry("other.txt", false)]);
        assert!(phantom.is_empty());
    }

    #[test]
    fn keeps_both_when_both_deleted() {
        // The file is genuinely gone under both cases; neither is phantom.
        let phantom = phantoms(&[entry("foo.txt", true), entry("Foo.txt", true)]);
        assert!(phantom.is_empty());
    }

    #[test]
    fn case_sensitive_never_reports_a_phantom() {
        // Same input as `drops_delete_with_present_case_sibling`: on a
        // case-sensitive FS the two paths are distinct files, so the delete
        // is real.
        let phantom = phantom_deletes_from(
            &[entry("foo.txt", true), entry("Foo.txt", false)],
            CaseSensitivity::Sensitive,
        );
        assert!(phantom.is_empty());
    }
}
