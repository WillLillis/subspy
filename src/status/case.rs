//! Case-insensitive filesystem handling (`core.ignorecase`).
//!
//! Two things follow from a filesystem that ignores case, and both live here
//! so the folding policy is stated once:
//!
//! - [`CaseSensitivity`] is the policy itself, resolved once per status
//!   request by [`super::assemble_status`] and handed to every consumer, so
//!   the config is read at most once. [`super::pathspec`] needs it because
//!   the cwd's canonicalized casing can differ from the casing the index
//!   recorded, and git's own pathspec matching folds case.
//! - [`phantom_deletes`] handles the collision that case-folding creates:
//!   two index entries differing only in case (e.g. `Foo.txt` and `foo.txt`,
//!   committed on a case-sensitive FS) collapse to one working file on
//!   checkout. libgit2's diff pairs that file with one entry and reports the
//!   other as a spurious `WT_DELETED`. Git collapses the pair to a single
//!   status line, so subspy suppresses the phantom.
//!
//! Folding is ASCII-only. That matches git for most of its own path
//! comparisons and covers the Windows/macOS collisions that occur in
//! practice. Full Unicode case-folding is not attempted.

use std::borrow::Cow;

use rustc_hash::FxHashSet;

/// Whether path comparison folds ASCII case.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CaseSensitivity {
    #[default]
    Sensitive,
    /// `core.ignorecase` is set: compare folding ASCII case.
    Insensitive,
}

impl CaseSensitivity {
    /// Builds the setting from a repo's `core.ignorecase`.
    #[must_use]
    pub const fn from_ignore_case(ignore_case: bool) -> Self {
        if ignore_case {
            Self::Insensitive
        } else {
            Self::Sensitive
        }
    }

    /// Whether this setting folds case, for callers that can skip work
    /// entirely on a case-sensitive filesystem.
    #[must_use]
    pub const fn folds(self) -> bool {
        matches!(self, Self::Insensitive)
    }

    /// The hash/equality key for `path`: the path itself when case-sensitive,
    /// its ASCII-lowercased form otherwise. Borrows in the common case.
    #[must_use]
    pub fn fold_key(self, path: &[u8]) -> Cow<'_, [u8]> {
        match self {
            Self::Sensitive => Cow::Borrowed(path),
            Self::Insensitive => Cow::Owned(path.to_ascii_lowercase()),
        }
    }

    /// `haystack.starts_with(prefix)`, folding case when insensitive.
    #[must_use]
    pub fn starts_with(self, haystack: &[u8], prefix: &[u8]) -> bool {
        match self {
            Self::Sensitive => haystack.starts_with(prefix),
            Self::Insensitive => {
                haystack.len() >= prefix.len()
                    && haystack[..prefix.len()].eq_ignore_ascii_case(prefix)
            }
        }
    }
}

/// Byte paths of the phantom deletes in `non_submod`. A case-sensitive
/// filesystem cannot produce a collision, so `case` short-circuits before
/// the scan. Otherwise, a single pass over the statuses returns empty unless
/// something is worktree-deleted, so the common case allocates nothing.
pub(super) fn phantom_deletes(
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

    use pretty_assertions::{assert_eq, assert_ne};

    // -- CaseSensitivity --

    #[test]
    fn from_ignore_case_maps_the_config_flag() {
        assert_eq!(
            CaseSensitivity::from_ignore_case(true),
            CaseSensitivity::Insensitive
        );
        assert_eq!(
            CaseSensitivity::from_ignore_case(false),
            CaseSensitivity::Sensitive
        );
    }

    #[test]
    fn folds_reports_whether_case_is_ignored() {
        assert!(CaseSensitivity::Insensitive.folds());
        assert!(!CaseSensitivity::Sensitive.folds());
    }

    #[test]
    fn sensitive_fold_key_borrows_verbatim() {
        let key = CaseSensitivity::Sensitive.fold_key(b"Foo.txt");
        assert_eq!(&*key, b"Foo.txt");
        assert!(matches!(key, Cow::Borrowed(_)));
    }

    #[test]
    fn insensitive_fold_key_collapses_case_siblings() {
        let insensitive = CaseSensitivity::Insensitive;
        assert_eq!(&*insensitive.fold_key(b"Foo.TXT"), b"foo.txt");
        assert_eq!(
            insensitive.fold_key(b"Foo.txt"),
            insensitive.fold_key(b"foo.txt")
        );
        let sensitive = CaseSensitivity::Sensitive;
        assert_ne!(
            sensitive.fold_key(b"Foo.txt"),
            sensitive.fold_key(b"foo.txt")
        );
    }

    #[test]
    fn fold_key_leaves_non_ascii_bytes_alone() {
        // ASCII-only folding: a high-byte component round-trips untouched.
        let key = CaseSensitivity::Insensitive.fold_key(b"CAF\xc3\x89.txt");
        assert_eq!(&*key, b"caf\xc3\x89.txt");
    }

    #[test]
    fn sensitive_starts_with_is_exact() {
        let case = CaseSensitivity::Sensitive;
        assert!(case.starts_with(b"src/main.rs", b"src/"));
        assert!(!case.starts_with(b"Src/main.rs", b"src/"));
    }

    #[test]
    fn insensitive_starts_with_folds() {
        let case = CaseSensitivity::Insensitive;
        assert!(case.starts_with(b"Src/main.rs", b"src/"));
        assert!(case.starts_with(b"SRC/main.rs", b"src/"));
        assert!(!case.starts_with(b"other/main.rs", b"src/"));
    }

    #[test]
    fn starts_with_rejects_a_prefix_longer_than_the_path() {
        for case in [CaseSensitivity::Sensitive, CaseSensitivity::Insensitive] {
            assert!(!case.starts_with(b"src", b"src/"));
        }
    }

    #[test]
    fn empty_prefix_always_matches() {
        for case in [CaseSensitivity::Sensitive, CaseSensitivity::Insensitive] {
            assert!(case.starts_with(b"anything", b""));
        }
    }

    // -- phantom_deletes --

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
