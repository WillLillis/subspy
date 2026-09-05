//! The `core.ignorecase` folding policy.
//!
//! [`CaseSensitivity`] is resolved once per status request by
//! [`super::assemble_status`] and handed to every consumer, so the config is
//! read at most once. [`super::pathspec`] needs it because the cwd's
//! canonicalized casing can differ from the casing the index recorded, and
//! git's own pathspec matching folds case. The phantom delete this policy
//! creates is corrected in [`super::effective_status`].
//!
//! Folding is ASCII-only. That matches git for most of its own path
//! comparisons and covers the Windows/macOS collisions that occur in
//! practice. Full Unicode case-folding is not attempted.

use std::borrow::Cow;

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
}
