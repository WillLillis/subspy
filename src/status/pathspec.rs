//! The cwd pathspec (`git status -- .`): restricts output to the subtree
//! rooted at the effective cwd.
//!
//! Tools that poll status for a directory pane pass `.` so the result is
//! scoped to what they display. At the repo root the pathspec selects
//! everything and is a no-op; from a subdirectory it is a real filter.
//!
//! Two behaviors of git's filter fall out of *where* it is applied rather
//! than from this module:
//!
//! - **Renames split.** git matches the pathspec before rename detection, so
//!   a rename that crosses the boundary degrades to the half that survives
//!   (`R a/f -> b/f` becomes `D a/f` from `a/`, `A b/f` from `b/`). Subspy
//!   pairs renames itself in [`super::tracked`], so filtering the raw
//!   add/delete set there reproduces this without a special case.
//! - **Paths stay repo-root-relative in porcelain v1.** The pathspec chooses
//!   *which* rows are emitted, never how they are spelled, so
//!   [`super::relativize`] is unaffected.
//!
//! What this module deliberately does *not* model is git descending into a
//! collapsed untracked directory to reach the pathspec: from `untr/sub`,
//! git reports `?? untr/sub/` where libgit2 only ever reports `?? untr/`.
//! Reproducing it means deciding whether the cwd subtree holds any
//! non-ignored file (an empty one yields no row at all).
//! [`PathFilter::contains_cwd`] detects that situation so
//! [`super::assemble_status`] can decline the request; the shim then forwards
//! to real git, which is always correct.
//!
//! Collapsed ignored directories do not descend either, but Git retains the
//! ancestor row (`!! ign/` stays `!! ign/` from `ign/x/y`).
//! [`PathFilter::keeps_ignored`] mirrors that behavior.
//!
//! # Path encoding
//!
//! Both sides of the comparison are `/`-separated repo-relative bytes, on
//! every platform. libgit2 reports entry paths in git's on-disk form, which
//! is always `/`; the cwd side is normalized by
//! [`super::os_path_to_slash_bytes`], which rewrites `\` to `/` on Windows.
//! [`super::relativize::Relativizer`] matches paths against the same
//! convention.
//!
//! Case handling comes from [`CaseSensitivity`], resolved once per status
//! request by [`super::assemble_status`]; this module never consults
//! `core.ignorecase` itself.

use super::case::CaseSensitivity;

/// What subset of the repo a status request covers.
///
/// Kept private so [`PathFilter::subtree`] is the only way to build a
/// `Subtree`, which lets it enforce the variant's invariant: the prefix is
/// non-empty and ends in `/`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Scope<'a> {
    /// No pathspec, or one that selects the whole repo (`-- .` at the root).
    All,
    /// Repo-relative cwd, always non-empty and `/`-terminated. The trailing
    /// slash makes `starts_with` a component-wise test, so a sibling like
    /// `srctests/` never matches the prefix `src/`.
    Subtree(&'a [u8]),
}

/// Restricts status rows to the effective cwd's subtree.
#[derive(Clone, Copy)]
pub struct PathFilter<'a> {
    scope: Scope<'a>,
    case: CaseSensitivity,
}

impl<'a> PathFilter<'a> {
    /// A filter that keeps every row.
    #[must_use]
    pub const fn all() -> Self {
        Self {
            scope: Scope::All,
            case: CaseSensitivity::Sensitive,
        }
    }

    /// Restricts to the subtree rooted at `cwd_rel`, the repo-relative cwd
    /// *without* a trailing separator (as [`super::cwd_relative_to_repo`]
    /// produces it).
    ///
    /// An empty `cwd_rel` means the cwd is the repo root, where `-- .`
    /// selects the whole repo; that collapses to [`PathFilter::all`] so the
    /// hot path skips the per-row check entirely.
    ///
    /// Takes `cwd_rel_slash`, a buffer the caller owns holding `cwd_rel`
    /// with `/` appended, so the filter can stay allocation-free and `Copy`.
    #[must_use]
    pub fn subtree(cwd_rel_slash: &'a [u8], case: CaseSensitivity) -> Self {
        debug_assert!(
            cwd_rel_slash.is_empty() || cwd_rel_slash.last() == Some(&b'/'),
            "subtree prefix must be `/`-terminated",
        );
        if cwd_rel_slash.is_empty() {
            return Self::all();
        }
        Self {
            scope: Scope::Subtree(cwd_rel_slash),
            case,
        }
    }

    /// Whether the filter admits every path, so callers can skip per-row work.
    #[must_use]
    pub const fn is_all(&self) -> bool {
        matches!(self.scope, Scope::All)
    }

    /// Whether a row for `path` survives the pathspec.
    ///
    /// A collapsed directory entry that *is* the cwd (`untr/sub/` from
    /// `untr/sub`) matches its own prefix and is kept, as git does.
    #[must_use]
    pub fn keeps(&self, path: &[u8]) -> bool {
        match self.scope {
            Scope::All => true,
            Scope::Subtree(prefix) => self.case.starts_with(path, prefix),
        }
    }

    /// Whether `path` is a collapsed directory entry strictly *containing*
    /// the cwd. This is the case this module can't render faithfully.
    ///
    /// Only libgit2's collapsed untracked/ignored directory rows end in `/`,
    /// so tracked entries never trip this.
    #[must_use]
    pub fn contains_cwd(&self, path: &[u8]) -> bool {
        match self.scope {
            Scope::All => false,
            Scope::Subtree(prefix) => {
                path.last() == Some(&b'/')
                    && path.len() < prefix.len()
                    && self.case.starts_with(prefix, path)
            }
        }
    }

    /// Whether an ignored row survives the cwd pathspec.
    ///
    /// Git keeps a collapsed ignored directory that contains the selected cwd
    /// rather than descending to the pathspec boundary, so ancestor rows are
    /// visible here even though ordinary rows use [`Self::keeps`].
    #[must_use]
    pub fn keeps_ignored(&self, path: &[u8]) -> bool {
        self.keeps(path) || self.contains_cwd(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn subtree(prefix: &[u8]) -> PathFilter<'_> {
        PathFilter::subtree(prefix, CaseSensitivity::Sensitive)
    }

    #[test]
    fn all_keeps_everything() {
        let f = PathFilter::all();
        assert!(f.is_all());
        assert!(f.keeps(b"src/main.rs"));
        assert!(f.keeps(b"README.md"));
        assert!(!f.contains_cwd(b"untr/"));
    }

    #[test]
    fn empty_prefix_collapses_to_all() {
        // cwd == repo root: `-- .` selects the whole repo.
        let f = subtree(b"");
        assert!(f.is_all());
        assert!(f.keeps(b"anything/at/all"));
    }

    #[test]
    fn subtree_keeps_only_descendants() {
        let f = subtree(b"src/");
        assert!(!f.is_all());
        assert!(f.keeps(b"src/main.rs"));
        assert!(f.keeps(b"src/deep/x.rs"));
        assert!(!f.keeps(b"README.md"));
        assert!(!f.keeps(b"tests/t.rs"));
    }

    #[test]
    fn sibling_sharing_a_name_prefix_is_excluded() {
        // The trailing `/` is what makes this component-wise: `srctests/`
        // must not be treated as living under `src/`.
        let f = subtree(b"src/");
        assert!(!f.keeps(b"srctests/foo.rs"));
    }

    #[test]
    fn nested_cwd_matches_git_scoping() {
        let f = subtree(b"a/b/");
        assert!(f.keeps(b"a/b/c.rs"));
        assert!(!f.keeps(b"a/c.rs"));
        assert!(!f.keeps(b"a/bb/c.rs"));
    }

    #[test]
    fn collapsed_dir_equal_to_cwd_is_kept_not_flagged() {
        // `?? untr/sub/` viewed from `untr/sub`: git emits it verbatim.
        let f = subtree(b"untr/sub/");
        assert!(f.keeps(b"untr/sub/"));
        assert!(!f.contains_cwd(b"untr/sub/"));
    }

    #[test]
    fn collapsed_ancestor_dir_is_flagged() {
        // `?? untr/` viewed from `untr/sub`: git would descend and report
        // `?? untr/sub/`; we decline instead.
        let f = subtree(b"untr/sub/");
        assert!(f.contains_cwd(b"untr/"));
        assert!(!f.keeps(b"untr/"));

        let deep = subtree(b"untr/sub/deep/");
        assert!(deep.contains_cwd(b"untr/"));
        assert!(deep.contains_cwd(b"untr/sub/"));
    }

    #[test]
    fn collapsed_ignored_ancestor_is_kept() {
        let f = subtree(b"ign/sub/");
        assert!(f.keeps_ignored(b"ign/"));
        assert!(f.keeps_ignored(b"ign/sub/file"));
        assert!(!f.keeps_ignored(b"other/"));
    }

    #[test]
    fn file_entry_never_counts_as_containing_cwd() {
        // Only collapsed directory rows end in `/`; a tracked file that
        // happens to share the prefix is just filtered normally.
        let f = subtree(b"untr/sub/");
        assert!(!f.contains_cwd(b"untr"));
        assert!(!f.contains_cwd(b"untr/file.txt"));
    }

    #[test]
    fn unrelated_dir_is_not_an_ancestor() {
        let f = subtree(b"src/");
        assert!(!f.contains_cwd(b"other/"));
        assert!(!f.contains_cwd(b"srctests/"));
    }

    // -- case folding (`core.ignorecase`) --

    #[test]
    fn case_sensitive_rejects_a_casing_mismatch() {
        let f = subtree(b"Src/");
        assert!(!f.keeps(b"src/main.rs"));
    }

    #[test]
    fn case_insensitive_accepts_a_casing_mismatch() {
        // On `core.ignorecase`, an index recording `src/` must still match a
        // cwd canonicalized to `Src`, as git's pathspec matching does.
        let f = PathFilter::subtree(b"Src/", CaseSensitivity::Insensitive);
        assert!(f.keeps(b"src/main.rs"));
        assert!(f.keeps(b"SRC/main.rs"));
        assert!(!f.keeps(b"other/main.rs"));
    }

    #[test]
    fn case_insensitive_still_respects_component_boundaries() {
        let f = PathFilter::subtree(b"src/", CaseSensitivity::Insensitive);
        assert!(!f.keeps(b"SRCTESTS/foo.rs"));
    }

    #[test]
    fn case_insensitive_ancestor_detection_folds_too() {
        let f = PathFilter::subtree(b"Untr/Sub/", CaseSensitivity::Insensitive);
        assert!(f.contains_cwd(b"untr/"));
    }
}
