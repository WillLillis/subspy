//! Streams repo-relative paths out as cwd-relative paths.
//!
//! Subspy stores paths relative to the repo root (canonical form for
//! IPC and submodule indexing). Real git's `status` output reports
//! paths relative to the invocation cwd (or `git -C <path>`'s target).
//! When the two differ - the user ran subspy from a subdirectory or
//! passed `--dir` - we need to rewrite the path before emitting it so
//! the output matches git.
//!
//! Path-formatting policy by output mode:
//! - Long, short, porcelain v2 (without `-z`): cwd-relative through
//!   this module.
//! - Porcelain v1: repo-root-relative regardless of cwd; goes through
//!   `Relativizer::new("")` as a no-op pass-through so the shared
//!   `xy_line` writer can use a single code path.
//! - Porcelain v2 with `-z`: repo-root-relative (paths are stable
//!   identifiers in `-z` mode).
//!
//! [`Relativizer`] streams the rewrite allocation-free: the path is
//! split into "N `../` prefixes" + "the suffix of the input path after
//! the common prefix", each piece written directly to the caller's
//! writer.

use std::io;

use super::quote::{QuoteMode, needs_quoting, write_escaped};

/// Converts repo-relative paths to cwd-relative paths at emission time.
///
/// Constructed once per `status::status` call with the cwd's path
/// relative to the repo root (empty when cwd == repo root, in which
/// case streaming is a single pass-through write).
pub struct Relativizer<'a> {
    cwd_rel: &'a str,
    /// Number of components in `cwd_rel` (i.e. count of `/` plus one for
    /// a non-empty value, zero for an empty value). Cached so each
    /// `write_to` call doesn't reslice.
    cwd_components: usize,
}

impl<'a> Relativizer<'a> {
    /// Builds a relativizer from `cwd_rel`, the path of the effective
    /// cwd relative to the repo root. Pass `""` when the cwd is the
    /// repo root itself.
    #[must_use]
    pub fn new(cwd_rel: &'a str) -> Self {
        let cwd_components = if cwd_rel.is_empty() {
            0
        } else {
            cwd_rel.bytes().filter(|&b| b == b'/').count() + 1
        };
        Self {
            cwd_rel,
            cwd_components,
        }
    }

    /// Streams the cwd-relative form of `path` into `out` with
    /// [`QuoteMode::Standard`] C-style quoting (git's default
    /// `core.quotePath=true`).
    ///
    /// # Errors
    ///
    /// Returns any `io::Error` raised by writing.
    pub fn write_to<W: io::Write>(&self, out: &mut W, path: &str) -> io::Result<()> {
        self.write_quoted(out, path, false, QuoteMode::Standard)
    }

    /// Streams the cwd-relative form of `path` with porcelain quoting
    /// applied. Wraps in `"..."` with C-style escapes when the remaining
    /// portion of the path trips [`needs_quoting`] under `mode`. The
    /// `../` prefix is plain ASCII and never triggers quoting on its
    /// own, but is wrapped inside the same `"..."` when the suffix does.
    ///
    /// Under `-z` (`null_terminate=true`) both quoting and
    /// relativization are skipped - the path is emitted as stored
    /// (repo-root-relative, byte-verbatim). This matches `git status
    /// --porcelain=2 -z`'s contract of emitting paths as stable
    /// identifiers, separated only by NUL.
    ///
    /// # Errors
    ///
    /// Returns any `io::Error` raised by writing.
    pub fn write_quoted<W: io::Write>(
        &self,
        out: &mut W,
        path: &str,
        null_terminate: bool,
        mode: QuoteMode,
    ) -> io::Result<()> {
        if null_terminate {
            return out.write_all(path.as_bytes());
        }
        let (ups, remaining) = self.split(path);
        let need_quote = needs_quoting(remaining, mode);

        if need_quote {
            out.write_all(b"\"")?;
        }
        for _ in 0..ups {
            out.write_all(b"../")?;
        }
        if need_quote {
            write_escaped(out, remaining)?;
        } else {
            out.write_all(remaining.as_bytes())?;
        }
        if need_quote {
            out.write_all(b"\"")?;
        }
        Ok(())
    }

    /// Returns `(ups, remaining)`: the count of `..` to prepend, and
    /// the slice of `path` after the common prefix with `cwd_rel`.
    /// Walks both paths once, no allocations.
    fn split<'p>(&self, path: &'p str) -> (usize, &'p str) {
        if self.cwd_components == 0 {
            return (0, path);
        }

        let mut path_cursor = 0;
        let mut matched = 0;

        for cwd_part in self.cwd_rel.split('/') {
            let rest = &path[path_cursor..];
            let (path_part, after) = rest
                .find('/')
                .map_or((rest, path.len()), |i| (&rest[..i], path_cursor + i + 1));
            if path_part == cwd_part {
                path_cursor = after;
                matched += 1;
            } else {
                break;
            }
        }

        (self.cwd_components - matched, &path[path_cursor..])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formatted(cwd_rel: &str, path: &str) -> String {
        let rel = Relativizer::new(cwd_rel);
        let mut out: Vec<u8> = Vec::new();
        rel.write_to(&mut out, path).unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn empty_cwd_rel_passes_through() {
        // cwd == repo root: paths emit verbatim.
        assert_eq!(formatted("", "src/main.rs"), "src/main.rs");
    }

    #[test]
    fn path_inside_cwd_strips_prefix() {
        // cwd = repo/src, file = src/main.rs -> "main.rs"
        assert_eq!(formatted("src", "src/main.rs"), "main.rs");
    }

    #[test]
    fn path_above_cwd_gets_dotdot() {
        // cwd = repo/src, file = README.md -> "../README.md"
        assert_eq!(formatted("src", "README.md"), "../README.md");
    }

    #[test]
    fn path_in_sibling_directory() {
        // cwd = repo/src, file = tests/foo.rs -> "../tests/foo.rs"
        assert_eq!(formatted("src", "tests/foo.rs"), "../tests/foo.rs");
    }

    #[test]
    fn cwd_two_levels_deep() {
        // cwd = repo/a/b, file = a/b/c/d.rs -> "c/d.rs"
        assert_eq!(formatted("a/b", "a/b/c/d.rs"), "c/d.rs");
        // cwd = repo/a/b, file = a/c/d.rs -> "../c/d.rs"
        assert_eq!(formatted("a/b", "a/c/d.rs"), "../c/d.rs");
        // cwd = repo/a/b, file = README.md -> "../../README.md"
        assert_eq!(formatted("a/b", "README.md"), "../../README.md");
    }

    #[test]
    fn partial_prefix_match_does_not_treat_as_common() {
        // cwd = repo/src, file = srctests/foo.rs (NOT inside src).
        // Should NOT match "src" as a prefix of "srctests" component.
        assert_eq!(formatted("src", "srctests/foo.rs"), "../srctests/foo.rs");
    }

    #[test]
    fn path_is_exactly_cwd_rel() {
        // Pathological: a status entry whose path equals the cwd. Not
        // expected in real use (files aren't directories) but make sure
        // we don't panic or produce nonsense.
        assert_eq!(formatted("src", "src"), "");
    }

    #[test]
    fn cwd_components_count_matches_split_count() {
        assert_eq!(Relativizer::new("").cwd_components, 0);
        assert_eq!(Relativizer::new("a").cwd_components, 1);
        assert_eq!(Relativizer::new("a/b").cwd_components, 2);
        assert_eq!(Relativizer::new("a/b/c").cwd_components, 3);
    }

    #[test]
    fn write_to_applies_standard_quoting_to_high_bytes() {
        // High-byte (UTF-8 e-acute) triggers Standard quoting per git's
        // default `core.quotePath=true`.
        assert_eq!(formatted("", "caf\u{00e9}.txt"), r#""caf\303\251.txt""#);
    }

    #[test]
    fn write_to_applies_standard_quoting_with_subdir_prefix() {
        // `../` prefix from subdir relativization sits inside the quotes
        // when the suffix needs escaping.
        assert_eq!(
            formatted("src", "caf\u{00e9}.txt"),
            r#""../caf\303\251.txt""#
        );
    }

    #[test]
    fn write_to_does_not_quote_plain_ascii() {
        // Regression: the quoting switch must not wrap unremarkable paths.
        assert_eq!(formatted("", "main.rs"), "main.rs");
        assert_eq!(formatted("src", "src/main.rs"), "main.rs");
    }
}
