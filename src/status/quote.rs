//! Path quoting for porcelain output (non-`-z` mode only).
//!
//! Mirrors the behavior of `quote_path` in git's `quote.c` when called with
//! `QUOTE_PATH_QUOTE_SP` (which `git status` passes). Paths containing
//! whitespace, double-quote, backslash, control characters, or high bytes
//! get wrapped in `"..."` with C-style escapes for the special chars and
//! octal `\NNN` for everything else that needs escaping.
//!
//! Under `-z`, paths are emitted verbatim with NUL terminators - the
//! caller skips this module entirely in that case.

use std::borrow::Cow;
use std::fmt::Write as _;

/// Selects the trigger condition for quoting. Mirrors git's
/// `QUOTE_PATH_QUOTE_SP` flag: porcelain v2 (`Standard`) uses git's default
/// trigger set; porcelain v1 (`QuoteSpace`) additionally quotes paths
/// containing a space.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuoteMode {
    Standard,
    QuoteSpace,
}

/// Returns whether `path` contains any byte that requires C-style quoting
/// under the given `mode`.
pub fn needs_quoting(path: &str, mode: QuoteMode) -> bool {
    path.bytes()
        .any(|b| is_special_byte(b) || (mode == QuoteMode::QuoteSpace && b == b' '))
}

/// Wraps `path` in `"..."` with the appropriate C-style escapes. The caller
/// is expected to have checked `needs_quoting` first; calling this on a
/// path that doesn't need quoting still returns a valid (if redundant)
/// double-quoted string.
pub fn quote_path(path: &str) -> String {
    let mut out = String::with_capacity(path.len() + 2);
    out.push('"');
    for &b in path.as_bytes() {
        match b {
            b'\\' => out.push_str(r"\\"),
            b'"' => out.push_str("\\\""),
            0x07 => out.push_str(r"\a"),
            0x08 => out.push_str(r"\b"),
            b'\t' => out.push_str(r"\t"),
            b'\n' => out.push_str(r"\n"),
            0x0b => out.push_str(r"\v"),
            0x0c => out.push_str(r"\f"),
            b'\r' => out.push_str(r"\r"),
            b if b < 0x20 || b == 0x7f || b >= 0x80 => {
                let _ = write!(out, "\\{b:03o}");
            }
            // Remaining bytes are printable ASCII (including space) - emit verbatim.
            b => out.push(b as char),
        }
    }
    out.push('"');
    out
}

/// Quotes `path` if needed and we're in non-`-z` mode; otherwise returns the
/// input borrowed unchanged. This is the orchestration callers usually want.
pub fn maybe_quote(path: &str, null_terminate: bool, mode: QuoteMode) -> Cow<'_, str> {
    if null_terminate || !needs_quoting(path, mode) {
        Cow::Borrowed(path)
    } else {
        Cow::Owned(quote_path(path))
    }
}

const fn is_special_byte(b: u8) -> bool {
    matches!(b, b'"' | b'\\' | 0..=0x1f | 0x7f) || b >= 0x80
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_quoting_for_plain_path() {
        assert!(!needs_quoting("normal.txt", QuoteMode::Standard));
        assert!(!needs_quoting("src/bin/foo.rs", QuoteMode::Standard));
        assert!(!needs_quoting("with-dash_and.dots", QuoteMode::Standard));
    }

    #[test]
    fn space_triggers_quoting_only_in_quote_space_mode() {
        assert!(!needs_quoting("with space.txt", QuoteMode::Standard));
        assert!(needs_quoting("with space.txt", QuoteMode::QuoteSpace));
        assert_eq!(quote_path("with space.txt"), "\"with space.txt\"");
    }

    #[test]
    fn double_quote_triggers_quoting() {
        assert!(needs_quoting("a\"b.txt", QuoteMode::Standard));
        assert_eq!(quote_path("a\"b.txt"), r#""a\"b.txt""#);
    }

    #[test]
    fn backslash_triggers_quoting() {
        assert!(needs_quoting("a\\b.txt", QuoteMode::Standard));
        assert_eq!(quote_path("a\\b.txt"), r#""a\\b.txt""#);
    }

    #[test]
    fn named_control_chars() {
        assert_eq!(quote_path("a\tb"), r#""a\tb""#);
        assert_eq!(quote_path("a\nb"), r#""a\nb""#);
        assert_eq!(quote_path("a\rb"), r#""a\rb""#);
        assert_eq!(quote_path("a\x07b"), r#""a\ab""#);
        assert_eq!(quote_path("a\x08b"), r#""a\bb""#);
        assert_eq!(quote_path("a\x0bb"), r#""a\vb""#);
        assert_eq!(quote_path("a\x0cb"), r#""a\fb""#);
    }

    #[test]
    fn other_control_chars_as_octal() {
        assert_eq!(quote_path("a\x01b"), r#""a\001b""#);
        assert_eq!(quote_path("a\x1fb"), r#""a\037b""#);
        assert_eq!(quote_path("a\x7fb"), r#""a\177b""#);
    }

    #[test]
    fn high_bytes_as_octal() {
        // UTF-8 for "é" is 0xc3 0xa9 -> \303\251
        assert_eq!(quote_path("é"), r#""\303\251""#);
        // UTF-8 for "µ" is 0xc2 0xb5 -> \302\265
        assert_eq!(quote_path("µ"), r#""\302\265""#);
    }

    #[test]
    fn maybe_quote_passes_through_under_z() {
        assert_eq!(
            maybe_quote("with space.txt", true, QuoteMode::QuoteSpace),
            "with space.txt"
        );
        assert_eq!(
            maybe_quote("normal.txt", true, QuoteMode::Standard),
            "normal.txt"
        );
    }

    #[test]
    fn maybe_quote_quotes_when_needed_without_z() {
        // QuoteSpace (porcelain v1): space triggers quoting
        assert_eq!(
            maybe_quote("with space.txt", false, QuoteMode::QuoteSpace),
            "\"with space.txt\""
        );
        // Standard (porcelain v2): space alone does not trigger
        assert_eq!(
            maybe_quote("with space.txt", false, QuoteMode::Standard),
            "with space.txt"
        );
        // Standard with high byte: still quotes
        assert_eq!(
            maybe_quote("é.txt", false, QuoteMode::Standard),
            r#""\303\251.txt""#
        );
    }
}
