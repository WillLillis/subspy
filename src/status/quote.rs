//! Path quoting for porcelain output (non-`-z` mode only).
//!
//! Mirrors the behavior of `quote_path` in git's `quote.c` when called with
//! `QUOTE_PATH_QUOTE_SP` (which `git status` passes). Paths containing
//! whitespace, double-quote, backslash, control characters, or high bytes
//! get wrapped in `"..."` with C-style escapes for the special chars and
//! octal `\NNN` for everything else that needs escaping.
//!
//! Under `-z`, paths are emitted verbatim with NUL terminators - the
//! caller skips quoting entirely in that case.

use std::io;

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

/// Writes `path` to `out` with C-style escapes applied per byte. The
/// caller is responsible for emitting the surrounding `"..."` and for
/// having checked [`needs_quoting`] when appropriate.
///
/// # Errors
///
/// Returns any `io::Error` raised by writing.
pub fn write_escaped<W: io::Write>(out: &mut W, path: &str) -> io::Result<()> {
    for &b in path.as_bytes() {
        match b {
            b'\\' => out.write_all(br"\\")?,
            b'"' => out.write_all(b"\\\"")?,
            0x07 => out.write_all(br"\a")?,
            0x08 => out.write_all(br"\b")?,
            b'\t' => out.write_all(br"\t")?,
            b'\n' => out.write_all(br"\n")?,
            0x0b => out.write_all(br"\v")?,
            0x0c => out.write_all(br"\f")?,
            b'\r' => out.write_all(br"\r")?,
            b if b < 0x20 || b == 0x7f || b >= 0x80 => write!(out, "\\{b:03o}")?,
            // Remaining bytes are printable ASCII (including space) - emit verbatim.
            b => out.write_all(&[b])?,
        }
    }
    Ok(())
}

const fn is_special_byte(b: u8) -> bool {
    matches!(b, b'"' | b'\\' | 0..=0x1f | 0x7f) || b >= 0x80
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Convenience wrapper: write into a `Vec<u8>` so test assertions can
    /// compare strings directly. The output is always ASCII so UTF-8
    /// validation is infallible.
    fn quoted(path: &str) -> String {
        let mut out: Vec<u8> = Vec::with_capacity(path.len() + 2);
        out.push(b'"');
        write_escaped(&mut out, path).unwrap();
        out.push(b'"');
        String::from_utf8(out).unwrap()
    }

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
        assert_eq!(quoted("with space.txt"), "\"with space.txt\"");
    }

    #[test]
    fn double_quote_triggers_quoting() {
        assert!(needs_quoting("a\"b.txt", QuoteMode::Standard));
        assert_eq!(quoted("a\"b.txt"), r#""a\"b.txt""#);
    }

    #[test]
    fn backslash_triggers_quoting() {
        assert!(needs_quoting("a\\b.txt", QuoteMode::Standard));
        assert_eq!(quoted("a\\b.txt"), r#""a\\b.txt""#);
    }

    #[test]
    fn named_control_chars() {
        assert_eq!(quoted("a\tb"), r#""a\tb""#);
        assert_eq!(quoted("a\nb"), r#""a\nb""#);
        assert_eq!(quoted("a\rb"), r#""a\rb""#);
        assert_eq!(quoted("a\x07b"), r#""a\ab""#);
        assert_eq!(quoted("a\x08b"), r#""a\bb""#);
        assert_eq!(quoted("a\x0bb"), r#""a\vb""#);
        assert_eq!(quoted("a\x0cb"), r#""a\fb""#);
    }

    #[test]
    fn other_control_chars_as_octal() {
        assert_eq!(quoted("a\x01b"), r#""a\001b""#);
        assert_eq!(quoted("a\x1fb"), r#""a\037b""#);
        assert_eq!(quoted("a\x7fb"), r#""a\177b""#);
    }

    #[test]
    fn high_bytes_as_octal() {
        // UTF-8 for "é" is 0xc3 0xa9 -> \303\251
        assert_eq!(quoted("é"), r#""\303\251""#);
        // UTF-8 for "µ" is 0xc2 0xb5 -> \302\265
        assert_eq!(quoted("µ"), r#""\302\265""#);
    }

    #[test]
    fn standard_mode_triggers_on_high_bytes() {
        // Standard mode (porcelain v2) doesn't quote on space alone, but a
        // high byte (e.g. UTF-8 continuation) still trips needs_quoting.
        assert!(needs_quoting("é.txt", QuoteMode::Standard));
        assert_eq!(quoted("é.txt"), r#""\303\251.txt""#);
    }

    #[test]
    fn plain_path_streams_verbatim() {
        let mut out: Vec<u8> = Vec::new();
        write_escaped(&mut out, "src/bin/foo.rs").unwrap();
        assert_eq!(out, b"src/bin/foo.rs");
    }
}
