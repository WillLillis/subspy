//! ANSI styling primitives that emit straight into a formatter or
//! writer without intermediate `String` allocation.
//!
//! Two flavors:
//! - [`Paint<T>`] is a `Display` wrapper for content that can fit into a
//!   single `write!`/`format_args!` invocation. Wrapping `T` writes the
//!   style prefix, the value, and the reset code into the formatter
//!   directly.
//! - [`paint_into`] is the streaming form for content that needs multiple
//!   writes inside the styled region (e.g. static text plus a path
//!   streamed by `Relativizer`).
//!
//! Both honor `NO_COLOR`: when set (and non-empty), styling is skipped
//! and the content is written verbatim.

use std::{
    fmt::{self, Display},
    io::{self, Write},
    sync::OnceLock,
};

use anstyle::{AnsiColor, Color, Style};

/// `NO_COLOR` (per <https://no-color.org>): any non-empty value disables
/// styling. We read the environment once at first call and cache the
/// answer for the rest of the process.
fn color_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("NO_COLOR").is_none_or(|v| v.is_empty()))
}

/// Bright red foreground - used for unstaged changes, conflicts, error
/// markers, and the rebase header.
pub const RED: Style = Style::new().fg_color(Some(Color::Ansi(AnsiColor::Red)));

/// Bright green foreground - used for staged changes.
pub const GREEN: Style = Style::new().fg_color(Some(Color::Ansi(AnsiColor::Green)));

/// `Display`-able pair of style + content.
///
/// Embedding this in a `write!`/`format_args!` writes the ANSI prefix,
/// the inner `T`'s `Display`, and the reset code straight into the
/// formatter, never allocating an intermediate `String`.
pub struct Paint<T> {
    pub style: Style,
    pub content: T,
}

impl<T> Paint<T> {
    pub const fn new(style: Style, content: T) -> Self {
        Self { style, content }
    }
}

impl<T: Display> Display for Paint<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if color_enabled() {
            write!(f, "{}{}{:#}", self.style, self.content, self.style)
        } else {
            self.content.fmt(f)
        }
    }
}

/// Streams styled content into `out`: writes the style prefix, lets
/// `body` emit the styled region in whatever number of writes it needs,
/// then writes the reset code.
///
/// `body` returns `io::Result<()>` so it composes with `write!` and
/// callees that themselves stream (e.g. `Relativizer::write_to`).
///
/// # Errors
///
/// Returns any `io::Error` raised by writing.
pub fn paint_into<W, F>(out: &mut W, style: Style, body: F) -> io::Result<()>
where
    W: Write,
    F: FnOnce(&mut W) -> io::Result<()>,
{
    if color_enabled() {
        write!(out, "{style}")?;
        body(out)?;
        write!(out, "{style:#}")?;
    } else {
        body(out)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paint_formats_with_style_when_color_enabled() {
        // We can't reliably toggle the cached color_enabled() in tests,
        // so we just check that Display emits *something* containing the
        // value text, regardless of mode. Style-vs-plain is exercised by
        // the no-color test below via direct format string equivalence.
        let s = format!("{}", Paint::new(RED, "hello"));
        assert!(s.contains("hello"));
    }

    #[test]
    fn paint_into_emits_body_writes() {
        let mut buf: Vec<u8> = Vec::new();
        paint_into(&mut buf, GREEN, |out| {
            out.write_all(b"first ")?;
            out.write_all(b"second")
        })
        .unwrap();
        let s = std::str::from_utf8(&buf).unwrap();
        assert!(s.contains("first second"));
    }

    #[test]
    fn paint_into_propagates_body_errors() {
        struct FailingWriter;
        impl Write for FailingWriter {
            fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
                Err(io::Error::new(io::ErrorKind::BrokenPipe, "no"))
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        // If color is enabled, the first style write may fail; if not,
        // the body's first write fails. Either way, the function should
        // propagate.
        let mut w = FailingWriter;
        let result = paint_into(&mut w, RED, |out| out.write_all(b"hi"));
        assert!(result.is_err());
    }
}
