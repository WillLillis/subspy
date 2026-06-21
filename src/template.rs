//! Format template parsing, validation, and expansion. Used by the `list`
//! and `prompt` subcommands for user-configurable output formatting.

use std::borrow::Cow;

use thiserror::Error;

pub type TemplateResult<T> = Result<T, TemplateError>;

#[derive(Error, Debug)]
pub enum TemplateError {
    #[error(transparent)]
    UnknownPlaceholder(UnknownPlaceholderError),
    #[error(transparent)]
    UnclosedBrace(UnclosedBraceError),
}

#[derive(Debug, Error)]
pub struct UnknownPlaceholderError {
    template: String,
    content_range: std::ops::Range<usize>,
}

impl std::fmt::Display for UnknownPlaceholderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Unknown placeholder:")?;
        writeln!(f, "{}", self.template)?;
        let col = self.template[..self.content_range.start].chars().count();
        let width = self.template[self.content_range.clone()].chars().count();
        writeln!(f, "{}{}", " ".repeat(col), "^".repeat(width))?;
        Ok(())
    }
}

#[derive(Debug, Error)]
pub struct UnclosedBraceError {
    template: String,
    index: usize,
}

impl std::fmt::Display for UnclosedBraceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Unclosed '{{' in format string:")?;
        writeln!(f, "{}", self.template)?;
        let col = self.template[..self.index].chars().count();
        writeln!(f, "{}^", " ".repeat(col))?;
        Ok(())
    }
}

/// Returns the _byte_ index of the first unescaped instance of `needle` inside
/// `haystack`, if present.
#[must_use]
pub fn find_unescaped(haystack: &str, needle: char) -> Option<usize> {
    let mut is_escaped = false;
    for (i, c) in haystack.char_indices() {
        if is_escaped {
            is_escaped = false;
            continue;
        }
        if c == '\\' {
            is_escaped = true;
            continue;
        }
        if c == needle {
            return Some(i);
        }
    }

    None
}

/// Finds the longest matching placeholder name within `content`.
///
/// Returns the placeholder's index and name, or `None` if no placeholder
/// matches. The longest match wins so that e.g. `"commit_long"` is
/// preferred over `"commit"`.
#[must_use]
pub fn find_placeholder<'a, const N: usize>(
    content: &str,
    placeholders: &[&'a str; N],
) -> Option<(usize, &'a str)> {
    placeholders
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, p)| content.contains(p))
        .max_by_key(|(_, p)| p.len())
}

/// One piece of a parsed [`Template`].
#[derive(Debug)]
enum Segment<'t> {
    /// Literal output text, with backslash escapes (`\n`, `\t`, `\{`, ...) resolved
    Literal(String),
    /// A `{...}` block. `idx`/`name` identify the matched placeholder; `content`
    /// is the full inside-braces text, so a wrapper like `{(name)}` is preserved
    /// and padded as a unit.
    Placeholder {
        idx: usize,
        name: &'t str,
        content: &'t str,
    },
}

/// A format template parsed once into literal/placeholder segments.
///
/// [`parse`](Template::parse) walks and validates the source string once, then
/// [`expand`](Template::expand) can then be called repeatedly without re-parsing.
#[derive(Debug)]
pub struct Template<'t, const N: usize> {
    segments: Vec<Segment<'t>>,
    used: [bool; N],
    overhead: [usize; N],
}

impl<'t, const N: usize> Template<'t, N> {
    /// Parses `template` against `placeholders` in a single pass, validating as
    /// it goes. Backslash-escaped braces (`\{`, `\}`) are literal; other escapes
    /// (`\n`, `\r`, `\t`, `\\`) are resolved into the literal segments.
    ///
    /// # Errors
    ///
    /// Returns [`TemplateError::UnclosedBrace`] if a `{` has no matching `}`, or
    /// [`TemplateError::UnknownPlaceholder`] if a block's content matches no
    /// entry in `placeholders`.
    pub fn parse(template: &'t str, placeholders: &[&'t str; N]) -> TemplateResult<Self> {
        let mut segments = Vec::new();
        let mut used = [false; N];
        let mut overhead = [0usize; N];
        let mut literal = String::new();
        let mut is_escaped = false;
        let mut skip_until = 0;
        for (i, c) in template.char_indices() {
            if i < skip_until {
                continue;
            }
            if is_escaped {
                is_escaped = false;
                match c {
                    'n' => literal.push('\n'),
                    'r' => literal.push('\r'),
                    't' => literal.push('\t'),
                    '\\' => literal.push('\\'),
                    '{' => literal.push('{'),
                    '}' => literal.push('}'),
                    other => {
                        literal.push('\\');
                        literal.push(other);
                    }
                }
                continue;
            }
            if c == '\\' {
                is_escaped = true;
                continue;
            }
            if c == '{' {
                if !literal.is_empty() {
                    segments.push(Segment::Literal(std::mem::take(&mut literal)));
                }
                let start = i + 1;
                let Some(end) = find_unescaped(&template[start..], '}') else {
                    return Err(TemplateError::UnclosedBrace(UnclosedBraceError {
                        template: template.to_string(),
                        index: i,
                    }));
                };
                let content = &template[start..start + end];
                let Some((idx, name)) = find_placeholder(content, placeholders) else {
                    return Err(TemplateError::UnknownPlaceholder(UnknownPlaceholderError {
                        template: template.to_string(),
                        content_range: start..start + end,
                    }));
                };
                used[idx] = true;
                overhead[idx] = content.chars().count() - name.len();
                segments.push(Segment::Placeholder { idx, name, content });
                skip_until = start + end + 1;
                continue;
            }
            literal.push(c);
        }
        if !literal.is_empty() {
            segments.push(Segment::Literal(literal));
        }
        Ok(Self {
            segments,
            used,
            overhead,
        })
    }

    /// Per-placeholder flag: whether the placeholder appears in the template.
    #[must_use]
    pub const fn used(&self) -> &[bool; N] {
        &self.used
    }

    /// Per-placeholder count of literal "overhead" characters inside the braces
    /// beyond the placeholder name (e.g. `2` for the parens in `{(name)}`),
    /// for column-width padding.
    #[must_use]
    pub const fn overhead(&self) -> &[usize; N] {
        &self.overhead
    }
}

impl<const N: usize> Template<'_, N> {
    /// Expands the template, calling `resolve(name)` for each placeholder and
    /// left-padding each resolved block to `widths[idx]` columns (zero width =
    /// no padding).
    #[must_use]
    pub fn expand<'a>(
        &self,
        resolve: impl Fn(&str) -> Cow<'a, str>,
        widths: &[usize; N],
    ) -> String {
        use std::fmt::Write as _;

        let mut output = String::new();
        for segment in &self.segments {
            match *segment {
                Segment::Literal(ref text) => output.push_str(text),
                Segment::Placeholder { idx, name, content } => {
                    let value = resolve(name);
                    let display = if content.len() == name.len() {
                        value
                    } else {
                        Cow::Owned(content.replacen(name, &value, 1))
                    };
                    let w = widths[idx];
                    if w > 0 {
                        let _ = write!(output, "{display:<w$}");
                    } else {
                        output.push_str(&display);
                    }
                }
            }
        }
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- find_unescaped --

    #[test]
    fn find_unescaped_basic() {
        assert_eq!(find_unescaped("hello}world", '}'), Some(5));
    }

    #[test]
    fn find_unescaped_escaped() {
        assert_eq!(find_unescaped(r"hello\}world}", '}'), Some(12));
    }

    #[test]
    fn find_unescaped_all_escaped() {
        assert_eq!(find_unescaped(r"hello\}", '}'), None);
    }

    #[test]
    fn find_unescaped_not_found() {
        assert_eq!(find_unescaped("hello world", '}'), None);
    }

    #[test]
    fn find_unescaped_empty() {
        assert_eq!(find_unescaped("", '}'), None);
    }

    #[test]
    fn find_unescaped_at_start() {
        assert_eq!(find_unescaped("}rest", '}'), Some(0));
    }

    #[test]
    fn find_unescaped_double_escape() {
        // \\} -> literal backslash followed by unescaped }
        assert_eq!(find_unescaped(r"\\}", '}'), Some(2));
    }

    #[test]
    fn find_unescaped_multibyte() {
        // needle after a multi-byte char
        assert_eq!(find_unescaped("café}", '}'), Some("café".len()));
    }

    // -- find_placeholder --

    const TEST_PH: [&str; 4] = ["name", "commit", "commit_long", "status"];

    #[test]
    fn find_placeholder_exact() {
        assert_eq!(find_placeholder("name", &TEST_PH), Some((0, "name")));
    }

    #[test]
    fn find_placeholder_longest_match() {
        // "commit_long" contains "commit", but longest wins
        assert_eq!(
            find_placeholder("commit_long", &TEST_PH),
            Some((2, "commit_long"))
        );
    }

    #[test]
    fn find_placeholder_substring_in_decorator() {
        // "(name)" contains "name"
        assert_eq!(find_placeholder("(name)", &TEST_PH), Some((0, "name")));
    }

    #[test]
    fn find_placeholder_no_match() {
        assert_eq!(find_placeholder("bogus", &TEST_PH), None);
    }

    #[test]
    fn find_placeholder_empty() {
        assert_eq!(find_placeholder("", &TEST_PH), None);
    }

    // -- Template::parse (validation) --

    const SIMPLE_PH: [&str; 3] = ["a", "b", "c"];

    /// Parse `template` and return its `used` flags.
    fn used(template: &str) -> [bool; 3] {
        *Template::parse(template, &SIMPLE_PH).unwrap().used()
    }

    /// Parse and expand `template` in one step.
    fn expand<'a>(
        template: &str,
        resolve: impl Fn(&str) -> Cow<'a, str>,
        widths: &[usize; 3],
    ) -> String {
        Template::parse(template, &SIMPLE_PH)
            .unwrap()
            .expand(resolve, widths)
    }

    #[test]
    fn validate_all_used() {
        assert_eq!(used("{a} {b} {c}"), [true, true, true]);
    }

    #[test]
    fn validate_partial_use() {
        assert_eq!(used("{b} only"), [false, true, false]);
    }

    #[test]
    fn validate_no_placeholders() {
        assert_eq!(used("just text"), [false, false, false]);
    }

    #[test]
    fn validate_escaped_braces() {
        // \{ should not be treated as a placeholder opening
        assert_eq!(used(r"\{a\}"), [false, false, false]);
    }

    #[test]
    fn validate_unclosed_brace() {
        let err = Template::parse("{a", &SIMPLE_PH).unwrap_err();
        assert!(matches!(err, TemplateError::UnclosedBrace(_)));
    }

    #[test]
    fn validate_unknown_placeholder() {
        let err = Template::parse("{xyz}", &SIMPLE_PH).unwrap_err();
        assert!(matches!(err, TemplateError::UnknownPlaceholder(_)));
    }

    #[test]
    fn validate_empty_braces() {
        let err = Template::parse("{}", &SIMPLE_PH).unwrap_err();
        assert!(matches!(err, TemplateError::UnknownPlaceholder(_)));
    }

    #[test]
    fn validate_decorator_text() {
        assert_eq!(used("{(a)}"), [true, false, false]);
    }

    #[test]
    fn validate_escaped_brace_inside_block() {
        // {a\}} -> content is "a\}", the \} is escaped so find_unescaped
        // finds the outer }
        assert_eq!(used(r"{a\}}"), [true, false, false]);
    }

    #[test]
    fn validate_repeated_placeholder() {
        assert_eq!(used("{a}{a}{a}"), [true, false, false]);
    }

    // -- Template::expand --

    #[test]
    fn expand_basic() {
        assert_eq!(
            expand(
                "{a} and {b}",
                |n| Cow::Owned(n.to_ascii_uppercase()),
                &[0; 3]
            ),
            "A and B"
        );
    }

    #[test]
    fn expand_escape_sequences() {
        assert_eq!(
            expand(r"tab:\there\nnewline", |_| unreachable!(), &[0; 3]),
            "tab:\there\nnewline"
        );
    }

    #[test]
    fn expand_escaped_braces() {
        assert_eq!(
            expand(r"\{not a placeholder\}", |_| unreachable!(), &[0; 3]),
            "{not a placeholder}"
        );
    }

    #[test]
    fn expand_carriage_return() {
        assert_eq!(expand(r"\r\n", |_| unreachable!(), &[0; 3]), "\r\n");
    }

    #[test]
    fn expand_decorator_text() {
        assert_eq!(expand("{[a]}", |_| Cow::Borrowed("val"), &[0; 3]), "[val]");
    }

    #[test]
    fn expand_with_padding() {
        assert_eq!(
            expand("{a}|{b}", |n| Cow::Owned(n.to_string()), &[5, 5, 0]),
            "a    |b    "
        );
    }

    #[test]
    fn expand_no_padding_when_zero() {
        assert_eq!(
            expand("{a}|{b}", |n| Cow::Owned(n.to_string()), &[0; 3]),
            "a|b"
        );
    }

    #[test]
    fn expand_decorator_with_padding() {
        // "(x)" is 3 chars, padded to 6
        assert_eq!(
            expand("{(a)}", |_| Cow::Borrowed("x"), &[6, 0, 0]),
            "(x)   "
        );
    }

    #[test]
    fn expand_unknown_escape_preserved() {
        assert_eq!(expand(r"\z", |_| unreachable!(), &[0; 3]), "\\z");
    }

    #[test]
    fn expand_literal_backslash() {
        assert_eq!(expand(r"\\", |_| unreachable!(), &[0; 3]), "\\");
    }

    #[test]
    fn expand_multibyte_literal() {
        assert_eq!(
            expand("café {a}", |_| Cow::Borrowed("!"), &[0; 3]),
            "café !"
        );
    }

    // -- error display --

    #[test]
    fn error_unknown_placeholder_caret_alignment() {
        let err = Template::parse("pre {xyz} post", &SIMPLE_PH).unwrap_err();
        let msg = err.to_string();
        assert_eq!(msg, "Unknown placeholder:\npre {xyz} post\n     ^^^\n");
    }

    #[test]
    fn error_unclosed_brace_caret_alignment() {
        let err = Template::parse("pre {abc", &SIMPLE_PH).unwrap_err();
        let msg = err.to_string();
        assert_eq!(msg, "Unclosed '{' in format string:\npre {abc\n    ^\n");
    }

    #[test]
    fn error_caret_with_multibyte_prefix() {
        let err = Template::parse("café {xyz}", &SIMPLE_PH).unwrap_err();
        let msg = err.to_string();
        // "café " is 5 chars (not 6 bytes), carets under "xyz"
        assert_eq!(msg, "Unknown placeholder:\ncafé {xyz}\n      ^^^\n");
    }
}
