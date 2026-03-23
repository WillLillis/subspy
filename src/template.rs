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

/// Validates a template string against a set of known placeholders.
///
/// Checks that every `{...}` block contains a recognized placeholder and
/// that all braces are closed. Backslash-escaped braces (`\{`, `\}`) are
/// treated as literal characters, not block delimiters. On success, returns
/// a per-placeholder boolean indicating which are present in the template.
///
/// # Errors
///
/// Returns `TemplateError::UnclosedBrace` if a `{` has no matching `}`,
/// or `TemplateError::UnknownPlaceholder` if a block's content doesn't
/// match any entry in `placeholders`.
pub fn validate_template<const N: usize>(
    template: &str,
    placeholders: &[&str; N],
) -> TemplateResult<[bool; N]> {
    let mut used = [false; N];
    let mut is_escaped = false;
    let mut skip_until = 0;
    for (i, c) in template.char_indices() {
        if i < skip_until {
            continue;
        }
        if is_escaped {
            is_escaped = false;
            continue;
        }
        if c == '\\' {
            is_escaped = true;
            continue;
        }
        if c == '{' {
            let start = i + 1;
            let Some(end) = find_unescaped(&template[start..], '}') else {
                return Err(TemplateError::UnclosedBrace(UnclosedBraceError {
                    template: template.to_string(),
                    index: i,
                }));
            };
            let content = &template[start..start + end];
            match find_placeholder(content, placeholders) {
                Some((idx, _)) => used[idx] = true,
                None => {
                    return Err(TemplateError::UnknownPlaceholder(UnknownPlaceholderError {
                        template: template.to_string(),
                        content_range: start..start + end,
                    }));
                }
            }
            skip_until = start + end + 1;
        }
    }
    Ok(used)
}

/// Expands `{...}` placeholders in a validated template string.
///
/// For each block, calls `resolve` with the placeholder name found via
/// [`find_placeholder`]. Literal text surrounding the placeholder inside the
/// braces (e.g. the parens in `{(name)}`) is preserved and padded as a unit
/// according to `widths`. Pass all-zero widths to disable padding.
///
/// Also interprets backslash escapes: `\n`, `\r`, `\t`, `\\`, `\{`, `\}`.
///
/// # Panics
///
/// Panics if `template` contains blocks not matching any placeholder.
/// Always call [`validate_template`] first.
#[must_use]
pub fn expand_template<'a, const N: usize>(
    template: &str,
    placeholders: &[&str; N],
    resolve: impl Fn(&str) -> Cow<'a, str>,
    widths: &[usize; N],
) -> String {
    use std::fmt::Write as _;

    let mut output = String::with_capacity(template.len());
    let mut is_escaped = false;
    let mut skip_until = 0;
    for (i, c) in template.char_indices() {
        if i < skip_until {
            continue;
        }
        if is_escaped {
            is_escaped = false;
            match c {
                'n' => output.push('\n'),
                'r' => output.push('\r'),
                't' => output.push('\t'),
                '\\' => output.push('\\'),
                '{' => output.push('{'),
                '}' => output.push('}'),
                _ => {
                    output.push('\\');
                    output.push(c);
                }
            }
            continue;
        }
        if c == '\\' {
            is_escaped = true;
            continue;
        }
        if c == '{' {
            let start = i + 1;
            let end = find_unescaped(&template[start..], '}').unwrap();
            let content = &template[start..start + end];
            let (idx, name) = find_placeholder(content, placeholders).unwrap();
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
            skip_until = start + end + 1;
            continue;
        }
        output.push(c);
    }
    output
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

    // -- validate_template --

    const SIMPLE_PH: [&str; 3] = ["a", "b", "c"];

    #[test]
    fn validate_all_used() {
        let used = validate_template("{a} {b} {c}", &SIMPLE_PH).unwrap();
        assert_eq!(used, [true, true, true]);
    }

    #[test]
    fn validate_partial_use() {
        let used = validate_template("{b} only", &SIMPLE_PH).unwrap();
        assert_eq!(used, [false, true, false]);
    }

    #[test]
    fn validate_no_placeholders() {
        let used = validate_template("just text", &SIMPLE_PH).unwrap();
        assert_eq!(used, [false, false, false]);
    }

    #[test]
    fn validate_escaped_braces() {
        // \{ should not be treated as a placeholder opening
        let used = validate_template(r"\{a\}", &SIMPLE_PH).unwrap();
        assert_eq!(used, [false, false, false]);
    }

    #[test]
    fn validate_unclosed_brace() {
        let err = validate_template("{a", &SIMPLE_PH).unwrap_err();
        assert!(matches!(err, TemplateError::UnclosedBrace(_)));
    }

    #[test]
    fn validate_unknown_placeholder() {
        let err = validate_template("{xyz}", &SIMPLE_PH).unwrap_err();
        assert!(matches!(err, TemplateError::UnknownPlaceholder(_)));
    }

    #[test]
    fn validate_empty_braces() {
        let err = validate_template("{}", &SIMPLE_PH).unwrap_err();
        assert!(matches!(err, TemplateError::UnknownPlaceholder(_)));
    }

    #[test]
    fn validate_decorator_text() {
        let used = validate_template("{(a)}", &SIMPLE_PH).unwrap();
        assert_eq!(used, [true, false, false]);
    }

    #[test]
    fn validate_escaped_brace_inside_block() {
        // {a\}} -> content is "a\}", the \} is escaped so find_unescaped
        // finds the outer }
        let used = validate_template(r"{a\}}", &SIMPLE_PH).unwrap();
        assert_eq!(used, [true, false, false]);
    }

    #[test]
    fn validate_repeated_placeholder() {
        let used = validate_template("{a}{a}{a}", &SIMPLE_PH).unwrap();
        assert_eq!(used, [true, false, false]);
    }

    // -- expand_template --

    #[test]
    fn expand_basic() {
        let result = expand_template(
            "{a} and {b}",
            &SIMPLE_PH,
            |name| Cow::Owned(name.to_ascii_uppercase()),
            &[0; 3],
        );
        assert_eq!(result, "A and B");
    }

    #[test]
    fn expand_escape_sequences() {
        let result = expand_template(
            r"tab:\there\nnewline",
            &SIMPLE_PH,
            |_| unreachable!(),
            &[0; 3],
        );
        assert_eq!(result, "tab:\there\nnewline");
    }

    #[test]
    fn expand_escaped_braces() {
        let result = expand_template(
            r"\{not a placeholder\}",
            &SIMPLE_PH,
            |_| unreachable!(),
            &[0; 3],
        );
        assert_eq!(result, "{not a placeholder}");
    }

    #[test]
    fn expand_carriage_return() {
        let result = expand_template(r"\r\n", &SIMPLE_PH, |_| unreachable!(), &[0; 3]);
        assert_eq!(result, "\r\n");
    }

    #[test]
    fn expand_decorator_text() {
        let result = expand_template("{[a]}", &SIMPLE_PH, |_| Cow::Borrowed("val"), &[0; 3]);
        assert_eq!(result, "[val]");
    }

    #[test]
    fn expand_with_padding() {
        let result = expand_template(
            "{a}|{b}",
            &SIMPLE_PH,
            |name| Cow::Owned(name.to_string()),
            &[5, 5, 0],
        );
        assert_eq!(result, "a    |b    ");
    }

    #[test]
    fn expand_no_padding_when_zero() {
        let result = expand_template(
            "{a}|{b}",
            &SIMPLE_PH,
            |name| Cow::Owned(name.to_string()),
            &[0; 3],
        );
        assert_eq!(result, "a|b");
    }

    #[test]
    fn expand_decorator_with_padding() {
        let result = expand_template("{(a)}", &SIMPLE_PH, |_| Cow::Borrowed("x"), &[6, 0, 0]);
        // "(x)" is 3 chars, padded to 6
        assert_eq!(result, "(x)   ");
    }

    #[test]
    fn expand_unknown_escape_preserved() {
        let result = expand_template(r"\z", &SIMPLE_PH, |_| unreachable!(), &[0; 3]);
        assert_eq!(result, "\\z");
    }

    #[test]
    fn expand_literal_backslash() {
        let result = expand_template(r"\\", &SIMPLE_PH, |_| unreachable!(), &[0; 3]);
        assert_eq!(result, "\\");
    }

    #[test]
    fn expand_multibyte_literal() {
        let result = expand_template("café {a}", &SIMPLE_PH, |_| Cow::Borrowed("!"), &[0; 3]);
        assert_eq!(result, "café !");
    }

    // -- error display --

    #[test]
    fn error_unknown_placeholder_caret_alignment() {
        let err = validate_template("pre {xyz} post", &SIMPLE_PH).unwrap_err();
        let msg = err.to_string();
        assert_eq!(msg, "Unknown placeholder:\npre {xyz} post\n     ^^^\n");
    }

    #[test]
    fn error_unclosed_brace_caret_alignment() {
        let err = validate_template("pre {abc", &SIMPLE_PH).unwrap_err();
        let msg = err.to_string();
        assert_eq!(msg, "Unclosed '{' in format string:\npre {abc\n    ^\n");
    }

    #[test]
    fn error_caret_with_multibyte_prefix() {
        let err = validate_template("café {xyz}", &SIMPLE_PH).unwrap_err();
        let msg = err.to_string();
        // "café " is 5 chars (not 6 bytes), carets under "xyz"
        assert_eq!(msg, "Unknown placeholder:\ncafé {xyz}\n      ^^^\n");
    }
}
