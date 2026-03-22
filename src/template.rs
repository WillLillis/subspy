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
