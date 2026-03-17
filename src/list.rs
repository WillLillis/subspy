use std::{borrow::Cow, fmt::Write as _, io::IsTerminal as _, path::Path};

use git2::Repository;
use thiserror::Error;

use crate::{
    StatusSummary,
    connection::client::{recv_status_response, send_status_request},
    status::StatusError,
};

pub type ListResult<T> = Result<T, ListError>;

#[derive(Error, Debug)]
pub enum ListError {
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error(transparent)]
    Status(#[from] StatusError),
    #[error("Unknown placeholder: {{{0}}}")]
    UnknownPlaceholder(String),
    #[error("Unclosed '{{' in format string")]
    UnclosedBrace,
}

const DEFAULT_FORMAT: &str =
    "{(name)}  {(path)}  {(commit)}  {(head)}  {(branch)}  {(head_branch)}  {(status)}\n";

struct SubmoduleInfo {
    name: String,
    path: String,
    commit: Option<git2::Oid>,
    head: Option<git2::Oid>,
    branch: Option<String>,
    head_branch: Option<String>,
    status: Option<StatusSummary>,
}

impl SubmoduleInfo {
    /// Maps a placeholder name to its value for this submodule.
    ///
    /// Only called with names from [`PLACEHOLDERS`], guaranteed by
    /// [`validate_template`].
    ///
    /// # Panics
    ///
    /// Panics if `name` is not a recognized placeholder.
    fn resolve_placeholder(&self, name: &str) -> Cow<'_, str> {
        match name {
            "name" => Cow::Borrowed(&self.name),
            "path" => Cow::Borrowed(&self.path),
            "commit" => Cow::Owned(short_oid(self.commit)),
            "commit_long" => Cow::Owned(long_oid(self.commit)),
            "head" => Cow::Owned(short_oid(self.head)),
            "head_long" => Cow::Owned(long_oid(self.head)),
            "branch" => Cow::Borrowed(self.branch.as_deref().unwrap_or("")),
            "head_branch" => Cow::Borrowed(self.head_branch.as_deref().unwrap_or("")),
            "status" => Cow::Owned(self.status.map_or_else(String::new, status_text)),
            _ => unreachable!("validate_template rejects unknown placeholders"),
        }
    }
}

fn short_oid(oid: Option<git2::Oid>) -> String {
    oid.map_or_else(String::new, |o| {
        let s = o.to_string();
        s[..7].to_string()
    })
}

fn long_oid(oid: Option<git2::Oid>) -> String {
    oid.map_or_else(String::new, |o| o.to_string())
}

/// Formats a [`StatusSummary`] as a comma-separated list of human-readable
/// flags (e.g. `"modified content, new commits"`). Includes `STAGED`, unlike
/// the `Display` impl which is tailored to the `status` command. Returns an
/// empty string for clean submodules.
fn status_text(status: StatusSummary) -> String {
    let mut parts = Vec::new();
    if status.contains(StatusSummary::MODIFIED_CONTENT) {
        parts.push("modified content");
    }
    if status.contains(StatusSummary::UNTRACKED_CONTENT) {
        parts.push("untracked content");
    }
    if status.contains(StatusSummary::NEW_COMMITS) {
        parts.push("new commits");
    }
    if status.contains(StatusSummary::STAGED) {
        parts.push("staged");
    }
    parts.join(", ")
}

const PLACEHOLDERS: [&str; 9] = [
    "name",
    "path",
    "commit",
    "commit_long",
    "head",
    "head_long",
    "branch",
    "head_branch",
    "status",
];

/// Indices of the two placeholders that require expensive per-submodule I/O.
const IDX_HEAD_BRANCH: usize = 7;
const IDX_STATUS: usize = 8;

/// Finds the longest matching placeholder name within `content`.
///
/// Returns the placeholder's index in [`PLACEHOLDERS`] and its name, or
/// `None` if no placeholder matches. The longest match wins so that e.g.
/// `"commit_long"` is preferred over `"commit"`.
fn find_placeholder(content: &str) -> Option<(usize, &'static str)> {
    PLACEHOLDERS
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, p)| content.contains(p))
        .max_by_key(|(_, p)| p.len())
}

/// Validates `template` and returns which placeholders it uses.
///
/// Checks that every `{...}` block contains a recognized placeholder and
/// that all braces are closed. Backslash-escaped braces (`\{`, `\}`) are
/// treated as literal characters, not block delimiters. On success, returns
/// a per-placeholder boolean indicating which are present in the template.
fn validate_template(template: &str) -> ListResult<[bool; 9]> {
    let mut used = [false; 9];
    let bytes = template.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\\' && i + 1 < bytes.len() {
            // Skip escaped characters (including \{ and \})
            i += 2;
        } else if bytes[i] == b'{' {
            let start = i + 1;
            let Some(end) = template[start..].find('}') else {
                return Err(ListError::UnclosedBrace);
            };
            let content = &template[start..start + end];
            match find_placeholder(content) {
                Some((idx, _)) => used[idx] = true,
                None => return Err(ListError::UnknownPlaceholder(content.to_string())),
            }
            i = start + end + 1;
        } else {
            i += 1;
        }
    }
    Ok(used)
}

/// Collects metadata for every submodule in the repository at `root_path`.
///
/// Cheap fields (name, path, hashes, branch) are extracted serially since
/// `git2::Submodule` is not `Send`. Expensive per-submodule I/O — opening
/// each submodule repo for `head_branch` and computing `submodule_status()`
/// for the `--no-server` path — is parallelized via rayon.
///
/// `need_head_branch` and `need_local_status` control whether the expensive
/// operations run at all, allowing callers to skip them when the template
/// doesn't use the corresponding placeholders.
fn gather_info(
    root_path: &Path,
    server_statuses: Option<&[(String, StatusSummary)]>,
    need_head_branch: bool,
    need_local_status: bool,
) -> ListResult<Vec<SubmoduleInfo>> {
    use rayon::prelude::*;

    let repo = Repository::open(root_path)?;
    let submodules = match repo.submodules() {
        Ok(s) => s,
        Err(e) if e.code() == git2::ErrorCode::NotFound => return Ok(Vec::new()),
        Err(e) => return Err(e.into()),
    };

    // Extract cheap fields serially (git2::Submodule is not Send)
    let partial: Vec<_> = submodules
        .iter()
        .map(|submod| {
            let name = submod.name().unwrap_or("?").to_string();
            let path_str = submod.path().to_str().unwrap_or("?").to_string();
            let commit = submod.head_id();
            let head = submod.workdir_id();
            let branch = submod.branch().map(String::from);
            (name, path_str, commit, head, branch)
        })
        .collect();

    let tl_repo = thread_local::ThreadLocal::new();

    // Resolve expensive fields in parallel
    partial
        .into_par_iter()
        .map(|(name, path_str, commit, head, branch)| {
            let head_branch = if need_head_branch {
                let full_path = root_path.join(&path_str);
                Repository::open(&full_path).ok().and_then(|sub_repo| {
                    let head_ref = sub_repo.head().ok()?;
                    if head_ref.is_branch() {
                        head_ref.shorthand().map(|s| s.to_string())
                    } else {
                        None
                    }
                })
            } else {
                None
            };

            let status = match server_statuses {
                Some(statuses) => Some(
                    statuses
                        .iter()
                        .find(|(p, _)| p == &path_str)
                        .map_or(StatusSummary::CLEAN, |(_, s)| *s),
                ),
                None if need_local_status => {
                    let repo = tl_repo.get_or_try(|| Repository::open(root_path))?;
                    Some(StatusSummary::from(
                        repo.submodule_status(&name, git2::SubmoduleIgnore::None)?,
                    ))
                }
                None => None,
            };

            Ok(SubmoduleInfo {
                name,
                path: path_str,
                commit,
                head,
                branch,
                head_branch,
                status,
            })
        })
        .collect()
}

/// Expands `{...}` placeholders in `template` by calling `resolve` for each
/// placeholder name found via [`find_placeholder`]. Literal text surrounding
/// the placeholder inside the braces (e.g. the parens in `{(name)}`) is
/// preserved via `replacen` and padded as a unit according to `widths`.
///
/// Also interprets backslash escapes: `\n`, `\t`, `\\`, `\{`, `\}`.
///
/// Assumes `template` has already been validated by [`validate_template`].
fn expand_template<'a>(
    template: &str,
    resolve: impl Fn(&str) -> Cow<'a, str>,
    widths: &[usize; 9],
) -> String {
    let mut output = String::new();
    let bytes = template.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'{' => {
                let start = i + 1;
                // Safety: template was validated by validate_template
                let end = template[start..].find('}').unwrap();
                let content = &template[start..start + end];
                let (idx, name) = find_placeholder(content).unwrap();
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
                i = start + end + 1;
            }
            b'\\' => match bytes.get(i + 1) {
                Some(b'n') => {
                    output.push('\n');
                    i += 2;
                }
                Some(b't') => {
                    output.push('\t');
                    i += 2;
                }
                Some(b'\\') => {
                    output.push('\\');
                    i += 2;
                }
                Some(b'{') => {
                    output.push('{');
                    i += 2;
                }
                Some(b'}') => {
                    output.push('}');
                    i += 2;
                }
                _ => {
                    output.push('\\');
                    i += 1;
                }
            },
            _ => {
                let ch = template[i..].chars().next().unwrap();
                output.push(ch);
                i += ch.len_utf8();
            }
        }
    }
    output
}

/// Computes the column width for each placeholder by taking the maximum of
/// the header label length and all data values, plus any literal overhead
/// characters inside the braces. Only placeholders that appear in `template`
/// are measured; unused placeholders keep a width of zero (no padding).
fn compute_placeholder_widths(template: &str, submod_info: &[SubmoduleInfo]) -> [usize; 9] {
    let mut widths = [0usize; 9];
    let mut overhead = [0usize; 9];
    let mut used = [false; 9];

    let bytes = template.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\\' && i + 1 < bytes.len() {
            i += 2;
        } else if bytes[i] == b'{' {
            let start = i + 1;
            // Safety: template was validated by validate_template
            let end = template[start..].find('}').unwrap();
            let content = &template[start..start + end];
            if let Some((idx, name)) = find_placeholder(content) {
                used[idx] = true;
                overhead[idx] = content.len() - name.len();
            }
            i = start + end + 1;
        } else {
            i += 1;
        }
    }

    // Header names (ASCII, so uppercase has the same byte length)
    for (idx, &placeholder) in PLACEHOLDERS.iter().enumerate() {
        if used[idx] {
            widths[idx] = placeholder.len() + overhead[idx];
        }
    }

    // Data values
    for info in submod_info {
        for (idx, &placeholder) in PLACEHOLDERS.iter().enumerate() {
            if used[idx] {
                widths[idx] =
                    widths[idx].max(info.resolve_placeholder(placeholder).len() + overhead[idx]);
            }
        }
    }

    widths
}

/// Formats all submodule info through `template`. When `header` is true,
/// computes column widths and prepends a header row with uppercased
/// placeholder names.
fn format_output(submod_info: &[SubmoduleInfo], template: &str, header: bool) -> String {
    let mut output = String::new();
    let widths = if header {
        compute_placeholder_widths(template, submod_info)
    } else {
        [0; 9]
    };
    if header {
        output.push_str(&expand_template(
            template,
            |name| Cow::Owned(name.to_ascii_uppercase()),
            &widths,
        ));
    }
    for info in submod_info {
        output.push_str(&expand_template(
            template,
            |name| info.resolve_placeholder(name),
            &widths,
        ));
    }
    output
}

/// Lists submodule metadata for the repository at `root_path`.
///
/// # Errors
///
/// Returns `Err` if the format template is invalid, the repository cannot be
/// opened, or communication with the watch server fails.
pub fn list(
    root_path: &Path,
    format: Option<&str>,
    header: bool,
    no_server: bool,
) -> ListResult<()> {
    let template = format.unwrap_or(DEFAULT_FORMAT);
    let used = validate_template(template)?;

    let server_statuses = if no_server {
        None
    } else {
        let mut conn = send_status_request(root_path)?;
        let display_progress = std::io::stderr().is_terminal();
        Some(recv_status_response(&mut conn, display_progress)?)
    };

    let need_head_branch = used[IDX_HEAD_BRANCH];
    let need_local_status = used[IDX_STATUS] && server_statuses.is_none();
    let infos = gather_info(
        root_path,
        server_statuses.as_deref(),
        need_head_branch,
        need_local_status,
    )?;
    let output = format_output(&infos, template, header);
    print!("{output}");
    Ok(())
}
