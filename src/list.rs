use std::{borrow::Cow, fmt::Write as _, io::IsTerminal as _, path::Path, path::PathBuf};

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

/// Indices into [`PLACEHOLDERS`] for fields that require per-submodule I/O.
const IDX_HEAD: usize = 4;
const IDX_HEAD_LONG: usize = 5;
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

/// Returns the _byte_ index of the first unescaped instance of `needle` inside
/// `haystack`, if present.
fn find_unescaped(haystack: &str, needle: char) -> Option<usize> {
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

/// Validates `template` and returns which placeholders it uses.
///
/// Checks that every `{...}` block contains a recognized placeholder and
/// that all braces are closed. Backslash-escaped braces (`\{`, `\}`) are
/// treated as literal characters, not block delimiters. On success, returns
/// a per-placeholder boolean indicating which are present in the template.
fn validate_template(template: &str) -> ListResult<[bool; 9]> {
    let mut used = [false; 9];
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
                return Err(ListError::UnclosedBrace(UnclosedBraceError {
                    template: template.to_string(),
                    index: i,
                }));
            };
            let content = &template[start..start + end];
            match find_placeholder(content) {
                Some((idx, _)) => used[idx] = true,
                None => {
                    return Err(ListError::UnknownPlaceholder(UnknownPlaceholderError {
                        template: template.to_string(),
                        content_range: start..start + end,
                    }));
                }
            }
            // Skip past the closing brace so characters inside the
            // placeholder block aren't re-scanned.
            skip_until = start + end + 1;
        }
    }

    Ok(used)
}

/// Resolves the `.git` directory for a submodule. Handles both `.git`
/// directories (normal repos) and `.git` files containing a `gitdir:` pointer
/// (the common case for submodules).
fn resolve_git_dir(submod_path: &Path) -> Option<PathBuf> {
    let dot_git = submod_path.join(".git");
    if dot_git.is_file() {
        // Submodule .git files contain a relative gitdir pointer
        // (e.g. "gitdir: ../../.git/modules/name")
        let content = std::fs::read_to_string(&dot_git).ok()?;
        let path_str = content.strip_prefix("gitdir: ")?.trim_end();
        Some(submod_path.join(path_str))
    } else if dot_git.is_dir() {
        Some(dot_git)
    } else {
        None
    }
}

/// Resolves a git ref (e.g. `refs/heads/main`) to an OID by checking loose
/// refs first, then falling back to `packed-refs`.
///
/// Does not follow symbolic refs (chains of `ref:` indirection). This is fine
/// for branch tips under `refs/heads/`, which are always direct OIDs.
fn resolve_ref(git_dir: &Path, ref_target: &str) -> Option<git2::Oid> {
    // Loose ref
    let ref_path = git_dir.join(ref_target);
    if let Ok(content) = std::fs::read_to_string(&ref_path) {
        return git2::Oid::from_str(content.trim_end()).ok();
    }
    // Packed refs
    let packed = std::fs::read_to_string(git_dir.join("packed-refs")).ok()?;
    for line in packed.lines() {
        if line.starts_with('#') || line.starts_with('^') {
            continue;
        }
        let Some((oid_str, name)) = line.split_once(' ') else {
            continue;
        };
        if name == ref_target {
            return git2::Oid::from_str(oid_str).ok();
        }
    }
    None
}

/// Reads a submodule's HEAD to get its current OID and branch name (if on a
/// branch). Returns `(None, None)` if the submodule isn't checked out.
fn read_submodule_head(submod_path: &Path) -> (Option<git2::Oid>, Option<String>) {
    let Some(git_dir) = resolve_git_dir(submod_path) else {
        return (None, None);
    };
    let Ok(content) = std::fs::read_to_string(git_dir.join("HEAD")) else {
        return (None, None);
    };
    let content = content.trim_end();
    content.strip_prefix("ref: ").map_or_else(
        // Detached HEAD -> raw OID
        || (git2::Oid::from_str(content).ok(), None),
        |ref_target| {
            let branch = ref_target
                .strip_prefix("refs/heads/")
                .map(|s| s.to_string());
            let oid = resolve_ref(&git_dir, ref_target);
            (oid, branch)
        },
    )
}

/// Parses `.gitmodules` to extract submodule name, path, and branch without
/// going through `repo.submodules()` (which triggers expensive per-submodule
/// config snapshot parsing in libgit2).
fn parse_gitmodules(root_path: &Path) -> ListResult<Vec<(String, String, Option<String>)>> {
    let gitmodules_path = root_path.join(".gitmodules");
    if !gitmodules_path.exists() {
        return Ok(Vec::new());
    }
    let config = git2::Config::open(&gitmodules_path)?;
    let mut entries = Vec::new();

    let mut iter = config.entries(Some("submodule\\..*\\.path"))?;
    while let Some(entry) = iter.next() {
        let entry = entry?;
        let key = entry.name().expect("non-UTF-8 key in .gitmodules");
        // Guaranteed by the regex filter on entries()
        let name = key
            .strip_prefix("submodule.")
            .and_then(|s| s.strip_suffix(".path"))
            .unwrap();
        let path = entry
            .value()
            .expect("non-UTF-8 path in .gitmodules")
            .to_string();
        let branch_key = format!("submodule.{name}.branch");
        let branch = config.get_string(&branch_key).ok();
        entries.push((name.to_string(), path, branch));
    }
    Ok(entries)
}

/// Collects metadata for every submodule in the repository at `root_path`.
///
/// Parses `.gitmodules` directly and reads the parent's `HEAD` tree for
/// committed OIDs, bypassing `repo.submodules()` to avoid libgit2's
/// per-submodule config snapshot overhead. Per-submodule I/O (reading the
/// submodule's HEAD for workdir OID/branch, computing status) is
/// parallelized via rayon.
///
/// `need_submod_head` and `need_local_status` control whether the expensive
/// operations run at all, allowing callers to skip them when the template
/// doesn't use the corresponding placeholders.
fn gather_info(
    root_path: &Path,
    server_statuses: Option<&[(String, StatusSummary)]>,
    need_submod_head: bool,
    need_local_status: bool,
) -> ListResult<Vec<SubmoduleInfo>> {
    use std::collections::HashMap;

    use rayon::prelude::*;

    let gitmodule_entries = parse_gitmodules(root_path)?;

    // Look up committed OIDs from the parent's HEAD tree
    let repo = Repository::open(root_path)?;
    let head_tree = repo.head()?.peel_to_tree()?;
    let partial: Vec<_> = gitmodule_entries
        .into_iter()
        .map(|(name, path_str, branch)| {
            let commit = head_tree
                .get_path(Path::new(&path_str))
                .ok()
                .map(|e| e.id());
            (name, path_str, commit, branch)
        })
        .collect();

    let status_map: Option<HashMap<&str, StatusSummary>> =
        server_statuses.map(|statuses| statuses.iter().map(|(p, s)| (p.as_str(), *s)).collect());
    let tl_repo = thread_local::ThreadLocal::new();

    // Resolve per-submodule fields in parallel
    let mut infos: Vec<SubmoduleInfo> = partial
        .into_par_iter()
        .map(|(name, path_str, commit, branch)| {
            let (head, head_branch) = if need_submod_head {
                read_submodule_head(&root_path.join(&path_str))
            } else {
                (None, None)
            };

            let status = match &status_map {
                Some(map) => Some(
                    map.get(path_str.as_str())
                        .copied()
                        .unwrap_or(StatusSummary::CLEAN),
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
        .collect::<ListResult<Vec<_>>>()?;

    infos.sort_unstable_by(|a, b| a.name.cmp(&b.name));
    Ok(infos)
}

/// Expands `{...}` placeholders in `template` by calling `resolve` for each
/// placeholder name found via [`find_placeholder`]. Literal text surrounding
/// the placeholder inside the braces (e.g. the parens in `{(name)}`) is
/// preserved via `replacen` and padded as a unit according to `widths`.
///
/// Also interprets backslash escapes: `\n`, `\r`, `\t`, `\\`, `\{`, `\}`.
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
                let template_start = &template[start..];
                // Safety: template was validated by `validate_template`
                let end = find_unescaped(template_start, '}').unwrap();
                let content = &template_start[..end];
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
                Some(b'r') => {
                    output.push('\r');
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
            // Safety: template was validated by `validate_template`
            let end = find_unescaped(&template[start..], '}').unwrap();
            let content = &template[start..start + end];
            if let Some((idx, name)) = find_placeholder(content) {
                used[idx] = true;
                // NOTE:  `name.len()` is fine here since all placeholders are ASCII
                overhead[idx] = content.chars().count() - name.len();
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
                widths[idx] = widths[idx]
                    .max(info.resolve_placeholder(placeholder).chars().count() + overhead[idx]);
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

    let need_submod_head = used[IDX_HEAD] || used[IDX_HEAD_LONG] || used[IDX_HEAD_BRANCH];
    let need_local_status = used[IDX_STATUS] && server_statuses.is_none();
    let infos = gather_info(
        root_path,
        server_statuses.as_deref(),
        need_submod_head,
        need_local_status,
    )?;
    let output = format_output(&infos, template, header);
    print!("{output}");
    Ok(())
}
