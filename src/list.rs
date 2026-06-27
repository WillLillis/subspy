//! The `list` subcommand: displays per-submodule metadata in a
//! user-configurable template format with optional column alignment.

use std::{borrow::Cow, io::IsTerminal as _, path::Path};

use git2::Repository;
use thiserror::Error;

use crate::{
    StatusSummary,
    connection::{
        IpcError,
        client::{recv_status_response, send_status_request},
    },
    git::{parse_gitmodules, read_submodule_head},
    template::{Template, TemplateError},
};

pub type ListResult<T> = Result<T, ListError>;

#[derive(Error, Debug)]
pub enum ListError {
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error(transparent)]
    Ipc(#[from] IpcError),
    #[error(transparent)]
    Template(#[from] TemplateError),
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
    if status.contains(StatusSummary::DELETED_WORKDIR) {
        parts.push("deleted");
    }
    if status.contains(StatusSummary::STAGED_NEW) {
        parts.push("staged (new)");
    } else if status.contains(StatusSummary::STAGED) {
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
                        .unwrap_or(StatusSummary::clean()),
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

/// Computes the column width for each placeholder by taking the maximum of
/// the header label length and all data values, plus any literal overhead
/// characters inside the braces. Only placeholders that appear in `template`
/// are measured; unused placeholders keep a width of zero (no padding).
fn compute_placeholder_widths(
    template: &Template<'_, 9>,
    submod_info: &[SubmoduleInfo],
) -> [usize; 9] {
    let mut widths = [0usize; 9];
    let used = template.used();
    let overhead = template.overhead();

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
fn format_output(
    submod_info: &[SubmoduleInfo],
    template: &Template<'_, 9>,
    header: bool,
) -> String {
    let mut output = String::new();
    let widths = if header {
        compute_placeholder_widths(template, submod_info)
    } else {
        [0; 9]
    };
    if header {
        output.push_str(&template.expand(|name| Cow::Owned(name.to_ascii_uppercase()), &widths));
    }
    for info in submod_info {
        output.push_str(&template.expand(|name| info.resolve_placeholder(name), &widths));
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
    // Parse once up front; `used` drives which fields we fetch and whether to
    // contact the server.
    let template = Template::parse(format.unwrap_or(DEFAULT_FORMAT), &PLACEHOLDERS)?;
    let used = *template.used();

    // Only contact (and possibly cold-start) the watch server when the format
    // template actually references `{status}`; otherwise the statuses are
    // discarded, so a status-free `--format` shouldn't spawn a daemon.
    let server_statuses = if no_server || !used[IDX_STATUS] {
        None
    } else {
        let display_progress = std::io::stderr().is_terminal();
        let mut conn = send_status_request(root_path, display_progress)?;
        Some(recv_status_response(&mut conn, display_progress)?.0)
    };

    let need_submod_head = used[IDX_HEAD] || used[IDX_HEAD_LONG] || used[IDX_HEAD_BRANCH];
    let need_local_status = used[IDX_STATUS] && server_statuses.is_none();
    let infos = gather_info(
        root_path,
        server_statuses.as_deref(),
        need_submod_head,
        need_local_status,
    )?;
    let output = format_output(&infos, &template, header);
    print!("{output}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- short_oid / long_oid --

    #[test]
    fn short_oid_some() {
        let oid = git2::Oid::from_str("abcdef1234567890abcdef1234567890abcdef12").unwrap();
        assert_eq!(short_oid(Some(oid)), "abcdef1");
    }

    #[test]
    fn short_oid_none() {
        assert_eq!(short_oid(None), "");
    }

    #[test]
    fn long_oid_some() {
        let oid = git2::Oid::from_str("abcdef1234567890abcdef1234567890abcdef12").unwrap();
        assert_eq!(
            long_oid(Some(oid)),
            "abcdef1234567890abcdef1234567890abcdef12"
        );
    }

    #[test]
    fn long_oid_none() {
        assert_eq!(long_oid(None), "");
    }

    // -- status_text --

    #[test]
    fn status_text_clean() {
        assert_eq!(status_text(StatusSummary::clean()), "");
    }

    #[test]
    fn status_text_single_flag() {
        assert_eq!(
            status_text(StatusSummary::MODIFIED_CONTENT),
            "modified content"
        );
    }

    #[test]
    fn status_text_multiple_flags() {
        let status =
            StatusSummary::MODIFIED_CONTENT | StatusSummary::NEW_COMMITS | StatusSummary::STAGED;
        assert_eq!(status_text(status), "modified content, new commits, staged");
    }

    #[test]
    fn status_text_all_flags() {
        let status = StatusSummary::MODIFIED_CONTENT
            | StatusSummary::UNTRACKED_CONTENT
            | StatusSummary::NEW_COMMITS
            | StatusSummary::STAGED;
        assert_eq!(
            status_text(status),
            "modified content, untracked content, new commits, staged"
        );
    }

    #[test]
    fn status_text_staged_new() {
        assert_eq!(status_text(StatusSummary::STAGED_NEW), "staged (new)");
    }

    #[test]
    fn status_text_staged_new_with_other_flags() {
        let status = StatusSummary::STAGED_NEW | StatusSummary::UNTRACKED_CONTENT;
        assert_eq!(status_text(status), "untracked content, staged (new)");
    }

    // -- format_output / compute_placeholder_widths --

    fn make_info(name: &str, path: &str, status: Option<StatusSummary>) -> SubmoduleInfo {
        SubmoduleInfo {
            name: name.to_string(),
            path: path.to_string(),
            commit: None,
            head: None,
            branch: None,
            head_branch: None,
            status,
        }
    }

    /// Parses a list template (9 placeholders) for the format tests.
    fn tmpl(source: &str) -> Template<'_, 9> {
        Template::parse(source, &PLACEHOLDERS).unwrap()
    }

    #[test]
    fn default_format_parses() {
        Template::parse(DEFAULT_FORMAT, &PLACEHOLDERS).expect("DEFAULT_FORMAT must be valid");
    }

    #[test]
    fn format_output_no_header() {
        let infos = vec![
            make_info("a", "libs/a", None),
            make_info("b", "libs/b", None),
        ];
        let output = format_output(&infos, &tmpl("{name}\n"), false);
        assert_eq!(output, "a\nb\n");
    }

    #[test]
    fn format_output_with_header() {
        let infos = vec![make_info("sub", "sub", None)];
        let output = format_output(&infos, &tmpl("{name}\n"), true);
        let lines: Vec<&str> = output.lines().collect();
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0].trim(), "NAME");
        assert_eq!(lines[1].trim(), "sub");
    }

    #[test]
    fn format_output_with_status() {
        let infos = vec![make_info(
            "sub",
            "sub",
            Some(StatusSummary::MODIFIED_CONTENT),
        )];
        let output = format_output(&infos, &tmpl("{name}: {status}\n"), false);
        assert_eq!(output, "sub: modified content\n");
    }

    #[test]
    fn compute_widths_pads_to_longest() {
        let infos = vec![
            make_info("short", "short", None),
            make_info("much_longer_name", "much_longer_name", None),
        ];
        let widths = compute_placeholder_widths(&tmpl("{name}\n"), &infos);
        // "much_longer_name" is 16 chars, "NAME" header is 4; max is 16
        assert_eq!(widths[0], 16);
    }

    #[test]
    fn compute_widths_unused_placeholder_is_zero() {
        let infos = vec![make_info("sub", "sub", None)];
        let widths = compute_placeholder_widths(&tmpl("{name}\n"), &infos);
        // "path" (index 1) is not in the template
        assert_eq!(widths[1], 0);
    }
}
