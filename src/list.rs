//! The `list` subcommand: displays per-submodule metadata in a
//! user-configurable template format with optional column alignment.

use std::{
    borrow::Cow,
    io::{IsTerminal as _, Write as _},
    path::Path,
};

use git2::Repository;
use thiserror::Error;

use crate::{
    StatusSummary,
    connection::{
        IpcError,
        client::{recv_status_response, send_status_request},
    },
    git::{parse_gitmodules, path::GitPath, read_submodule_head, substatus},
    status::{
        ConfigDefaults,
        quote::{QuoteMode, needs_quoting, write_escaped},
    },
    template::{Template, TemplateError, display_width},
};

pub type ListResult<T> = Result<T, ListError>;

#[derive(Error, Debug)]
pub enum ListError {
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error(transparent)]
    Substatus(#[from] substatus::SubstatusError),
    #[error(transparent)]
    Ipc(#[from] IpcError),
    #[error(transparent)]
    Template(#[from] TemplateError),
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

const DEFAULT_FORMAT: &str =
    "{(name)}  {(path)}  {(commit)}  {(head)}  {(branch)}  {(head_branch)}  {(status)}\n";

struct SubmoduleInfo {
    /// The name `.gitmodules` records for this path, if it has an entry.
    name: Option<Vec<u8>>,
    path: GitPath,
    commit: Option<git2::Oid>,
    head: Option<git2::Oid>,
    branch: Option<Vec<u8>>,
    head_branch: Option<String>,
    status: Option<StatusSummary>,
}

impl SubmoduleInfo {
    /// Maps a placeholder name to its value for this submodule. Names, paths,
    /// and branches are quoted as git quotes paths, honoring `quote_path`
    /// (`core.quotePath`).
    ///
    /// Only called with names from [`PLACEHOLDERS`], guaranteed by
    /// [`Template::parse`].
    ///
    /// # Panics
    ///
    /// Panics if `name` is not a recognized placeholder.
    fn resolve_placeholder(&self, name: &str, quote_path: bool) -> Cow<'_, [u8]> {
        match name {
            "name" => quoted(self.name.as_deref().unwrap_or_default(), quote_path),
            "path" => quoted(self.path.as_bytes(), quote_path),
            "commit" => Cow::Owned(short_oid(self.commit).into_bytes()),
            "commit_long" => Cow::Owned(long_oid(self.commit).into_bytes()),
            "head" => Cow::Owned(short_oid(self.head).into_bytes()),
            "head_long" => Cow::Owned(long_oid(self.head).into_bytes()),
            "branch" => quoted(self.branch.as_deref().unwrap_or_default(), quote_path),
            "head_branch" => quoted(
                self.head_branch.as_deref().unwrap_or_default().as_bytes(),
                quote_path,
            ),
            "status" => Cow::Owned(
                self.status
                    .map_or_else(String::new, status_text)
                    .into_bytes(),
            ),
            _ => unreachable!("validate_template rejects unknown placeholders"),
        }
    }
}

/// `value` quoted the way git quotes a path: wrapped in `"..."` with C-style
/// escapes when it holds a control character, `"`, `\`, or, under `quote_path`,
/// a byte above 0x7f.
fn quoted(value: &[u8], quote_path: bool) -> Cow<'_, [u8]> {
    let mode = QuoteMode {
        quote_space: false,
        quote_path,
    };
    if !needs_quoting(value, mode) {
        return Cow::Borrowed(value);
    }
    let mut out = Vec::with_capacity(value.len() + 2);
    out.push(b'"');
    write_escaped(&mut out, value, mode).unwrap();
    out.push(b'"');
    Cow::Owned(out)
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
/// flags (e.g. `"new commits, modified content"`). Includes `STAGED`, unlike
/// the `Display` impl which is tailored to the `status` command. Returns an
/// empty string for clean submodules.
fn status_text(status: StatusSummary) -> String {
    let mut text = String::new();
    let mut push = |part: &str| {
        if !text.is_empty() {
            text.push_str(", ");
        }
        text.push_str(part);
    };
    if status.contains(StatusSummary::UNREADABLE) {
        push("unreadable");
    }
    if status.contains(StatusSummary::NEW_COMMITS) {
        push("new commits");
    }
    if status.contains(StatusSummary::MODIFIED_CONTENT) {
        push("modified content");
    }
    if status.contains(StatusSummary::UNTRACKED_CONTENT) {
        push("untracked content");
    }
    if status.contains(StatusSummary::DELETED_WORKDIR) {
        push("deleted");
    }
    if status.contains(StatusSummary::STAGED_NEW) {
        push("staged (new)");
    } else if status.contains(StatusSummary::STAGED) {
        push("staged");
    }

    text
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

/// Collects metadata for every gitlink in the index of the repository at
/// `root_path`, in path order.
///
/// Parses `.gitmodules` directly for names and branches and reads the parent's
/// `HEAD` tree for committed OIDs, bypassing `repo.submodules()` to avoid
/// libgit2's per-submodule config snapshot overhead. Per-submodule I/O (reading
/// the submodule's HEAD for workdir OID/branch, computing status) is
/// parallelized via rayon.
///
/// `need_submod_head` and `need_local_status` select the expensive operations
/// required by the template.
fn gather_info(
    root_path: &Path,
    server_statuses: Option<&[(GitPath, StatusSummary)]>,
    need_submod_head: bool,
    need_local_status: bool,
) -> ListResult<Vec<SubmoduleInfo>> {
    use std::collections::HashMap;

    use rayon::prelude::*;

    let repo = Repository::open(root_path)?;
    let mut gitmodules = parse_gitmodules(root_path)?;

    // Look up committed OIDs from the parent's HEAD tree
    let head_tree = repo.head()?.peel_to_tree()?;
    let partial: Vec<_> = substatus::gitlink_paths(&repo)?
        .into_iter()
        .map(|path| {
            let commit = path
                .to_path()
                .ok()
                .and_then(|rel| head_tree.get_path(rel).ok())
                .map(|e| e.id());
            let gitmodule = gitmodules.remove(&path);
            (path, commit, gitmodule)
        })
        .collect();

    let status_map: Option<HashMap<&GitPath, StatusSummary>> =
        server_statuses.map(|statuses| statuses.iter().map(|(p, s)| (p, *s)).collect());
    let tl_repo = thread_local::ThreadLocal::new();

    // Resolve per-submodule fields in parallel. The gitlinks arrive in index
    // (path) order, which `collect` preserves.
    partial
        .into_par_iter()
        .map(|(path, commit, gitmodule)| {
            // A path this platform cannot represent has no workdir to read.
            let (head, head_branch) = match path.to_path() {
                Ok(rel) if need_submod_head => read_submodule_head(&root_path.join(rel)),
                _ => (None, None),
            };

            let status = match &status_map {
                Some(map) => Some(map.get(&path).copied().unwrap_or(StatusSummary::clean())),
                None if need_local_status => {
                    let repo = tl_repo.get_or_try(|| Repository::open(root_path))?;
                    Some(
                        substatus::submodule_status(repo, &path)
                            .unwrap_or(StatusSummary::UNREADABLE),
                    )
                }
                None => None,
            };

            let (name, branch) = gitmodule.map_or((None, None), |g| (Some(g.name), g.branch));
            Ok(SubmoduleInfo {
                name,
                path,
                commit,
                head,
                branch,
                head_branch,
                status,
            })
        })
        .collect()
}

/// Computes the column width for each placeholder by taking the maximum of
/// the header label length and all data values, plus any literal overhead
/// characters inside the braces. Placeholders absent from `template` retain
/// a width of zero.
fn compute_placeholder_widths(
    template: &Template<'_, 9>,
    submod_info: &[SubmoduleInfo],
    quote_path: bool,
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
                let value = info.resolve_placeholder(placeholder, quote_path);
                widths[idx] = widths[idx].max(display_width(&value) + overhead[idx]);
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
    quote_path: bool,
) -> Vec<u8> {
    let mut output = Vec::new();
    let widths = if header {
        compute_placeholder_widths(template, submod_info, quote_path)
    } else {
        [0; 9]
    };
    if header {
        output.extend(template.expand(
            |name| Cow::Owned(name.to_ascii_uppercase().into_bytes()),
            &widths,
        ));
    }
    for info in submod_info {
        output.extend(template.expand(|name| info.resolve_placeholder(name, quote_path), &widths));
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
    // The placeholder bitmap controls which metadata fields are fetch and whether
    // the server is contacted.
    let template = Template::parse(format.unwrap_or(DEFAULT_FORMAT), &PLACEHOLDERS)?;
    let used = *template.used();

    // Contact (and possibly cold-start) the watch server only when `{status}` is
    // requested and server use is enabled. Other  formats gather all required
    // fields locally.
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
    let quote_path = ConfigDefaults::read(root_path).quote_path;
    let output = format_output(&infos, &template, header, quote_path);
    std::io::stdout().write_all(&output)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;
    use rstest_reuse::apply;
    use testutil::{HarnessBuilder, RefFormat};

    use crate::test_support::formats;

    // -- gather_info --

    #[apply(formats)]
    fn local_status_of_an_unopenable_submodule_is_unreadable(ref_format: RefFormat) {
        let harness = HarnessBuilder::new()
            .no_server()
            .ref_format(ref_format)
            .submodule("sub_a")
            .submodule("sub_b")
            .build();
        let statuses = || -> Vec<(GitPath, Option<StatusSummary>)> {
            gather_info(harness.root().path(), None, false, true)
                .unwrap()
                .into_iter()
                .map(|info| (info.path, info.status))
                .collect()
        };
        assert_eq!(
            statuses(),
            [
                (GitPath::from("sub_a"), Some(StatusSummary::clean())),
                (GitPath::from("sub_b"), Some(StatusSummary::clean())),
            ]
        );

        harness.submodule("sub_a").declare_unsupported_extension();
        assert_eq!(
            statuses(),
            [
                (GitPath::from("sub_a"), Some(StatusSummary::UNREADABLE)),
                (GitPath::from("sub_b"), Some(StatusSummary::clean())),
            ]
        );
    }

    /// Rows come from the index, so a gitlink without a `.gitmodules` entry
    /// still lists, with an empty name.
    #[apply(formats)]
    fn gitlink_without_a_gitmodules_entry_lists_without_a_name(ref_format: RefFormat) {
        let harness = HarnessBuilder::new()
            .no_server()
            .ref_format(ref_format)
            .submodule("sub_a")
            .submodule("sub_b")
            .build();
        let rows = || {
            let infos = gather_info(harness.root().path(), None, false, false).unwrap();
            String::from_utf8(format_output(&infos, &tmpl("{name} {path}\n"), false, true)).unwrap()
        };
        assert_eq!(rows(), "sub_a sub_a\nsub_b sub_b\n");

        harness.root().run_git(&[
            "config",
            "-f",
            ".gitmodules",
            "--remove-section",
            "submodule.sub_b",
        ]);
        assert_eq!(rows(), "sub_a sub_a\n sub_b\n");
    }

    /// A name and path that are not UTF-8 print quoted under `core.quotePath`
    /// and verbatim without it.
    ///
    /// Linux-only: Windows (NTFS is UTF-16) and macOS (EILSEQ) refuse the name.
    #[cfg(target_os = "linux")]
    #[apply(formats)]
    fn non_utf8_name_and_path_follow_quote_path(ref_format: RefFormat) {
        let harness = HarnessBuilder::new()
            .no_server()
            .ref_format(ref_format)
            .submodule(b"sub\xff")
            .build();
        let infos = gather_info(harness.root().path(), None, false, false).unwrap();
        let template = tmpl("{name} {path}\n");
        assert_eq!(
            format_output(&infos, &template, false, true),
            b"\"sub\\377\" \"sub\\377\"\n"
        );
        assert_eq!(
            format_output(&infos, &template, false, false),
            b"sub\xff sub\xff\n"
        );
    }

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
        assert_eq!(status_text(status), "new commits, modified content, staged");
    }

    #[test]
    fn status_text_all_flags() {
        let status = StatusSummary::MODIFIED_CONTENT
            | StatusSummary::UNTRACKED_CONTENT
            | StatusSummary::NEW_COMMITS
            | StatusSummary::STAGED;
        assert_eq!(
            status_text(status),
            "new commits, modified content, untracked content, staged"
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
            name: Some(name.as_bytes().to_vec()),
            path: GitPath::from(path),
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
        let output = format_output(&infos, &tmpl("{name}\n"), false, true);
        assert_eq!(output, b"a\nb\n");
    }

    #[test]
    fn format_output_with_header() {
        let infos = vec![make_info("sub", "sub", None)];
        let output = format_output(&infos, &tmpl("{name}\n"), true, true);
        let output = String::from_utf8(output).unwrap();
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
        let output = format_output(&infos, &tmpl("{name}: {status}\n"), false, true);
        assert_eq!(output, b"sub: modified content\n");
    }

    #[test]
    fn compute_widths_pads_to_longest() {
        let infos = vec![
            make_info("short", "short", None),
            make_info("much_longer_name", "much_longer_name", None),
        ];
        let widths = compute_placeholder_widths(&tmpl("{name}\n"), &infos, true);
        // "much_longer_name" is 16 chars, "NAME" header is 4; max is 16
        assert_eq!(widths[0], 16);
    }

    #[test]
    fn compute_widths_unused_placeholder_is_zero() {
        let infos = vec![make_info("sub", "sub", None)];
        let widths = compute_placeholder_widths(&tmpl("{name}\n"), &infos, true);
        // "path" (index 1) is not in the template
        assert_eq!(widths[1], 0);
    }
}
