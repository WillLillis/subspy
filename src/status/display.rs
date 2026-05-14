//! Human-readable `git status` output, including the staged/unstaged/untracked
//! sections, summary footer, and submodule lock-failure errors.

use git2::{Repository, Statuses};

use std::io::{self, Write};

use crate::{
    StatusSummary,
    paint::{GREEN, RED, paint_into},
};

use super::relativize::Relativizer;

use super::{
    StatusResult,
    header::{print_header, print_unmerged_paths},
};

const STAGED_HEADER: &str = "Changes to be committed:
  (use \"git restore --staged <file>...\" to unstage)";

const UNTRACKED_HEADER: &str = "Untracked files:
  (use \"git add <file>...\" to include in what will be committed)";

const LOCK_FILE_ERROR_FOOTER: &str =
    "Another git/subspy process seems to be running in this repository, e.g.
an editor opened by 'git commit'. Please make sure all processes
are terminated then try `subspy reindex`. If it still fails, a git/subspy
process may have crashed in this repository earlier:
remove the file manually, `subspy reindex`, and retry to continue.";

fn unstaged_header(rm_in_workdir: bool, has_submod_changes: bool) -> String {
    format!(
        "Changes not staged for commit:
  (use \"git add{} <file>...\" to update what will be committed)
  (use \"git restore <file>...\" to discard changes in working directory){}",
        if rm_in_workdir { "/rm" } else { "" },
        if has_submod_changes {
            "\n  (commit or discard the untracked or modified content in submodules)"
        } else {
            ""
        }
    )
}

// -- Submodule display predicates --
//
// These capture the filtering logic used by `print_staged_changes`,
// `print_unstaged_changes`, and `print_lock_file_errors` so the
// decisions about which submodules appear in each section are testable
// independently of the rendering.

/// Returns `true` if `st` should appear in the "Changes to be committed" section.
const fn is_staged(st: StatusSummary) -> bool {
    (st.contains(StatusSummary::STAGED) || st.contains(StatusSummary::STAGED_NEW))
        && !st.contains(StatusSummary::LOCK_FAILURE)
}

/// Returns the display label for a staged submodule.
const fn staged_label(st: StatusSummary) -> &'static str {
    if st.contains(StatusSummary::STAGED_NEW) {
        "new file:   "
    } else {
        "modified:   "
    }
}

/// Returns `true` if `st` has unstaged changes that belong in the
/// "Changes not staged for commit" section.
fn is_unstaged(st: StatusSummary) -> bool {
    !st.is_empty()
        && st != StatusSummary::STAGED
        && st != StatusSummary::STAGED_NEW
        && !st.contains(StatusSummary::LOCK_FAILURE)
}

/// Returns the display label for an unstaged submodule entry.
const fn unstaged_label(st: StatusSummary) -> &'static str {
    if st.contains(StatusSummary::DELETED_WORKDIR) {
        "deleted:    "
    } else {
        "modified:   "
    }
}

/// Returns `true` if `st` has untracked or modified content within the
/// submodule's working tree. Controls whether the
/// "(commit or discard the untracked or modified content in submodules)"
/// hint appears in the unstaged header. `NEW_COMMITS` alone (a gitlink
/// divergence) does not qualify.
const fn has_workdir_changes(st: StatusSummary) -> bool {
    st.contains(StatusSummary::MODIFIED_CONTENT) || st.contains(StatusSummary::UNTRACKED_CONTENT)
}

/// Prints the "Changes to be committed:" section for staged files, submodules,
/// and deleted submodule paths. Returns `true` if anything was printed.
fn print_staged_changes(
    non_submod: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    deleted_submodule_paths: &[String],
    rel: &Relativizer<'_>,
    stdout: &mut impl Write,
) -> Result<bool, io::Error> {
    let mut header = false;

    for entry in non_submod
        .iter()
        .filter(|e| e.status() != git2::Status::CURRENT)
    {
        let istatus = match entry.status() {
            s if s.contains(git2::Status::INDEX_NEW) => "new file:   ",
            s if s.contains(git2::Status::INDEX_MODIFIED) => "modified:   ",
            s if s.contains(git2::Status::INDEX_DELETED) => "deleted:    ",
            s if s.contains(git2::Status::INDEX_RENAMED) => "renamed:    ",
            s if s.contains(git2::Status::INDEX_TYPECHANGE) => "typechange: ",
            _ => continue,
        };
        if !header {
            writeln!(stdout, "{STAGED_HEADER}")?;
            header = true;
        }
        let Some(index) = entry.head_to_index() else {
            continue;
        };
        let old_path = index.old_file().path();
        let new_path = index.new_file().path();
        match (old_path, new_path) {
            (Some(old), Some(new)) if old != new => {
                let old_str = old.to_string_lossy();
                let new_str = new.to_string_lossy();
                paint_into(stdout, GREEN, |out| {
                    write!(out, "\t{istatus}")?;
                    rel.write_to(out, &old_str)?;
                    out.write_all(b" -> ")?;
                    rel.write_to(out, &new_str)
                })?;
                writeln!(stdout)?;
            }
            (old, new) => {
                let path_str = old.or(new).unwrap().to_string_lossy();
                paint_into(stdout, GREEN, |out| {
                    write!(out, "\t{istatus}")?;
                    rel.write_to(out, &path_str)
                })?;
                writeln!(stdout)?;
            }
        }
    }

    for path in deleted_submodule_paths {
        if !header {
            writeln!(stdout, "{STAGED_HEADER}")?;
            header = true;
        }
        paint_into(stdout, GREEN, |out| {
            write!(out, "\tdeleted:    ")?;
            rel.write_to(out, path)
        })?;
        writeln!(stdout)?;
    }

    for (submod_path, st) in submodule_statuses.iter().filter(|(_, st)| is_staged(*st)) {
        if !header {
            writeln!(stdout, "{STAGED_HEADER}")?;
            header = true;
        }
        let label = staged_label(*st);
        paint_into(stdout, GREEN, |out| {
            write!(out, "\t{label}")?;
            rel.write_to(out, submod_path)
        })?;
        writeln!(stdout)?;
    }

    if header {
        writeln!(stdout)?;
    }
    Ok(header)
}

/// Prints the "Changes not staged for commit:" section for modified, deleted,
/// and dirty-submodule entries. Returns `true` if anything was printed.
fn print_unstaged_changes(
    non_submod: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    rm_in_workdir: bool,
    rel: &Relativizer<'_>,
    stdout: &mut impl Write,
) -> Result<bool, io::Error> {
    let has_submod_changes = submodule_statuses
        .iter()
        .any(|(_, st)| has_workdir_changes(*st));
    let mut header = false;

    for entry in non_submod.iter() {
        let status = entry.status();
        if status == git2::Status::CURRENT || status.contains(git2::Status::CONFLICTED) {
            continue;
        }
        let Some(workdir) = entry.index_to_workdir() else {
            continue;
        };
        let istatus = match status {
            s if s.contains(git2::Status::WT_MODIFIED) => "modified:   ",
            s if s.contains(git2::Status::WT_DELETED) => "deleted:    ",
            s if s.contains(git2::Status::WT_RENAMED) => "renamed:    ",
            s if s.contains(git2::Status::WT_TYPECHANGE) => "typechange: ",
            _ => continue,
        };
        if !header {
            writeln!(
                stdout,
                "{}",
                unstaged_header(rm_in_workdir, has_submod_changes)
            )?;
            header = true;
        }
        let old_path = workdir.old_file().path();
        let new_path = workdir.new_file().path();
        match (old_path, new_path) {
            (Some(old), Some(new)) if old != new => {
                let old_str = old.to_string_lossy();
                let new_str = new.to_string_lossy();
                paint_into(stdout, RED, |out| {
                    write!(out, "\t{istatus}")?;
                    rel.write_to(out, &old_str)?;
                    out.write_all(b" -> ")?;
                    rel.write_to(out, &new_str)
                })?;
                writeln!(stdout)?;
            }
            (old, new) => {
                let path_str = old.or(new).unwrap().to_string_lossy();
                paint_into(stdout, RED, |out| {
                    write!(out, "\t{istatus}")?;
                    rel.write_to(out, &path_str)
                })?;
                writeln!(stdout)?;
            }
        }
    }

    for (submod_path, submod_status) in submodule_statuses.iter().filter(|(_, st)| is_unstaged(*st))
    {
        if !header {
            writeln!(
                stdout,
                "{}",
                unstaged_header(rm_in_workdir, has_submod_changes)
            )?;
            header = true;
        }
        let label = unstaged_label(*submod_status);
        let istatus = submod_status.to_string();
        paint_into(stdout, RED, |out| {
            write!(out, "\t{label}")?;
            rel.write_to(out, submod_path)
        })?;
        if istatus.is_empty() {
            writeln!(stdout)?;
        } else {
            writeln!(stdout, " {istatus}")?;
        }
    }

    if header {
        writeln!(stdout)?;
    }
    Ok(header)
}

/// Prints the "Untracked files:" section. Returns `true` if any were printed.
fn print_untracked_files(
    non_submod: &Statuses<'_>,
    rel: &Relativizer<'_>,
    stdout: &mut impl Write,
) -> Result<bool, io::Error> {
    let mut header = false;
    for entry in non_submod
        .iter()
        .filter(|e| e.status() == git2::Status::WT_NEW)
    {
        let Some(file) = entry
            .index_to_workdir()
            .and_then(|idx| idx.old_file().path())
        else {
            continue;
        };
        if !header {
            writeln!(stdout, "{UNTRACKED_HEADER}")?;
            header = true;
        }
        let file_str = file.to_string_lossy();
        stdout.write_all(b"\t")?;
        paint_into(stdout, RED, |out| rel.write_to(out, &file_str))?;
        writeln!(stdout)?;
    }
    if header {
        writeln!(stdout)?;
    }
    Ok(header)
}

/// Prints the footer hint (e.g. "nothing added to commit but untracked files present").
fn print_summary(
    changes_in_index: bool,
    changed_in_workdir: bool,
    has_untracked: bool,
    stdout: &mut impl Write,
) -> Result<(), io::Error> {
    match (changes_in_index, changed_in_workdir, has_untracked) {
        (false, true, _) => {
            writeln!(
                stdout,
                "no changes added to commit (use \"git add\" and/or \"git commit -a\")"
            )?;
        }
        (false, false, false) => writeln!(stdout, "nothing to commit, working tree clean")?,
        (false, false, true) => {
            writeln!(
                stdout,
                "nothing added to commit but untracked files present (use \"git add\" to track)"
            )?;
        }
        _ => {}
    }

    Ok(())
}

/// Prints error messages for submodules whose `index.lock` could not be acquired.
fn print_lock_file_errors(
    submodule_statuses: &[(String, StatusSummary)],
    stdout: &mut impl Write,
) -> Result<(), io::Error> {
    let mut footer = false;
    for (submod_path, _) in submodule_statuses
        .iter()
        .filter(|(_, st)| st.contains(StatusSummary::LOCK_FAILURE))
    {
        if !footer {
            writeln!(stdout)?;
        }
        footer = true;
        writeln!(
            stdout,
            "error: Unable to create index.lock file for '{submod_path}': File exists."
        )?;
    }
    if footer {
        writeln!(stdout, "\n{LOCK_FILE_ERROR_FOOTER}")?;
    }

    Ok(())
}

/// Formats and prints the full `git status`-style output: header, staged changes,
/// unmerged paths, unstaged changes, untracked files, and lock file errors.
// Basic logic originally adapted from https://github.com/rust-lang/git2-rs/blob/master/examples/status.rs
pub fn display_status(
    out: &mut impl Write,
    repo: &Repository,
    non_submodule_statuses: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    deleted_submodule_paths: &[String],
    rel: &Relativizer<'_>,
) -> StatusResult<()> {
    // Fast path: nothing dirty
    if non_submodule_statuses.is_empty()
        && submodule_statuses.is_empty()
        && deleted_submodule_paths.is_empty()
    {
        print_header(repo, out)?;
        writeln!(out, "nothing to commit, working tree clean")?;
        return Ok(());
    }

    print_header(repo, out)?;

    let rm_in_workdir = non_submodule_statuses
        .iter()
        .any(|e| e.status().contains(git2::Status::WT_DELETED))
        || submodule_statuses
            .iter()
            .any(|(_, st)| st.contains(StatusSummary::DELETED_WORKDIR));

    let changes_in_index = print_staged_changes(
        non_submodule_statuses,
        submodule_statuses,
        deleted_submodule_paths,
        rel,
        out,
    )?;
    let has_conflicts = print_unmerged_paths(repo, rel, out)?;
    let changed_in_workdir = print_unstaged_changes(
        non_submodule_statuses,
        submodule_statuses,
        rm_in_workdir,
        rel,
        out,
    )?;
    let has_untracked = print_untracked_files(non_submodule_statuses, rel, out)?;

    print_summary(
        changes_in_index,
        changed_in_workdir || has_conflicts,
        has_untracked,
        out,
    )?;

    print_lock_file_errors(submodule_statuses, out)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn staged_modified_submodule() {
        let st = StatusSummary::STAGED;
        assert!(is_staged(st));
        assert_eq!(staged_label(st), "modified:   ");
        assert!(!is_unstaged(st));
    }

    #[test]
    fn staged_new_submodule() {
        let st = StatusSummary::STAGED_NEW;
        assert!(is_staged(st));
        assert_eq!(staged_label(st), "new file:   ");
        assert!(!is_unstaged(st));
    }

    #[test]
    fn staged_with_unstaged_changes() {
        let st = StatusSummary::STAGED | StatusSummary::MODIFIED_CONTENT;
        assert!(is_staged(st));
        assert_eq!(staged_label(st), "modified:   ");
        assert!(is_unstaged(st));
    }

    #[test]
    fn staged_new_with_unstaged_changes() {
        let st = StatusSummary::STAGED_NEW | StatusSummary::UNTRACKED_CONTENT;
        assert!(is_staged(st));
        assert_eq!(staged_label(st), "new file:   ");
        assert!(is_unstaged(st));
    }

    #[test]
    fn unstaged_only() {
        let st = StatusSummary::MODIFIED_CONTENT;
        assert!(!is_staged(st));
        assert!(is_unstaged(st));
    }

    #[test]
    fn new_commits_only() {
        let st = StatusSummary::NEW_COMMITS;
        assert!(!is_staged(st));
        assert!(is_unstaged(st));
    }

    #[test]
    fn lock_failure_excluded_from_both() {
        let st = StatusSummary::LOCK_FAILURE;
        assert!(!is_staged(st));
        assert!(!is_unstaged(st));
    }

    #[test]
    fn lock_failure_with_staged_excluded() {
        let st = StatusSummary::STAGED | StatusSummary::LOCK_FAILURE;
        assert!(!is_staged(st));
        assert!(!is_unstaged(st));
    }

    #[test]
    fn clean_is_not_unstaged() {
        assert!(!is_unstaged(StatusSummary::clean()));
    }

    // -- has_workdir_changes --

    #[test]
    fn workdir_changes_modified_content() {
        assert!(has_workdir_changes(StatusSummary::MODIFIED_CONTENT));
    }

    #[test]
    fn workdir_changes_untracked_content() {
        assert!(has_workdir_changes(StatusSummary::UNTRACKED_CONTENT));
    }

    #[test]
    fn workdir_changes_new_commits_only() {
        assert!(!has_workdir_changes(StatusSummary::NEW_COMMITS));
    }

    #[test]
    fn workdir_changes_staged_only() {
        assert!(!has_workdir_changes(StatusSummary::STAGED));
    }

    #[test]
    fn workdir_changes_new_commits_with_untracked() {
        let st = StatusSummary::NEW_COMMITS | StatusSummary::UNTRACKED_CONTENT;
        assert!(has_workdir_changes(st));
    }

    #[test]
    fn workdir_changes_clean() {
        assert!(!has_workdir_changes(StatusSummary::clean()));
    }
}
