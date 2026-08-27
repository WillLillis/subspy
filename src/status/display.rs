//! Human-readable `git status` output, including the staged/unstaged/untracked
//! sections, summary footer, and submodule lock-failure errors.

use git2::{Repository, Statuses};
use rustc_hash::FxHashSet;

use std::io::{self, Write};

use crate::{
    StatusSummary,
    paint::{GREEN, RED, paint_into},
};

use super::{
    PathFilter, StatusEntries, StatusResult,
    conflict::path_within_any,
    header::{print_header, print_unmerged_paths},
    interleave::{Row, SubRow, for_each_merged},
    relativize::Relativizer,
    tracked::{TrackedOrSubRow, TrackedRow, for_each_tracked_row, normalized_tracked_rows},
};

const STAGED_HEADER: &str = "Changes to be committed:
  (use \"git restore --staged <file>...\" to unstage)";

/// Staged-section header when HEAD is unborn: there's no commit to restore
/// from, so git tells you to use `git rm --cached` to unstage.
const STAGED_HEADER_UNBORN: &str = "Changes to be committed:
  (use \"git rm --cached <file>...\" to unstage)";

const UNTRACKED_HEADER: &str = "Untracked files:
  (use \"git add <file>...\" to include in what will be committed)";

const IGNORED_HEADER: &str = "Ignored files:
  (use \"git add -f <file>...\" to include in what will be committed)";

const UNREADABLE_HEADER: &str = "Submodules with unreadable status:
  (use \"git -C <path> status\" to see the underlying error)";

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

/// Returns `true` if `st` should appear in the "Changes to be committed" section.
const fn is_staged(st: StatusSummary) -> bool {
    st.contains(StatusSummary::STAGED) || st.contains(StatusSummary::STAGED_NEW)
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
        && !st.contains(StatusSummary::UNREADABLE)
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

/// Returns `true` if `st`'s `Display` impl emits the trailing
/// `(modified content, ...)` suffix on a submodule entry.
const fn has_status_info(st: StatusSummary) -> bool {
    st.intersects(
        StatusSummary::MODIFIED_CONTENT
            .union(StatusSummary::UNTRACKED_CONTENT)
            .union(StatusSummary::NEW_COMMITS),
    )
}

/// Prints the "Changes to be committed:" section for staged files, submodules,
/// renames, and deleted submodule paths. Returns `true` if anything was printed.
#[expect(
    clippy::too_many_lines,
    reason = "interleaves files with three submodule row kinds, each rendered inline"
)]
fn print_staged_changes(
    tracked_rows: Vec<TrackedRow<'_>>,
    submodule_statuses: &[(String, StatusSummary)],
    deleted_submodule_paths: &[String],
    renamed_submodules: &[super::SubmoduleRename],
    rel: &Relativizer<'_>,
    is_unborn: bool,
    out: &mut impl Write,
) -> Result<bool, io::Error> {
    let mut header = false;
    let staged_header = if is_unborn {
        STAGED_HEADER_UNBORN
    } else {
        STAGED_HEADER
    };

    // git lists staged files and staged submodule changes (modified/new,
    // deleted, renamed) in one path-sorted stream. The file rows come
    // pre-classified (renames reconciled to match git) in `tracked_rows`;
    // libgit2 excludes submodules from them, so interleave the submodule rows.
    // Non-staged (worktree-only) entries fall through the `istatus` match below.
    let mut submods: Vec<SubRow<'_>> = Vec::new();
    submods.extend(
        deleted_submodule_paths
            .iter()
            .map(|path| SubRow::Deleted(path)),
    );
    submods.extend(renamed_submodules.iter().map(SubRow::Renamed));
    submods.extend(
        submodule_statuses
            .iter()
            .filter(|(_, st)| is_staged(*st))
            .map(|(path, st)| SubRow::Modified(path, *st)),
    );

    for_each_tracked_row(tracked_rows, submods, |row| match row {
        TrackedOrSubRow::File(TrackedRow::Entry(entry)) => {
            // RENAMED before MODIFIED: git2 sets both on a rename that also
            // changes content, and git labels it `renamed:`, not `modified:`.
            let istatus = match entry.status() {
                s if s.contains(git2::Status::INDEX_NEW) => "new file:   ",
                s if s.contains(git2::Status::INDEX_RENAMED) => "renamed:    ",
                s if s.contains(git2::Status::INDEX_MODIFIED) => "modified:   ",
                s if s.contains(git2::Status::INDEX_DELETED) => "deleted:    ",
                s if s.contains(git2::Status::INDEX_TYPECHANGE) => "typechange: ",
                // Worktree-only entry; rendered by the unstaged section instead.
                _ => return Ok(()),
            };
            let Some(index) = entry.head_to_index() else {
                return Ok(());
            };
            if !header {
                writeln!(out, "{staged_header}")?;
                header = true;
            }
            let old_path = index.old_file().path_bytes();
            let new_path = index.new_file().path_bytes();
            match (old_path, new_path) {
                (Some(old), Some(new)) if old != new => {
                    paint_into(out, GREEN, |out| {
                        write!(out, "\t{istatus}")?;
                        rel.write_to(out, old)?;
                        out.write_all(b" -> ")?;
                        rel.write_to(out, new)
                    })?;
                }
                (old, new) => {
                    let path = old.or(new).unwrap();
                    paint_into(out, GREEN, |out| {
                        write!(out, "\t{istatus}")?;
                        rel.write_to(out, path)
                    })?;
                }
            }
            writeln!(out)
        }
        TrackedOrSubRow::File(TrackedRow::SyntheticOrdinary(row)) => {
            let istatus = match row.x {
                'A' => "new file:   ",
                'D' => "deleted:    ",
                _ => return Ok(()),
            };
            if !header {
                writeln!(out, "{staged_header}")?;
                header = true;
            }
            paint_into(out, GREEN, |out| {
                write!(out, "\t{istatus}")?;
                rel.write_to(out, &row.path)
            })?;
            writeln!(out)
        }
        TrackedOrSubRow::File(TrackedRow::SyntheticRename(row)) => {
            if !header {
                writeln!(out, "{staged_header}")?;
                header = true;
            }
            paint_into(out, GREEN, |out| {
                write!(out, "\trenamed:    ")?;
                rel.write_to(out, &row.old.path)?;
                out.write_all(b" -> ")?;
                rel.write_to(out, &row.new.path)
            })?;
            writeln!(out)
        }
        TrackedOrSubRow::Sub(SubRow::Deleted(path)) => {
            if !header {
                writeln!(out, "{staged_header}")?;
                header = true;
            }
            paint_into(out, GREEN, |out| {
                write!(out, "\tdeleted:    ")?;
                rel.write_to(out, path.as_bytes())
            })?;
            writeln!(out)
        }
        TrackedOrSubRow::Sub(SubRow::Renamed(rename)) => {
            if !header {
                writeln!(out, "{staged_header}")?;
                header = true;
            }
            paint_into(out, GREEN, |out| {
                write!(out, "\trenamed:    ")?;
                rel.write_to(out, rename.old.as_bytes())?;
                out.write_all(b" -> ")?;
                rel.write_to(out, rename.new.as_bytes())
            })?;
            writeln!(out)
        }
        TrackedOrSubRow::Sub(SubRow::Modified(submod_path, st)) => {
            if !header {
                writeln!(out, "{staged_header}")?;
                header = true;
            }
            let label = staged_label(st);
            paint_into(out, GREEN, |out| {
                write!(out, "\t{label}")?;
                rel.write_to(out, submod_path.as_bytes())
            })?;
            writeln!(out)
        }
    })?;

    if header {
        writeln!(out)?;
    }
    Ok(header)
}

/// Prints the "Changes not staged for commit:" section for modified, deleted,
/// and dirty-submodule entries. Returns `true` if anything was printed.
fn print_unstaged_changes(
    non_submod: &Statuses<'_>,
    phantom_deletes: &FxHashSet<Vec<u8>>,
    path_filter: PathFilter<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    rm_in_workdir: bool,
    rel: &Relativizer<'_>,
    out: &mut impl Write,
) -> Result<bool, io::Error> {
    let has_submod_changes = submodule_statuses
        .iter()
        .any(|(_, st)| has_workdir_changes(*st));
    let mut header = false;

    // git lists unstaged file changes and dirty submodules in one path-sorted
    // stream. Deleted/renamed submodule rows are staged-only, so this section
    // interleaves files with the unstaged submodule rows. libgit2 excludes
    // submodules from `non_submod`.
    let files = non_submod.iter().filter(|e| {
        let st = e.status();
        path_filter.keeps(e.path_bytes())
            && !st.contains(git2::Status::CONFLICTED)
            && (phantom_deletes.is_empty() || !phantom_deletes.contains(e.path_bytes()))
            && st.intersects(
                git2::Status::WT_MODIFIED
                    | git2::Status::WT_DELETED
                    | git2::Status::WT_RENAMED
                    | git2::Status::WT_TYPECHANGE,
            )
    });
    let submods: Vec<SubRow<'_>> = submodule_statuses
        .iter()
        .filter(|(_, st)| is_unstaged(*st))
        .map(|(path, st)| SubRow::Modified(path, *st))
        .collect();

    for_each_merged(files, submods, |row| match row {
        Row::File(entry) => {
            let Some(workdir) = entry.index_to_workdir() else {
                return Ok(());
            };
            // RENAMED before MODIFIED, matching the staged section above. (git
            // does not detect unstaged worktree renames, so WT_RENAMED does not
            // arise in practice, but keep the ordering consistent and correct.)
            let istatus = match entry.status() {
                s if s.contains(git2::Status::WT_RENAMED) => "renamed:    ",
                s if s.contains(git2::Status::WT_MODIFIED) => "modified:   ",
                s if s.contains(git2::Status::WT_DELETED) => "deleted:    ",
                s if s.contains(git2::Status::WT_TYPECHANGE) => "typechange: ",
                _ => return Ok(()),
            };
            if !header {
                writeln!(
                    out,
                    "{}",
                    unstaged_header(rm_in_workdir, has_submod_changes)
                )?;
                header = true;
            }
            let old_path = workdir.old_file().path_bytes();
            let new_path = workdir.new_file().path_bytes();
            match (old_path, new_path) {
                (Some(old), Some(new)) if old != new => {
                    paint_into(out, RED, |out| {
                        write!(out, "\t{istatus}")?;
                        rel.write_to(out, old)?;
                        out.write_all(b" -> ")?;
                        rel.write_to(out, new)
                    })?;
                }
                (old, new) => {
                    let path = old.or(new).unwrap();
                    paint_into(out, RED, |out| {
                        write!(out, "\t{istatus}")?;
                        rel.write_to(out, path)
                    })?;
                }
            }
            writeln!(out)
        }
        Row::Sub(SubRow::Modified(submod_path, submod_status)) => {
            if !header {
                writeln!(
                    out,
                    "{}",
                    unstaged_header(rm_in_workdir, has_submod_changes)
                )?;
                header = true;
            }
            let label = unstaged_label(submod_status);
            paint_into(out, RED, |out| {
                write!(out, "\t{label}")?;
                rel.write_to(out, submod_path.as_bytes())
            })?;
            if has_status_info(submod_status) {
                writeln!(out, " {submod_status}")
            } else {
                writeln!(out)
            }
        }
        // Deleted/renamed submodule rows are staged changes; they never appear
        // in the unstaged section, so this section builds none of them.
        Row::Sub(SubRow::Deleted(_) | SubRow::Renamed(_)) => Ok(()),
    })?;

    if header {
        writeln!(out)?;
    }
    Ok(header)
}

/// Prints the "Untracked files:" section. Returns `true` if any were printed.
fn print_untracked_files(
    non_submod: &Statuses<'_>,
    conflicted_paths: &FxHashSet<Vec<u8>>,
    path_filter: PathFilter<'_>,
    rel: &Relativizer<'_>,
    out: &mut impl Write,
) -> Result<bool, io::Error> {
    let mut header = false;
    for entry in non_submod
        .iter()
        .filter(|e| e.status() == git2::Status::WT_NEW && path_filter.keeps(e.path_bytes()))
    {
        let Some(file) = entry
            .index_to_workdir()
            .and_then(|idx| idx.old_file().path_bytes())
        else {
            continue;
        };
        // libgit2 reports a conflicted submodule's working tree as untracked
        // (`sub/`, or `sub/...` under `-uall`); git shows it only under "Unmerged
        // paths", so drop those rows.
        if path_within_any(file, conflicted_paths) {
            continue;
        }
        if !header {
            writeln!(out, "{UNTRACKED_HEADER}")?;
            header = true;
        }
        out.write_all(b"\t")?;
        paint_into(out, RED, |out| rel.write_to(out, file))?;
        writeln!(out)?;
    }
    if header {
        writeln!(out)?;
    }
    Ok(header)
}

/// Prints the "Ignored files:" section.
fn print_ignored_files(
    non_submod: &Statuses<'_>,
    path_filter: PathFilter<'_>,
    rel: &Relativizer<'_>,
    out: &mut impl Write,
) -> Result<(), io::Error> {
    let mut header = false;
    for entry in non_submod.iter().filter(|e| {
        e.status() == git2::Status::IGNORED && path_filter.keeps_ignored(e.path_bytes())
    }) {
        let Some(file) = entry
            .index_to_workdir()
            .and_then(|idx| idx.old_file().path_bytes())
        else {
            continue;
        };
        if !header {
            writeln!(out, "{IGNORED_HEADER}")?;
            header = true;
        }
        out.write_all(b"\t")?;
        paint_into(out, RED, |out| rel.write_to(out, file))?;
        writeln!(out)?;
    }
    if header {
        writeln!(out)?;
    }
    Ok(())
}

/// Prints the section listing submodules whose status could not be read.
fn print_unreadable_submodules(
    submodules: &[(String, StatusSummary)],
    out: &mut impl Write,
) -> Result<bool, io::Error> {
    let mut header = false;
    for (path, _) in submodules
        .iter()
        .filter(|(_, st)| st.contains(StatusSummary::UNREADABLE))
    {
        if !header {
            writeln!(out, "{UNREADABLE_HEADER}")?;
            header = true;
        }
        writeln!(out, "\t{path}")?;
    }
    if header {
        writeln!(out)?;
    }
    Ok(header)
}

/// What the working tree looks like, for the footer-summary decision.
#[expect(
    clippy::struct_excessive_bools,
    reason = "four independent signals about the working tree; no natural grouping"
)]
struct SummaryState {
    changes_in_index: bool,
    changed_in_workdir: bool,
    has_untracked: bool,
    has_unreadable: bool,
    is_unborn: bool,
}

/// Prints the footer hint (e.g. "nothing added to commit but untracked files present").
fn print_summary(state: &SummaryState, out: &mut impl Write) -> Result<(), io::Error> {
    let &SummaryState {
        changes_in_index,
        changed_in_workdir,
        has_untracked,
        has_unreadable,
        is_unborn,
    } = state;
    match (changes_in_index, changed_in_workdir, has_untracked) {
        (false, true, _) => {
            writeln!(
                out,
                "no changes added to commit (use \"git add\" and/or \"git commit -a\")"
            )?;
        }
        // Nothing observed changed. Stay silent when a submodule couldn't be read, we can't claim
        // a clean tree here.
        (false, false, false) if !has_unreadable => {
            if is_unborn {
                writeln!(
                    out,
                    "nothing to commit (create/copy files and use \"git add\" to track)"
                )?;
            } else {
                writeln!(out, "nothing to commit, working tree clean")?;
            }
        }
        (false, false, true) => {
            writeln!(
                out,
                "nothing added to commit but untracked files present (use \"git add\" to track)"
            )?;
        }
        _ => {}
    }

    Ok(())
}

/// Formats and prints the full `git status`-style output: header, staged changes,
/// unmerged paths, unstaged changes, untracked files, and lock file errors.
// Basic logic originally adapted from https://github.com/rust-lang/git2-rs/blob/master/examples/status.rs
pub fn display_status(
    out: &mut impl Write,
    repo: &Repository,
    entries: &StatusEntries<'_>,
    rel: &Relativizer<'_>,
    ahead_behind: bool,
    show_stash: bool,
) -> StatusResult<()> {
    let StatusEntries {
        non_submod,
        submodules,
        deleted_submodules,
        renamed_submodules,
        conflicted_paths,
        phantom_deletes,
        // Long format renders an unmerged submodule via `print_unmerged_paths`
        // and relies on it already being excluded from `submodules`; the folded
        // `S<c><m><u>` status is a porcelain-v2-only concern.
        conflicted_submodules: _,
        path_filter,
    } = *entries;

    let is_unborn = repo
        .head()
        .err()
        .is_some_and(|e| e.code() == git2::ErrorCode::UnbornBranch);

    print_header(repo, out, ahead_behind)?;

    let rm_in_workdir = non_submod.iter().any(|e| {
        path_filter.keeps(e.path_bytes())
            && e.status().contains(git2::Status::WT_DELETED)
            && (phantom_deletes.is_empty() || !phantom_deletes.contains(e.path_bytes()))
    }) || submodules
        .iter()
        .any(|(_, st)| st.contains(StatusSummary::DELETED_WORKDIR));

    let tracked_rows = normalized_tracked_rows(repo, entries);
    let changes_in_index = print_staged_changes(
        tracked_rows,
        submodules,
        deleted_submodules,
        renamed_submodules,
        rel,
        is_unborn,
        out,
    )?;
    let has_conflicts = print_unmerged_paths(repo, path_filter, rel, out)?;
    let changed_in_workdir = print_unstaged_changes(
        non_submod,
        phantom_deletes,
        path_filter,
        submodules,
        rm_in_workdir,
        rel,
        out,
    )?;
    let has_untracked = print_untracked_files(non_submod, conflicted_paths, path_filter, rel, out)?;
    print_ignored_files(non_submod, path_filter, rel, out)?;
    let has_unreadable = print_unreadable_submodules(submodules, out)?;

    print_summary(
        &SummaryState {
            changes_in_index,
            changed_in_workdir: changed_in_workdir || has_conflicts,
            has_untracked,
            has_unreadable,
            is_unborn,
        },
        out,
    )?;

    if show_stash {
        print_stash_trailer(repo, out)?;
    }

    Ok(())
}

/// Emits git's `--show-stash` trailer line (`Your stash currently has
/// N entry/entries`), or nothing when the repo has no stashes. Stashes
/// are tracked via the `refs/stash` reflog; missing reflog means 0.
fn print_stash_trailer(repo: &Repository, out: &mut impl Write) -> Result<(), io::Error> {
    let count = repo.reflog("refs/stash").map_or(0, |r| r.len());
    if count == 0 {
        return Ok(());
    }
    let noun = if count == 1 { "entry" } else { "entries" };
    writeln!(out, "Your stash currently has {count} {noun}")
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
    fn clean_is_not_unstaged() {
        assert!(!is_unstaged(StatusSummary::clean()));
    }

    #[test]
    fn unreadable_excluded() {
        let st = StatusSummary::UNREADABLE;
        assert!(!is_staged(st));
        assert!(!is_unstaged(st));
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

    // -- has_status_info --

    #[test]
    fn status_info_modified_content() {
        assert!(has_status_info(StatusSummary::MODIFIED_CONTENT));
    }

    #[test]
    fn status_info_untracked_content() {
        assert!(has_status_info(StatusSummary::UNTRACKED_CONTENT));
    }

    #[test]
    fn status_info_new_commits() {
        // NEW_COMMITS alone does qualify here, unlike `has_workdir_changes`.
        assert!(has_status_info(StatusSummary::NEW_COMMITS));
    }

    #[test]
    fn status_info_staged_only() {
        // Display omits STAGED bits, so a STAGED-only status produces
        // no suffix and the predicate must return false.
        assert!(!has_status_info(StatusSummary::STAGED));
        assert!(!has_status_info(StatusSummary::STAGED_NEW));
    }

    #[test]
    fn status_info_deleted_workdir_only() {
        // Display also omits DELETED_WORKDIR (the "deleted:" label
        // already carries that info).
        assert!(!has_status_info(StatusSummary::DELETED_WORKDIR));
    }

    #[test]
    fn status_info_clean() {
        assert!(!has_status_info(StatusSummary::clean()));
    }
}
