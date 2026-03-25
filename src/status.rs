//! The `status` subcommand: displays submodule and working-tree status
//! in a format that mirrors `git status`.

use anstyle::AnsiColor;
use git2::{Repository, Statuses};
use std::{cmp::Ordering, fs, path::Path};
use thiserror::Error;

use crate::{
    RepoKind, StatusSummary,
    connection::client::{recv_status_response, send_status_request},
    paint,
    watch::{LockFileError, LockFileGuard},
};

pub type StatusResult<T> = Result<T, StatusError>;

#[derive(Error, Debug)]
pub enum StatusError {
    #[error(transparent)]
    BincodeEncode(#[from] bincode::error::EncodeError),
    #[error(transparent)]
    BincodeDecode(#[from] bincode::error::DecodeError),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error(transparent)]
    LockFile(#[from] LockFileError),
    #[error(transparent)]
    VersionMismatch(#[from] crate::connection::VersionMismatchError),
}

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

#[derive(Debug, PartialEq, Eq)]
struct RebaseInfo {
    onto_short: String,
    head_name: String,
    done_ops: Vec<String>,
    total_done: usize,
    remaining_ops: Vec<String>,
    total_remaining: usize,
    is_interactive: bool,
    is_editing: bool,
}

/// Parses lines from a rebase todo/done file, skipping blanks and comments, and shortening
/// any 40-char hex hash in the second field to 7 chars (matching git's status display format).
fn parse_rebase_lines(content: &str) -> Vec<String> {
    content
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|line| {
            let mut parts = line.splitn(3, ' ');
            let Some(cmd) = parts.next() else {
                return line.to_string();
            };
            let Some(hash_or_arg) = parts.next() else {
                return line.to_string();
            };
            if hash_or_arg.len() >= 40 && hash_or_arg.chars().all(|c| c.is_ascii_hexdigit()) {
                let short = &hash_or_arg[..7];
                parts.next().map_or_else(
                    || format!("{cmd} {short}"),
                    |rest| format!("{cmd} {short} {rest}"),
                )
            } else {
                line.to_string()
            }
        })
        .collect()
}

fn get_rebase_info(repo: &Repository) -> StatusResult<Option<RebaseInfo>> {
    // Use git2 for state detection; `open_rebase()` is not used because libgit2 does not
    // support opening interactive rebases started by the git command-line.
    let state = repo.state();
    let is_interactive = state == git2::RepositoryState::RebaseInteractive;
    if !is_interactive && state != git2::RepositoryState::RebaseMerge {
        return Ok(None);
    }

    let rebase_merge = repo.path().join("rebase-merge");
    if !rebase_merge.is_dir() {
        return Ok(None);
    }

    let onto_raw = fs::read_to_string(rebase_merge.join("onto")).unwrap_or_default();
    let onto_short: String = onto_raw.trim().chars().take(7).collect();
    if onto_short.is_empty() {
        return Ok(None);
    }

    let head_name_raw = fs::read_to_string(rebase_merge.join("head-name")).unwrap_or_default();
    let head_name = head_name_raw
        .trim()
        .strip_prefix("refs/heads/")
        .unwrap_or_else(|| head_name_raw.trim())
        .to_string();

    let done_raw = fs::read_to_string(rebase_merge.join("done")).unwrap_or_default();
    let all_done = parse_rebase_lines(&done_raw);
    let total_done = all_done.len();
    // Show last 2 done ops to match git's display limit
    let done_ops: Vec<String> = all_done.into_iter().rev().take(2).rev().collect();

    let todo_raw = fs::read_to_string(rebase_merge.join("git-rebase-todo")).unwrap_or_default();
    let all_remaining = parse_rebase_lines(&todo_raw);
    let total_remaining = all_remaining.len();
    // Show next 2 remaining ops to match git's display limit
    let remaining_ops: Vec<String> = all_remaining.into_iter().take(2).collect();

    // Editing mode: the `amend` file is written by git after successfully applying an
    // 'edit' operation. Use git2's index API to confirm there are no unresolved conflicts.
    let is_editing = rebase_merge.join("amend").exists() && !repo.index()?.has_conflicts();

    Ok(Some(RebaseInfo {
        onto_short,
        head_name,
        done_ops,
        total_done,
        remaining_ops,
        total_remaining,
        is_interactive,
        is_editing,
    }))
}

fn print_rebase_header(info: &RebaseInfo) {
    let label = if info.is_interactive {
        "interactive rebase"
    } else {
        "rebase"
    };
    println!(
        "{} {}",
        paint(Some(AnsiColor::Red), &format!("{label} in progress; onto")),
        info.onto_short
    );

    if info.total_done > 0 {
        let shown = info.done_ops.len();
        if shown == 1 {
            println!("Last command done ({} command done):", info.total_done);
        } else {
            println!(
                "Last {shown} commands done ({} commands done):",
                info.total_done
            );
        }
        for cmd in &info.done_ops {
            println!("   {cmd}");
        }
    }

    if info.total_remaining == 0 {
        println!("No commands remaining.");
    } else {
        let shown = info.remaining_ops.len();
        if shown == 1 {
            println!(
                "Next command to do ({} remaining command):",
                info.total_remaining
            );
        } else {
            println!(
                "Next {shown} commands to do ({} remaining commands):",
                info.total_remaining
            );
        }
        for cmd in &info.remaining_ops {
            println!("   {cmd}");
        }
        println!("  (use \"git rebase --edit-todo\" to view and edit)");
    }

    if info.is_editing {
        println!(
            "You are currently editing a commit while rebasing branch '{}' on '{}'.",
            info.head_name, info.onto_short
        );
        println!("  (use \"git commit --amend\" to amend the current commit)");
        println!("  (use \"git rebase --continue\" once you are satisfied with your changes)");
    } else {
        println!(
            "You are currently rebasing branch '{}' on '{}'.",
            info.head_name, info.onto_short
        );
        println!("  (fix conflicts and then run \"git rebase --continue\")");
        println!("  (use \"git rebase --skip\" to skip this patch)");
        println!("  (use \"git rebase --abort\" to check out the original branch)");
    }
    println!();
}

/// Prints the "Unmerged paths:" section for any conflicts in the index.
/// Returns `true` if there were conflicts.
fn print_unmerged_paths(repo: &Repository) -> StatusResult<bool> {
    let index = repo.index()?;
    if !index.has_conflicts() {
        return Ok(false);
    }

    println!("Unmerged paths:");
    println!("  (use \"git restore --staged <file>...\" to unstage)");
    println!("  (use \"git add <file>...\" to mark resolution)");

    for conflict in index.conflicts()? {
        let conflict = conflict?;
        let path = conflict
            .our
            .as_ref()
            .or(conflict.their.as_ref())
            .or(conflict.ancestor.as_ref())
            .and_then(|e| std::str::from_utf8(&e.path).ok())
            .unwrap_or("<unknown path>");

        // Padded to 17 chars to match git's column alignment
        #[allow(clippy::match_same_arms)]
        let type_str = match (
            conflict.ancestor.is_some(),
            conflict.our.is_some(),
            conflict.their.is_some(),
        ) {
            (true, true, true) => "both modified:   ",
            (false, true, true) => "both added:      ",
            (true, false, true) => "deleted by us:   ",
            (true, true, false) => "deleted by them: ",
            (true, false, false) => "both deleted:    ",
            (false, true, false) => "added by us:     ",
            (false, false, true) => "added by them:   ",
            (false, false, false) => "both modified:   ",
        };
        println!(
            "{}",
            paint(Some(AnsiColor::Red), &format!("\t{type_str}{path}"))
        );
    }
    println!();
    Ok(true)
}

/// The detected repository state, used to print the appropriate header.
#[derive(Debug, PartialEq, Eq)]
enum HeaderState {
    Rebase(RebaseInfo),
    CherryPick {
        short_oid: String,
        has_conflicts: bool,
    },
    Merge {
        has_conflicts: bool,
    },
    Revert {
        short_oid: String,
        has_conflicts: bool,
    },
    Bisect,
    ApplyMailbox {
        has_conflicts: bool,
    },
    /// Rebase using the apply backend (`git rebase --apply`), which uses
    /// the `rebase-apply/` directory instead of `rebase-merge/`.
    RebaseWithApplyBackend {
        has_conflicts: bool,
    },
    Normal {
        branch_display: String,
        upstream: Option<(String, &'static str)>,
    },
}

/// Reads a `*_HEAD` file (e.g. `CHERRY_PICK_HEAD`, `REVERT_HEAD`) and returns
/// the first 7 characters of the OID, or the full content if shorter.
fn read_short_oid(repo: &Repository, filename: &str) -> String {
    let path = repo.path().join(filename);
    let oid = fs::read_to_string(path).unwrap_or_default();
    let trimmed = oid.trim();
    trimmed.get(..7).unwrap_or(trimmed).to_string()
}

fn get_header_state(repo: &Repository) -> StatusResult<HeaderState> {
    if let Some(info) = get_rebase_info(repo)? {
        return Ok(HeaderState::Rebase(info));
    }

    // `git rebase --apply` uses `rebase-apply/` instead of `rebase-merge/`.
    // git2 reports this as `RepositoryState::Rebase`, which `get_rebase_info`
    // doesn't handle since it only reads from `rebase-merge/`.
    if repo.path().join("rebase-apply").join("rebasing").exists() {
        let has_conflicts = repo.index()?.has_conflicts();
        return Ok(HeaderState::RebaseWithApplyBackend { has_conflicts });
    }

    let branch_display = current_branch_display(repo)?;
    let has_conflicts = repo.index()?.has_conflicts();

    match repo.state() {
        git2::RepositoryState::CherryPick | git2::RepositoryState::CherryPickSequence => {
            Ok(HeaderState::CherryPick {
                short_oid: read_short_oid(repo, "CHERRY_PICK_HEAD"),
                has_conflicts,
            })
        }
        git2::RepositoryState::Merge => Ok(HeaderState::Merge { has_conflicts }),
        git2::RepositoryState::Revert | git2::RepositoryState::RevertSequence => {
            Ok(HeaderState::Revert {
                short_oid: read_short_oid(repo, "REVERT_HEAD"),
                has_conflicts,
            })
        }
        git2::RepositoryState::Bisect => Ok(HeaderState::Bisect),
        git2::RepositoryState::ApplyMailbox | git2::RepositoryState::ApplyMailboxOrRebase => {
            // rebase-apply/rebasing exists for `git rebase --apply`,
            // rebase-apply/applying exists for `git am`.
            let rebase_apply = repo.path().join("rebase-apply");
            if rebase_apply.join("rebasing").exists() {
                Ok(HeaderState::RebaseWithApplyBackend { has_conflicts })
            } else {
                Ok(HeaderState::ApplyMailbox { has_conflicts })
            }
        }
        _ => Ok(HeaderState::Normal {
            branch_display,
            upstream: get_upstream_status(repo)?,
        }),
    }
}

fn print_header(repo: &Repository) -> StatusResult<()> {
    let state = get_header_state(repo)?;
    print_header_state(&state);
    Ok(())
}

fn print_header_state(state: &HeaderState) {
    match state {
        HeaderState::Rebase(info) => print_rebase_header(info),
        HeaderState::CherryPick {
            short_oid,
            has_conflicts,
        } => {
            println!("You are currently cherry-picking commit {short_oid}.");
            if *has_conflicts {
                println!("  (fix conflicts and run \"git cherry-pick --continue\")");
            } else {
                println!("  (all conflicts fixed: run \"git cherry-pick --continue\")");
            }
            println!("  (use \"git cherry-pick --skip\" to skip this patch)");
            println!("  (use \"git cherry-pick --abort\" to cancel the cherry-pick operation)");
            println!();
        }
        HeaderState::Merge { has_conflicts } => {
            if *has_conflicts {
                println!("You have unmerged paths.");
                println!("  (fix conflicts and run \"git commit\")");
                println!("  (use \"git merge --abort\" to abort the merge)");
            } else {
                println!("All conflicts fixed but you are still merging.");
                println!("  (use \"git commit\" to conclude merge)");
            }
            println!();
        }
        HeaderState::Revert {
            short_oid,
            has_conflicts,
        } => {
            println!("You are currently reverting commit {short_oid}.");
            if *has_conflicts {
                println!("  (fix conflicts and run \"git revert --continue\")");
            } else {
                println!("  (all conflicts fixed: run \"git revert --continue\")");
            }
            println!("  (use \"git revert --skip\" to skip this patch)");
            println!("  (use \"git revert --abort\" to cancel the revert operation)");
            println!();
        }
        HeaderState::Bisect => {
            println!("You are currently bisecting.");
            println!("  (use \"git bisect reset\" to get back to the original branch)");
            println!();
        }
        HeaderState::ApplyMailbox { has_conflicts } => {
            println!("You are in the middle of an am session.");
            if *has_conflicts {
                println!("  (fix conflicts and then run \"git am --continue\")");
            } else {
                println!("  (all conflicts fixed: run \"git am --continue\")");
            }
            println!("  (use \"git am --skip\" to skip this patch)");
            println!("  (use \"git am --abort\" to restore the original branch)");
            println!();
        }
        HeaderState::RebaseWithApplyBackend { has_conflicts } => {
            println!("You are currently rebasing.");
            if *has_conflicts {
                println!("  (fix conflicts and then run \"git rebase --continue\")");
            } else {
                println!("  (all conflicts fixed: run \"git rebase --continue\")");
            }
            println!("  (use \"git rebase --skip\" to skip this patch)");
            println!("  (use \"git rebase --abort\" to check out the original branch)");
            println!();
        }
        HeaderState::Normal {
            branch_display,
            upstream,
        } => {
            println!("{branch_display}");
            if let Some((status_line, hint)) = upstream {
                println!("{status_line}");
                if !hint.is_empty() {
                    println!("  {hint}");
                }
                println!();
            }
        }
    }
}

fn print_staged_changes(
    non_submod: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    new_submodule_paths: &[String],
    deleted_submodule_paths: &[String],
) -> bool {
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
            println!("{STAGED_HEADER}");
            header = true;
        }
        let Some(index) = entry.head_to_index() else {
            continue;
        };
        let old_path = index.old_file().path();
        let new_path = index.new_file().path();
        match (old_path, new_path) {
            (Some(old), Some(new)) if old != new => println!(
                "{}",
                paint(
                    Some(AnsiColor::Green),
                    &format!("\t{istatus}{} -> {}", old.display(), new.display()),
                )
            ),
            (old, new) => println!(
                "{}",
                paint(
                    Some(AnsiColor::Green),
                    &format!("\t{istatus}{}", old.or(new).unwrap().display()),
                )
            ),
        }
    }

    for path in new_submodule_paths {
        if !header {
            println!("{STAGED_HEADER}");
            header = true;
        }
        println!(
            "{}",
            paint(Some(AnsiColor::Green), &format!("\tnew file:   {path}"))
        );
    }

    for path in deleted_submodule_paths {
        if !header {
            println!("{STAGED_HEADER}");
            header = true;
        }
        println!(
            "{}",
            paint(Some(AnsiColor::Green), &format!("\tdeleted:    {path}"))
        );
    }

    for (submod_path, _) in submodule_statuses.iter().filter(|(_, st)| {
        st.contains(StatusSummary::STAGED) && !st.contains(StatusSummary::LOCK_FAILURE)
    }) {
        if !header {
            println!("{STAGED_HEADER}");
            header = true;
        }
        println!(
            "{}",
            paint(
                Some(AnsiColor::Green),
                &format!("\tmodified:   {submod_path}")
            )
        );
    }

    if header {
        println!();
    }
    header
}

fn print_unstaged_changes(
    non_submod: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    rm_in_workdir: bool,
) -> bool {
    let has_submod_changes = submodule_statuses
        .iter()
        .any(|(_, st)| !st.eq(&StatusSummary::STAGED) && !st.contains(StatusSummary::LOCK_FAILURE));
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
            println!("{}", unstaged_header(rm_in_workdir, has_submod_changes));
            header = true;
        }
        let old_path = workdir.old_file().path();
        let new_path = workdir.new_file().path();
        match (old_path, new_path) {
            (Some(old), Some(new)) if old != new => println!(
                "{}",
                paint(
                    Some(AnsiColor::Red),
                    &format!("\t{istatus}{} -> {}", old.display(), new.display()),
                )
            ),
            (old, new) => println!(
                "{}",
                paint(
                    Some(AnsiColor::Red),
                    &format!("\t{istatus}{}", old.or(new).unwrap().display()),
                )
            ),
        }
    }

    for (submod_path, submod_status) in submodule_statuses.iter().filter(|(_, st)| {
        !st.eq(&StatusSummary::STAGED) && !st.contains(StatusSummary::LOCK_FAILURE)
    }) {
        if !header {
            println!("{}", unstaged_header(rm_in_workdir, true));
            header = true;
        }
        let istatus = submod_status.to_string();
        print!(
            "{}",
            paint(
                Some(AnsiColor::Red),
                &format!("\tmodified:   {submod_path}")
            )
        );
        if istatus.is_empty() {
            println!();
        } else {
            println!(" {istatus}");
        }
    }

    if header {
        println!();
    }
    header
}

fn print_untracked_files(non_submod: &Statuses<'_>) -> bool {
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
            println!("{UNTRACKED_HEADER}");
            header = true;
        }
        println!(
            "\t{}",
            paint(Some(AnsiColor::Red), &format!("{}", file.display()))
        );
    }
    if header {
        println!();
    }
    header
}

fn print_summary(changes_in_index: bool, changed_in_workdir: bool, has_untracked: bool) {
    match (changes_in_index, changed_in_workdir, has_untracked) {
        (false, true, _) => {
            println!("no changes added to commit (use \"git add\" and/or \"git commit -a\")");
        }
        (false, false, false) => println!("nothing to commit, working tree clean"),
        (false, false, true) => {
            println!(
                "nothing added to commit but untracked files present (use \"git add\" to track)"
            );
        }
        _ => {}
    }
}

fn print_lock_file_errors(submodule_statuses: &[(String, StatusSummary)]) {
    let mut footer = false;
    for (submod_path, _) in submodule_statuses
        .iter()
        .filter(|(_, st)| st.contains(StatusSummary::LOCK_FAILURE))
    {
        if !footer {
            println!();
        }
        footer = true;
        println!("error: Unable to create index.lock file for '{submod_path}': File exists.");
    }
    if footer {
        println!("\n{LOCK_FILE_ERROR_FOOTER}");
    }
}

fn current_branch_display(repo: &Repository) -> StatusResult<String> {
    let head_ref = repo.head()?;
    if !head_ref.is_branch() {
        return Ok(format!(
            "{} {}",
            paint(Some(AnsiColor::Red), "HEAD detached at"),
            head_ref.target().map_or_else(
                || "unknown".to_string(),
                |oid| oid.to_string().chars().take(7).collect()
            ),
        ));
    }
    let branch_name = head_ref.shorthand().unwrap().to_string();
    Ok(format!("On branch {branch_name}"))
}

fn get_upstream_status(repo: &Repository) -> StatusResult<Option<(String, &'static str)>> {
    let head_ref = repo.head()?;
    if !head_ref.is_branch() {
        return Ok(None);
    }

    let local_branch = git2::Branch::wrap(head_ref);
    let Ok(upstream_branch) = local_branch.upstream() else {
        return Ok(None);
    };

    let name = upstream_branch
        .get()
        .shorthand()
        .unwrap_or("unknown")
        .to_string();

    // Get local and upstream commit OIDs
    let local_oid = local_branch.get().peel_to_commit()?.id();
    let upstream_oid = upstream_branch.get().peel_to_commit()?.id();

    // Compare graphs
    let (ahead, behind) = repo.graph_ahead_behind(local_oid, upstream_oid)?;

    let commit_s = |n: usize| if n == 1 { "commit" } else { "commits" };

    match (ahead.cmp(&0), behind.cmp(&0)) {
        (Ordering::Equal, Ordering::Equal) => Ok(Some((
            format!("Your branch is up to date with '{name}'."),
            "",
        ))),
        (Ordering::Greater, Ordering::Equal) => Ok(Some((
            format!(
                "Your branch is ahead of '{name}' by {ahead} {}.",
                commit_s(ahead)
            ),
            "(use \"git push\" to publish your local commits)",
        ))),
        (Ordering::Equal, Ordering::Greater) => Ok(Some((
            format!(
                "Your branch is behind '{name}' by {behind} {}, and can be fast-forwarded.",
                commit_s(behind)
            ),
            "(use \"git pull\" to update your local branch)",
        ))),
        _ => {
            Ok(Some((
                format!(
                    "Your branch and '{name}' have diverged,\nand have {ahead} and {behind} different {} each, respectively.",
                    commit_s(ahead + behind) // git uses plural when total > 1
                ),
                "(use \"git pull\" if you want to integrate the remote branch with yours)",
            )))
        }
    }
}

// Basic logic originally adapted from https://github.com/rust-lang/git2-rs/blob/master/examples/status.rs
fn display_status(
    repo: &Repository,
    non_submodule_statuses: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    new_submodule_paths: &[String],
    deleted_submodule_paths: &[String],
) -> StatusResult<()> {
    // Fast path: nothing dirty
    if non_submodule_statuses.is_empty()
        && submodule_statuses.is_empty()
        && new_submodule_paths.is_empty()
        && deleted_submodule_paths.is_empty()
    {
        print_header(repo)?;
        println!("nothing to commit, working tree clean");
        print_lock_file_errors(submodule_statuses);
        return Ok(());
    }

    print_header(repo)?;

    let rm_in_workdir = non_submodule_statuses
        .iter()
        .any(|e| e.status().contains(git2::Status::WT_DELETED));

    let changes_in_index = print_staged_changes(
        non_submodule_statuses,
        submodule_statuses,
        new_submodule_paths,
        deleted_submodule_paths,
    );
    let has_conflicts = print_unmerged_paths(repo)?;
    let changed_in_workdir =
        print_unstaged_changes(non_submodule_statuses, submodule_statuses, rm_in_workdir);
    let has_untracked = print_untracked_files(non_submodule_statuses);

    print_summary(
        changes_in_index,
        changed_in_workdir || has_conflicts,
        has_untracked,
    );

    print_lock_file_errors(submodule_statuses);

    Ok(())
}

/// Returns the relative paths of newly-added submodules.
///
/// These are submodules whose gitlink has been staged via `git submodule add`
/// but not yet committed (present in the index but absent from HEAD).
///
/// # Errors
///
/// Returns `Err` if the repository index cannot be read.
pub fn new_submodule_paths(repo: &Repository) -> StatusResult<Vec<String>> {
    let head_tree = repo.head().ok().and_then(|h| h.peel_to_tree().ok());
    let index = repo.index()?;
    let paths = index
        .iter()
        .filter(|entry| {
            // `FileMode::Commit` is the gitlink mode used for submodule entries. Note that
            // `FileMode::Commit as u32` gives the enum discriminant (6), not the mode value,
            // so the `From` impl must be used.
            entry.mode == u32::from(git2::FileMode::Commit)
                && head_tree.as_ref().is_none_or(|t| {
                    std::str::from_utf8(&entry.path).is_ok_and(|p| {
                        matches!(
                            t.get_path(Path::new(p)),
                            // New submodules are staged but not in the HEAD commit yet, so looking
                            // them up should return `NotFound`.
                            Err(e) if e.code() == git2::ErrorCode::NotFound
                        )
                    })
                })
        })
        .filter_map(|entry| String::from_utf8(entry.path).ok())
        .collect();
    Ok(paths)
}

/// Returns the relative paths of submodules staged for deletion.
///
/// These are submodules whose gitlink is in the HEAD commit but has been removed
/// from the index (via `git rm`), the symmetric counterpart to [`new_submodule_paths`].
///
/// # Errors
///
/// Returns `Err` if the HEAD tree cannot be walked or the index cannot be read.
pub fn deleted_submodule_paths(repo: &Repository) -> StatusResult<Vec<String>> {
    let Some(head_tree) = repo.head().ok().and_then(|h| h.peel_to_tree().ok()) else {
        return Ok(Vec::new());
    };
    let index = repo.index()?;

    let mut deleted = Vec::new();
    head_tree.walk(git2::TreeWalkMode::PreOrder, |root, entry| {
        if entry.filemode() == i32::from(git2::FileMode::Commit) {
            let Some(name) = entry.name() else {
                return git2::TreeWalkResult::Skip;
            };
            let path = if root.is_empty() {
                name.to_string()
            } else {
                format!("{root}{name}")
            };
            if index.get_path(Path::new(&path), 0).is_none() {
                deleted.push(path);
            }
            git2::TreeWalkResult::Skip
        } else {
            git2::TreeWalkResult::Ok
        }
    })?;

    Ok(deleted)
}

/// Retrieves and displays the statuses for the repository at `path`.
///
/// # Errors
///
/// Returns `Err` if statuses cannot be retrieved from the repository or watch server
pub fn status(
    root_path: &Path,
    repo_kind: RepoKind,
    display_progress: bool,
    use_server: bool,
) -> StatusResult<()> {
    // Send IPC request early so the server starts processing while we do local work.
    let mut conn = if use_server {
        Some(send_status_request(root_path)?)
    } else {
        None
    };

    let repo = Repository::open(root_path)?;

    let mut opts = git2::StatusOptions::new();
    opts.include_untracked(true)
        .recurse_untracked_dirs(false)
        .include_ignored(false);

    // Ignore submodules _only_ if we are the top level, in which case submodule statuses
    // are provided by the watch server or computed locally below.
    if repo_kind == RepoKind::WithSubmodules {
        opts.exclude_submodules(true);
    }

    let non_submodule_statuses = repo.statuses(Some(&mut opts))?;
    let new_submodule_paths = new_submodule_paths(&repo)?;
    let deleted_submodule_paths = deleted_submodule_paths(&repo)?;

    let submodule_statuses = match conn {
        Some(ref mut c) => recv_status_response(c, display_progress)?.0,
        None if repo_kind == RepoKind::WithSubmodules => compute_local_statuses(root_path, &repo)?,
        None => Vec::new(),
    };

    display_status(
        &repo,
        &non_submodule_statuses,
        &submodule_statuses,
        &new_submodule_paths,
        &deleted_submodule_paths,
    )?;

    Ok(())
}

/// Computes submodule statuses locally via git2 without the watch server.
///
/// # Errors
///
/// Returns `StatusError` if the lock file cannot be acquired or git2 fails
/// to read submodule status.
///
/// # Panics
///
/// Panics if a submodule path contains non-UTF-8.
pub fn compute_local_statuses(
    root_path: &Path,
    repo: &Repository,
) -> StatusResult<Vec<(String, StatusSummary)>> {
    use rayon::prelude::*;

    let lock_path = repo.path().join("index.lock");
    let submodules = {
        let _lock = LockFileGuard::acquire(&lock_path, None)?;
        repo.submodules()?
    };
    let tl_repo = thread_local::ThreadLocal::new();

    let paths: Vec<&str> = submodules
        .iter()
        .map(|s| s.path().to_str().expect("Submodule path is not UTF-8"))
        .collect();

    let statuses: StatusResult<Vec<_>> = paths
        .into_par_iter()
        .map(|path| -> StatusResult<(&str, StatusSummary)> {
            let repo = tl_repo.get_or_try(|| Repository::open(root_path))?;
            let st = repo.submodule_status(path, git2::SubmoduleIgnore::None)?;
            let summary: StatusSummary = st.into();
            Ok((path, summary))
        })
        .filter(|r| !matches!(r, Ok((_, s)) if *s == StatusSummary::CLEAN))
        .map(|r| r.map(|(path, s)| (path.to_string(), s)))
        .collect();

    statuses
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn git(args: &[&str]) {
        let output = std::process::Command::new("git")
            .args(["-c", "user.name=Test", "-c", "user.email=test@test.com"])
            .args(args)
            .output()
            .expect("failed to run git");
        assert!(
            output.status.success(),
            "git {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    /// Creates a repo with an initial commit containing `file.txt`.
    fn init_repo() -> (TempDir, Repository) {
        let tmp = TempDir::new().unwrap();
        let root = tmp.path().display().to_string();
        git(&["-C", &root, "init"]);
        std::fs::write(tmp.path().join("file.txt"), "initial\n").unwrap();
        git(&["-C", &root, "add", "-A"]);
        git(&["-C", &root, "commit", "-m", "initial"]);
        let repo = Repository::open(tmp.path()).unwrap();
        (tmp, repo)
    }

    /// Creates a diverged branch that conflicts on `file.txt`.
    fn create_conflicting_branch(root: &str, root_path: &Path, branch: &str) {
        git(&["-C", root, "checkout", "-b", branch]);
        std::fs::write(root_path.join("file.txt"), format!("{branch} content\n")).unwrap();
        git(&["-C", root, "add", "-A"]);
        git(&["-C", root, "commit", "-m", &format!("{branch} commit")]);
        git(&["-C", root, "checkout", "master"]);
        std::fs::write(root_path.join("file.txt"), "master content\n").unwrap();
        git(&["-C", root, "add", "-A"]);
        git(&["-C", root, "commit", "-m", "master diverge"]);
    }

    #[test]
    fn header_state_clean_repo() {
        let (_tmp, repo) = init_repo();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(state, HeaderState::Normal { .. }),
            "expected Normal, got {state:?}"
        );
    }

    #[test]
    fn header_state_cherry_pick_with_conflict() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "pick-me");

        // Cherry-pick the conflicting commit (will fail with conflict)
        let output = std::process::Command::new("git")
            .args(["-c", "user.name=Test", "-c", "user.email=test@test.com"])
            .args(["-C", &root, "cherry-pick", "pick-me"])
            .output()
            .unwrap();
        assert!(!output.status.success(), "expected cherry-pick to conflict");

        // Re-open repo to pick up state changes
        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state,
                HeaderState::CherryPick {
                    has_conflicts: true,
                    ..
                }
            ),
            "expected CherryPick with conflicts, got {state:?}"
        );
        if let HeaderState::CherryPick { short_oid, .. } = &state {
            assert_eq!(short_oid.len(), 7);
        }
    }

    #[test]
    fn header_state_merge_with_conflict() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "feature");

        let output = std::process::Command::new("git")
            .args(["-C", &root, "merge", "feature"])
            .output()
            .unwrap();
        assert!(!output.status.success(), "expected merge to conflict");

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state,
                HeaderState::Merge {
                    has_conflicts: true
                }
            ),
            "expected Merge with conflicts, got {state:?}"
        );
    }

    #[test]
    fn header_state_revert_with_conflict() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();

        // Commit A: change file.txt to "aaa"
        std::fs::write(tmp.path().join("file.txt"), "aaa\n").unwrap();
        git(&["-C", &root, "add", "-A"]);
        git(&["-C", &root, "commit", "-m", "commit A"]);

        // Commit B: change file.txt to "bbb"
        std::fs::write(tmp.path().join("file.txt"), "bbb\n").unwrap();
        git(&["-C", &root, "add", "-A"]);
        git(&["-C", &root, "commit", "-m", "commit B"]);

        // Revert commit A (changes "aaa" -> "initial"), but current is "bbb",
        // so git can't apply the reverse patch cleanly.
        let output = std::process::Command::new("git")
            .args([
                "-c",
                "user.name=Test",
                "-c",
                "user.email=test@test.com",
                "-C",
                &root,
                "revert",
                "HEAD~1",
                "--no-edit",
            ])
            .output()
            .unwrap();
        assert!(!output.status.success(), "expected revert to conflict");

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state,
                HeaderState::Revert {
                    has_conflicts: true,
                    ..
                }
            ),
            "expected Revert with conflicts, got {state:?}"
        );
        if let HeaderState::Revert { short_oid, .. } = &state {
            assert_eq!(short_oid.len(), 7);
        }
    }

    #[test]
    fn header_state_cherry_pick_conflicts_resolved() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "pick-me");

        let output = std::process::Command::new("git")
            .args(["-c", "user.name=Test", "-c", "user.email=test@test.com"])
            .args(["-C", &root, "cherry-pick", "pick-me"])
            .output()
            .unwrap();
        assert!(!output.status.success(), "expected cherry-pick to conflict");

        // Resolve the conflict by accepting the incoming content and staging
        std::fs::write(tmp.path().join("file.txt"), "resolved\n").unwrap();
        git(&["-C", &root, "add", "file.txt"]);

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state,
                HeaderState::CherryPick {
                    has_conflicts: false,
                    ..
                }
            ),
            "expected CherryPick without conflicts, got {state:?}"
        );
    }

    #[test]
    fn header_state_merge_conflicts_resolved() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "feature");

        let output = std::process::Command::new("git")
            .args(["-C", &root, "merge", "feature"])
            .output()
            .unwrap();
        assert!(!output.status.success(), "expected merge to conflict");

        // Resolve and stage
        std::fs::write(tmp.path().join("file.txt"), "resolved\n").unwrap();
        git(&["-C", &root, "add", "file.txt"]);

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state,
                HeaderState::Merge {
                    has_conflicts: false
                }
            ),
            "expected Merge without conflicts, got {state:?}"
        );
    }

    #[test]
    fn header_state_bisect() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();

        // Add a second commit so we have a range to bisect
        std::fs::write(tmp.path().join("file.txt"), "changed\n").unwrap();
        git(&["-C", &root, "add", "-A"]);
        git(&["-C", &root, "commit", "-m", "second"]);

        git(&["-C", &root, "bisect", "start"]);
        git(&["-C", &root, "bisect", "bad", "HEAD"]);
        git(&["-C", &root, "bisect", "good", "HEAD~1"]);

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert_eq!(state, HeaderState::Bisect);
    }

    #[test]
    fn header_state_git_am_with_conflict() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "patch-src");

        // Generate a patch from the conflicting branch
        let patch_output = std::process::Command::new("git")
            .args(["-C", &root, "format-patch", "master..patch-src", "--stdout"])
            .output()
            .unwrap();
        assert!(patch_output.status.success());
        let patch_file = tmp.path().join("conflict.patch");
        std::fs::write(&patch_file, &patch_output.stdout).unwrap();

        // Apply the patch (will conflict with master's diverged file.txt)
        let output = std::process::Command::new("git")
            .args(["-C", &root, "am", &patch_file.display().to_string()])
            .output()
            .unwrap();
        assert!(!output.status.success(), "expected git am to conflict");

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        // git am patch failures don't produce index conflicts - the patch
        // simply fails to apply and the index stays clean.
        assert!(
            matches!(state, HeaderState::ApplyMailbox { .. }),
            "expected ApplyMailbox, got {state:?}"
        );
    }

    #[test]
    fn header_state_rebase_apply_backend_with_conflict() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "rebase-src");

        // Rebase master onto rebase-src using the apply backend
        let output = std::process::Command::new("git")
            .args([
                "-c",
                "user.name=Test",
                "-c",
                "user.email=test@test.com",
                "-C",
                &root,
                "rebase",
                "--apply",
                "rebase-src",
            ])
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "expected rebase --apply to conflict"
        );

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state,
                HeaderState::RebaseWithApplyBackend {
                    has_conflicts: true
                }
            ),
            "expected RebaseWithApplyBackend with conflicts, got {state:?}"
        );
    }
}
