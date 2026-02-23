use anstyle::AnsiColor;
use git2::{Repository, Statuses};
use std::{fs, path::Path};
use thiserror::Error;

use crate::{RepoKind, StatusSummary, connection::client::request_status, paint};

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

fn print_normal_header(repo: &Repository) -> StatusResult<()> {
    println!("{}", current_branch_display(repo)?);
    if let (Some(upstream_status), Some(upstream_name)) =
        (get_upstream_status(repo)?, get_upstream_ref_name(repo)?)
    {
        println!("Your branch is {upstream_status} with '{upstream_name}'.\n");
    }
    Ok(())
}

fn print_staged_changes(
    non_submod: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    new_submodule_paths: &[String],
) -> bool {
    let mut header = false;

    for entry in non_submod
        .iter()
        .filter(|e| e.status() != git2::Status::CURRENT)
    {
        let istatus = match entry.status() {
            s if s.contains(git2::Status::INDEX_NEW) => "new file: ",
            s if s.contains(git2::Status::INDEX_MODIFIED) => "modified: ",
            s if s.contains(git2::Status::INDEX_DELETED) => "deleted: ",
            s if s.contains(git2::Status::INDEX_RENAMED) => "renamed: ",
            s if s.contains(git2::Status::INDEX_TYPECHANGE) => "typechange:",
            _ => continue,
        };
        if !header {
            println!("{STAGED_HEADER}");
            header = true;
        }
        let old_path = entry.head_to_index().unwrap().old_file().path();
        let new_path = entry.head_to_index().unwrap().new_file().path();
        match (old_path, new_path) {
            (Some(old), Some(new)) if old != new => println!(
                "{}",
                paint(
                    Some(AnsiColor::Green),
                    &format!("\t{istatus}  {} -> {}", old.display(), new.display()),
                )
            ),
            (old, new) => println!(
                "{}",
                paint(
                    Some(AnsiColor::Green),
                    &format!("\t{istatus}  {}", old.or(new).unwrap().display()),
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

    for (submod_path, _) in submodule_statuses.iter().filter(|(_, st)| {
        st.contains(StatusSummary::STAGED) && !st.eq(&StatusSummary::LOCK_FAILURE)
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
        .any(|(_, st)| !st.eq(&StatusSummary::STAGED));
    let mut header = false;

    for entry in non_submod.iter() {
        if entry.status() == git2::Status::CURRENT || entry.index_to_workdir().is_none() {
            continue;
        }
        if entry.status().contains(git2::Status::CONFLICTED) {
            continue;
        }
        let istatus = match entry.status() {
            s if s.contains(git2::Status::WT_MODIFIED) => "modified: ",
            s if s.contains(git2::Status::WT_DELETED) => "deleted: ",
            s if s.contains(git2::Status::WT_RENAMED) => "renamed: ",
            s if s.contains(git2::Status::WT_TYPECHANGE) => "typechange:",
            _ => continue,
        };
        if !header {
            println!("{}", unstaged_header(rm_in_workdir, has_submod_changes));
            header = true;
        }
        let old_path = entry.index_to_workdir().unwrap().old_file().path();
        let new_path = entry.index_to_workdir().unwrap().new_file().path();
        match (old_path, new_path) {
            (Some(old), Some(new)) if old != new => println!(
                "{}",
                paint(
                    Some(AnsiColor::Red),
                    &format!("\t{istatus}  {} -> {}", old.display(), new.display()),
                )
            ),
            (old, new) => println!(
                "{}",
                paint(
                    Some(AnsiColor::Red),
                    &format!("\t{istatus}  {}", old.or(new).unwrap().display()),
                )
            ),
        }
    }

    for (submod_path, submod_status) in submodule_statuses
        .iter()
        .filter(|(_, st)| !st.eq(&StatusSummary::STAGED) && !st.eq(&StatusSummary::LOCK_FAILURE))
    {
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
        if !header {
            println!("{UNTRACKED_HEADER}");
            header = true;
        }
        let file = entry.index_to_workdir().unwrap().old_file().path().unwrap();
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
        .filter(|(_, st)| st.eq(&StatusSummary::LOCK_FAILURE))
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

fn get_upstream_ref_name(repo: &Repository) -> StatusResult<Option<String>> {
    let head = repo.head()?;
    if !head.is_branch() {
        return Ok(None); // Detached HEAD, no upstream
    }
    let current_branch = git2::Branch::wrap(head);
    let Ok(upstream) = current_branch.upstream() else {
        // No upstream set
        return Ok(None);
    };
    let upstream_ref = upstream.get();
    let name = upstream_ref.shorthand().map(|s| s.to_string());
    Ok(name)
}

fn get_upstream_status(repo: &Repository) -> StatusResult<Option<String>> {
    let head_ref = repo.head()?;
    if !head_ref.is_branch() {
        return Ok(None);
    }

    let local_branch = git2::Branch::wrap(head_ref);
    let Ok(upstream_branch) = local_branch.upstream() else {
        return Ok(None);
    };

    // Get local and upstream commit OIDs
    let local_oid = local_branch.get().peel_to_commit()?.id();
    let upstream_oid = upstream_branch.get().peel_to_commit()?.id();

    // Compare graphs
    let (ahead, behind) = repo.graph_ahead_behind(local_oid, upstream_oid)?;

    if ahead == 0 && behind == 0 {
        Ok(Some("up to date".to_string()))
    } else if ahead > 0 && behind == 0 {
        Ok(Some(format!("ahead by {ahead} commit(s)")))
    } else if ahead == 0 && behind > 0 {
        Ok(Some(format!("behind by {behind} commit(s)")))
    } else if ahead > 0 && behind > 0 {
        Ok(Some(format!(
            "diverged (ahead by {ahead}, behind by {behind})",
        )))
    } else {
        Ok(None)
    }
}

// Basic logic originally adapted from https://github.com/rust-lang/git2-rs/blob/master/examples/status.rs
fn display_status(
    repo: &Repository,
    non_submodule_statues: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    new_submodule_paths: &[String],
) -> StatusResult<()> {
    match get_rebase_info(repo)? {
        Some(ref info) => print_rebase_header(info),
        None => print_normal_header(repo)?,
    }

    let rm_in_workdir = non_submodule_statues
        .iter()
        .any(|e| e.status().contains(git2::Status::WT_DELETED));

    let changes_in_index = print_staged_changes(
        non_submodule_statues,
        submodule_statuses,
        new_submodule_paths,
    );
    let has_conflicts = print_unmerged_paths(repo)?;
    let changed_in_workdir =
        print_unstaged_changes(non_submodule_statues, submodule_statuses, rm_in_workdir);
    let has_untracked = print_untracked_files(non_submodule_statues);

    print_summary(
        changes_in_index,
        changed_in_workdir || has_conflicts,
        has_untracked,
    );

    print_lock_file_errors(submodule_statuses);

    Ok(())
}

/// Retrieves and displays the statuses for the repository at `path`.
///
/// # Errors
///
/// Returns `Err` if statuses cannot be retrieved from the repository or watch server
pub fn status(root_path: &Path, repo_kind: RepoKind) -> StatusResult<()> {
    let repo = Repository::open(root_path)?;

    let mut opts = git2::StatusOptions::new();
    opts.include_untracked(true)
        .recurse_untracked_dirs(false)
        .include_ignored(false);

    // Ignore submodules _only_ if we are the top level, in which case submodule statuses
    // are provided by the watch server.
    if repo_kind == RepoKind::WithSubmodules {
        opts.exclude_submodules(true);
    }

    let non_submodule_statuses = repo.statuses(Some(&mut opts))?;

    // `exclude_submodules` also filters out newly-staged gitlinks (INDEX_NEW submodules), so we
    // detect those separately by scanning the index for gitlink entries absent from HEAD.
    let head_tree = repo.head().ok().and_then(|h| h.peel_to_tree().ok());
    let index = repo.index()?;
    let new_submodule_paths: Vec<String> = index
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

    let submodule_statuses = if repo_kind == RepoKind::WithSubmodules {
        match request_status(root_path) {
            Ok(statuses) => statuses,
            Err(e) => {
                eprintln!(
                    "Failed to retrieve submodule statuses. Have you started a watch server?"
                );
                Err(e)?
            }
        }
    } else {
        Vec::new()
    };
    display_status(
        &repo,
        &non_submodule_statuses,
        &submodule_statuses,
        &new_submodule_paths,
    )?;

    Ok(())
}
