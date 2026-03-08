use anstyle::AnsiColor;
use git2::Repository;
use std::{cmp::Ordering, fs, path::Path};
use thiserror::Error;

use crate::{
    BranchInfo, ConflictEntry, ConflictType, FileChange, FileStatusEntry, FileZone,
    FullRepoStatus, RebaseInfo, RepoKind, StatusSummary, UpstreamStatus,
    connection::client::request_status, paint,
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

// ---------------------------------------------------------------------------
// Data-gathering helpers
// ---------------------------------------------------------------------------

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
    let total_done = all_done.len() as u32;
    // Show last 2 done ops to match git's display limit
    let done_ops: Vec<String> = all_done.into_iter().rev().take(2).rev().collect();

    let todo_raw = fs::read_to_string(rebase_merge.join("git-rebase-todo")).unwrap_or_default();
    let all_remaining = parse_rebase_lines(&todo_raw);
    let total_remaining = all_remaining.len() as u32;
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

fn get_branch_info(repo: &Repository) -> StatusResult<BranchInfo> {
    let head_ref = repo.head()?;
    if !head_ref.is_branch() {
        let short_hash = head_ref.target().map_or_else(
            || "unknown".to_string(),
            |oid| oid.to_string().chars().take(7).collect(),
        );
        return Ok(BranchInfo::Detached(short_hash));
    }
    let branch_name = head_ref.shorthand().unwrap().to_string();
    Ok(BranchInfo::Branch(branch_name))
}

fn get_upstream_info(repo: &Repository) -> StatusResult<Option<UpstreamStatus>> {
    let head_ref = repo.head()?;
    if !head_ref.is_branch() {
        return Ok(None);
    }

    let local_branch = git2::Branch::wrap(head_ref);
    let Ok(upstream_branch) = local_branch.upstream() else {
        return Ok(None);
    };

    let upstream_name = upstream_branch
        .get()
        .shorthand()
        .unwrap_or("unknown")
        .to_string();

    let local_oid = local_branch.get().peel_to_commit()?.id();
    let upstream_oid = upstream_branch.get().peel_to_commit()?.id();
    let (ahead, behind) = repo.graph_ahead_behind(local_oid, upstream_oid)?;

    Ok(Some(UpstreamStatus {
        upstream_name,
        ahead: ahead as u32,
        behind: behind as u32,
    }))
}

fn get_conflicts(repo: &Repository) -> StatusResult<Vec<ConflictEntry>> {
    let index = repo.index()?;
    if !index.has_conflicts() {
        return Ok(Vec::new());
    }

    let mut conflicts = Vec::new();
    for conflict in index.conflicts()? {
        let conflict = conflict?;
        let path = conflict
            .our
            .as_ref()
            .or(conflict.their.as_ref())
            .or(conflict.ancestor.as_ref())
            .and_then(|e| std::str::from_utf8(&e.path).ok())
            .unwrap_or("<unknown path>")
            .to_string();

        #[allow(clippy::match_same_arms)]
        let conflict_type = match (
            conflict.ancestor.is_some(),
            conflict.our.is_some(),
            conflict.their.is_some(),
        ) {
            (true, true, true) => ConflictType::BothModified,
            (false, true, true) => ConflictType::BothAdded,
            (true, false, true) => ConflictType::DeletedByUs,
            (true, true, false) => ConflictType::DeletedByThem,
            (true, false, false) => ConflictType::BothDeleted,
            (false, true, false) => ConflictType::AddedByUs,
            (false, false, true) => ConflictType::AddedByThem,
            (false, false, false) => ConflictType::BothModified,
        };

        conflicts.push(ConflictEntry {
            path,
            conflict_type,
        });
    }
    Ok(conflicts)
}

/// Returns the relative paths of newly-added submodules.
///
/// These are submodules whose gitlink has been staged via `git submodule add`
/// but not yet committed (present in the index but absent from HEAD).
///
/// # Errors
///
/// Returns `Err` if the repository index cannot be read.
fn new_submodule_paths(repo: &Repository) -> StatusResult<Vec<String>> {
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

// ---------------------------------------------------------------------------
// gather_full_status — builds the complete FullRepoStatus from a Repository
// ---------------------------------------------------------------------------

/// Extracts path strings from a `git2::DiffDelta`, returning `(primary_path, renamed_path)`.
/// `renamed_path` is `Some` only when the old and new paths differ (i.e. renames).
fn diff_paths(delta: &git2::DiffDelta<'_>) -> (String, Option<String>) {
    let old = delta.old_file().path().map(|p| p.to_string_lossy().into_owned());
    let new = delta.new_file().path().map(|p| p.to_string_lossy().into_owned());
    match (&old, &new) {
        (Some(o), Some(n)) if o != n => (o.clone(), Some(n.clone())),
        _ => (old.or(new).unwrap(), None),
    }
}

/// Walks `git2::Statuses` and produces a flat list of `FileStatusEntry` items.
/// Returns the entries and whether any workdir deletion was seen (`rm_in_workdir`).
fn extract_file_statuses(statuses: &git2::Statuses<'_>) -> (Vec<FileStatusEntry>, bool) {
    let mut out = Vec::new();
    let mut rm_in_workdir = false;

    for entry in statuses.iter() {
        let s = entry.status();
        if s == git2::Status::CURRENT {
            continue;
        }

        // Staged (index) changes
        if let Some(change) = match s {
            s if s.contains(git2::Status::INDEX_NEW) => Some(FileChange::New),
            s if s.contains(git2::Status::INDEX_MODIFIED) => Some(FileChange::Modified),
            s if s.contains(git2::Status::INDEX_DELETED) => Some(FileChange::Deleted),
            s if s.contains(git2::Status::INDEX_RENAMED) => Some(FileChange::Renamed),
            s if s.contains(git2::Status::INDEX_TYPECHANGE) => Some(FileChange::Typechange),
            _ => None,
        } {
            let (path, new_path) = diff_paths(&entry.head_to_index().unwrap());
            out.push(FileStatusEntry {
                change,
                zone: FileZone::Staged,
                path,
                new_path,
            });
        }

        // Unstaged (workdir) changes
        if entry.index_to_workdir().is_some()
            && !s.contains(git2::Status::CONFLICTED)
            && let Some(change) = match s {
                s if s.contains(git2::Status::WT_MODIFIED) => Some(FileChange::Modified),
                s if s.contains(git2::Status::WT_DELETED) => {
                    rm_in_workdir = true;
                    Some(FileChange::Deleted)
                }
                s if s.contains(git2::Status::WT_RENAMED) => Some(FileChange::Renamed),
                s if s.contains(git2::Status::WT_TYPECHANGE) => Some(FileChange::Typechange),
                _ => None,
            }
        {
            let (path, new_path) = diff_paths(&entry.index_to_workdir().unwrap());
            out.push(FileStatusEntry {
                change,
                zone: FileZone::Unstaged,
                path,
                new_path,
            });
        }

        // Untracked files
        if s == git2::Status::WT_NEW {
            let file = entry
                .index_to_workdir()
                .unwrap()
                .old_file()
                .path()
                .unwrap();
            out.push(FileStatusEntry {
                change: FileChange::New,
                zone: FileZone::Untracked,
                path: file.to_string_lossy().into_owned(),
                new_path: None,
            });
        }
    }

    (out, rm_in_workdir)
}

/// Gathers the complete repository status into a serializable `FullRepoStatus`.
///
/// When `exclude_submodules` is `true`, `git2::StatusOptions` will skip submodule
/// entries (used when called from the server, where submodule statuses come from
/// the watch server's cache). When `false`, submodules are included in the git2
/// status output (used for the local fallback when no server is running).
///
/// # Errors
///
/// Returns `Err` if the repository cannot be opened or its status cannot be read.
pub fn gather_full_status(
    root_path: &Path,
    submodule_statuses: Vec<(String, StatusSummary)>,
    exclude_submodules: bool,
) -> StatusResult<FullRepoStatus> {
    let repo = Repository::open(root_path)?;

    let mut opts = git2::StatusOptions::new();
    opts.include_untracked(true)
        .recurse_untracked_dirs(false)
        .include_ignored(false);

    if exclude_submodules {
        opts.exclude_submodules(true);
    }

    let statuses = repo.statuses(Some(&mut opts))?;
    let (file_statuses, rm_in_workdir) = extract_file_statuses(&statuses);

    let branch = get_branch_info(&repo)?;
    let upstream = get_upstream_info(&repo)?;
    let rebase = get_rebase_info(&repo)?;
    let conflicts = get_conflicts(&repo)?;
    let new_submodule_paths = new_submodule_paths(&repo)?;

    Ok(FullRepoStatus {
        submodule_statuses,
        file_statuses,
        branch,
        upstream,
        rebase,
        conflicts,
        new_submodule_paths,
        rm_in_workdir,
    })
}

// ---------------------------------------------------------------------------
// Display helpers — print from FullRepoStatus data
// ---------------------------------------------------------------------------

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

fn print_upstream_info(upstream: &UpstreamStatus) {
    let name = &upstream.upstream_name;
    let ahead = upstream.ahead as usize;
    let behind = upstream.behind as usize;

    let commit_s = |n: usize| if n == 1 { "commit" } else { "commits" };

    let (status_line, hint) = match (ahead.cmp(&0), behind.cmp(&0)) {
        (Ordering::Equal, Ordering::Equal) => (
            format!("Your branch is up to date with '{name}'."),
            "",
        ),
        (Ordering::Greater, Ordering::Equal) => (
            format!(
                "Your branch is ahead of '{name}' by {ahead} {}.",
                commit_s(ahead)
            ),
            "(use \"git push\" to publish your local commits)",
        ),
        (Ordering::Equal, Ordering::Greater) => (
            format!(
                "Your branch is behind '{name}' by {behind} {}, and can be fast-forwarded.",
                commit_s(behind)
            ),
            "(use \"git pull\" to update your local branch)",
        ),
        _ => (
            format!(
                "Your branch and '{name}' have diverged,\nand have {ahead} and {behind} different {} each, respectively.",
                commit_s(ahead + behind)
            ),
            "(use \"git pull\" if you want to integrate the remote branch with yours)",
        ),
    };

    println!("{status_line}");
    if !hint.is_empty() {
        println!("  {hint}");
    }
    println!();
}

fn print_conflicts(conflicts: &[ConflictEntry]) -> bool {
    if conflicts.is_empty() {
        return false;
    }

    println!("Unmerged paths:");
    println!("  (use \"git restore --staged <file>...\" to unstage)");
    println!("  (use \"git add <file>...\" to mark resolution)");

    for entry in conflicts {
        // Padded to 17 chars to match git's column alignment
        let type_str = match entry.conflict_type {
            ConflictType::BothModified => "both modified:   ",
            ConflictType::BothAdded => "both added:      ",
            ConflictType::DeletedByUs => "deleted by us:   ",
            ConflictType::DeletedByThem => "deleted by them: ",
            ConflictType::BothDeleted => "both deleted:    ",
            ConflictType::AddedByUs => "added by us:     ",
            ConflictType::AddedByThem => "added by them:   ",
        };
        println!(
            "{}",
            paint(
                Some(AnsiColor::Red),
                &format!("\t{type_str}{}", entry.path)
            )
        );
    }
    println!();
    true
}

fn print_staged_from_data(status: &FullRepoStatus) -> bool {
    let mut header = false;

    for entry in status
        .file_statuses
        .iter()
        .filter(|e| e.zone == FileZone::Staged)
    {
        if !header {
            println!("{STAGED_HEADER}");
            header = true;
        }
        let label = entry.change.label();
        match &entry.new_path {
            Some(new) => println!(
                "{}",
                paint(
                    Some(AnsiColor::Green),
                    &format!("\t{label}  {} -> {new}", entry.path),
                )
            ),
            None => println!(
                "{}",
                paint(
                    Some(AnsiColor::Green),
                    &format!("\t{label}  {}", entry.path),
                )
            ),
        }
    }

    for path in &status.new_submodule_paths {
        if !header {
            println!("{STAGED_HEADER}");
            header = true;
        }
        println!(
            "{}",
            paint(Some(AnsiColor::Green), &format!("\tnew file:   {path}"))
        );
    }

    for (submod_path, _) in status.submodule_statuses.iter().filter(|(_, st)| {
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

fn print_unstaged_from_data(status: &FullRepoStatus) -> bool {
    let has_submod_changes = status
        .submodule_statuses
        .iter()
        .any(|(_, st)| !st.eq(&StatusSummary::STAGED));
    let mut header = false;

    for entry in status
        .file_statuses
        .iter()
        .filter(|e| e.zone == FileZone::Unstaged)
    {
        if !header {
            println!(
                "{}",
                unstaged_header(status.rm_in_workdir, has_submod_changes)
            );
            header = true;
        }
        let label = entry.change.label();
        match &entry.new_path {
            Some(new) => println!(
                "{}",
                paint(
                    Some(AnsiColor::Red),
                    &format!("\t{label}  {} -> {new}", entry.path),
                )
            ),
            None => println!(
                "{}",
                paint(
                    Some(AnsiColor::Red),
                    &format!("\t{label}  {}", entry.path),
                )
            ),
        }
    }

    for (submod_path, submod_status) in status
        .submodule_statuses
        .iter()
        .filter(|(_, st)| !st.eq(&StatusSummary::STAGED) && !st.eq(&StatusSummary::LOCK_FAILURE))
    {
        if !header {
            println!(
                "{}",
                unstaged_header(status.rm_in_workdir, true)
            );
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

fn print_untracked_from_data(status: &FullRepoStatus) -> bool {
    let mut header = false;
    for entry in status
        .file_statuses
        .iter()
        .filter(|e| e.zone == FileZone::Untracked)
    {
        if !header {
            println!("{UNTRACKED_HEADER}");
            header = true;
        }
        println!(
            "\t{}",
            paint(Some(AnsiColor::Red), &entry.path)
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

// ---------------------------------------------------------------------------
// display_from_full_status — prints the complete status from gathered data
// ---------------------------------------------------------------------------

/// Displays the full repository status from pre-gathered data.
///
/// # Errors
///
/// Currently infallible, but returns `StatusResult` for forward compatibility.
pub fn display_from_full_status(status: &FullRepoStatus) -> StatusResult<()> {
    if let Some(info) = &status.rebase {
        print_rebase_header(info);
    } else {
        match &status.branch {
            BranchInfo::Branch(name) => println!("On branch {name}"),
            BranchInfo::Detached(hash) => println!(
                "{} {hash}",
                paint(Some(AnsiColor::Red), "HEAD detached at")
            ),
        }
        if let Some(upstream) = &status.upstream {
            print_upstream_info(upstream);
        }
    }

    let changes_in_index = print_staged_from_data(status);
    let has_conflicts = print_conflicts(&status.conflicts);
    let changed_in_workdir = print_unstaged_from_data(status);
    let has_untracked = print_untracked_from_data(status);

    print_summary(
        changes_in_index,
        changed_in_workdir || has_conflicts,
        has_untracked,
    );

    print_lock_file_errors(&status.submodule_statuses);

    Ok(())
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Retrieves and displays the statuses for the repository at `path`.
///
/// # Errors
///
/// Returns `Err` if statuses cannot be retrieved from the repository or watch server
pub fn status(root_path: &Path, repo_kind: RepoKind, display_progress: bool) -> StatusResult<()> {
    let full_status = if repo_kind == RepoKind::WithSubmodules {
        request_status(root_path, display_progress)?
    } else {
        gather_full_status(root_path, Vec::new(), false)?
    };
    display_from_full_status(&full_status)
}
