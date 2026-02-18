use anstyle::AnsiColor;
use git2::{Repository, Statuses};
use std::path::Path;
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

const UNTRACKED_HEADER: &str = "Untracked files
  (use \"git add <file>...\" to include in what will be committed)";

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

// Adapted from https://github.com/rust-lang/git2-rs/blob/master/examples/status.rs
#[expect(clippy::too_many_lines)]
fn display_status(
    repo: &Repository,
    non_submodule_statues: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    new_submodule_paths: &[String],
) -> StatusResult<()> {
    let mut header = false;
    let mut rm_in_workdir = false;
    let mut changes_in_index = false;
    let mut changed_in_workdir = false;
    println!("{}", current_branch_display(repo)?);
    if let (Some(upstream_status), Some(upstream_name)) =
        (get_upstream_status(repo)?, get_upstream_ref_name(repo)?)
    {
        println!("Your branch is {upstream_status} with '{upstream_name}'.\n");
    }

    // Print index changes
    for entry in non_submodule_statues
        .iter()
        .filter(|e| e.status() != git2::Status::CURRENT)
    {
        if entry.status().contains(git2::Status::WT_DELETED) {
            rm_in_workdir = true;
        }
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
            (Some(old), Some(new)) if old != new => {
                println!(
                    "{}",
                    paint(
                        Some(AnsiColor::Green),
                        &format!("\t{}  {} -> {}", istatus, old.display(), new.display()),
                    )
                );
            }
            (old, new) => {
                println!(
                    "{}",
                    paint(
                        Some(AnsiColor::Green),
                        &format!("\t{}  {}", istatus, old.or(new).unwrap().display()),
                    )
                );
            }
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

    for (submod_path, _) in submodule_statuses
        .iter()
        .filter(|(_, st)| st.contains(StatusSummary::STAGED))
    {
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
        changes_in_index = true;
        println!();
    }
    header = false;

    let has_submod_changes = submodule_statuses
        .iter()
        .filter(|(_, st)| !st.eq(&StatusSummary::STAGED))
        .count()
        > 0;

    // Print workdir changes to tracked files
    for entry in non_submodule_statues.iter() {
        if entry.status() == git2::Status::CURRENT || entry.index_to_workdir().is_none() {
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
            (Some(old), Some(new)) if old != new => {
                println!(
                    "{}",
                    paint(
                        Some(AnsiColor::Red),
                        &format!("\t{}  {} -> {}", istatus, old.display(), new.display()),
                    )
                );
            }
            (old, new) => {
                println!(
                    "{}",
                    paint(
                        Some(AnsiColor::Red),
                        &format!("\t{}  {}", istatus, old.or(new).unwrap().display()),
                    )
                );
            }
        }
    }

    for (submod_path, submod_status) in submodule_statuses
        .iter()
        .filter(|(_, st)| !st.eq(&StatusSummary::STAGED))
    {
        let istatus = submod_status.to_string();
        if !header {
            println!("{}", unstaged_header(rm_in_workdir, true));
            header = true;
        }
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
        changed_in_workdir = true;
        println!();
    }
    header = false;

    let mut has_untracked = false;
    // Print untracked files
    for entry in non_submodule_statues
        .iter()
        .filter(|e| e.status() == git2::Status::WT_NEW)
    {
        if !header {
            println!("{UNTRACKED_HEADER}");
            header = true;
            has_untracked = true;
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
        .recurse_untracked_dirs(false) // not needed?
        .exclude_submodules(true)
        .include_ignored(false); // Skip ignored files if not needed
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
