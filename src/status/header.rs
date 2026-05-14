//! Branch/upstream/operation-state header rendering for the human-readable
//! `git status` output.
//!
//! Detects in-progress operations (rebase, merge, cherry-pick, revert,
//! bisect, am, apply-backend rebase) and renders the same hint blocks
//! git uses, plus the `On branch X` / `HEAD detached at Y` line and
//! upstream tracking summary for the normal case.

use git2::Repository;

use std::{
    cmp::Ordering,
    fs,
    io::{self, Write},
};

use crate::paint::{Paint, RED, paint_into};

use super::{StatusResult, relativize::Relativizer};

/// Length of the short-OID prefix git uses in `status` output (matches
/// `core.abbrev`'s default of 7 hex chars).
const SHORT_OID_LEN: usize = 7;

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
/// any 40-char hex hash in the second field to [`SHORT_OID_LEN`] chars
/// (matching git's status display format).
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
                let short = &hash_or_arg[..SHORT_OID_LEN];
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

/// Reads rebase state from `.git/rebase-merge/` if an interactive or merge-backend
/// rebase is in progress. Returns `None` if no such rebase is active.
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
    let onto_short: String = onto_raw.trim().chars().take(SHORT_OID_LEN).collect();
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

/// Prints the rebase status header with done/remaining operation lists.
fn print_rebase_header(info: &RebaseInfo, stdout: &mut impl Write) -> Result<(), io::Error> {
    let label = if info.is_interactive {
        "interactive rebase"
    } else {
        "rebase"
    };
    writeln!(
        stdout,
        "{} {}",
        Paint(RED, format_args!("{label} in progress?; onto")),
        info.onto_short
    )?;

    if info.total_done > 0 {
        let shown = info.done_ops.len();
        if shown == 1 {
            writeln!(
                stdout,
                "Last command done ({} command done):",
                info.total_done
            )?;
        } else {
            writeln!(
                stdout,
                "Last {shown} commands done ({} commands done):",
                info.total_done
            )?;
        }
        for cmd in &info.done_ops {
            writeln!(stdout, "   {cmd}")?;
        }
    }

    if info.total_remaining == 0 {
        writeln!(stdout, "No commands remaining.")?;
    } else {
        let shown = info.remaining_ops.len();
        if shown == 1 {
            writeln!(
                stdout,
                "Next command to do ({} remaining command):",
                info.total_remaining
            )?;
        } else {
            writeln!(
                stdout,
                "Next {shown} commands to do ({} remaining commands):",
                info.total_remaining
            )?;
        }
        for cmd in &info.remaining_ops {
            writeln!(stdout, "   {cmd}")?;
        }
        writeln!(
            stdout,
            "  (use \"git rebase --edit-todo\" to view and edit)"
        )?;
    }

    if info.is_editing {
        writeln!(
            stdout,
            "You are currently editing a commit while rebasing branch '{}' on '{}'.",
            info.head_name, info.onto_short
        )?;
        writeln!(
            stdout,
            "  (use \"git commit --amend\" to amend the current commit)"
        )?;
        writeln!(
            stdout,
            "  (use \"git rebase --continue\" once you are satisfied with your changes)"
        )?;
    } else {
        writeln!(
            stdout,
            "You are currently rebasing branch '{}' on '{}'.",
            info.head_name, info.onto_short
        )?;
        writeln!(
            stdout,
            "  (fix conflicts and then run \"git rebase --continue\")"
        )?;
        writeln!(stdout, "  (use \"git rebase --skip\" to skip this patch)")?;
        writeln!(
            stdout,
            "  (use \"git rebase --abort\" to check out the original branch)"
        )?;
    }
    writeln!(stdout)?;

    Ok(())
}

/// Prints the "Unmerged paths:" section for any conflicts in the index.
/// Returns `true` if there were conflicts. Paths are routed through `rel`
/// so they render cwd-relative, matching the rest of the human display.
pub fn print_unmerged_paths(
    repo: &Repository,
    rel: &Relativizer<'_>,
    stdout: &mut impl Write,
) -> StatusResult<bool> {
    let index = repo.index()?;
    if !index.has_conflicts() {
        return Ok(false);
    }

    writeln!(stdout, "Unmerged paths:")?;
    // Note: the `(use "git restore --staged <file>...")` hint belongs
    // to the "Changes to be committed:" header (see `STAGED_HEADER` in
    // `display.rs`), not here. Real `git status` only emits it there,
    // gated on the existence of staged changes.
    writeln!(stdout, "  (use \"git add <file>...\" to mark resolution)")?;

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
        paint_into(stdout, RED, |out| {
            write!(out, "\t{type_str}")?;
            rel.write_to(out, path)
        })?;
        writeln!(stdout)?;
    }
    writeln!(stdout)?;
    Ok(true)
}

/// The detected repository state, used to print the appropriate header.
///
/// `branch_display` is the "On branch X" / "HEAD detached at <oid>" line
/// that real git emits before the operation-state body. It's `None` only
/// for rebase variants, which describe HEAD position internally (via the
/// rebase header's `head_name` / `onto` fields).
#[derive(Debug, PartialEq, Eq)]
struct HeaderState {
    branch_display: Option<String>,
    body: HeaderBody,
}

/// The operation-specific portion of the header.
#[derive(Debug, PartialEq, Eq)]
enum HeaderBody {
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
        upstream: Option<(String, &'static str)>,
    },
}

/// Reads a `*_HEAD` file (e.g. `CHERRY_PICK_HEAD`, `REVERT_HEAD`) and returns
/// the first [`SHORT_OID_LEN`] characters of the OID, or the full content if
/// shorter.
fn read_short_oid(repo: &Repository, filename: &str) -> String {
    let path = repo.path().join(filename);
    let oid = fs::read_to_string(path).unwrap_or_default();
    let trimmed = oid.trim();
    trimmed.get(..SHORT_OID_LEN).unwrap_or(trimmed).to_string()
}

/// Determines the repository's current operation state (rebase, merge, cherry-pick,
/// etc.) and returns it along with branch/upstream info for display.
fn get_header_state(repo: &Repository) -> StatusResult<HeaderState> {
    if let Some(info) = get_rebase_info(repo)? {
        return Ok(HeaderState {
            branch_display: None,
            body: HeaderBody::Rebase(info),
        });
    }

    // `git rebase --apply` uses `rebase-apply/` instead of `rebase-merge/`.
    // git2 reports this as `RepositoryState::Rebase`, which `get_rebase_info`
    // doesn't handle since it only reads from `rebase-merge/`.
    if repo.path().join("rebase-apply").join("rebasing").exists() {
        let has_conflicts = repo.index()?.has_conflicts();
        return Ok(HeaderState {
            branch_display: None,
            body: HeaderBody::RebaseWithApplyBackend { has_conflicts },
        });
    }

    let head_ref = repo.head()?;
    let branch_display = current_branch_display(&head_ref);
    let has_conflicts = repo.index()?.has_conflicts();

    let body = match repo.state() {
        git2::RepositoryState::CherryPick | git2::RepositoryState::CherryPickSequence => {
            HeaderBody::CherryPick {
                short_oid: read_short_oid(repo, "CHERRY_PICK_HEAD"),
                has_conflicts,
            }
        }
        git2::RepositoryState::Merge => HeaderBody::Merge { has_conflicts },
        git2::RepositoryState::Revert | git2::RepositoryState::RevertSequence => {
            HeaderBody::Revert {
                short_oid: read_short_oid(repo, "REVERT_HEAD"),
                has_conflicts,
            }
        }
        git2::RepositoryState::Bisect => HeaderBody::Bisect,
        git2::RepositoryState::ApplyMailbox | git2::RepositoryState::ApplyMailboxOrRebase => {
            // rebase-apply/rebasing exists for `git rebase --apply`,
            // rebase-apply/applying exists for `git am`.
            let rebase_apply = repo.path().join("rebase-apply");
            if rebase_apply.join("rebasing").exists() {
                HeaderBody::RebaseWithApplyBackend { has_conflicts }
            } else {
                HeaderBody::ApplyMailbox { has_conflicts }
            }
        }
        _ => HeaderBody::Normal {
            upstream: get_upstream_status(repo, head_ref)?,
        },
    };

    Ok(HeaderState {
        branch_display: Some(branch_display),
        body,
    })
}

/// Prints the status header: branch name, upstream tracking info, and any
/// in-progress operation (rebase, merge, cherry-pick, etc.).
pub fn print_header(repo: &Repository, stdout: &mut impl Write) -> StatusResult<()> {
    let state = get_header_state(repo)?;
    print_header_state(&state, stdout)?;
    Ok(())
}

/// Prints the operation-specific portion of the header (hints, conflict guidance, etc.).
#[expect(clippy::too_many_lines, reason = "git has so much to say")]
fn print_header_state(state: &HeaderState, stdout: &mut impl Write) -> Result<(), io::Error> {
    if let Some(branch) = &state.branch_display {
        writeln!(stdout, "{branch}")?;
    }
    match &state.body {
        HeaderBody::Rebase(info) => print_rebase_header(info, stdout)?,
        HeaderBody::CherryPick {
            short_oid,
            has_conflicts,
        } => {
            writeln!(
                stdout,
                "You are currently cherry-picking commit {short_oid}."
            )?;
            if *has_conflicts {
                writeln!(
                    stdout,
                    "  (fix conflicts and run \"git cherry-pick --continue\")"
                )?;
            } else {
                writeln!(
                    stdout,
                    "  (all conflicts fixed: run \"git cherry-pick --continue\")"
                )?;
            }
            writeln!(
                stdout,
                "  (use \"git cherry-pick --skip\" to skip this patch)"
            )?;
            writeln!(
                stdout,
                "  (use \"git cherry-pick --abort\" to cancel the cherry-pick operation)"
            )?;
            writeln!(stdout)?;
        }
        HeaderBody::Merge { has_conflicts } => {
            if *has_conflicts {
                writeln!(stdout, "You have unmerged paths.")?;
                writeln!(stdout, "  (fix conflicts and run \"git commit\")")?;
                writeln!(stdout, "  (use \"git merge --abort\" to abort the merge)")?;
            } else {
                writeln!(stdout, "All conflicts fixed but you are still merging.")?;
                writeln!(stdout, "  (use \"git commit\" to conclude merge)")?;
            }
            writeln!(stdout)?;
        }
        HeaderBody::Revert {
            short_oid,
            has_conflicts,
        } => {
            writeln!(stdout, "You are currently reverting commit {short_oid}.")?;
            if *has_conflicts {
                writeln!(
                    stdout,
                    "  (fix conflicts and run \"git revert --continue\")"
                )?;
            } else {
                writeln!(
                    stdout,
                    "  (all conflicts fixed: run \"git revert --continue\")"
                )?;
            }
            writeln!(stdout, "  (use \"git revert --skip\" to skip this patch)")?;
            writeln!(
                stdout,
                "  (use \"git revert --abort\" to cancel the revert operation)"
            )?;
            writeln!(stdout)?;
        }
        HeaderBody::Bisect => {
            writeln!(stdout, "You are currently bisecting.")?;
            writeln!(
                stdout,
                "  (use \"git bisect reset\" to get back to the original branch)"
            )?;
            writeln!(stdout)?;
        }
        HeaderBody::ApplyMailbox { has_conflicts } => {
            writeln!(stdout, "You are in the middle of an am session.")?;
            if *has_conflicts {
                writeln!(
                    stdout,
                    "  (fix conflicts and then run \"git am --continue\")"
                )?;
            } else {
                writeln!(stdout, "  (all conflicts fixed: run \"git am --continue\")")?;
            }
            writeln!(stdout, "  (use \"git am --skip\" to skip this patch)")?;
            writeln!(
                stdout,
                "  (use \"git am --abort\" to restore the original branch)"
            )?;
            writeln!(stdout)?;
        }
        HeaderBody::RebaseWithApplyBackend { has_conflicts } => {
            writeln!(stdout, "You are currently rebasing.")?;
            if *has_conflicts {
                writeln!(
                    stdout,
                    "  (fix conflicts and then run \"git rebase --continue\")"
                )?;
            } else {
                writeln!(
                    stdout,
                    "  (all conflicts fixed: run \"git rebase --continue\")"
                )?;
            }
            writeln!(stdout, "  (use \"git rebase --skip\" to skip this patch)")?;
            writeln!(
                stdout,
                "  (use \"git rebase --abort\" to check out the original branch)"
            )?;
            writeln!(stdout)?;
        }
        HeaderBody::Normal { upstream } => {
            if let Some((status_line, hint)) = upstream {
                writeln!(stdout, "{status_line}")?;
                if !hint.is_empty() {
                    writeln!(stdout, "  {hint}")?;
                }
                writeln!(stdout)?;
            }
        }
    }

    Ok(())
}

/// Returns the "On branch <name>" or "HEAD detached at <oid>" display string.
fn current_branch_display(head_ref: &git2::Reference<'_>) -> String {
    if !head_ref.is_branch() {
        return format!(
            "{} {}",
            Paint(RED, "HEAD detached at"),
            head_ref.target().map_or_else(
                || "unknown".to_string(),
                |oid| {
                    // git2's `Oid::Display` writes 40 hex chars and does
                    // not honor format precision, so we materialize then
                    // truncate. One alloc instead of two.
                    let mut s = oid.to_string();
                    s.truncate(SHORT_OID_LEN);
                    s
                }
            ),
        );
    }
    let branch_name = head_ref.shorthand().unwrap();
    format!("On branch {branch_name}")
}

/// Returns the upstream tracking status (e.g. "ahead 3", "behind 1") and a hint
/// string, or `None` if HEAD is detached or has no upstream configured.
fn get_upstream_status(
    repo: &Repository,
    head_ref: git2::Reference<'_>,
) -> StatusResult<Option<(String, &'static str)>> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;
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
            matches!(state.body, HeaderBody::Normal { .. }),
            "expected Normal, got {state:?}"
        );
    }

    #[test]
    fn header_state_cherry_pick_with_conflict() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "pick-me");

        let output = std::process::Command::new("git")
            .args(["-c", "user.name=Test", "-c", "user.email=test@test.com"])
            .args(["-C", &root, "cherry-pick", "pick-me"])
            .output()
            .unwrap();
        assert!(!output.status.success(), "expected cherry-pick to conflict");

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state.body,
                HeaderBody::CherryPick {
                    has_conflicts: true,
                    ..
                }
            ),
            "expected CherryPick with conflicts, got {state:?}"
        );
        if let HeaderBody::CherryPick { short_oid, .. } = &state.body {
            assert_eq!(short_oid.len(), SHORT_OID_LEN);
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
                state.body,
                HeaderBody::Merge {
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

        std::fs::write(tmp.path().join("file.txt"), "aaa\n").unwrap();
        git(&["-C", &root, "add", "-A"]);
        git(&["-C", &root, "commit", "-m", "commit A"]);

        std::fs::write(tmp.path().join("file.txt"), "bbb\n").unwrap();
        git(&["-C", &root, "add", "-A"]);
        git(&["-C", &root, "commit", "-m", "commit B"]);

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
                state.body,
                HeaderBody::Revert {
                    has_conflicts: true,
                    ..
                }
            ),
            "expected Revert with conflicts, got {state:?}"
        );
        if let HeaderBody::Revert { short_oid, .. } = &state.body {
            assert_eq!(short_oid.len(), SHORT_OID_LEN);
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

        std::fs::write(tmp.path().join("file.txt"), "resolved\n").unwrap();
        git(&["-C", &root, "add", "file.txt"]);

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state.body,
                HeaderBody::CherryPick {
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

        std::fs::write(tmp.path().join("file.txt"), "resolved\n").unwrap();
        git(&["-C", &root, "add", "file.txt"]);

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert!(
            matches!(
                state.body,
                HeaderBody::Merge {
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

        std::fs::write(tmp.path().join("file.txt"), "changed\n").unwrap();
        git(&["-C", &root, "add", "-A"]);
        git(&["-C", &root, "commit", "-m", "second"]);

        git(&["-C", &root, "bisect", "start"]);
        git(&["-C", &root, "bisect", "bad", "HEAD"]);
        git(&["-C", &root, "bisect", "good", "HEAD~1"]);

        let repo = Repository::open(tmp.path()).unwrap();
        let state = get_header_state(&repo).unwrap();
        assert_eq!(state.body, HeaderBody::Bisect);
    }

    #[test]
    fn header_state_git_am_with_conflict() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "patch-src");

        let patch_output = std::process::Command::new("git")
            .args(["-C", &root, "format-patch", "master..patch-src", "--stdout"])
            .output()
            .unwrap();
        assert!(patch_output.status.success());
        let patch_file = tmp.path().join("conflict.patch");
        std::fs::write(&patch_file, &patch_output.stdout).unwrap();

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
            matches!(state.body, HeaderBody::ApplyMailbox { .. }),
            "expected ApplyMailbox, got {state:?}"
        );
    }

    #[test]
    fn header_state_rebase_apply_backend_with_conflict() {
        let (tmp, _repo) = init_repo();
        let root = tmp.path().display().to_string();
        create_conflicting_branch(&root, tmp.path(), "rebase-src");

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
                state.body,
                HeaderBody::RebaseWithApplyBackend {
                    has_conflicts: true
                }
            ),
            "expected RebaseWithApplyBackend with conflicts, got {state:?}"
        );
    }

    // -- parse_rebase_lines --

    #[test]
    fn rebase_lines_shortens_full_hash() {
        let input = "pick abcdef1234567890abcdef1234567890abcdef12 Fix the bug\n";
        let result = parse_rebase_lines(input);
        assert_eq!(result, ["pick abcdef1 Fix the bug"]);
    }

    #[test]
    fn rebase_lines_preserves_short_hash() {
        let input = "pick abcdef1 Fix the bug\n";
        let result = parse_rebase_lines(input);
        assert_eq!(result, ["pick abcdef1 Fix the bug"]);
    }

    #[test]
    fn rebase_lines_skips_comments_and_blanks() {
        let input = "# This is a comment\n\npick abcdef1 Do stuff\n";
        let result = parse_rebase_lines(input);
        assert_eq!(result, ["pick abcdef1 Do stuff"]);
    }

    #[test]
    fn rebase_lines_full_hash_no_message() {
        let input = "drop abcdef1234567890abcdef1234567890abcdef12\n";
        let result = parse_rebase_lines(input);
        assert_eq!(result, ["drop abcdef1"]);
    }

    #[test]
    fn rebase_lines_real_done_file_format() {
        let input = "\
            pick 4e0411814cb5bd9cf38ee803978966a39df7ac54 # feature 1\n\
            pick 66ec2060c6cb15d5ca911f52502d0f009f17233c # feature 2\n";
        let result = parse_rebase_lines(input);
        assert_eq!(
            result,
            ["pick 4e04118 # feature 1", "pick 66ec206 # feature 2"]
        );
    }

    #[test]
    fn rebase_lines_multiple_ops() {
        let input = "\
            pick aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa First commit\n\
            fixup bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb Second commit\n\
            reword cccccccccccccccccccccccccccccccccccccccc Third commit\n";
        let result = parse_rebase_lines(input);
        assert_eq!(
            result,
            [
                "pick aaaaaaa First commit",
                "fixup bbbbbbb Second commit",
                "reword ccccccc Third commit",
            ]
        );
    }

    // -- get_upstream_status --

    /// Creates a repo cloned from a local bare remote so that
    /// `get_upstream_status` has a tracking branch to compare against.
    fn init_repo_with_remote() -> (TempDir, Repository) {
        let tmp = TempDir::new().unwrap();

        let remote_path = tmp.path().join("remote.git");
        git(&["init", "--bare", &remote_path.display().to_string()]);

        let local_path = tmp.path().join("local");
        git(&[
            "-c",
            "protocol.file.allow=always",
            "clone",
            &remote_path.display().to_string(),
            &local_path.display().to_string(),
        ]);

        let local = local_path.display().to_string();
        std::fs::write(local_path.join("file.txt"), "initial\n").unwrap();
        git(&["-C", &local, "add", "-A"]);
        git(&["-C", &local, "commit", "-m", "initial"]);
        git(&["-C", &local, "push"]);

        let repo = Repository::open(&local_path).unwrap();
        (tmp, repo)
    }

    #[test]
    fn upstream_up_to_date() {
        let (_tmp, repo) = init_repo_with_remote();
        let (status_line, hint) = get_upstream_status(&repo, repo.head().unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(
            status_line,
            "Your branch is up to date with 'origin/master'."
        );
        assert_eq!(hint, "");
    }

    #[test]
    fn upstream_ahead() {
        let (_tmp, repo) = init_repo_with_remote();
        let local = repo.workdir().unwrap().display().to_string();
        std::fs::write(repo.workdir().unwrap().join("file.txt"), "ahead\n").unwrap();
        git(&["-C", &local, "add", "-A"]);
        git(&["-C", &local, "commit", "-m", "local commit"]);

        let repo = Repository::open(repo.workdir().unwrap()).unwrap();
        let (status_line, hint) = get_upstream_status(&repo, repo.head().unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(
            status_line,
            "Your branch is ahead of 'origin/master' by 1 commit."
        );
        assert_eq!(hint, "(use \"git push\" to publish your local commits)");
    }

    #[test]
    fn upstream_behind() {
        let (tmp, repo) = init_repo_with_remote();
        let remote_path = tmp.path().join("remote.git");

        let other = tmp.path().join("other");
        git(&[
            "-c",
            "protocol.file.allow=always",
            "clone",
            &remote_path.display().to_string(),
            &other.display().to_string(),
        ]);
        let other_str = other.display().to_string();
        std::fs::write(other.join("file.txt"), "remote change\n").unwrap();
        git(&["-C", &other_str, "add", "-A"]);
        git(&["-C", &other_str, "commit", "-m", "remote commit"]);
        git(&["-C", &other_str, "push"]);

        let local = repo.workdir().unwrap().display().to_string();
        git(&["-C", &local, "fetch"]);

        let repo = Repository::open(repo.workdir().unwrap()).unwrap();
        let (status_line, hint) = get_upstream_status(&repo, repo.head().unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(
            status_line,
            "Your branch is behind 'origin/master' by 1 commit, and can be fast-forwarded."
        );
        assert_eq!(hint, "(use \"git pull\" to update your local branch)");
    }

    #[test]
    fn upstream_diverged() {
        let (tmp, repo) = init_repo_with_remote();
        let remote_path = tmp.path().join("remote.git");

        let other = tmp.path().join("other");
        git(&[
            "-c",
            "protocol.file.allow=always",
            "clone",
            &remote_path.display().to_string(),
            &other.display().to_string(),
        ]);
        let other_str = other.display().to_string();
        std::fs::write(other.join("other.txt"), "remote\n").unwrap();
        git(&["-C", &other_str, "add", "-A"]);
        git(&["-C", &other_str, "commit", "-m", "remote commit"]);
        git(&["-C", &other_str, "push"]);

        let local = repo.workdir().unwrap().display().to_string();
        std::fs::write(repo.workdir().unwrap().join("local.txt"), "local\n").unwrap();
        git(&["-C", &local, "add", "-A"]);
        git(&["-C", &local, "commit", "-m", "local commit"]);
        git(&["-C", &local, "fetch"]);

        let repo = Repository::open(repo.workdir().unwrap()).unwrap();
        let (status_line, hint) = get_upstream_status(&repo, repo.head().unwrap())
            .unwrap()
            .unwrap();
        assert_eq!(
            status_line,
            "Your branch and 'origin/master' have diverged,\n\
             and have 1 and 1 different commits each, respectively."
        );
        assert_eq!(
            hint,
            "(use \"git pull\" if you want to integrate the remote branch with yours)"
        );
    }

    #[test]
    fn upstream_none_without_remote() {
        let (_tmp, repo) = init_repo();
        assert!(
            get_upstream_status(&repo, repo.head().unwrap())
                .unwrap()
                .is_none()
        );
    }
}
