//! Submodule status computation and filtering.

use git2::Repository;

use std::path::Path;

use crate::{StatusSummary, git::parse_gitmodules, watch::LockFileGuard};

use super::{IgnoreSubmodules, StatusResult};

/// Returns the relative paths of submodules staged for deletion.
///
/// These are submodules whose gitlink is in the HEAD commit but has been removed
/// from the index (via `git rm`).
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
            let Ok(name) = entry.name() else {
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

/// Masks submodule statuses according to `--ignore-submodules` mode.
pub fn apply_ignore_submodules(
    statuses: Vec<(String, StatusSummary)>,
    mode: IgnoreSubmodules,
) -> Vec<(String, StatusSummary)> {
    let mask = match mode {
        IgnoreSubmodules::None => return statuses,
        IgnoreSubmodules::All => return Vec::new(),
        IgnoreSubmodules::Untracked => !StatusSummary::UNTRACKED_CONTENT,
        IgnoreSubmodules::Dirty => {
            !(StatusSummary::UNTRACKED_CONTENT | StatusSummary::MODIFIED_CONTENT)
        }
    };
    statuses
        .into_iter()
        .map(|(path, st)| (path, st & mask))
        .filter(|(_, st)| !st.is_empty())
        .collect()
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
    let gitmodule_entries = {
        let _lock = LockFileGuard::acquire(&lock_path)?;
        parse_gitmodules(root_path)?
    };
    let tl_repo = thread_local::ThreadLocal::new();

    let statuses: StatusResult<Vec<_>> = gitmodule_entries
        .into_par_iter()
        .map(|(_, path, _)| -> StatusResult<(String, StatusSummary)> {
            let repo = tl_repo.get_or_try(|| Repository::open(root_path))?;
            let st = repo.submodule_status(&path, git2::SubmoduleIgnore::None)?;
            let summary: StatusSummary = st.into();
            Ok((path, summary))
        })
        .filter(|r| !matches!(r, Ok((_, s)) if *s == StatusSummary::clean()))
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

    #[test]
    fn compute_local_statuses_clean_repo() {
        let tmp = TempDir::new().unwrap();
        let root = tmp.path().join("root");
        let sub_src = tmp.path().join("sub_src");

        // Create a source repo for the submodule
        let sub_src_str = sub_src.display().to_string();
        git(&["-C", &tmp.path().display().to_string(), "init", "sub_src"]);
        std::fs::write(sub_src.join("README.md"), "sub\n").unwrap();
        git(&["-C", &sub_src_str, "add", "-A"]);
        git(&["-C", &sub_src_str, "commit", "-m", "init sub"]);

        // Create root repo with a submodule
        let root_str = root.display().to_string();
        git(&["-C", &tmp.path().display().to_string(), "init", "root"]);
        std::fs::write(root.join("file.txt"), "root\n").unwrap();
        git(&["-C", &root_str, "add", "-A"]);
        git(&["-C", &root_str, "commit", "-m", "init root"]);
        git(&[
            "-C",
            &root_str,
            "-c",
            "protocol.file.allow=always",
            "submodule",
            "add",
            &sub_src_str,
            "my_sub",
        ]);
        git(&["-C", &root_str, "commit", "-m", "add submodule"]);

        let repo = Repository::open(&root).unwrap();
        let statuses = compute_local_statuses(&root, &repo).unwrap();
        assert!(
            statuses.is_empty(),
            "clean repo should have no dirty submodules"
        );
    }

    #[test]
    fn compute_local_statuses_dirty_submodule() {
        let tmp = TempDir::new().unwrap();
        let root = tmp.path().join("root");
        let sub_src = tmp.path().join("sub_src");

        let sub_src_str = sub_src.display().to_string();
        git(&["-C", &tmp.path().display().to_string(), "init", "sub_src"]);
        std::fs::write(sub_src.join("README.md"), "sub\n").unwrap();
        git(&["-C", &sub_src_str, "add", "-A"]);
        git(&["-C", &sub_src_str, "commit", "-m", "init sub"]);

        let root_str = root.display().to_string();
        git(&["-C", &tmp.path().display().to_string(), "init", "root"]);
        std::fs::write(root.join("file.txt"), "root\n").unwrap();
        git(&["-C", &root_str, "add", "-A"]);
        git(&["-C", &root_str, "commit", "-m", "init root"]);
        git(&[
            "-C",
            &root_str,
            "-c",
            "protocol.file.allow=always",
            "submodule",
            "add",
            &sub_src_str,
            "my_sub",
        ]);
        git(&["-C", &root_str, "commit", "-m", "add submodule"]);

        // Dirty the submodule
        std::fs::write(root.join("my_sub").join("new.txt"), "untracked\n").unwrap();

        let repo = Repository::open(&root).unwrap();
        let statuses = compute_local_statuses(&root, &repo).unwrap();
        assert_eq!(statuses.len(), 1);
        assert_eq!(statuses[0].0, "my_sub");
        assert!(statuses[0].1.contains(StatusSummary::UNTRACKED_CONTENT));
    }
}
