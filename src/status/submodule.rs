//! Submodule status computation and filtering.

use git2::Repository;

use std::path::Path;

use crate::{StatusSummary, git::parse_gitmodules, watch::LockFileGuard};

use super::{IgnoreSubmodules, StatusResult};

/// A submodule that was renamed (`git mv old new`) since HEAD: same
/// gitlink OID, different path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubmoduleRename {
    pub old: String,
    pub new: String,
}

/// HEAD-to-index submodule changes that don't show up in
/// `git status`'s submodule status: deletions (HEAD path missing from
/// the index) and renames (same gitlink OID at a different path).
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SubmoduleChanges {
    pub deleted: Vec<String>,
    pub renamed: Vec<SubmoduleRename>,
}

/// Returns submodules that are deleted or renamed in the index relative
/// to the HEAD commit.
///
/// Renames are detected by matching gitlink OIDs: if a HEAD-tracked
/// submodule path is missing from the index but its gitlink OID appears
/// at a different path, it's classified as renamed. The OID match is
/// the only signal -- gitlinks don't carry similarity-scoreable
/// content, so a submodule advance + rename in the same commit will
/// register as a deletion plus a new entry.
///
/// Fast path: if no HEAD gitlink is missing from the index, we never
/// scan the full index -- iteration cost is proportional to the number
/// of submodules in HEAD, not the size of the index.
///
/// # Errors
///
/// Returns `Err` if the HEAD tree cannot be walked or the index cannot be read.
pub fn submodule_changes(repo: &Repository) -> StatusResult<SubmoduleChanges> {
    let Some(head_tree) = repo.head().ok().and_then(|h| h.peel_to_tree().ok()) else {
        return Ok(SubmoduleChanges::default());
    };
    let index = repo.index()?;

    // Collect every HEAD gitlink so we can later distinguish "this
    // index entry is a fresh path" (rename candidate) from "this index
    // entry is just HEAD's own submodule at the same path" (no rename).
    let mut head_gitlinks: Vec<(String, git2::Oid)> = Vec::new();
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
            head_gitlinks.push((path, entry.id()));
            git2::TreeWalkResult::Skip
        } else {
            git2::TreeWalkResult::Ok
        }
    })?;

    // Subset of `head_gitlinks` whose path no longer exists in the
    // index (`git rm` or `git mv` on a submodule).
    let mut missing: Vec<(String, git2::Oid)> = head_gitlinks
        .iter()
        .filter(|(path, _)| index.get_path(Path::new(path), 0).is_none())
        .cloned()
        .collect();

    if missing.is_empty() {
        return Ok(SubmoduleChanges::default());
    }

    // Walk the index once for gitlinks. An index entry counts as the
    // new side of a rename when:
    //   - its path is NOT in HEAD (otherwise it's an existing submodule
    //     that just happens to share an OID with the missing one), and
    //   - its OID matches one of the missing entries.
    // Anything left in `missing` after the walk is genuinely deleted.
    // Linear scans here stay cheap because `missing` is typically 0-2
    // entries and submodule counts top out in the low thousands even
    // for chromium-scale repos.
    let mut changes = SubmoduleChanges::default();
    let gitlink_mode = u32::from(git2::FileMode::Commit);
    for entry in index.iter() {
        if entry.mode != gitlink_mode {
            continue;
        }
        let new_path_bytes: &[u8] = &entry.path;
        let in_head = head_gitlinks
            .iter()
            .any(|(p, _)| p.as_bytes() == new_path_bytes);
        if in_head {
            continue;
        }
        let Some(pos) = missing.iter().position(|(_, oid)| *oid == entry.id) else {
            continue;
        };
        let (old_path, _) = missing.remove(pos);
        let new_path = String::from_utf8_lossy(new_path_bytes).into_owned();
        changes.renamed.push(SubmoduleRename {
            old: old_path,
            new: new_path,
        });
    }
    changes.deleted = missing.into_iter().map(|(path, _)| path).collect();

    Ok(changes)
}

/// Drops submodule statuses whose path is the new side of a rename.
/// The watch server reports the rename's new path as `STAGED_NEW` (a
/// fresh gitlink relative to HEAD); that row is already covered by the
/// rename's `old -> new` line, so we drop it here to match git's output.
///
/// In-place; no allocation. Early-exits when `renames` is empty (the
/// common case). The inner linear scan is fine since rename counts are
/// 0-2 in any realistic workflow.
pub fn filter_rename_new_paths(
    statuses: &mut Vec<(String, StatusSummary)>,
    renames: &[SubmoduleRename],
) {
    if renames.is_empty() {
        return;
    }
    statuses.retain(|(path, _)| !renames.iter().any(|r| r.new == *path));
}

/// Returns the bit-mask to AND each status against to honor `mode`. `None`
/// is unmasked; `All` returns `clean()` so any subsequent test filters out
/// the entry entirely.
fn mode_mask(mode: IgnoreSubmodules) -> StatusSummary {
    match mode {
        IgnoreSubmodules::None => StatusSummary::all(),
        IgnoreSubmodules::All => StatusSummary::clean(),
        IgnoreSubmodules::Untracked => !StatusSummary::UNTRACKED_CONTENT,
        IgnoreSubmodules::Dirty => {
            !(StatusSummary::UNTRACKED_CONTENT | StatusSummary::MODIFIED_CONTENT)
        }
    }
}

/// Masks submodule statuses according to `--ignore-submodules` mode plus any
/// per-submodule `submodule.<name>.ignore` config. The global mode takes
/// priority: only when it's `None` do we consult `per_submodule`.
pub fn apply_ignore_submodules(
    statuses: Vec<(String, StatusSummary)>,
    mode: IgnoreSubmodules,
    per_submodule: &rustc_hash::FxHashMap<String, IgnoreSubmodules>,
) -> Vec<(String, StatusSummary)> {
    if mode == IgnoreSubmodules::All {
        return Vec::new();
    }
    if mode == IgnoreSubmodules::None && per_submodule.is_empty() {
        return statuses;
    }
    statuses
        .into_iter()
        .filter_map(|(path, st)| {
            let effective = if mode == IgnoreSubmodules::None {
                per_submodule
                    .get(&path)
                    .copied()
                    .unwrap_or(IgnoreSubmodules::None)
            } else {
                mode
            };
            let masked = st & mode_mask(effective);
            (!masked.is_empty()).then_some((path, masked))
        })
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

    /// Two submodules cloned from the same source repo share a gitlink
    /// OID. Removing one of them must not be misclassified as a rename
    /// onto the surviving one.
    #[test]
    fn submodule_changes_same_oid_deletion_not_rename() {
        let tmp = TempDir::new().unwrap();
        let root = tmp.path().join("root");
        let sub_src = tmp.path().join("sub_src");

        // Seed the source repo.
        let sub_src_str = sub_src.display().to_string();
        git(&["-C", &tmp.path().display().to_string(), "init", "sub_src"]);
        std::fs::write(sub_src.join("README.md"), "sub\n").unwrap();
        git(&["-C", &sub_src_str, "add", "-A"]);
        git(&["-C", &sub_src_str, "commit", "-m", "init sub"]);

        // Root repo with two submodules both pointing at the same OID.
        let root_str = root.display().to_string();
        git(&["-C", &tmp.path().display().to_string(), "init", "root"]);
        std::fs::write(root.join("file.txt"), "root\n").unwrap();
        git(&["-C", &root_str, "add", "-A"]);
        git(&["-C", &root_str, "commit", "-m", "init root"]);
        for name in ["sub_a", "sub_b"] {
            git(&[
                "-C",
                &root_str,
                "-c",
                "protocol.file.allow=always",
                "submodule",
                "add",
                &sub_src_str,
                name,
            ]);
        }
        git(&["-C", &root_str, "commit", "-m", "add submodules"]);

        // Stage removal of one of them.
        git(&["-C", &root_str, "rm", "-f", "sub_b"]);

        let repo = Repository::open(&root).unwrap();
        let changes = submodule_changes(&repo).unwrap();
        assert_eq!(changes.deleted, vec!["sub_b".to_string()]);
        assert!(
            changes.renamed.is_empty(),
            "expected no renames, got {:?}",
            changes.renamed
        );
    }
}
