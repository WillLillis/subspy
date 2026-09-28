//! Submodule status computation and filtering.

use git2::Repository;
use rustc_hash::FxHashMap;

use std::path::Path;

use crate::{
    StatusSummary,
    git::{path::GitPath, read_submodule_head, substatus},
};

use super::{IgnoreSubmodules, StatusResult, conflict::conflicted_paths};

/// A submodule that was renamed (`git mv old new`) since HEAD: same
/// gitlink OID, different path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubmoduleRename {
    pub old: GitPath,
    pub new: GitPath,
}

/// HEAD-to-index submodule changes that don't show up in
/// `git status`'s submodule status: deletions (HEAD path missing from
/// the index) and renames (same gitlink OID at a different path).
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SubmoduleChanges {
    pub deleted: Vec<GitPath>,
    pub renamed: Vec<SubmoduleRename>,
}

/// Returns submodules that are deleted or renamed in the index relative
/// to the HEAD commit.
///
/// Renames are detected by matching gitlink OIDs. A HEAD-tracked submodule
/// from the index is renamed when its OID appears at another path. Gitlinks
/// expose OIDs as their matching signal, so a simultaneous submodule
/// advance and rename appears as a deletion plus a new entry.
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
    let mut head_gitlinks = Vec::new();
    tree_gitlinks(repo, &head_tree, &mut Vec::new(), &mut head_gitlinks)?;

    // HEAD gitlinks lacking a stage-0 entry are candidates for `git rm` or
    // `git mv`. Per-path `get_path` lookups form the fast-path gate, allowing the
    // common case to return before scanning the full index or conflict state. A
    // path this platform cannot represent has no lookup, so it never counts as
    // missing.
    let mut missing: Vec<(GitPath, git2::Oid)> = head_gitlinks
        .iter()
        .filter(|(path, _)| {
            path.to_path()
                .is_ok_and(|path| index.get_path(path, 0).is_none())
        })
        .cloned()
        .collect();

    if missing.is_empty() {
        return Ok(SubmoduleChanges::default());
    }

    // A gitlink can lack a stage-0 entry because it is *unmerged*, not deleted:
    // a conflict (e.g. a rebase/merge where the submodule commit diverged) leaves
    // it at stages 1-3 only, which git shows under "Unmerged paths". Drop those
    // from `missing` so they aren't misreported as staged deletions. The conflict
    // scan is paid only here, off the fast path, when something is actually
    // missing from stage 0.
    let conflicted = conflicted_paths(&index)?;
    missing.retain(|(path, _)| !conflicted.contains(path.as_bytes()));

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
        // A conflict-stage gitlink (an add/add conflict at a fresh path) is
        // unmerged, not a rename target, so it must not be matched against a
        // missing entry's OID.
        if conflicted.contains(new_path_bytes) {
            continue;
        }
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
        changes.renamed.push(SubmoduleRename {
            old: old_path,
            new: GitPath::from(new_path_bytes),
        });
    }
    changes.deleted = missing.into_iter().map(|(path, _)| path).collect();

    Ok(changes)
}

/// Appends every gitlink under `tree` to `gitlinks`, each with its path below
/// `prefix`.
///
/// `Tree::walk` hands its callback each directory as `&str` and aborts on one
/// that is not UTF-8, so this recurses over the entries' byte names instead.
fn tree_gitlinks(
    repo: &Repository,
    tree: &git2::Tree<'_>,
    prefix: &mut Vec<u8>,
    gitlinks: &mut Vec<(GitPath, git2::Oid)>,
) -> Result<(), git2::Error> {
    for entry in tree {
        let len = prefix.len();
        prefix.extend_from_slice(entry.name_bytes());
        let mode = entry.filemode();
        if mode == i32::from(git2::FileMode::Commit) {
            gitlinks.push((GitPath::from(&prefix[..]), entry.id()));
        } else if mode == i32::from(git2::FileMode::Tree) {
            prefix.push(b'/');
            tree_gitlinks(repo, &repo.find_tree(entry.id())?, prefix, gitlinks)?;
        }
        prefix.truncate(len);
    }
    Ok(())
}

/// Folds each unmerged gitlink submodule into one status keyed by path. Git
/// reports these through the unmerged machinery. Renderers use the result to
/// remove normal submodule rows and populate procelain v2 `u`-line's `S<c><m><u>`
/// field.
///
/// The status carries:
///
/// - `MODIFIED_CONTENT`, `UNTRACKED_CONTENT`, and `DELETED_WORKDIR` from the
///   previously gathered `dirty_submodules`.
/// - `NEW_COMMITS` from comparing the submodule's HEAD with the "ours" stage
///   gitlink, git's reference for the `c` flag during a conflict.
///
/// Callers invoke this after detecting a conflict, limiting conflict scan and
/// submodule HEAD reads to that path.
///
/// # Errors
///
/// Returns `Err` if the index or its conflict iterator cannot be read.
pub fn conflicted_submodule_statuses(
    repo: &Repository,
    root_path: &Path,
    dirty_submodules: &[(GitPath, StatusSummary)],
) -> StatusResult<FxHashMap<GitPath, StatusSummary>> {
    let gitlink_mode = u32::from(git2::FileMode::Commit);
    let index = repo.index()?;
    let mut map = FxHashMap::default();
    for conflict in index.conflicts()? {
        let conflict = conflict?;
        // Any present stage carries the shared path and the gitlink mode. File
        // conflicts have a non-gitlink mode and are skipped.
        let Some(any) = conflict
            .our
            .as_ref()
            .or(conflict.their.as_ref())
            .or(conflict.ancestor.as_ref())
        else {
            continue;
        };
        if any.mode != gitlink_mode {
            continue;
        }
        let path = GitPath::from(&any.path[..]);

        // m/u (and a deleted workdir) from the submodule's own status.
        let mut st = dirty_submodules.iter().find(|(p, _)| *p == path).map_or(
            StatusSummary::clean(),
            |(_, s)| {
                *s & (StatusSummary::MODIFIED_CONTENT
                    | StatusSummary::UNTRACKED_CONTENT
                    | StatusSummary::DELETED_WORKDIR)
            },
        );

        // libgit2 reports no `WD_DELETED` for a gitlink with no stage-0 entry,
        // so the scan above cannot see a missing workdir here. git stats the
        // path for the same answer, as the `c` read below already does. A path
        // this platform cannot represent has no workdir either.
        let workdir = path.to_path().ok().map(|rel| root_path.join(rel));
        if !workdir.as_deref().is_some_and(Path::exists) {
            st |= StatusSummary::DELETED_WORKDIR;
        }

        // c: the submodule advanced past the "ours" gitlink.
        if let (Some(ours), Some(workdir)) = (&conflict.our, &workdir) {
            let (head, _) = read_submodule_head(workdir);
            if head.is_some_and(|h| h != ours.id) {
                st |= StatusSummary::NEW_COMMITS;
            }
        }

        map.insert(path, st);
    }
    Ok(map)
}

/// Drops submodule statuses whose path is the new side of a rename. The watch
/// server reports that path as `STAGED_NEW`, a fresh gitlink relative to HEAD.
/// The rename's `old -> new` line already covers it.
pub fn filter_rename_new_paths(
    statuses: &mut Vec<(GitPath, StatusSummary)>,
    renames: &[SubmoduleRename],
) {
    if renames.is_empty() {
        return;
    }
    statuses.retain(|(path, _)| !renames.iter().any(|r| r.new == *path));
}

/// Returns the mask to AND each status against to honor `mode`.
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
    statuses: Vec<(GitPath, StatusSummary)>,
    mode: IgnoreSubmodules,
    untracked: super::UntrackedFiles,
    per_submodule: &rustc_hash::FxHashMap<GitPath, IgnoreSubmodules>,
) -> Vec<(GitPath, StatusSummary)> {
    if mode == IgnoreSubmodules::All {
        return Vec::new();
    }
    // `-uno` hides untracked content inside submodules as well as at the top
    // level, so a submodule dirtied only that way reports clean.
    let untracked_mask = if untracked == super::UntrackedFiles::No {
        !StatusSummary::UNTRACKED_CONTENT
    } else {
        StatusSummary::all()
    };
    if mode == IgnoreSubmodules::None && per_submodule.is_empty() && untracked_mask.is_all() {
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
            let masked = st & mode_mask(effective) & untracked_mask;
            (!masked.is_empty()).then_some((path, masked))
        })
        .collect()
}

/// Computes submodule statuses locally via git2 without the watch server, for
/// every gitlink in the index, the same set the watch server reports.
///
/// # Errors
///
/// Returns `git2::Error` if the repository or its index cannot be read.
pub fn compute_local_statuses(
    root_path: &Path,
) -> Result<Vec<(GitPath, StatusSummary)>, git2::Error> {
    use rayon::prelude::*;

    let paths = substatus::gitlink_paths(&Repository::open(root_path)?)?;
    let tl_repo = thread_local::ThreadLocal::new();

    let statuses: Vec<_> = paths
        .into_par_iter()
        .map(|path| -> (GitPath, StatusSummary) {
            let summary = tl_repo
                .get_or_try(|| Repository::open(root_path))
                .map_err(substatus::SubstatusError::from)
                .and_then(|repo| substatus::submodule_status(repo, &path))
                .unwrap_or(StatusSummary::UNREADABLE);
            (path, summary)
        })
        .filter(|(_, s)| *s != StatusSummary::clean())
        .collect();

    Ok(statuses)
}

#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;
    use rstest_reuse::apply;
    use tempfile::TempDir;
    use testutil::{HarnessBuilder, RefFormat, Repo};

    use crate::test_support::formats;

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

    #[apply(formats)]
    fn compute_local_statuses_clean_repo(ref_format: RefFormat) {
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
        Repo::new(&root).migrate_refs(ref_format);

        let statuses = compute_local_statuses(&root).unwrap();
        assert!(
            statuses.is_empty(),
            "clean repo should have no dirty submodules"
        );
    }

    #[apply(formats)]
    fn compute_local_statuses_dirty_submodule(ref_format: RefFormat) {
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
        Repo::new(&root).migrate_refs(ref_format);

        // Dirty the submodule
        std::fs::write(root.join("my_sub").join("new.txt"), "untracked\n").unwrap();

        let statuses = compute_local_statuses(&root).unwrap();
        assert_eq!(statuses.len(), 1);
        assert_eq!(statuses[0].0, "my_sub");
        assert!(statuses[0].1.contains(StatusSummary::UNTRACKED_CONTENT));
    }

    /// Each submodule is read in its own ref format, whatever the root's.
    #[rstest::rstest]
    #[case::reftable_submodules(RefFormat::Files, RefFormat::Reftable)]
    #[case::files_submodules(RefFormat::Reftable, RefFormat::Files)]
    #[ignore = "reftable: needs libgit2 support (git2-rs#1259)"]
    fn compute_local_statuses_mixed_ref_formats(
        #[case] root_format: RefFormat,
        #[case] submodule_format: RefFormat,
    ) {
        let harness = HarnessBuilder::new()
            .no_server()
            .ref_format(root_format)
            .submodule_ref_format(submodule_format)
            .submodule("sub_a")
            .submodule("sub_b")
            .build();
        let assert_statuses = |expected: &[(&str, StatusSummary)]| {
            let statuses = compute_local_statuses(harness.root().path()).unwrap();
            let expected: Vec<_> = expected
                .iter()
                .map(|(path, status)| (GitPath::from(*path), *status))
                .collect();
            assert_eq!(statuses, expected);
        };
        assert_statuses(&[]);

        harness.submodule("sub_a").write("untracked.txt", "x\n");
        assert_statuses(&[("sub_a", StatusSummary::UNTRACKED_CONTENT)]);

        let sub_b = harness.submodule("sub_b");
        sub_b.write("new.txt", "content\n");
        assert_statuses(&[
            ("sub_a", StatusSummary::UNTRACKED_CONTENT),
            ("sub_b", StatusSummary::UNTRACKED_CONTENT),
        ]);

        sub_b.add_all();
        assert_statuses(&[
            ("sub_a", StatusSummary::UNTRACKED_CONTENT),
            ("sub_b", StatusSummary::MODIFIED_CONTENT),
        ]);

        sub_b.commit("add new.txt");
        assert_statuses(&[
            ("sub_a", StatusSummary::UNTRACKED_CONTENT),
            ("sub_b", StatusSummary::NEW_COMMITS),
        ]);
    }

    /// Two submodules cloned from the same source repo share a gitlink
    /// OID. Removing one of them must not be misclassified as a rename
    /// onto the surviving one.
    #[apply(formats)]
    fn submodule_changes_same_oid_deletion_not_rename(ref_format: RefFormat) {
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
        Repo::new(&root).migrate_refs(ref_format);

        // Stage removal of one of them.
        git(&["-C", &root_str, "rm", "-f", "sub_b"]);

        let repo = Repository::open(&root).unwrap();
        let changes = submodule_changes(&repo).unwrap();
        assert_eq!(changes.deleted, vec![GitPath::from("sub_b")]);
        assert!(
            changes.renamed.is_empty(),
            "expected no renames, got {:?}",
            changes.renamed
        );
    }

    /// The HEAD walk descends into a directory whose name is not UTF-8 and finds
    /// the gitlink below it.
    ///
    /// Linux-only: Windows (NTFS is UTF-16) and macOS (EILSEQ) refuse the name.
    #[cfg(target_os = "linux")]
    #[apply(formats)]
    fn submodule_changes_walks_non_utf8_directories(ref_format: RefFormat) {
        use std::{ffi::OsStr, os::unix::ffi::OsStrExt as _};

        let harness = HarnessBuilder::new()
            .ref_format(ref_format)
            .submodule(b"dir\xff/sub")
            .no_server()
            .build();
        let root = harness.root().path();
        let changes = || submodule_changes(&Repository::open(root).unwrap()).unwrap();
        assert_eq!(changes(), SubmoduleChanges::default());

        // `git` from the helper above takes `&str` arguments.
        let status = std::process::Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["rm", "-q", "-f"])
            .arg(OsStr::from_bytes(b"dir\xff/sub"))
            .status()
            .unwrap();
        assert!(status.success());
        assert_eq!(
            changes().deleted,
            vec![GitPath::from(b"dir\xff/sub".as_slice())]
        );
    }
}
