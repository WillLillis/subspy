//! Lightweight git helpers that bypass expensive libgit2 machinery.

use git2::{Config, Repository};
use rustc_hash::FxHashMap;

use std::path::Path;

use crate::status::IgnoreSubmodules;

/// Configures global libgit2 options for subspy's read-only, local-only use case.
///
/// Skips ownership validation and SHA1 hash verification on object reads.
/// Must be called before any threads are spawned, as these options mutate
/// global libgit2 state.
pub fn configure_git2() {
    // SAFETY: Caller guarantees single-threaded context.
    unsafe {
        // Skip the per-open ownership stat checks that verify the .git directory
        // is owned by the current user (CVE-2022-24765 mitigation). We only open
        // repos the user explicitly points us at.
        let _ = git2::opts::set_verify_owner_validation(false);
        // Skip SHA1 checksum verification on object reads. We trust the local
        // filesystem and don't need to detect repository corruption.
        git2::opts::strict_hash_verification(false);
    }
}

/// The `gitdir:` target path from a `.git` gitlink *file*'s raw bytes.
///
/// `dot_git_bytes` belongs to a submodule, linked worktree, or other gitlink
/// `.git`. Returns `None` if the bytes aren't a `gitdir:` pointer (git writes the
/// file as exactly `gitdir: <path>\n`).
#[inline]
#[must_use]
pub fn gitlink_target(dot_git_bytes: &[u8]) -> Option<&[u8]> {
    dot_git_bytes.trim_ascii().strip_prefix(b"gitdir: ")
}

/// The submodule "modules subpath" (the path *within* a `.git/modules/`
/// directory).
///
/// A submodule's gitdir lives under its superproject's `.git/modules/<name>`,
/// or, when the submodule is nested in a linked worktree, under that worktree's
/// private `.git/worktrees/<wt>/modules/<name>`. The returned subpath is the
/// `<name>` portion.
#[must_use]
pub fn submodule_modules_subpath(dot_git_bytes: &[u8]) -> Option<&[u8]> {
    let target = gitlink_target(dot_git_bytes)?;
    // `.git/modules/<name>`: a submodule of a normal superproject.
    if let Some(subpath) = after_marker(target, b".git/modules/") {
        return Some(subpath);
    }
    // `.git/worktrees/<wt>/modules/<name>`: a submodule nested in a worktree.
    let after_worktree = after_marker(target, b".git/worktrees/")?;
    after_marker(after_worktree, b"/modules/")
}

/// The bytes following the first occurrence of `marker` in `haystack`, or `None`
/// if `marker` is absent. Allocation-free.
fn after_marker<'a>(haystack: &'a [u8], marker: &[u8]) -> Option<&'a [u8]> {
    haystack
        .windows(marker.len())
        .position(|window| window == marker)
        .map(|start| &haystack[start + marker.len()..])
}

/// Whether a `.git` gitlink *file* points at a **linked worktree**.
///
/// Git writes a `commondir` file into every linked worktree's private gitdir
/// (`<main>/.git/worktrees/<id>/commondir`; see `gitrepository-layout(5)`),
/// whereas a submodule's gitdir and a `--separate-git-dir` gitdir never have
/// one.
///
/// `repo_root` is the directory holding the `.git` file; a relative `gitdir:`
/// target resolves against it (git's rule for gitlink files), while an absolute
/// one stands alone. Returns `false` if the bytes aren't a `gitdir:` pointer,
/// the target can't be represented as a path on this platform, or the marker is
/// absent or unreadable.
#[must_use]
pub fn gitlink_points_at_worktree(dot_git_bytes: &[u8], repo_root: &Path) -> bool {
    gitlink_target(dot_git_bytes).is_some_and(|target| gitdir_has_commondir(repo_root, target))
}

/// Whether the gitdir named by `target` contains git's `commondir` marker.
#[cfg(unix)]
fn gitdir_has_commondir(repo_root: &Path, target: &[u8]) -> bool {
    use std::os::unix::ffi::OsStrExt as _;
    let gitdir = repo_root.join(std::ffi::OsStr::from_bytes(target));
    gitdir.join("commondir").exists()
}

/// Whether the gitdir named by `target` contains git's `commondir` marker. Off
/// Unix a gitdir path must be valid Unicode, so a non-UTF-8 `target` cannot be
/// resolved and is reported as not-a-worktree.
#[cfg(not(unix))]
fn gitdir_has_commondir(repo_root: &Path, target: &[u8]) -> bool {
    let Ok(target) = std::str::from_utf8(target) else {
        return false;
    };
    repo_root.join(target).join("commondir").exists()
}

fn parse_ignore_mode(s: &str) -> Option<IgnoreSubmodules> {
    match s {
        "none" => Some(IgnoreSubmodules::None),
        "untracked" => Some(IgnoreSubmodules::Untracked),
        "dirty" => Some(IgnoreSubmodules::Dirty),
        "all" => Some(IgnoreSubmodules::All),
        _ => None,
    }
}

/// Scans `config` for `submodule.<name>.path` and `submodule.<name>.ignore`
/// entries, accumulating into the supplied maps. Used by
/// [`parse_per_submodule_ignore`] to combine `.gitmodules` (always read) with
/// `.git/config` (overrides per key).
fn scan_submodule_props(
    config: &Config,
    name_to_path: &mut FxHashMap<String, String>,
    name_to_ignore: &mut FxHashMap<String, IgnoreSubmodules>,
) {
    let Ok(mut iter) = config.entries(Some("submodule\\..*\\.(path|ignore)")) else {
        return;
    };
    while let Some(Ok(entry)) = iter.next() {
        let Ok(key) = entry.name() else { continue };
        let Some(rest) = key.strip_prefix("submodule.") else {
            continue;
        };
        if let Some(name) = rest.strip_suffix(".path") {
            if let Ok(val) = entry.value() {
                name_to_path.insert(name.to_string(), val.to_string());
            }
        } else if let Some(name) = rest.strip_suffix(".ignore")
            && let Some(mode) = entry.value().ok().and_then(parse_ignore_mode)
        {
            name_to_ignore.insert(name.to_string(), mode);
        }
    }
}

/// Cheap byte-scan: returns `true` if `path` is readable and contains the
/// sub-slice `ignore`. Most repos never set per-submodule ignore, so a
/// negative answer here lets [`parse_per_submodule_ignore`] short-circuit
/// without paying the cost of opening a git config.
fn file_mentions_ignore(path: &Path) -> bool {
    let Ok(bytes) = std::fs::read(path) else {
        return false;
    };
    memchr::memmem::find(&bytes, b"ignore").is_some()
}

/// Returns per-submodule `ignore` settings keyed by submodule path.
///
/// Merges `.gitmodules` (read first) with `.git/config` (read second so it
/// overrides per key). Submodules with no explicit `ignore` entry are
/// absent from the result.
///
/// Fast path: if neither config file even mentions the substring `ignore`,
/// returns an empty map without opening either as a git config (full parse
/// costs hundreds of microseconds on submodule-heavy repos).
#[must_use]
pub fn parse_per_submodule_ignore(
    repo: &Repository,
    root_path: &Path,
) -> FxHashMap<String, IgnoreSubmodules> {
    let gitmodules_path = root_path.join(".gitmodules");
    let repo_config_path = repo.path().join("config");
    if !file_mentions_ignore(&gitmodules_path) && !file_mentions_ignore(&repo_config_path) {
        return FxHashMap::default();
    }

    let mut name_to_path: FxHashMap<String, String> = FxHashMap::default();
    let mut name_to_ignore: FxHashMap<String, IgnoreSubmodules> = FxHashMap::default();

    if let Ok(gm) = Config::open(&gitmodules_path) {
        scan_submodule_props(&gm, &mut name_to_path, &mut name_to_ignore);
    }
    if let Ok(repo_cfg) = repo.config() {
        // Only the ignore side: `.git/config` doesn't redefine paths.
        scan_submodule_props(&repo_cfg, &mut FxHashMap::default(), &mut name_to_ignore);
    }

    name_to_ignore
        .into_iter()
        .filter_map(|(name, mode)| name_to_path.get(&name).map(|p| (p.clone(), mode)))
        .collect()
}

/// Parses `.gitmodules` to extract submodule name, path, and branch without
/// going through `repo.submodules()` (which triggers expensive per-submodule
/// config snapshot parsing in libgit2).
///
/// # Errors
///
/// Returns `git2::Error` if `.gitmodules` cannot be parsed.
pub fn parse_gitmodules(
    root_path: &Path,
) -> Result<Vec<(String, String, Option<String>)>, git2::Error> {
    let gitmodules_path = root_path.join(".gitmodules");
    let config = git2::Config::open(&gitmodules_path)?;
    let mut entries = Vec::new();

    let mut branch_key = String::from("submodule.");
    let mut iter = config.entries(Some("submodule\\..*\\.path"))?;
    while let Some(entry) = iter.next() {
        let entry = entry?;
        // Skip entries with a non-UTF-8 key or path instead of panicking: a
        // submodule path is arbitrary bytes on Linux, and git tolerates it.
        // Mirrors `scan_submodule_props`.
        let Ok(key) = entry.name() else { continue };
        // The regex filter on entries() guarantees this shape; skip defensively.
        let Some(name) = key
            .strip_prefix("submodule.")
            .and_then(|s| s.strip_suffix(".path"))
        else {
            continue;
        };
        let Ok(path) = entry.value() else { continue };
        let path = path.to_string();
        branch_key.truncate("submodule.".len());
        branch_key.push_str(name);
        branch_key.push_str(".branch");
        let branch = config.get_string(&branch_key).ok();
        entries.push((name.to_string(), path, branch));
    }
    Ok(entries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn write_gitmodules(root: &Path, content: &str) {
        std::fs::write(root.join(".gitmodules"), content).unwrap();
    }

    #[test]
    fn submodule_modules_subpath_extracts_name() {
        // `.git/modules/<name>` (relative target, as git writes for submodules):
        assert_eq!(
            submodule_modules_subpath(b"gitdir: ../.git/modules/sub\n"),
            Some(b"sub".as_slice())
        );
        // Multi-component submodule name:
        assert_eq!(
            submodule_modules_subpath(b"gitdir: ../../.git/modules/libs/foo\n"),
            Some(b"libs/foo".as_slice())
        );
        // A submodule nested in a linked worktree.
        assert_eq!(
            submodule_modules_subpath(b"gitdir: /m/.git/worktrees/wt/modules/sub\n"),
            Some(b"sub".as_slice())
        );
    }

    #[test]
    fn submodule_modules_subpath_rejects_non_submodules() {
        // A linked worktree itself is not a submodule.
        assert_eq!(
            submodule_modules_subpath(b"gitdir: /m/.git/worktrees/wt\n"),
            None
        );
        // An external (`--separate-git-dir`) gitdir.
        assert_eq!(
            submodule_modules_subpath(b"gitdir: /var/lib/git/x.git\n"),
            None
        );
        // Not a `gitdir:` pointer at all.
        assert_eq!(submodule_modules_subpath(b"garbage"), None);
        assert_eq!(submodule_modules_subpath(b""), None);
    }

    #[test]
    fn worktree_detected_by_commondir_marker() {
        // A gitdir carrying the `commondir` marker is a linked worktree, found by
        // resolving an absolute target.
        let tmp = TempDir::new().unwrap();
        let root = tmp.path();
        let gitdir = root.join("main").join(".git").join("worktrees").join("wt");
        std::fs::create_dir_all(&gitdir).unwrap();
        std::fs::write(gitdir.join("commondir"), "../..\n").unwrap();

        let bytes = format!("gitdir: {}\n", gitdir.display());
        assert!(gitlink_points_at_worktree(bytes.as_bytes(), root));
    }

    #[test]
    fn worktree_detection_resolves_relative_target() {
        // Submodules (and some worktrees) use a relative `gitdir:` resolved
        // against the repo root holding `.git`.
        let tmp = TempDir::new().unwrap();
        let root = tmp.path();
        let gitdir = root.join("main").join(".git").join("worktrees").join("wt");
        std::fs::create_dir_all(&gitdir).unwrap();
        std::fs::write(gitdir.join("commondir"), "../..\n").unwrap();

        assert!(gitlink_points_at_worktree(
            b"gitdir: main/.git/worktrees/wt\n",
            root
        ));
    }

    #[test]
    fn submodule_gitdir_is_not_a_worktree() {
        // A submodule gitdir (no `commondir`) must not be taken for a worktree,
        // even though its path contains `.git/...`.
        let tmp = TempDir::new().unwrap();
        let root = tmp.path();
        let gitdir = root.join(".git").join("modules").join("sub");
        std::fs::create_dir_all(&gitdir).unwrap();

        assert!(!gitlink_points_at_worktree(
            b"gitdir: .git/modules/sub\n",
            root
        ));
    }

    #[test]
    fn worktree_lookalike_without_commondir_is_not_a_worktree() {
        // A `--separate-git-dir` whose path merely *looks* like a worktree
        // (`.git/worktrees/...`) but has no `commondir` marker is not a worktree.
        let tmp = TempDir::new().unwrap();
        let root = tmp.path();
        let gitdir = root
            .join("other")
            .join(".git")
            .join("worktrees")
            .join("proj");
        std::fs::create_dir_all(&gitdir).unwrap(); // no `commondir`

        let bytes = format!("gitdir: {}\n", gitdir.display());
        assert!(!gitlink_points_at_worktree(bytes.as_bytes(), root));
    }

    #[test]
    fn non_gitdir_bytes_are_not_a_worktree() {
        let tmp = TempDir::new().unwrap();
        assert!(!gitlink_points_at_worktree(b"garbage", tmp.path()));
        assert!(!gitlink_points_at_worktree(b"", tmp.path()));
    }

    #[test]
    fn single_submodule() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"sub\"]\n\tpath = sub\n\turl = https://example.com/sub.git\n",
        );
        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].0, "sub");
        assert_eq!(entries[0].1, "sub");
        assert_eq!(entries[0].2, None);
    }

    #[test]
    fn multiple_submodules() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"a\"]\n\tpath = a\n\turl = u\n\
             [submodule \"b\"]\n\tpath = libs/b\n\turl = u\n",
        );
        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].0, "a");
        assert_eq!(entries[0].1, "a");
        assert_eq!(entries[1].0, "b");
        assert_eq!(entries[1].1, "libs/b");
    }

    #[test]
    fn submodule_with_branch() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"sub\"]\n\tpath = sub\n\turl = u\n\tbranch = main\n",
        );
        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert_eq!(entries[0].2, Some("main".to_string()));
    }

    #[test]
    fn nested_path() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"vendor/lib\"]\n\tpath = vendor/lib\n\turl = u\n",
        );
        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert_eq!(entries[0].0, "vendor/lib");
        assert_eq!(entries[0].1, "vendor/lib");
    }

    #[test]
    fn dotted_name() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"my.lib\"]\n\tpath = my.lib\n\turl = u\n",
        );
        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert_eq!(entries[0].0, "my.lib");
    }

    #[test]
    fn empty_gitmodules() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(tmp.path(), "");
        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert!(entries.is_empty());
    }

    #[test]
    fn missing_gitmodules_returns_empty() {
        let tmp = TempDir::new().unwrap();
        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert!(entries.is_empty());
    }

    #[test]
    fn non_utf8_path_is_skipped_not_panicking() {
        // A submodule path is arbitrary bytes on Linux; libgit2 surfaces the
        // entry but `value()` returns Err for the non-UTF-8 byte. The bad entry
        // must be skipped, not crash the process (which would take down the
        // whole daemon under `panic = "abort"`).
        let tmp = TempDir::new().unwrap();
        let mut content = Vec::new();
        content.extend_from_slice(b"[submodule \"good\"]\n\tpath = good\n\turl = u\n");
        content.extend_from_slice(b"[submodule \"bad\"]\n\tpath = b\xffd\n\turl = u\n");
        std::fs::write(tmp.path().join(".gitmodules"), content).unwrap();

        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert!(entries.iter().any(|(n, p, _)| n == "good" && p == "good"));
        assert!(!entries.iter().any(|(n, _, _)| n == "bad"));
    }

    #[test]
    fn boost_gitmodules() {
        let tmp = TempDir::new().unwrap();
        std::fs::copy(
            concat!(env!("CARGO_MANIFEST_DIR"), "/src/testdata/boost_gitmodules"),
            tmp.path().join(".gitmodules"),
        )
        .unwrap();
        let entries = parse_gitmodules(tmp.path()).unwrap();
        assert_eq!(entries.len(), 172);
        // All entries should have non-empty name and path
        for (name, path, _) in &entries {
            assert!(!name.is_empty(), "empty name in boost .gitmodules");
            assert!(!path.is_empty(), "empty path in boost .gitmodules");
        }
        // All boost submodules use `branch = .`
        for (_, _, branch) in &entries {
            assert_eq!(branch.as_deref(), Some("."));
        }
        // Spot check a few known entries
        assert!(
            entries
                .iter()
                .any(|(n, p, _)| n == "system" && p == "libs/system")
        );
        assert!(
            entries
                .iter()
                .any(|(n, p, _)| n == "math" && p == "libs/math")
        );
    }

    #[test]
    fn per_submodule_ignore_fast_path_returns_empty() {
        // No "ignore" string anywhere -> short-circuit, empty map.
        let tmp = TempDir::new().unwrap();
        write_gitmodules(tmp.path(), "[submodule \"sub\"]\n\tpath = sub\n\turl = u\n");
        let repo = git2::Repository::init(tmp.path()).unwrap();
        let map = parse_per_submodule_ignore(&repo, tmp.path());
        assert!(map.is_empty());
    }

    #[test]
    fn per_submodule_ignore_from_gitmodules() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"vendor/foo\"]\n\
             \tpath = vendor/foo\n\
             \turl = u\n\
             \tignore = dirty\n\
             [submodule \"vendor/bar\"]\n\
             \tpath = vendor/bar\n\
             \turl = u\n",
        );
        let repo = git2::Repository::init(tmp.path()).unwrap();
        let map = parse_per_submodule_ignore(&repo, tmp.path());
        assert_eq!(map.len(), 1);
        assert_eq!(map.get("vendor/foo"), Some(&IgnoreSubmodules::Dirty));
        assert_eq!(map.get("vendor/bar"), None);
    }

    #[test]
    fn per_submodule_ignore_repo_config_overrides_gitmodules() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"vendor/foo\"]\n\
             \tpath = vendor/foo\n\
             \turl = u\n\
             \tignore = dirty\n",
        );
        let repo = git2::Repository::init(tmp.path()).unwrap();
        // Override in .git/config to `untracked`.
        repo.config()
            .unwrap()
            .set_str("submodule.vendor/foo.ignore", "untracked")
            .unwrap();
        let map = parse_per_submodule_ignore(&repo, tmp.path());
        assert_eq!(map.get("vendor/foo"), Some(&IgnoreSubmodules::Untracked));
    }
}
