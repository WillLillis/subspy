//! Lightweight git helpers that bypass expensive libgit2 machinery.

pub mod path;
pub mod substatus;

use git2::{Config, Repository, RepositoryOpenFlags};
use rustc_hash::FxHashMap;

use std::path::Path;

use crate::status::IgnoreSubmodules;

use path::GitPath;

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

/// The path git recorded as raw `bytes`. Unix paths are arbitrary bytes, so
/// the conversion is a noop.
///
/// # Errors
///
/// On non-Unix platforms, git records paths as UTF-8, and bytes that are not
/// UTF-8 return [`std::str::Utf8Error`].
pub fn path_from_bytes(bytes: &[u8]) -> Result<&Path, std::str::Utf8Error> {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt as _;
        Ok(Path::new(std::ffi::OsStr::from_bytes(bytes)))
    }
    #[cfg(not(unix))]
    {
        std::str::from_utf8(bytes).map(Path::new)
    }
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
/// at `<main>/.git/worktrees/<id>/commondir` (`gitrepository-layout(5)`).
/// Its presence distinguishes linked worktress from submodule and
/// `--separate-git-dir` gitdirs.
///
/// `repo_root` is the directory containing the `.git` file. Relative `gitdir:`
/// target resolves against it, while absolute targets are used directly. Returns
/// `false`  for malformed pointers, paths unsupported by the platform, and missing
/// or unreadable `commondir` markers.
#[must_use]
pub fn gitlink_points_at_worktree(dot_git_bytes: &[u8], repo_root: &Path) -> bool {
    gitlink_target(dot_git_bytes).is_some_and(|target| gitdir_has_commondir(repo_root, target))
}

/// Whether the gitdir named by `target` (raw path bytes, resolved against
/// `repo_root`) contains git's `commondir` marker. A target the platform cannot
/// represent returns `false`.
fn gitdir_has_commondir(repo_root: &Path, target: &[u8]) -> bool {
    path_from_bytes(target).is_ok_and(|gitdir| repo_root.join(gitdir).join("commondir").exists())
}

/// Reads a submodule's HEAD to get its current OID and branch name (if on a
/// branch). Returns `(None, None)` if the submodule isn't checked out or its
/// repository cannot be opened.
#[must_use]
pub fn read_submodule_head(submod_path: &Path) -> (Option<git2::Oid>, Option<String>) {
    // `NO_SEARCH` keeps an uninitialized workdir from resolving upward to the
    // superproject.
    let Ok(repo) = Repository::open_ext(
        submod_path,
        RepositoryOpenFlags::NO_SEARCH,
        &[] as &[&std::ffi::OsStr],
    ) else {
        return (None, None);
    };
    match repo.head() {
        Ok(head) => {
            let branch = if head.is_branch() {
                head.shorthand().ok().map(str::to_owned)
            } else {
                None
            };
            (head.target(), branch)
        }
        Err(e) if e.code() == git2::ErrorCode::UnbornBranch => {
            let branch = repo.find_reference("HEAD").ok().and_then(|head| {
                let target = head.symbolic_target().ok().flatten()?;
                target.strip_prefix("refs/heads/").map(str::to_owned)
            });
            (None, branch)
        }
        Err(_) => (None, None),
    }
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

/// What a `.gitmodules`-style config sets for one submodule. Paths and branches
/// are bytes, as git records them.
#[derive(Default)]
struct SubmoduleConfig {
    path: Option<GitPath>,
    branch: Option<Vec<u8>>,
    ignore: Option<IgnoreSubmodules>,
}

/// Collects the `submodule.<name>.path`, `.branch`, and `.ignore` entries in
/// `config`, keyed by the submodule name's bytes. A later entry overrides an
/// earlier one, as in git.
///
/// # Errors
///
/// Returns `git2::Error` if the entries cannot be read.
fn scan_submodules(config: &Config) -> Result<FxHashMap<Vec<u8>, SubmoduleConfig>, git2::Error> {
    let mut submodules: FxHashMap<Vec<u8>, SubmoduleConfig> = FxHashMap::default();
    let mut iter = config.entries(Some("submodule\\..*\\.(path|branch|ignore)"))?;
    while let Some(entry) = iter.next() {
        let entry = entry?;
        // `submodule.<name>.<key>`, where the name can contain dots and the key
        // cannot.
        let Some(rest) = entry.name_bytes().strip_prefix(b"submodule.") else {
            continue;
        };
        let Some(dot) = rest.iter().rposition(|&b| b == b'.') else {
            continue;
        };
        // A key written without `=` has no value, and `value_bytes` panics on it.
        if !entry.has_value() {
            continue;
        }
        let value = entry.value_bytes();
        let submodule = submodules.entry(rest[..dot].to_vec()).or_default();
        match &rest[dot + 1..] {
            b"path" => submodule.path = Some(GitPath::from(value)),
            b"branch" => submodule.branch = Some(value.to_vec()),
            b"ignore" => {
                if let Some(mode) = std::str::from_utf8(value).ok().and_then(parse_ignore_mode) {
                    submodule.ignore = Some(mode);
                }
            }
            _ => {}
        }
    }
    Ok(submodules)
}

/// Cheap byte scan for  `ignore` in a readable file. A `false` result lets
/// [`parse_per_submodule_ignore`] return before opening a git config.
fn file_mentions_ignore(path: &Path) -> bool {
    let Ok(bytes) = std::fs::read(path) else {
        return false;
    };
    memchr::memmem::find(&bytes, b"ignore").is_some()
}

/// Returns per-submodule `ignore` settings keyed by submodule path.
///
/// Merges `.gitmodules` (read first) with `.git/config` (read second so it overrides
/// per key). Submodules with no explicit `ignore` entry are absent from the result.
///
/// Fast path:  when byte scans find no `ignore` substring in either file, returns
/// an empty map and avoids full config parsing.
#[must_use]
pub fn parse_per_submodule_ignore(
    repo: &Repository,
    root_path: &Path,
) -> FxHashMap<GitPath, IgnoreSubmodules> {
    let gitmodules_path = root_path.join(".gitmodules");
    let repo_config_path = repo.path().join("config");
    if !file_mentions_ignore(&gitmodules_path) && !file_mentions_ignore(&repo_config_path) {
        return FxHashMap::default();
    }

    let mut submodules = Config::open(&gitmodules_path)
        .and_then(|config| scan_submodules(&config))
        .unwrap_or_default();
    // `.git/config` overrides `ignore` per name. Submodule paths come from
    // `.gitmodules`.
    if let Ok(overrides) = repo.config().and_then(|config| scan_submodules(&config)) {
        for (name, submodule) in overrides {
            if let Some(ignore) = submodule.ignore {
                submodules.entry(name).or_default().ignore = Some(ignore);
            }
        }
    }

    submodules
        .into_values()
        .filter_map(|submodule| Some((submodule.path?, submodule.ignore?)))
        .collect()
}

/// What `.gitmodules` records for a submodule besides its path. Bytes, as git
/// records them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Gitmodule {
    pub name: Vec<u8>,
    pub branch: Option<Vec<u8>>,
}

/// Parses `.gitmodules` directly via [`git2::Config`] for each submodule's name
/// and branch, keyed by path. A missing file parses as no entries.
///
/// # Errors
///
/// Returns `git2::Error` if `.gitmodules` cannot be parsed.
pub fn parse_gitmodules(root_path: &Path) -> Result<FxHashMap<GitPath, Gitmodule>, git2::Error> {
    let config = Config::open(&root_path.join(".gitmodules"))?;
    Ok(scan_submodules(&config)?
        .into_iter()
        .filter_map(|(name, submodule)| {
            let branch = submodule.branch;
            Some((submodule.path?, Gitmodule { name, branch }))
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::path::PathBuf;

    use pretty_assertions::assert_eq;
    use rstest_reuse::apply;
    use tempfile::TempDir;
    use testutil::{RefFormat, Repo};

    use crate::test_support::formats;

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

    /// A `.gitmodules` entry as `(path, name, branch)`.
    type Entry<'a> = (&'a [u8], &'a [u8], Option<&'a [u8]>);

    /// The expected [`parse_gitmodules`] result for `entries`.
    fn gitmodules<const N: usize>(entries: [Entry<'_>; N]) -> FxHashMap<GitPath, Gitmodule> {
        entries
            .into_iter()
            .map(|(path, name, branch)| {
                let gitmodule = Gitmodule {
                    name: name.to_vec(),
                    branch: branch.map(<[u8]>::to_vec),
                };
                (GitPath::from(path), gitmodule)
            })
            .collect()
    }

    #[test]
    fn single_submodule() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"sub\"]\n\tpath = sub\n\turl = https://example.com/sub.git\n",
        );
        assert_eq!(
            parse_gitmodules(tmp.path()).unwrap(),
            gitmodules([(b"sub", b"sub", None)])
        );
    }

    #[test]
    fn multiple_submodules() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"a\"]\n\tpath = a\n\turl = u\n\
             [submodule \"b\"]\n\tpath = libs/b\n\turl = u\n",
        );
        assert_eq!(
            parse_gitmodules(tmp.path()).unwrap(),
            gitmodules([(b"a", b"a", None), (b"libs/b", b"b", None)])
        );
    }

    #[test]
    fn submodule_with_branch() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"sub\"]\n\tpath = sub\n\turl = u\n\tbranch = main\n",
        );
        assert_eq!(
            parse_gitmodules(tmp.path()).unwrap(),
            gitmodules([(b"sub", b"sub", Some(b"main"))])
        );
    }

    #[test]
    fn nested_path() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"vendor/lib\"]\n\tpath = vendor/lib\n\turl = u\n",
        );
        assert_eq!(
            parse_gitmodules(tmp.path()).unwrap(),
            gitmodules([(b"vendor/lib", b"vendor/lib", None)])
        );
    }

    #[test]
    fn dotted_name() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"my.lib\"]\n\tpath = my.lib\n\turl = u\n",
        );
        assert_eq!(
            parse_gitmodules(tmp.path()).unwrap(),
            gitmodules([(b"my.lib", b"my.lib", None)])
        );
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

    /// Git records names, paths, and branches as bytes, so ones that are not
    /// UTF-8 come through intact.
    #[test]
    fn non_utf8_entries_are_kept() {
        let tmp = TempDir::new().unwrap();
        let mut content = Vec::new();
        content.extend_from_slice(b"[submodule \"good\"]\n\tpath = good\n\turl = u\n");
        content.extend_from_slice(
            b"[submodule \"b\xffd\"]\n\tpath = p\xffth\n\turl = u\n\tbranch = br\xff\n",
        );
        std::fs::write(tmp.path().join(".gitmodules"), content).unwrap();

        assert_eq!(
            parse_gitmodules(tmp.path()).unwrap(),
            gitmodules([
                (b"good", b"good", None),
                (b"p\xffth", b"b\xffd", Some(b"br\xff")),
            ])
        );
    }

    /// A key written without `=` has no value, which git2's value accessors
    /// panic on.
    #[test]
    fn bare_key_is_skipped() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"bare\"]\n\tpath\n\turl = u\n\
             [submodule \"ok\"]\n\tpath = ok\n\turl = u\n",
        );
        assert_eq!(
            parse_gitmodules(tmp.path()).unwrap(),
            gitmodules([(b"ok", b"ok", None)])
        );
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
        for (path, gitmodule) in &entries {
            assert!(
                !gitmodule.name.is_empty(),
                "empty name in boost .gitmodules"
            );
            assert!(
                !path.as_bytes().is_empty(),
                "empty path in boost .gitmodules"
            );
        }
        // All boost submodules use `branch = .`
        for gitmodule in entries.values() {
            assert_eq!(gitmodule.branch.as_deref(), Some(b".".as_slice()));
        }
        // Spot check a few known entries
        assert_eq!(entries[b"libs/system".as_slice()].name, b"system");
        assert_eq!(entries[b"libs/math".as_slice()].name, b"math");
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
        assert_eq!(
            map.get(b"vendor/foo".as_slice()),
            Some(&IgnoreSubmodules::Dirty)
        );
        assert_eq!(map.get(b"vendor/bar".as_slice()), None);
    }

    /// A bare `ignore` key has no value, which git2's value accessors panic on.
    #[test]
    fn per_submodule_ignore_skips_a_bare_key() {
        let tmp = TempDir::new().unwrap();
        write_gitmodules(
            tmp.path(),
            "[submodule \"sub\"]\n\tpath = sub\n\turl = u\n\tignore\n",
        );
        let repo = git2::Repository::init(tmp.path()).unwrap();
        assert!(parse_per_submodule_ignore(&repo, tmp.path()).is_empty());
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
        assert_eq!(
            map.get(b"vendor/foo".as_slice()),
            Some(&IgnoreSubmodules::Untracked)
        );
    }

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

    /// Creates a repo with a single submodule checked out on `master`.
    fn init_repo_with_submodule(ref_format: RefFormat) -> (TempDir, PathBuf) {
        let tmp = TempDir::new().unwrap();

        // Source repo
        let source = tmp.path().join("source");
        std::fs::create_dir_all(&source).unwrap();
        git(&["-C", &source.display().to_string(), "init"]);
        std::fs::write(source.join("README.md"), "hello\n").unwrap();
        git(&["-C", &source.display().to_string(), "add", "-A"]);
        git(&[
            "-C",
            &source.display().to_string(),
            "commit",
            "-m",
            "initial",
        ]);

        // Root repo with submodule
        let root = tmp.path().join("root");
        std::fs::create_dir_all(&root).unwrap();
        git(&["-C", &root.display().to_string(), "init"]);
        git(&[
            "-C",
            &root.display().to_string(),
            "commit",
            "--allow-empty",
            "-m",
            "init",
        ]);
        git(&[
            "-C",
            &root.display().to_string(),
            "-c",
            "protocol.file.allow=always",
            "submodule",
            "add",
            &source.display().to_string(),
            "sub",
        ]);
        git(&["-C", &root.display().to_string(), "commit", "-m", "add sub"]);
        Repo::new(&root).migrate_refs(ref_format);

        let submod_path = root.join("sub");
        (tmp, submod_path)
    }

    #[apply(formats)]
    fn read_submodule_head_on_branch(ref_format: RefFormat) {
        let (_tmp, submod_path) = init_repo_with_submodule(ref_format);
        let (oid, branch) = read_submodule_head(&submod_path);
        assert!(oid.is_some(), "should have an OID");
        assert_eq!(branch.as_deref(), Some("master"));
    }

    #[apply(formats)]
    fn read_submodule_head_detached(ref_format: RefFormat) {
        let (_tmp, submod_path) = init_repo_with_submodule(ref_format);
        // Detach HEAD
        git(&[
            "-C",
            &submod_path.display().to_string(),
            "checkout",
            "--detach",
        ]);
        let (oid, branch) = read_submodule_head(&submod_path);
        assert!(oid.is_some(), "should have an OID");
        assert!(branch.is_none(), "detached HEAD has no branch");
    }

    #[test]
    fn read_submodule_head_nonexistent() {
        let tmp = TempDir::new().unwrap();
        let (oid, branch) = read_submodule_head(tmp.path());
        assert!(oid.is_none());
        assert!(branch.is_none());
    }

    #[apply(formats)]
    fn read_submodule_head_unborn_branch(ref_format: RefFormat) {
        let tmp = TempDir::new().unwrap();
        git(&[
            "-C",
            &tmp.path().display().to_string(),
            "init",
            "-b",
            "master",
        ]);
        Repo::new(tmp.path()).migrate_refs(ref_format);
        assert_eq!(
            read_submodule_head(tmp.path()),
            (None, Some("master".to_owned()))
        );
    }

    #[apply(formats)]
    fn read_submodule_head_unsupported_extension(ref_format: RefFormat) {
        let (_tmp, submod_path) = init_repo_with_submodule(ref_format);
        assert_eq!(
            read_submodule_head(&submod_path).1.as_deref(),
            Some("master")
        );

        Repo::new(&submod_path).declare_unsupported_extension();
        assert_eq!(read_submodule_head(&submod_path), (None, None));
    }
}
