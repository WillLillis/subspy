//! Lightweight git helpers that bypass expensive libgit2 machinery.

use std::path::Path;

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

/// Parses `.gitmodules` to extract submodule name, path, and branch without
/// going through `repo.submodules()` (which triggers expensive per-submodule
/// config snapshot parsing in libgit2).
///
/// # Errors
///
/// Returns `git2::Error` if `.gitmodules` cannot be parsed.
///
/// # Panics
///
/// Panics if a `.gitmodules` entry contains non-UTF-8 keys or paths.
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
        let key = entry.name().expect("non-UTF-8 key in .gitmodules");
        // Guaranteed by the regex filter on entries()
        let name = key
            .strip_prefix("submodule.")
            .and_then(|s| s.strip_suffix(".path"))
            .unwrap();
        let path = entry
            .value()
            .expect("non-UTF-8 path in .gitmodules")
            .to_string();
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
}
