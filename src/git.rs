use std::path::Path;

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
        let branch_key = format!("submodule.{name}.branch");
        let branch = config.get_string(&branch_key).ok();
        entries.push((name.to_string(), path, branch));
    }
    Ok(entries)
}
