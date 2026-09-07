//! Directory rows libgit2 reports that git never emits.
//!
//! git has no concept of a tracked directory, so it resolves a candidate
//! untracked directory two ways libgit2 does not. `index_name_is_other` strips
//! the trailing slash and looks the name up in the index, which suppresses the
//! row when a tracked file was replaced by a directory of the same name. And an
//! empty directory holds nothing git could report, so it produces no row at
//! all, ignored or otherwise.

use git2::Repository;
use rustc_hash::FxHashSet;

/// Paths of reported directory entries git renders nothing for.
///
/// Only entries whose path ends in `/` are considered, so a repository with no
/// directory rows pays one pass over the reported statuses and nothing else.
pub fn phantom_directories(
    repo: &Repository,
    non_submod: &git2::Statuses<'_>,
) -> FxHashSet<Vec<u8>> {
    let mut phantom = FxHashSet::default();
    let index = repo.index().ok();
    for entry in non_submod.iter() {
        let path = entry.path_bytes();
        let Some(name) = path.strip_suffix(b"/") else {
            continue;
        };
        let shadows_index_entry = index
            .as_ref()
            .is_some_and(|index| index.get_path(bytes_to_path(name), 0).is_some());
        if shadows_index_entry || is_empty_dir(repo, path) {
            phantom.insert(path.to_vec());
        }
    }
    phantom
}

/// Whether the worktree directory at `path` holds no entries.
fn is_empty_dir(repo: &Repository, path: &[u8]) -> bool {
    let Some(workdir) = repo.workdir() else {
        return false;
    };
    let Ok(mut dir) = std::fs::read_dir(workdir.join(bytes_to_path(path))) else {
        return false;
    };
    dir.next().is_none()
}

#[cfg(unix)]
fn bytes_to_path(bytes: &[u8]) -> &std::path::Path {
    use std::os::unix::ffi::OsStrExt as _;
    std::path::Path::new(std::ffi::OsStr::from_bytes(bytes))
}

#[cfg(windows)]
fn bytes_to_path(bytes: &[u8]) -> &std::path::Path {
    // Index paths are UTF-8 on Windows, so a lossy conversion cannot lose
    // anything a lookup would have matched.
    std::path::Path::new(std::str::from_utf8(bytes).unwrap_or(""))
}
