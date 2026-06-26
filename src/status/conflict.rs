//! Shared conflict-index parsing.
//!
//! Both the XY-line renderers (short, porcelain v1) and porcelain v2's
//! rich `u`-line derive conflict information from the index's
//! three-stage entries. This module owns the lookup so the formats
//! stay aligned.

use rustc_hash::{FxHashMap, FxHashSet};

use super::StatusResult;

pub(super) struct ConflictEntry {
    pub ancestor: Option<(u32, git2::Oid)>,
    pub ours: Option<(u32, git2::Oid)>,
    pub theirs: Option<(u32, git2::Oid)>,
}

/// The raw byte paths of every unresolved-conflict entry in the index (stages
/// 1-3). Such a path has no stage-0 entry but is *unmerged*, not deleted, and
/// git reports it only under "Unmerged paths". Callers use it to keep a
/// conflicted submodule from being mistaken for a staged deletion
/// (`submodule_changes`) or for an untracked directory (libgit2 reports a
/// conflicted submodule's working tree as `WT_NEW` because, lacking a stage-0
/// gitlink, it no longer recognizes the path as a submodule).
///
/// The conflict iterator already yields nothing on a clean index, so there is no
/// `has_conflicts()` guard -- that call is itself a full O(n) entry scan, so a
/// guard would only double-scan a conflicted index. Callers gate this instead.
pub(super) fn conflicted_paths(index: &git2::Index) -> StatusResult<FxHashSet<Vec<u8>>> {
    let mut paths = FxHashSet::default();
    for conflict in index.conflicts()? {
        let conflict = conflict?;
        // Every side of a given conflict shares the same path; take whichever is
        // present (a delete/modify conflict is missing one side).
        if let Some(entry) = conflict.our.or(conflict.their).or(conflict.ancestor) {
            paths.insert(entry.path);
        }
    }
    Ok(paths)
}

/// Whether `path` is at-or-under any of the `conflicted` paths. Used to drop the
/// untracked rows libgit2 emits for a conflicted submodule's working tree
/// (`sub/`, or `sub/...` under `-uall`) when `sub` is a conflicted gitlink path;
/// git shows it only under "Unmerged paths". Byte-exact, so non-UTF-8 paths match.
pub(super) fn path_within_any(path: &[u8], conflicted: &FxHashSet<Vec<u8>>) -> bool {
    conflicted.iter().any(|prefix| path_within(path, prefix))
}

/// Whether `path` is `prefix` itself or lies within the directory it names.
fn path_within(path: &[u8], prefix: &[u8]) -> bool {
    path == prefix || (path.starts_with(prefix) && path.get(prefix.len()) == Some(&b'/'))
}

pub(super) fn build_conflict_map(
    index: &git2::Index,
) -> StatusResult<FxHashMap<String, ConflictEntry>> {
    let mut map = FxHashMap::default();
    if !index.has_conflicts() {
        return Ok(map);
    }
    for conflict in index.conflicts()? {
        let c = conflict?;
        let path = c
            .our
            .as_ref()
            .or(c.their.as_ref())
            .or(c.ancestor.as_ref())
            .and_then(|e| std::str::from_utf8(&e.path).ok())
            .map(str::to_string);
        let Some(path) = path else { continue };
        map.insert(
            path,
            ConflictEntry {
                ancestor: c.ancestor.map(|e| (e.mode, e.id)),
                ours: c.our.map(|e| (e.mode, e.id)),
                theirs: c.their.map(|e| (e.mode, e.id)),
            },
        );
    }
    Ok(map)
}
