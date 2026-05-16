//! Shared conflict-index parsing.
//!
//! Both the XY-line renderers (short, porcelain v1) and porcelain v2's
//! rich `u`-line derive conflict information from the index's
//! three-stage entries. This module owns the lookup so the formats
//! stay aligned.

use rustc_hash::FxHashMap;

use super::StatusResult;

pub(super) struct ConflictEntry {
    pub ancestor: Option<(u32, git2::Oid)>,
    pub ours: Option<(u32, git2::Oid)>,
    pub theirs: Option<(u32, git2::Oid)>,
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
