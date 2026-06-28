//! Shared tracked-row model and rename reconciliation.
//!
//! libgit2's rename detection diverges from git near the 50% similarity
//! threshold: it keeps renames git would split into add+delete, and misses
//! pairs git would join. [`normalized_tracked_rows`] reconciles a repo's
//! tracked changes into one path-sorted stream of [`TrackedRow`]s that every
//! output format (porcelain v1/v2, short, long) renders, so they all match git.
//!
//! The add/delete pairing is bounded by `diff.renameLimit` and signature-cached
//! (each blob hashed once, with a size short-circuit) via [`super::rename_score`].

use git2::Repository;

use std::cmp::Reverse;

use super::{StatusEntries, interleave::SubRow, rename_score};

/// git's default when `diff.renameLimit` is unset or non-positive.
const DEFAULT_RENAME_LIMIT: usize = 1000;

/// One tracked (non-submodule) change, after rename reconciliation: either a
/// raw libgit2 entry, or a synthetic row subspy built to match git's
/// classification (a split add/delete, or a paired rename).
pub(super) enum TrackedRow<'a> {
    Entry(git2::StatusEntry<'a>),
    SyntheticOrdinary(SyntheticOrdinary),
    SyntheticRename(SyntheticRename),
}

impl TrackedRow<'_> {
    fn key(&self) -> &[u8] {
        match self {
            Self::Entry(entry) => entry_sort_key(entry),
            Self::SyntheticOrdinary(row) => &row.path,
            Self::SyntheticRename(row) => &row.new.path,
        }
    }
}

/// A subspy-built ordinary `1`-line row (a below-threshold rename split into its
/// halves, or an add/delete that did not pair). `x`/`y` use porcelain v2's `.`
/// for the unmodified slot; v1/short map that to a blank.
pub(super) struct SyntheticOrdinary {
    pub x: char,
    pub y: char,
    pub m_head: u32,
    pub m_idx: u32,
    pub m_work: u32,
    pub h_head: git2::Oid,
    pub h_idx: git2::Oid,
    pub path: Vec<u8>,
}

/// One side (old or new) of a rename: its path, file mode, and blob OID.
#[derive(Clone)]
pub(super) struct RenameSide {
    pub path: Vec<u8>,
    pub mode: u32,
    pub oid: git2::Oid,
}

/// A subspy-built rename `2`-line row, carrying the similarity `score` computed
/// once so renderers never recompute it.
pub(super) struct SyntheticRename {
    pub y: char,
    pub old: RenameSide,
    pub new: RenameSide,
    pub score: u8,
}

/// Either a tracked file row or an interleaved submodule row.
pub(super) enum TrackedOrSubRow<'a> {
    File(TrackedRow<'a>),
    Sub(SubRow<'a>),
}

const fn sub_row_key<'a>(row: &'a SubRow<'_>) -> &'a [u8] {
    match row {
        SubRow::Modified(path, _) | SubRow::Deleted(path) => path.as_bytes(),
        SubRow::Renamed(rename) => rename.new.as_bytes(),
    }
}

/// Merges the tracked file rows with the submodule rows in path order, calling
/// `on_row` for each. Both streams are sorted here.
pub(super) fn for_each_tracked_row<'a, E>(
    mut files: Vec<TrackedRow<'a>>,
    mut submods: Vec<SubRow<'a>>,
    mut on_row: impl FnMut(TrackedOrSubRow<'a>) -> Result<(), E>,
) -> Result<(), E> {
    files.sort_by(|x, y| x.key().cmp(y.key()));
    submods.sort_by(|x, y| sub_row_key(x).cmp(sub_row_key(y)));

    let mut files = files.into_iter();
    let mut submods = submods.into_iter();
    let mut pending_file = files.next();
    let mut pending_sub = submods.next();
    loop {
        match (pending_file.take(), pending_sub.take()) {
            (Some(file), Some(sub)) => {
                if sub_row_key(&sub) < file.key() {
                    on_row(TrackedOrSubRow::Sub(sub))?;
                    pending_file = Some(file);
                    pending_sub = submods.next();
                } else {
                    on_row(TrackedOrSubRow::File(file))?;
                    pending_sub = Some(sub);
                    pending_file = files.next();
                }
            }
            (Some(file), None) => {
                on_row(TrackedOrSubRow::File(file))?;
                pending_file = files.next();
            }
            (None, Some(sub)) => {
                on_row(TrackedOrSubRow::Sub(sub))?;
                pending_sub = submods.next();
            }
            (None, None) => break,
        }
    }
    Ok(())
}

/// Reconciles `entries`' tracked changes into a stream of [`TrackedRow`]s whose
/// rename classification matches git.
pub(super) fn normalized_tracked_rows<'a>(
    repo: &Repository,
    entries: &StatusEntries<'a>,
) -> Vec<TrackedRow<'a>> {
    let mut rows = Vec::new();
    let mut additions = Vec::new();
    let mut deletions = Vec::new();
    collect_initial_tracked_rows(repo, entries, &mut rows, &mut additions, &mut deletions);
    pair_unmatched_adds_and_deletes(repo, &mut rows, additions, deletions);
    rows
}

fn collect_initial_tracked_rows<'a>(
    repo: &Repository,
    entries: &StatusEntries<'a>,
    rows: &mut Vec<TrackedRow<'a>>,
    additions: &mut Vec<RenameSide>,
    deletions: &mut Vec<RenameSide>,
) {
    for entry in entries.non_submod.iter().filter(|entry| {
        let st = entry.status();
        st != git2::Status::CURRENT
            && st != git2::Status::WT_NEW
            && !st.contains(git2::Status::IGNORED)
            && (entries.phantom_deletes.is_empty()
                || !entries.phantom_deletes.contains(entry.path_bytes()))
    }) {
        let st = entry.status();
        if st.contains(git2::Status::CONFLICTED) {
            rows.push(TrackedRow::Entry(entry));
        } else if st.intersects(git2::Status::INDEX_RENAMED | git2::Status::WT_RENAMED) {
            let EntryModesAndOids {
                m_head,
                m_idx,
                m_work,
                h_head,
                h_idx,
            } = extract_modes_and_oids(&entry);
            let score = rename_similarity(repo, h_head, h_idx);
            match rename_sides(&entry) {
                // Kept rename: carry the score we already computed so the v2
                // writer doesn't recompute it. Renders the same `2` line a
                // libgit2 rename entry would.
                Some((old, new)) if score >= 50 => {
                    rows.push(TrackedRow::SyntheticRename(SyntheticRename {
                        y: worktree_y(st),
                        old,
                        new,
                        score,
                    }));
                }
                // Below git's 50% threshold: split into add + delete. The
                // deleted (old) path has no worktree presence, so its `y` is
                // always `.`; the added (new) path keeps the entry's worktree
                // status (e.g. a rename whose new file was further modified in
                // the worktree renders `AM`, matching git).
                Some((old, new)) => {
                    rows.push(TrackedRow::SyntheticOrdinary(SyntheticOrdinary {
                        x: 'D',
                        y: '.',
                        m_head,
                        m_idx: 0,
                        m_work: 0,
                        h_head,
                        h_idx: git2::Oid::ZERO_SHA1,
                        path: old.path,
                    }));
                    rows.push(TrackedRow::SyntheticOrdinary(SyntheticOrdinary {
                        x: 'A',
                        y: worktree_y(st),
                        m_head: 0,
                        m_idx,
                        m_work,
                        h_head: git2::Oid::ZERO_SHA1,
                        h_idx,
                        path: new.path,
                    }));
                }
                // No delta paths (rare): fall back to the entry-based writer.
                None => rows.push(TrackedRow::Entry(entry)),
            }
        } else if st == git2::Status::INDEX_NEW {
            if let Some(side) = added_side(&entry) {
                additions.push(side);
            } else {
                rows.push(TrackedRow::Entry(entry));
            }
        } else if st == git2::Status::INDEX_DELETED {
            if let Some(side) = deleted_side(&entry) {
                deletions.push(side);
            } else {
                rows.push(TrackedRow::Entry(entry));
            }
        } else {
            rows.push(TrackedRow::Entry(entry));
        }
    }
}

fn pair_unmatched_adds_and_deletes(
    repo: &Repository,
    rows: &mut Vec<TrackedRow<'_>>,
    additions: Vec<RenameSide>,
    deletions: Vec<RenameSide>,
) {
    // Nothing to pair, or too many candidates: git skips inexact rename
    // detection once `adds * deletes` exceeds `diff.renameLimit` squared and
    // reports plain add/delete. Match that instead of doing the cross-product.
    if additions.is_empty()
        || deletions.is_empty()
        || additions.len().saturating_mul(deletions.len()) > rename_limit(repo).saturating_pow(2)
    {
        for old in deletions {
            push_synthetic_delete(rows, old);
        }
        for new in additions {
            push_synthetic_add(rows, new);
        }
        return;
    }

    // Hash each candidate blob once (git's signature cache), then compare from
    // the cache with a size short-circuit, so the cross-product stays cheap.
    let del_sigs: Vec<Option<rename_score::Signature>> = deletions
        .iter()
        .map(|old| blob_signature(repo, old.oid))
        .collect();
    let add_sigs: Vec<Option<rename_score::Signature>> = additions
        .iter()
        .map(|new| blob_signature(repo, new.oid))
        .collect();

    let mut pairs = Vec::new();
    for (delete_idx, del_sig) in del_sigs.iter().enumerate() {
        let Some(del_sig) = del_sig else { continue };
        for (add_idx, add_sig) in add_sigs.iter().enumerate() {
            let Some(add_sig) = add_sig else { continue };
            if !size_allows_rename(del_sig.size(), add_sig.size()) {
                continue;
            }
            let score = rename_score::score_sigs(del_sig, add_sig);
            if score >= 50 {
                pairs.push((score, delete_idx, add_idx));
            }
        }
    }

    let mut used_additions = vec![false; additions.len()];
    let mut used_deletions = vec![false; deletions.len()];
    pairs.sort_by_key(|pair| Reverse(pair.0));
    for (score, delete_idx, add_idx) in pairs {
        if used_deletions[delete_idx] || used_additions[add_idx] {
            continue;
        }
        used_deletions[delete_idx] = true;
        used_additions[add_idx] = true;
        rows.push(TrackedRow::SyntheticRename(SyntheticRename {
            y: '.',
            old: deletions[delete_idx].clone(),
            new: additions[add_idx].clone(),
            score,
        }));
    }

    for (idx, old) in deletions.into_iter().enumerate() {
        if !used_deletions[idx] {
            push_synthetic_delete(rows, old);
        }
    }
    for (idx, new) in additions.into_iter().enumerate() {
        if !used_additions[idx] {
            push_synthetic_add(rows, new);
        }
    }
}

fn rename_limit(repo: &Repository) -> usize {
    repo.config()
        .and_then(|c| c.get_i32("diff.renameLimit"))
        .ok()
        .and_then(|v| usize::try_from(v).ok())
        .filter(|&v| v > 0)
        .unwrap_or(DEFAULT_RENAME_LIMIT)
}

/// git's `estimate_similarity` size gate: a pair cannot reach the 50% rename
/// threshold once the size delta exceeds half the larger blob, so skip such a
/// pair before reading or hashing any content.
fn size_allows_rename(a: usize, b: usize) -> bool {
    let max = a.max(b) as u64;
    let delta = a.abs_diff(b) as u64;
    // max * (100 - threshold) >= delta * 100, with threshold = 50.
    max * 50 >= delta * 100
}

fn blob_signature(repo: &Repository, oid: git2::Oid) -> Option<rename_score::Signature> {
    let blob = repo.find_blob(oid).ok()?;
    Some(rename_score::Signature::new(blob.content()))
}

fn push_synthetic_delete(rows: &mut Vec<TrackedRow<'_>>, old: RenameSide) {
    rows.push(TrackedRow::SyntheticOrdinary(SyntheticOrdinary {
        x: 'D',
        y: '.',
        m_head: old.mode,
        m_idx: 0,
        m_work: 0,
        h_head: old.oid,
        h_idx: git2::Oid::ZERO_SHA1,
        path: old.path,
    }));
}

fn push_synthetic_add(rows: &mut Vec<TrackedRow<'_>>, new: RenameSide) {
    rows.push(TrackedRow::SyntheticOrdinary(SyntheticOrdinary {
        x: 'A',
        y: '.',
        m_head: 0,
        m_idx: new.mode,
        m_work: new.mode,
        h_head: git2::Oid::ZERO_SHA1,
        h_idx: new.oid,
        path: new.path,
    }));
}

fn entry_sort_key<'e>(entry: &'e git2::StatusEntry<'_>) -> &'e [u8] {
    entry
        .head_to_index()
        .or_else(|| entry.index_to_workdir())
        .and_then(|delta| delta.new_file().path_bytes())
        .unwrap_or_else(|| entry.path_bytes())
}

fn added_side(entry: &git2::StatusEntry<'_>) -> Option<RenameSide> {
    let delta = entry.head_to_index()?;
    Some(RenameSide {
        path: delta.new_file().path_bytes()?.to_vec(),
        mode: u32::from(delta.new_file().mode()),
        oid: delta.new_file().id(),
    })
}

fn deleted_side(entry: &git2::StatusEntry<'_>) -> Option<RenameSide> {
    let delta = entry.head_to_index()?;
    Some(RenameSide {
        path: delta.old_file().path_bytes()?.to_vec(),
        mode: u32::from(delta.old_file().mode()),
        oid: delta.old_file().id(),
    })
}

fn rename_sides(entry: &git2::StatusEntry<'_>) -> Option<(RenameSide, RenameSide)> {
    let delta = entry.head_to_index().or_else(|| entry.index_to_workdir())?;
    Some((
        RenameSide {
            path: delta.old_file().path_bytes()?.to_vec(),
            mode: u32::from(delta.old_file().mode()),
            oid: delta.old_file().id(),
        },
        RenameSide {
            path: delta.new_file().path_bytes()?.to_vec(),
            mode: u32::from(delta.new_file().mode()),
            oid: delta.new_file().id(),
        },
    ))
}

/// File modes and blob OIDs for the HEAD/index/workdir versions of a
/// non-submodule entry, suitable for the porcelain v2 `1`/`2` lines.
pub(super) struct EntryModesAndOids {
    pub m_head: u32,
    pub m_idx: u32,
    pub m_work: u32,
    pub h_head: git2::Oid,
    pub h_idx: git2::Oid,
}

/// Resolves the modes and OIDs for a `1`/`2` line. For workdir-only changes,
/// HEAD falls back to index (they're identical when the file isn't staged).
pub(super) fn extract_modes_and_oids(entry: &git2::StatusEntry<'_>) -> EntryModesAndOids {
    let m_idx = entry
        .head_to_index()
        .map(|d| u32::from(d.new_file().mode()))
        .or_else(|| {
            entry
                .index_to_workdir()
                .map(|d| u32::from(d.old_file().mode()))
        })
        .unwrap_or(0);
    let m_head = entry
        .head_to_index()
        .map_or(m_idx, |d| u32::from(d.old_file().mode()));
    let m_work = entry
        .index_to_workdir()
        .map_or(m_idx, |d| u32::from(d.new_file().mode()));
    let h_idx = entry
        .head_to_index()
        .map(|d| d.new_file().id())
        .or_else(|| entry.index_to_workdir().map(|d| d.old_file().id()))
        .unwrap_or(git2::Oid::ZERO_SHA1);
    let h_head = entry.head_to_index().map_or(h_idx, |d| d.old_file().id());
    EntryModesAndOids {
        m_head,
        m_idx,
        m_work,
        h_head,
        h_idx,
    }
}

/// Similarity score (0-100) between two blob OIDs, for a single rename pair (no
/// signature reuse). Equal OIDs short-circuit to 100; an unreadable blob falls
/// back to 100 (treat as a pure rename rather than fabricate a split).
pub(super) fn rename_similarity(repo: &Repository, old_oid: git2::Oid, new_oid: git2::Oid) -> u8 {
    if old_oid == new_oid {
        return 100;
    }

    let Ok(old_blob) = repo.find_blob(old_oid) else {
        return 100;
    };
    let Ok(new_blob) = repo.find_blob(new_oid) else {
        return 100;
    };

    rename_score::score(old_blob.content(), new_blob.content())
}

/// Porcelain v2 worktree status char (the `y` of a `1`/`2` line) for a kept
/// rename: `.` unless the renamed file also has worktree changes.
const fn worktree_y(st: git2::Status) -> char {
    if st.contains(git2::Status::WT_RENAMED) {
        'R'
    } else if st.contains(git2::Status::WT_MODIFIED) {
        'M'
    } else if st.contains(git2::Status::WT_DELETED) {
        'D'
    } else if st.contains(git2::Status::WT_TYPECHANGE) {
        'T'
    } else {
        '.'
    }
}
