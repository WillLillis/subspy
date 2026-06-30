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
use rustc_hash::{FxHashMap, FxHashSet};

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

/// One side (old or new) of a rename: its path, file mode, and blob OID, plus
/// the worktree status to render when this side is emitted as a synthetic row.
///
/// `wt_y` / `wt_mode` are only meaningful for the added (new) side: a rename's
/// deleted source has no worktree presence, so it carries `.` / `0`.
#[derive(Clone)]
pub(super) struct RenameSide {
    pub path: Vec<u8>,
    /// Index mode (added side) or HEAD mode (deleted side).
    pub mode: u32,
    /// Index OID (added side) or HEAD OID (deleted side): used for rename
    /// scoring and as the rendered blob hash.
    pub oid: git2::Oid,
    /// Worktree status char (the porcelain v2 `y`): `.` unless the new file also
    /// changed in the worktree (e.g. `M` for a staged add edited again, `D` if
    /// it was then deleted from the worktree).
    pub wt_y: char,
    /// Workdir mode (`m_work`): equals `mode` for an unmodified or
    /// content-modified file, `0` when the workdir copy was deleted.
    pub wt_mode: u32,
}

/// A subspy-built rename `2`-line row, carrying the similarity `score` computed
/// once so renderers never recompute it. The rendered worktree status (`y`) and
/// workdir mode come from `new`, the rename destination.
pub(super) struct SyntheticRename {
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
///
/// Renames are reconciled from the raw add/delete set (libgit2's own rename
/// detection is off; see [`super::build_status_options`]), mirroring git's
/// phases:
///   1. collect raw changes (additions, deletions, everything else as entries);
///   2. pair exact (same-blob) renames with no limit, as git does;
///   3. only if the remaining inexact matrix fits under `diff.renameLimit`,
///      pair inexact renames by similarity.
///
/// What this cannot match: git breaks ties among equal-similarity candidates
/// using its internal `rename_src` array order through an unstable `qsort`. That
/// is undocumented, depends on unrelated diff entries, and is not portable
/// across git's platforms, so a handful of adversarial near-duplicate cases (all
/// pairings equally valid renames) may pick a different equal blob than git.
pub(super) fn normalized_tracked_rows<'a>(
    repo: &Repository,
    entries: &StatusEntries<'a>,
) -> Vec<TrackedRow<'a>> {
    let mut rows = Vec::new();
    let mut additions = Vec::new();
    let mut deletions = Vec::new();
    collect_initial_tracked_rows(entries, &mut rows, &mut additions, &mut deletions);

    // git's exact rename pass runs with no rename limit, so do it first and
    // unconditionally; it also shrinks the inexact matrix the limit applies to.
    pair_exact_renames(&mut rows, &mut additions, &mut deletions);

    // Similarity-pair the remaining candidates, unless git would skip inexact
    // detection for this status (matrix over `diff.renameLimit`).
    if !over_rename_limit(deletions.len(), additions.len(), rename_limit(repo)) {
        pair_inexact_renames(repo, &mut rows, &mut additions, &mut deletions);
    }
    for old in deletions {
        push_synthetic_delete(&mut rows, old);
    }
    for new in additions {
        push_synthetic_add(&mut rows, new);
    }

    rows
}

/// Whether `entry` is a tracked change the normalized stream renders as a
/// file row: not clean, not untracked, not ignored, not a case-collision
/// phantom delete. Conflicts pass this filter (they render as entry rows).
fn is_tracked_change(st: git2::Status, path: &[u8], phantom_deletes: &FxHashSet<Vec<u8>>) -> bool {
    st != git2::Status::CURRENT
        && st != git2::Status::WT_NEW
        && !st.contains(git2::Status::IGNORED)
        && (phantom_deletes.is_empty() || !phantom_deletes.contains(path))
}

/// git's `too_many_rename_candidates`: the inexact rename matrix is too big when
/// both dimensions exceed the limit, or their product exceeds its square.
const fn over_rename_limit(sources: usize, destinations: usize, limit: usize) -> bool {
    (destinations > limit && sources > limit)
        || destinations.saturating_mul(sources) > limit.saturating_pow(2)
}

fn collect_initial_tracked_rows<'a>(
    entries: &StatusEntries<'a>,
    rows: &mut Vec<TrackedRow<'a>>,
    additions: &mut Vec<RenameSide>,
    deletions: &mut Vec<RenameSide>,
) {
    for entry in entries.non_submod.iter().filter(|entry| {
        is_tracked_change(entry.status(), entry.path_bytes(), entries.phantom_deletes)
    }) {
        let st = entry.status();
        if st.contains(git2::Status::CONFLICTED) {
            rows.push(TrackedRow::Entry(entry));
        } else if st.contains(git2::Status::INDEX_NEW) {
            // `.contains`, not `==`: a staged add whose new file was also
            // changed in the worktree (`INDEX_NEW | WT_MODIFIED`, etc.) is still
            // a rename destination for git. `added_side` carries the worktree
            // state so it renders correctly whether or not it pairs.
            if let Some(side) = added_side(&entry) {
                additions.push(side);
            } else {
                rows.push(TrackedRow::Entry(entry));
            }
        } else if st == git2::Status::INDEX_DELETED {
            // A rename's source is always a clean index deletion (the old path
            // has no worktree presence), so an exact match suffices here; a
            // `git rm --cached` (`INDEX_DELETED | WT_NEW`) is not a rename source
            // and stays on the entry path.
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

/// git's exact rename pass (no rename limit): pair standalone deletions with
/// standalone additions carrying the identical blob. libgit2 omits these
/// whenever it is over its own rename limit, but git always finds them.
fn pair_exact_renames(
    rows: &mut Vec<TrackedRow<'_>>,
    additions: &mut Vec<RenameSide>,
    deletions: &mut Vec<RenameSide>,
) {
    if additions.is_empty() || deletions.is_empty() {
        return;
    }
    let mut adds_by_oid: FxHashMap<git2::Oid, Vec<usize>> = FxHashMap::default();
    for (add_idx, add) in additions.iter().enumerate() {
        adds_by_oid.entry(add.oid).or_default().push(add_idx);
    }
    let mut pairs = Vec::new();
    for (delete_idx, del) in deletions.iter().enumerate() {
        if let Some(add_indices) = adds_by_oid.get(&del.oid) {
            for &add_idx in add_indices {
                pairs.push((rename_score::Similarity::EXACT, delete_idx, add_idx));
            }
        }
    }
    assign_renames(rows, additions, deletions, pairs);
}

/// git's inexact rename pass: similarity-pair the remaining standalone
/// candidates. Each blob is hashed once (the signature cache), then an inverted
/// index over the additions' spans finds the pairs that share content, skipping
/// the zero-overlap majority of the matrix. Only called when the matrix fits
/// under the rename limit.
fn pair_inexact_renames(
    repo: &Repository,
    rows: &mut Vec<TrackedRow<'_>>,
    additions: &mut Vec<RenameSide>,
    deletions: &mut Vec<RenameSide>,
) {
    if additions.is_empty() || deletions.is_empty() {
        return;
    }

    let del_sigs: Vec<Option<rename_score::Signature>> = deletions
        .iter()
        .map(|old| blob_signature(repo, old.oid))
        .collect();
    let add_sigs: Vec<Option<rename_score::Signature>> = additions
        .iter()
        .map(|new| blob_signature(repo, new.oid))
        .collect();

    let pairs: Vec<(rename_score::Similarity, usize, usize)> =
        rename_score::overlapping_pairs(&del_sigs, &add_sigs)
            .into_iter()
            .filter(|(_, _, sim)| sim.percent() >= 50)
            .map(|(delete_idx, add_idx, sim)| (sim, delete_idx, add_idx))
            .collect();
    assign_renames(rows, additions, deletions, pairs);
}

/// Greedily turns rename `pairs` (`(score, delete_idx, add_idx)`) into
/// `SyntheticRename` rows, then drops the matched sides from the pools. Mirrors
/// git's matrix sort + greedy walk: a candidate wins by higher score, then by
/// matching basename (git's name-score tie-break), then by lowest source path,
/// then lowest destination path. This ordering also yields git's parallel-sorted
/// pairing for exact (same-blob) renames.
fn assign_renames(
    rows: &mut Vec<TrackedRow<'_>>,
    additions: &mut Vec<RenameSide>,
    deletions: &mut Vec<RenameSide>,
    mut pairs: Vec<(rename_score::Similarity, usize, usize)>,
) {
    pairs.sort_by(|&(sim_a, del_a, add_a), &(sim_b, del_b, add_b)| {
        let basename_a = basename(&deletions[del_a].path) == basename(&additions[add_a].path);
        let basename_b = basename(&deletions[del_b].path) == basename(&additions[add_b].path);
        sim_b
            .cmp(&sim_a)
            .then_with(|| basename_b.cmp(&basename_a))
            .then_with(|| deletions[del_a].path.cmp(&deletions[del_b].path))
            .then_with(|| additions[add_a].path.cmp(&additions[add_b].path))
    });

    let mut paired_add = vec![false; additions.len()];
    let mut paired_del = vec![false; deletions.len()];
    for (sim, delete_idx, add_idx) in pairs {
        if paired_del[delete_idx] || paired_add[add_idx] {
            continue;
        }
        paired_del[delete_idx] = true;
        paired_add[add_idx] = true;
        rows.push(TrackedRow::SyntheticRename(SyntheticRename {
            old: deletions[delete_idx].clone(),
            new: additions[add_idx].clone(),
            score: sim.percent(),
        }));
    }
    retain_unpaired(additions, &paired_add);
    retain_unpaired(deletions, &paired_del);
}

/// The final path component (after the last `/`), for git's basename rename
/// tie-break.
fn basename(path: &[u8]) -> &[u8] {
    path.iter()
        .rposition(|&b| b == b'/')
        .map_or(path, |slash| &path[slash + 1..])
}

/// Drops the entries of `sides` whose original index is marked `true` in
/// `paired` (matched by an exact or inexact pass).
fn retain_unpaired(sides: &mut Vec<RenameSide>, paired: &[bool]) {
    *sides = std::mem::take(sides)
        .into_iter()
        .enumerate()
        .filter(|(idx, _)| !paired[*idx])
        .map(|(_, side)| side)
        .collect();
}

fn rename_limit(repo: &Repository) -> usize {
    repo.config()
        .and_then(|c| c.get_i32("diff.renameLimit"))
        .ok()
        .and_then(|v| usize::try_from(v).ok())
        .filter(|&v| v > 0)
        .unwrap_or(DEFAULT_RENAME_LIMIT)
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
        y: new.wt_y,
        m_head: 0,
        m_idx: new.mode,
        m_work: new.wt_mode,
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
    let mode = u32::from(delta.new_file().mode());
    Some(RenameSide {
        path: delta.new_file().path_bytes()?.to_vec(),
        mode,
        oid: delta.new_file().id(),
        wt_y: worktree_y(entry.status()),
        wt_mode: workdir_mode(entry, mode),
    })
}

fn deleted_side(entry: &git2::StatusEntry<'_>) -> Option<RenameSide> {
    let delta = entry.head_to_index()?;
    Some(RenameSide {
        path: delta.old_file().path_bytes()?.to_vec(),
        mode: u32::from(delta.old_file().mode()),
        oid: delta.old_file().id(),
        // A deletion is the rename source: no worktree row of its own.
        wt_y: '.',
        wt_mode: 0,
    })
}

/// Workdir file mode (`m_work`) for an entry's index->workdir side: the new
/// file's mode, falling back to `index_mode` when the file is unchanged in the
/// worktree. `0` when the workdir copy was deleted (libgit2 reports a zero
/// mode), matching git.
fn workdir_mode(entry: &git2::StatusEntry<'_>, index_mode: u32) -> u32 {
    entry
        .index_to_workdir()
        .map_or(index_mode, |d| u32::from(d.new_file().mode()))
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
