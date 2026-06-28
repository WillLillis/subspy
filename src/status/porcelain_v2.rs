//! Porcelain v2 output format (rich `1`/`2`/`u`/`?`/`!` lines).
//!
//! Per `git-status(1)`, ordinary entries get a `1 XY <sub> <modes> <oids> PATH`
//! line, renames get a `2 ...` line, conflicts get a `u XY ...` line, and
//! untracked/ignored use the same `?`/`!` markers as v1. The `--branch` flag
//! prepends `# branch.oid`/`# branch.head`/`# branch.upstream`/`# branch.ab`
//! header lines.

use git2::Repository;
use rustc_hash::FxHashMap;

use std::{
    borrow::Cow,
    cmp::Reverse,
    io::{self, Write},
    path::Path,
};

use crate::StatusSummary;

use super::{
    Divergence, PorcelainOpts, StatusEntries, StatusResult, UpstreamStatus,
    conflict::{ConflictEntry, build_conflict_map, path_within_any},
    interleave::SubRow,
    line_terminator,
    quote::QuoteMode,
    relativize::Relativizer,
    rename_score, unborn_branch_name, upstream_status,
};

/// Per-call rendering constants shared by every `write_*` helper:
/// where to slot paths relative to (`rel`), whether the line
/// terminator is NUL (`null_terminate`), and the quoting policy
/// (`quote_mode`).
struct RenderOpts<'a> {
    rel: &'a Relativizer<'a>,
    null_terminate: bool,
    quote_mode: QuoteMode,
}

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

#[derive(Clone)]
pub(super) struct RenameSide {
    pub path: Vec<u8>,
    pub mode: u32,
    pub oid: git2::Oid,
}

pub(super) struct SyntheticRename {
    pub y: char,
    pub old: RenameSide,
    pub new: RenameSide,
    pub score: u8,
}

/// Renders the full porcelain v2 output to `out`: optional `# branch.*`
/// header lines followed by one `1`/`2`/`u`/`?`/`!` line per entry,
/// terminated by LF or NUL per `opts.null_terminate`. `rel` is the
/// cwd-aware relativizer; under `-z` it falls back to repo-root paths
/// internally.
///
/// Quoting policy: porcelain v2 doesn't treat a plain space as
/// "unusual" (no `QUOTE_PATH_QUOTE_SP`). High bytes are quoted unless
/// the caller passed `-c core.quotepath=false` via `opts.quote_path`.
#[expect(
    clippy::too_many_lines,
    reason = "branch headers plus the interleaved tracked pass and untracked/ignored passes"
)]
pub fn display_porcelain_v2(
    out: &mut impl Write,
    repo: &Repository,
    entries: &StatusEntries<'_>,
    rel: &Relativizer<'_>,
    opts: PorcelainOpts,
) -> StatusResult<()> {
    let PorcelainOpts {
        null_terminate,
        branch,
        ahead_behind,
        quote_path,
        show_stash,
    } = opts;
    let render_opts = RenderOpts {
        rel,
        null_terminate,
        quote_mode: QuoteMode {
            quote_path,
            ..QuoteMode::STANDARD
        },
    };

    if branch {
        write_branch_headers(repo, out, ahead_behind)?;
        if show_stash {
            // Stashes are tracked via the `refs/stash` reflog: count
            // entries to get the stash count. Missing reflog (no stashes
            // ever made) means 0.
            let count = repo.reflog("refs/stash").map_or(0, |r| r.len());
            writeln!(out, "# stash {count}")?;
        }
    }

    let index = repo.index()?;
    let conflicts = build_conflict_map(&index)?;
    let head_tree = repo.head().ok().and_then(|h| h.peel_to_tree().ok());

    // git emits tracked changes (ordinary/renamed/conflicted, including
    // submodules) in one path-sorted stream, then untracked, then ignored.
    // libgit2 excludes submodules from `non_submod`, so interleave the
    // submodule rows among the tracked file rows by path.
    let tracked = normalized_tracked_rows(repo, entries);
    let mut submods: Vec<SubRow<'_>> = Vec::new();
    submods.extend(
        entries
            .submodules
            .iter()
            .map(|(path, st)| SubRow::Modified(path, *st)),
    );
    submods.extend(
        entries
            .deleted_submodules
            .iter()
            .map(|path| SubRow::Deleted(path)),
    );
    submods.extend(entries.renamed_submodules.iter().map(SubRow::Renamed));

    // Gitlink OIDs come from HEAD's tree and the index, keyed by submodule path.
    let head_oid = |path: &str| {
        head_tree
            .as_ref()
            .and_then(|t| t.get_path(Path::new(path)).ok())
            .map_or(git2::Oid::ZERO_SHA1, |e| e.id())
    };
    let index_oid = |path: &str| {
        index
            .get_path(Path::new(path), 0)
            .map_or(git2::Oid::ZERO_SHA1, |e| e.id)
    };

    for_each_tracked_row(tracked, submods, |row| match row {
        TrackedOrSubRow::File(row) => match row {
            TrackedRow::Entry(entry) => {
                let st = entry.status();
                if st.contains(git2::Status::CONFLICTED) {
                    write_conflict(
                        &entry,
                        &conflicts,
                        entries.conflicted_submodules,
                        out,
                        &render_opts,
                    )
                } else if st.intersects(git2::Status::INDEX_RENAMED | git2::Status::WT_RENAMED) {
                    write_renamed(repo, &entry, out, &render_opts)
                } else {
                    write_ordinary(&entry, out, &render_opts)
                }
            }
            TrackedRow::SyntheticOrdinary(row) => write_synthetic_ordinary(&row, out, &render_opts),
            TrackedRow::SyntheticRename(row) => write_synthetic_rename(&row, out, &render_opts),
        },
        TrackedOrSubRow::Sub(SubRow::Modified(path, st)) => {
            write_submodule(path, st, head_oid(path), index_oid(path), out, &render_opts)
        }
        TrackedOrSubRow::Sub(SubRow::Deleted(path)) => {
            write_deleted_submodule(path, head_oid(path), out, &render_opts)
        }
        TrackedOrSubRow::Sub(SubRow::Renamed(rename)) => write_renamed_submodule(
            rename,
            head_oid(&rename.old),
            index_oid(&rename.new),
            out,
            &render_opts,
        ),
    })?;

    for entry in entries
        .non_submod
        .iter()
        .filter(|e| e.status() == git2::Status::WT_NEW)
    {
        // Drop the phantom untracked row libgit2 emits for a conflicted
        // submodule's working tree; git lists it only as an unmerged (`u`) entry.
        if path_within_any(entry.path_bytes(), entries.conflicted_paths) {
            continue;
        }
        out.write_all(b"? ")?;
        render_opts.rel.write_quoted(
            out,
            entry.path_bytes(),
            render_opts.null_terminate,
            render_opts.quote_mode,
        )?;
        out.write_all(line_terminator(render_opts.null_terminate).as_bytes())?;
    }

    for entry in entries
        .non_submod
        .iter()
        .filter(|e| e.status().contains(git2::Status::IGNORED))
    {
        out.write_all(b"! ")?;
        render_opts.rel.write_quoted(
            out,
            entry.path_bytes(),
            render_opts.null_terminate,
            render_opts.quote_mode,
        )?;
        out.write_all(line_terminator(render_opts.null_terminate).as_bytes())?;
    }

    Ok(())
}

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
            if score >= 50 {
                rows.push(TrackedRow::Entry(entry));
            } else if let Some((old, new)) = rename_sides(&entry) {
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
                    y: '.',
                    m_head: 0,
                    m_idx,
                    m_work,
                    h_head: git2::Oid::ZERO_SHA1,
                    h_idx,
                    path: new.path,
                }));
            } else {
                rows.push(TrackedRow::Entry(entry));
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

/// git's default when `diff.renameLimit` is unset or non-positive.
const DEFAULT_RENAME_LIMIT: usize = 1000;

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

/// Writes the `# branch.*` header lines for porcelain v2 output.
///
/// With `ahead_behind = false` and a diverged upstream, emits
/// `# branch.ab +? -?` rather than computing exact counts. When the
/// OIDs are equal we emit `+0 -0` without the graph walk.
fn write_branch_headers(
    repo: &Repository,
    out: &mut impl Write,
    ahead_behind: bool,
) -> StatusResult<()> {
    let Ok(head) = repo.head() else {
        // Unborn HEAD (empty repo, no commits yet).
        let head_ref = repo.find_reference("HEAD").ok();
        let branch = head_ref
            .as_ref()
            .and_then(unborn_branch_name)
            .unwrap_or("(unknown)");
        writeln!(out, "# branch.oid (initial)")?;
        writeln!(out, "# branch.head {branch}")?;
        return Ok(());
    };

    let oid = head
        .peel_to_commit()
        .ok()
        .map_or(git2::Oid::ZERO_SHA1, |c| c.id());
    writeln!(out, "# branch.oid {oid}")?;

    // Display via lossy bytes so a non-UTF-8 ref still renders something
    // sensible. `find_branch` below needs the strict `&str` form (git2
    // config keys are ASCII-only), so resolve that separately.
    let branch_display = if head.is_branch() {
        String::from_utf8_lossy(head.shorthand_bytes())
    } else {
        Cow::Borrowed("(detached)")
    };
    writeln!(out, "# branch.head {branch_display}")?;

    match upstream_status(repo, &head, ahead_behind)? {
        UpstreamStatus::None => {}
        UpstreamStatus::Gone { name } => writeln!(out, "# branch.upstream {name}")?,
        UpstreamStatus::Tracking { name, divergence } => {
            writeln!(out, "# branch.upstream {name}")?;
            match divergence {
                Divergence::Counts(ahead, behind) => {
                    writeln!(out, "# branch.ab +{ahead} -{behind}")?;
                }
                Divergence::Skipped => writeln!(out, "# branch.ab +? -?")?,
            }
        }
    }

    Ok(())
}

/// Maps a `git2::Status` to the XY index/worktree characters used in porcelain v2.
///
/// `RENAMED` is checked before `MODIFIED`: git2 sets both on a rename that also
/// changes content, and git's `2` line reports `R` (not `M`) in that column.
const fn regular_xy(st: git2::Status) -> (char, char) {
    let x = if st.contains(git2::Status::INDEX_NEW) {
        'A'
    } else if st.contains(git2::Status::INDEX_RENAMED) {
        'R'
    } else if st.contains(git2::Status::INDEX_MODIFIED) {
        'M'
    } else if st.contains(git2::Status::INDEX_DELETED) {
        'D'
    } else if st.contains(git2::Status::INDEX_TYPECHANGE) {
        'T'
    } else {
        '.'
    };
    let y = if st.contains(git2::Status::WT_RENAMED) {
        'R'
    } else if st.contains(git2::Status::WT_MODIFIED) {
        'M'
    } else if st.contains(git2::Status::WT_DELETED) {
        'D'
    } else if st.contains(git2::Status::WT_TYPECHANGE) {
        'T'
    } else {
        '.'
    };
    (x, y)
}

/// Maps a `StatusSummary` to the XY characters for a submodule porcelain v2 entry.
fn submodule_xy(st: StatusSummary) -> (char, char) {
    let x = if st.contains(StatusSummary::STAGED_NEW) {
        'A'
    } else if st.contains(StatusSummary::STAGED) {
        'M'
    } else {
        '.'
    };
    let y = if st.contains(StatusSummary::DELETED_WORKDIR) {
        'D'
    } else if st.intersects(
        StatusSummary::NEW_COMMITS
            | StatusSummary::MODIFIED_CONTENT
            | StatusSummary::UNTRACKED_CONTENT,
    ) {
        'M'
    } else {
        '.'
    };
    (x, y)
}

/// The `c`/`m`/`u` characters of a submodule's porcelain v2 `S<C><M><U>`
/// sub-field: commit changed, content modified, untracked content present.
const fn submodule_cmu(st: StatusSummary) -> (char, char, char) {
    let c = if st.contains(StatusSummary::NEW_COMMITS) {
        'C'
    } else {
        '.'
    };
    let m = if st.contains(StatusSummary::MODIFIED_CONTENT) {
        'M'
    } else {
        '.'
    };
    let u = if st.contains(StatusSummary::UNTRACKED_CONTENT) {
        'U'
    } else {
        '.'
    };
    (c, m, u)
}

/// File modes and blob OIDs for the HEAD/index/workdir versions of a
/// non-submodule entry, suitable for the porcelain v2 `1`/`2` lines.
struct EntryModesAndOids {
    m_head: u32,
    m_idx: u32,
    m_work: u32,
    h_head: git2::Oid,
    h_idx: git2::Oid,
}

/// Resolves the modes and OIDs for a `1`/`2` line. For workdir-only
/// changes, HEAD falls back to index (they're identical when the file
/// isn't staged).
fn extract_modes_and_oids(entry: &git2::StatusEntry<'_>) -> EntryModesAndOids {
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

/// Writes a non-rename, non-conflict tracked entry as a porcelain v2
/// `1` line: `1 XY <sub> <m_head> <m_idx> <m_work> <h_head> <h_idx> PATH`.
/// `sub` is always `N...` here (non-submodule); modes and OIDs come
/// from [`extract_modes_and_oids`].
fn write_ordinary(
    entry: &git2::StatusEntry<'_>,
    out: &mut impl Write,
    render_opts: &RenderOpts<'_>,
) -> Result<(), io::Error> {
    let (x, y) = regular_xy(entry.status());
    let EntryModesAndOids {
        m_head,
        m_idx,
        m_work,
        h_head,
        h_idx,
    } = extract_modes_and_oids(entry);
    write!(
        out,
        "1 {x}{y} N... {m_head:06o} {m_idx:06o} {m_work:06o} {h_head} {h_idx} ",
    )?;
    render_opts.rel.write_quoted(
        out,
        entry.path_bytes(),
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(line_terminator(render_opts.null_terminate).as_bytes())
}

fn write_synthetic_ordinary(
    row: &SyntheticOrdinary,
    out: &mut impl Write,
    render_opts: &RenderOpts<'_>,
) -> Result<(), io::Error> {
    let SyntheticOrdinary {
        x,
        y,
        m_head,
        m_idx,
        m_work,
        h_head,
        h_idx,
        path,
    } = row;
    write!(
        out,
        "1 {x}{y} N... {m_head:06o} {m_idx:06o} {m_work:06o} {h_head} {h_idx} ",
    )?;
    render_opts.rel.write_quoted(
        out,
        path,
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(line_terminator(render_opts.null_terminate).as_bytes())
}

/// Writes a rename entry as a porcelain v2 `2` line:
/// `2 XY <sub> <modes> <oids> R<score> NEW<sep>OLD`. The separator
/// between paths is TAB (`\t`) without `-z` and NUL (`\0`) with `-z`,
/// per `git-status(1)`. The similarity is computed locally with the
/// clean-room scorer in [`rename_score`].
fn write_renamed(
    repo: &Repository,
    entry: &git2::StatusEntry<'_>,
    out: &mut impl Write,
    render_opts: &RenderOpts<'_>,
) -> Result<(), io::Error> {
    let st = entry.status();
    let (x, y) = regular_xy(st);
    // For renames, both paths come from the diff delta - `entry.path()` is
    // the entry's key, which is just the old path again.
    let delta = if st.contains(git2::Status::INDEX_RENAMED) {
        entry.head_to_index()
    } else {
        entry.index_to_workdir()
    };
    let old_path = delta
        .as_ref()
        .and_then(|d| d.old_file().path_bytes())
        .unwrap_or(b"");
    let new_path = delta
        .as_ref()
        .and_then(|d| d.new_file().path_bytes())
        .unwrap_or(b"");
    let EntryModesAndOids {
        m_head,
        m_idx,
        m_work,
        h_head,
        h_idx,
    } = extract_modes_and_oids(entry);
    let score = rename_similarity(repo, h_head, h_idx);
    write!(
        out,
        "2 {x}{y} N... {m_head:06o} {m_idx:06o} {m_work:06o} {h_head} {h_idx} R{score} ",
    )?;
    render_opts.rel.write_quoted(
        out,
        new_path,
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    // Path separator: NUL with -z, TAB without.
    out.write_all(if render_opts.null_terminate {
        b"\0"
    } else {
        b"\t"
    })?;
    render_opts.rel.write_quoted(
        out,
        old_path,
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(line_terminator(render_opts.null_terminate).as_bytes())
}

fn write_synthetic_rename(
    row: &SyntheticRename,
    out: &mut impl Write,
    render_opts: &RenderOpts<'_>,
) -> Result<(), io::Error> {
    write!(
        out,
        "2 R{y} N... {m_head:06o} {m_idx:06o} {m_work:06o} {h_head} {h_idx} R{score} ",
        y = row.y,
        m_head = row.old.mode,
        m_idx = row.new.mode,
        m_work = row.new.mode,
        h_head = row.old.oid,
        h_idx = row.new.oid,
        score = row.score,
    )?;
    render_opts.rel.write_quoted(
        out,
        &row.new.path,
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(if render_opts.null_terminate {
        b"\0"
    } else {
        b"\t"
    })?;
    render_opts.rel.write_quoted(
        out,
        &row.old.path,
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(line_terminator(render_opts.null_terminate).as_bytes())
}

fn rename_similarity(repo: &Repository, old_oid: git2::Oid, new_oid: git2::Oid) -> u8 {
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

/// Writes an unmerged entry as a porcelain v2 `u` line:
/// `u XY <sub> <m1> <m2> <m3> <m_work> <h1> <h2> <h3> PATH`, where
/// `m1`/`h1` come from the ancestor stage, `m2`/`h2` from ours,
/// `m3`/`h3` from theirs. `XY` decodes from which stages are present
/// (AA/DD/DU/UD), falling back to `UU`.
///
/// `sub` is `N...` for a file. When the conflict is on a gitlink (the stage
/// modes are `160000`) it is the submodule's `S<c><m><u>` field, with the
/// folded state from `conflicted_submodules` and the gitlink workdir mode --
/// matching git. (libgit2 would emit `N...` and a zero workdir mode here,
/// because without a stage-0 gitlink it no longer sees the path as a submodule.)
fn write_conflict(
    entry: &git2::StatusEntry<'_>,
    conflicts: &FxHashMap<String, ConflictEntry>,
    conflicted_submodules: &FxHashMap<String, StatusSummary>,
    out: &mut impl Write,
    render_opts: &RenderOpts<'_>,
) -> Result<(), io::Error> {
    let path = entry.path().unwrap_or("");
    let (xy, m1, m2, m3, h1, h2, h3) = conflicts.get(path).map_or(
        (
            "UU",
            0u32,
            0u32,
            0u32,
            git2::Oid::ZERO_SHA1,
            git2::Oid::ZERO_SHA1,
            git2::Oid::ZERO_SHA1,
        ),
        |c| {
            let xy = match (c.ancestor.is_some(), c.ours.is_some(), c.theirs.is_some()) {
                (false, true, true) => "AA",
                (true, false, false) => "DD",
                (true, false, true) => "DU",
                (true, true, false) => "UD",
                _ => "UU",
            };
            let m1 = c.ancestor.map_or(0u32, |(m, _)| m);
            let m2 = c.ours.map_or(0u32, |(m, _)| m);
            let m3 = c.theirs.map_or(0u32, |(m, _)| m);
            let h1 = c.ancestor.map_or(git2::Oid::ZERO_SHA1, |(_, id)| id);
            let h2 = c.ours.map_or(git2::Oid::ZERO_SHA1, |(_, id)| id);
            let h3 = c.theirs.map_or(git2::Oid::ZERO_SHA1, |(_, id)| id);
            (xy, m1, m2, m3, h1, h2, h3)
        },
    );
    // A gitlink conflict (any stage mode is the gitlink mode) is an unmerged
    // submodule: emit `S<c><m><u>` and the gitlink workdir mode rather than
    // `N...`/`000000`. `conflicted_submodules` carries its folded state.
    let gitlink_mode = u32::from(git2::FileMode::Commit);
    let (s0, s1, s2, s3, m_work) = if m1 == gitlink_mode || m2 == gitlink_mode || m3 == gitlink_mode
    {
        let st = conflicted_submodules
            .get(path)
            .copied()
            .unwrap_or_else(StatusSummary::clean);
        let (c, m, u) = submodule_cmu(st);
        let m_work = if st.contains(StatusSummary::DELETED_WORKDIR) {
            0u32
        } else {
            0o160_000_u32
        };
        ('S', c, m, u, m_work)
    } else {
        let m_work = entry
            .index_to_workdir()
            .map_or(0u32, |d| u32::from(d.new_file().mode()));
        ('N', '.', '.', '.', m_work)
    };
    write!(
        out,
        "u {xy} {s0}{s1}{s2}{s3} {m1:06o} {m2:06o} {m3:06o} {m_work:06o} {h1} {h2} {h3} ",
    )?;
    render_opts.rel.write_quoted(
        out,
        entry.path_bytes(),
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(line_terminator(render_opts.null_terminate).as_bytes())
}

/// Writes a submodule entry as a porcelain v2 `1` line with the `sub`
/// field set to `S<C><M><U>` (commit changed / content modified /
/// untracked content present). File modes are the gitlink mode
/// (`160000`) for head/index, zero on the workdir side when
/// `DELETED_WORKDIR` is set, and `0` for `m_head` when `STAGED_NEW`
/// (no head entry yet).
#[expect(clippy::many_single_char_names)]
fn write_submodule(
    path: &str,
    st: StatusSummary,
    h_head: git2::Oid,
    h_index: git2::Oid,
    out: &mut impl Write,
    render_opts: &RenderOpts<'_>,
) -> Result<(), io::Error> {
    // `x`/`y` mirror git's XY notation; `c`/`m`/`u` mirror the
    // porcelain v2 `S<C><M><U>` sub-field positions.
    let (x, y) = submodule_xy(st);
    let (c, m, u) = submodule_cmu(st);
    let m_head = if st.contains(StatusSummary::STAGED_NEW) {
        0u32
    } else {
        0o160_000_u32
    };
    let m_work = if st.contains(StatusSummary::DELETED_WORKDIR) {
        0u32
    } else {
        0o160_000_u32
    };
    write!(
        out,
        "1 {x}{y} S{c}{m}{u} {:06o} {:06o} {:06o} {h_head} {h_index} ",
        m_head, 0o160_000_u32, m_work,
    )?;
    render_opts.rel.write_quoted(
        out,
        path.as_bytes(),
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(line_terminator(render_opts.null_terminate).as_bytes())
}

/// Writes a submodule whose gitlink was removed from the index (via
/// `git rm`) as `1 D. S... 160000 0 0 <h_head> 0000... PATH`. The
/// workdir side is zeroed since the entry no longer exists in the
/// index either.
fn write_deleted_submodule(
    path: &str,
    h_head: git2::Oid,
    out: &mut impl Write,
    render_opts: &RenderOpts<'_>,
) -> Result<(), io::Error> {
    write!(
        out,
        "1 D. S... {:06o} {:06o} {:06o} {h_head} {} ",
        0o160_000_u32,
        0u32,
        0u32,
        git2::Oid::ZERO_SHA1,
    )?;
    render_opts.rel.write_quoted(
        out,
        path.as_bytes(),
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(line_terminator(render_opts.null_terminate).as_bytes())
}

/// Writes a submodule rename as a porcelain v2 `2 R. S<C><M><U>` line:
/// gitlink mode at all three positions, same OID at head/index (it's a
/// pure rename), score 100, then `<new>\t<old>` (or NUL-separated with
/// `-z`).
fn write_renamed_submodule(
    rename: &super::SubmoduleRename,
    h_head: git2::Oid,
    h_index: git2::Oid,
    out: &mut impl Write,
    render_opts: &RenderOpts<'_>,
) -> Result<(), io::Error> {
    let gitlink = 0o160_000_u32;
    write!(
        out,
        "2 R. S... {gitlink:06o} {gitlink:06o} {gitlink:06o} {h_head} {h_index} R100 ",
    )?;
    render_opts.rel.write_quoted(
        out,
        rename.new.as_bytes(),
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(if render_opts.null_terminate {
        b"\0"
    } else {
        b"\t"
    })?;
    render_opts.rel.write_quoted(
        out,
        rename.old.as_bytes(),
        render_opts.null_terminate,
        render_opts.quote_mode,
    )?;
    out.write_all(line_terminator(render_opts.null_terminate).as_bytes())
}
