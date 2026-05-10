//! Porcelain v2 output format (rich `1`/`2`/`u`/`?`/`!` lines).
//!
//! Per `git-status(1)`, ordinary entries get a `1 XY <sub> <modes> <oids> PATH`
//! line, renames get a `2 ...` line, conflicts get a `u XY ...` line, and
//! untracked/ignored use the same `?`/`!` markers as v1. The `--branch` flag
//! prepends `# branch.oid`/`# branch.head`/`# branch.upstream`/`# branch.ab`
//! header lines.

use git2::{Repository, Statuses};
use rustc_hash::FxHashMap;

use std::{
    io::{self, Write},
    path::Path,
};

use crate::StatusSummary;

use super::{
    StatusResult,
    conflict::{ConflictEntry, build_conflict_map},
    line_terminator,
    quote::{QuoteMode, maybe_quote},
};

/// Porcelain v2 uses `Standard` mode (matches `git status --porcelain=2`,
/// which uses `quote_c_style` without `QUOTE_PATH_QUOTE_SP`). Spaces are
/// preserved verbatim; only escapes/control/high-bytes/`"`/`\` trigger
/// quoting.
const QUOTE_MODE: QuoteMode = QuoteMode::Standard;

/// Writes the `# branch.*` header lines for porcelain v2 output.
fn write_branch_headers(repo: &Repository, out: &mut impl Write) -> StatusResult<()> {
    let head = repo.head().ok();

    let oid_str = head
        .as_ref()
        .and_then(|h| h.peel_to_commit().ok())
        .map_or_else(
            || "0000000000000000000000000000000000000000".to_string(),
            |c| c.id().to_string(),
        );

    writeln!(out, "# branch.oid {oid_str}")?;

    let branch_name = head
        .as_ref()
        .filter(|h| h.is_branch())
        .and_then(|h| h.shorthand())
        .map(str::to_string);
    writeln!(
        out,
        "# branch.head {}",
        branch_name.as_deref().unwrap_or("(detached)")
    )?;

    if let Some(name) = branch_name
        && let Ok(local) = repo.find_branch(&name, git2::BranchType::Local)
        && let Ok(upstream) = local.upstream()
        && let Some(upstream_name) = upstream.get().shorthand()
    {
        writeln!(out, "# branch.upstream {upstream_name}")?;
        let local_oid = local.get().peel_to_commit().map(|c| c.id());
        let up_oid = upstream.get().peel_to_commit().map(|c| c.id());
        if let (Ok(l), Ok(u)) = (local_oid, up_oid)
            && let Ok((ahead, behind)) = repo.graph_ahead_behind(l, u)
        {
            writeln!(out, "# branch.ab +{ahead} -{behind}")?;
        }
    }

    Ok(())
}

/// Maps a `git2::Status` to the XY index/worktree characters used in porcelain v2.
const fn regular_xy(st: git2::Status) -> (char, char) {
    let x = if st.contains(git2::Status::INDEX_NEW) {
        'A'
    } else if st.contains(git2::Status::INDEX_MODIFIED) {
        'M'
    } else if st.contains(git2::Status::INDEX_DELETED) {
        'D'
    } else if st.contains(git2::Status::INDEX_RENAMED) {
        'R'
    } else if st.contains(git2::Status::INDEX_TYPECHANGE) {
        'T'
    } else {
        '.'
    };
    let y = if st.contains(git2::Status::WT_MODIFIED) {
        'M'
    } else if st.contains(git2::Status::WT_DELETED) {
        'D'
    } else if st.contains(git2::Status::WT_RENAMED) {
        'R'
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
    let y = if st.intersects(
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

/// Returns the 4-char submodule sub-field (`S<c><m><u>`) for a porcelain v2 entry.
fn submodule_sub(st: StatusSummary) -> String {
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
    format!("S{c}{m}{u}")
}

fn write_ordinary_entry(
    entry: &git2::StatusEntry<'_>,
    out: &mut impl Write,
    null_terminate: bool,
) -> Result<(), io::Error> {
    let (x, y) = regular_xy(entry.status());
    let path = maybe_quote(entry.path().unwrap_or(""), null_terminate, QUOTE_MODE);
    // Compute index state first; HEAD falls back to index when file is not staged
    // (HEAD and index are the same for workdir-only changes).
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
        .unwrap_or_else(git2::Oid::zero);
    let h_head = entry.head_to_index().map_or(h_idx, |d| d.old_file().id());
    let term = line_terminator(null_terminate);
    write!(
        out,
        "1 {x}{y} N... {m_head:06o} {m_idx:06o} {m_work:06o} {h_head} {h_idx} {path}{term}",
    )
}

fn write_renamed_entry(
    entry: &git2::StatusEntry<'_>,
    out: &mut impl Write,
    null_terminate: bool,
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
    let path_str =
        |p: Option<&std::path::Path>| p.map(|p| p.display().to_string()).unwrap_or_default();
    let old_path = maybe_quote(
        &path_str(delta.as_ref().and_then(|d| d.old_file().path())),
        null_terminate,
        QUOTE_MODE,
    )
    .into_owned();
    let new_path = maybe_quote(
        &path_str(delta.as_ref().and_then(|d| d.new_file().path())),
        null_terminate,
        QUOTE_MODE,
    )
    .into_owned();
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
        .unwrap_or_else(git2::Oid::zero);
    let h_head = entry.head_to_index().map_or(h_idx, |d| d.old_file().id());
    // Path separator: NUL with -z, TAB without.
    let path_sep = if null_terminate { '\0' } else { '\t' };
    let term = line_terminator(null_terminate);
    write!(
        out,
        "2 {x}{y} N... {m_head:06o} {m_idx:06o} {m_work:06o} {h_head} {h_idx} R100 {new_path}{path_sep}{old_path}{term}",
    )
}

fn write_conflict_entry(
    entry: &git2::StatusEntry<'_>,
    conflicts: &FxHashMap<String, ConflictEntry>,
    out: &mut impl Write,
    null_terminate: bool,
) -> Result<(), io::Error> {
    let path = entry.path().unwrap_or("");
    let m_work = entry
        .index_to_workdir()
        .map_or(0u32, |d| u32::from(d.new_file().mode()));
    let path_for_emit = maybe_quote(path, null_terminate, QUOTE_MODE);
    let (xy, m1, m2, m3, h1, h2, h3) = conflicts.get(path).map_or_else(
        || {
            (
                "UU",
                0u32,
                0u32,
                0u32,
                git2::Oid::zero(),
                git2::Oid::zero(),
                git2::Oid::zero(),
            )
        },
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
            let h1 = c.ancestor.map_or_else(git2::Oid::zero, |(_, id)| id);
            let h2 = c.ours.map_or_else(git2::Oid::zero, |(_, id)| id);
            let h3 = c.theirs.map_or_else(git2::Oid::zero, |(_, id)| id);
            (xy, m1, m2, m3, h1, h2, h3)
        },
    );
    let term = line_terminator(null_terminate);
    write!(
        out,
        "u {xy} N... {m1:06o} {m2:06o} {m3:06o} {m_work:06o} {h1} {h2} {h3} {path_for_emit}{term}",
    )
}

fn write_submodule_entry(
    path: &str,
    st: StatusSummary,
    h_head: git2::Oid,
    h_index: git2::Oid,
    out: &mut impl Write,
    null_terminate: bool,
) -> Result<(), io::Error> {
    let (x, y) = submodule_xy(st);
    let sub = submodule_sub(st);
    let m_head = if st.contains(StatusSummary::STAGED_NEW) {
        0u32
    } else {
        0o160_000_u32
    };
    let path = maybe_quote(path, null_terminate, QUOTE_MODE);
    let term = line_terminator(null_terminate);
    write!(
        out,
        "1 {x}{y} {sub} {:06o} {:06o} {:06o} {h_head} {h_index} {path}{term}",
        m_head, 0o160_000_u32, 0o160_000_u32
    )
}

fn write_deleted_submodule_entry(
    path: &str,
    h_head: git2::Oid,
    out: &mut impl Write,
    null_terminate: bool,
) -> Result<(), io::Error> {
    let path = maybe_quote(path, null_terminate, QUOTE_MODE);
    let term = line_terminator(null_terminate);
    write!(
        out,
        "1 D. S... {:06o} {:06o} {:06o} {h_head} {} {path}{term}",
        0o160_000_u32,
        0u32,
        0u32,
        git2::Oid::zero()
    )
}

pub fn display_porcelain_v2(
    out: &mut impl Write,
    repo: &Repository,
    non_submod: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    deleted_submodule_paths: &[String],
    null_terminate: bool,
    branch: bool,
) -> StatusResult<()> {
    if branch {
        write_branch_headers(repo, out)?;
    }

    let index = repo.index()?;
    let conflicts = build_conflict_map(&index)?;
    let head_tree = repo.head().ok().and_then(|h| h.peel_to_tree().ok());

    // Match git's three-pass ordering: tracked (modified/staged/conflicted/
    // renamed) first, then untracked, then ignored.
    for entry in non_submod.iter() {
        let st = entry.status();
        if st == git2::Status::CURRENT
            || st == git2::Status::WT_NEW
            || st.contains(git2::Status::IGNORED)
        {
            continue;
        }
        if st.contains(git2::Status::CONFLICTED) {
            write_conflict_entry(&entry, &conflicts, out, null_terminate)?;
        } else if st.intersects(git2::Status::INDEX_RENAMED | git2::Status::WT_RENAMED) {
            write_renamed_entry(&entry, out, null_terminate)?;
        } else {
            write_ordinary_entry(&entry, out, null_terminate)?;
        }
    }

    for (path, st) in submodule_statuses {
        let h_head = head_tree
            .as_ref()
            .and_then(|t| t.get_path(Path::new(path)).ok())
            .map_or_else(git2::Oid::zero, |e| e.id());
        let h_index = index
            .get_path(Path::new(path), 0)
            .map_or_else(git2::Oid::zero, |e| e.id);
        write_submodule_entry(path, *st, h_head, h_index, out, null_terminate)?;
    }

    for path in deleted_submodule_paths {
        let h_head = head_tree
            .as_ref()
            .and_then(|t| t.get_path(Path::new(path)).ok())
            .map_or_else(git2::Oid::zero, |e| e.id());
        write_deleted_submodule_entry(path, h_head, out, null_terminate)?;
    }

    let term = line_terminator(null_terminate);
    for entry in non_submod
        .iter()
        .filter(|e| e.status() == git2::Status::WT_NEW)
    {
        let path = maybe_quote(entry.path().unwrap_or(""), null_terminate, QUOTE_MODE);
        write!(out, "? {path}{term}")?;
    }

    for entry in non_submod
        .iter()
        .filter(|e| e.status().contains(git2::Status::IGNORED))
    {
        let path = maybe_quote(entry.path().unwrap_or(""), null_terminate, QUOTE_MODE);
        write!(out, "! {path}{term}")?;
    }

    Ok(())
}
