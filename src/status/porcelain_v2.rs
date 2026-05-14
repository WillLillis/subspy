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
    quote::QuoteMode,
    relativize::Relativizer,
    unborn_branch_name,
};

/// Porcelain v2 uses `Standard` mode (matches `git status --porcelain=2`,
/// which uses `quote_c_style` without `QUOTE_PATH_QUOTE_SP`). Spaces are
/// preserved verbatim; only escapes/control/high-bytes/`"`/`\` trigger
/// quoting.
const QUOTE_MODE: QuoteMode = QuoteMode::Standard;

/// Renders the full porcelain v2 output to `out`: optional `# branch.*`
/// header lines followed by one `1`/`2`/`u`/`?`/`!` line per entry,
/// terminated by LF or NUL per `null_terminate`. `rel` is the
/// cwd-aware relativizer; under `-z` it falls back to repo-root paths
/// internally.
#[expect(clippy::too_many_arguments)]
pub fn display_porcelain_v2(
    out: &mut impl Write,
    repo: &Repository,
    non_submod: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    deleted_submodule_paths: &[String],
    rel: &Relativizer<'_>,
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
            write_conflict(&entry, &conflicts, out, rel, null_terminate)?;
        } else if st.intersects(git2::Status::INDEX_RENAMED | git2::Status::WT_RENAMED) {
            write_renamed(&entry, out, rel, null_terminate)?;
        } else {
            write_ordinary(&entry, out, rel, null_terminate)?;
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
        write_submodule(path, *st, h_head, h_index, out, rel, null_terminate)?;
    }

    for path in deleted_submodule_paths {
        let h_head = head_tree
            .as_ref()
            .and_then(|t| t.get_path(Path::new(path)).ok())
            .map_or_else(git2::Oid::zero, |e| e.id());
        write_deleted_submodule(path, h_head, out, rel, null_terminate)?;
    }

    for entry in non_submod
        .iter()
        .filter(|e| e.status() == git2::Status::WT_NEW)
    {
        out.write_all(b"? ")?;
        rel.write_quoted(out, entry.path().unwrap_or(""), null_terminate, QUOTE_MODE)?;
        out.write_all(line_terminator(null_terminate).as_bytes())?;
    }

    for entry in non_submod
        .iter()
        .filter(|e| e.status().contains(git2::Status::IGNORED))
    {
        out.write_all(b"! ")?;
        rel.write_quoted(out, entry.path().unwrap_or(""), null_terminate, QUOTE_MODE)?;
        out.write_all(line_terminator(null_terminate).as_bytes())?;
    }

    Ok(())
}

/// Writes the `# branch.*` header lines for porcelain v2 output.
fn write_branch_headers(repo: &Repository, out: &mut impl Write) -> StatusResult<()> {
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
        .map_or_else(git2::Oid::zero, |c| c.id());
    writeln!(out, "# branch.oid {oid}")?;

    let branch_name = Some(&head)
        .filter(|h| h.is_branch())
        .and_then(|h| h.shorthand());
    writeln!(out, "# branch.head {}", branch_name.unwrap_or("(detached)"))?;

    if let Some(name) = branch_name
        && let Ok(local) = repo.find_branch(name, git2::BranchType::Local)
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
        .unwrap_or_else(git2::Oid::zero);
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
    rel: &Relativizer<'_>,
    null_terminate: bool,
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
    rel.write_quoted(out, entry.path().unwrap_or(""), null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}

/// Writes a rename entry as a porcelain v2 `2` line:
/// `2 XY <sub> <modes> <oids> R<score> NEW<sep>OLD`. The separator
/// between paths is TAB (`\t`) without `-z` and NUL (`\0`) with `-z`,
/// per `git-status(1)`. Similarity is always reported as `R100` -
/// libgit2's rename detection returns the pair but not a score.
fn write_renamed(
    entry: &git2::StatusEntry<'_>,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
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
    let old_path = path_str(delta.as_ref().and_then(|d| d.old_file().path()));
    let new_path = path_str(delta.as_ref().and_then(|d| d.new_file().path()));
    let EntryModesAndOids {
        m_head,
        m_idx,
        m_work,
        h_head,
        h_idx,
    } = extract_modes_and_oids(entry);
    write!(
        out,
        "2 {x}{y} N... {m_head:06o} {m_idx:06o} {m_work:06o} {h_head} {h_idx} R100 ",
    )?;
    rel.write_quoted(out, &new_path, null_terminate, QUOTE_MODE)?;
    // Path separator: NUL with -z, TAB without.
    out.write_all(if null_terminate { b"\0" } else { b"\t" })?;
    rel.write_quoted(out, &old_path, null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}

/// Writes a conflicted entry as a porcelain v2 `u` line:
/// `u XY N... <m1> <m2> <m3> <m_work> <h1> <h2> <h3> PATH`, where
/// `m1`/`h1` come from the ancestor stage, `m2`/`h2` from ours,
/// `m3`/`h3` from theirs. `XY` decodes from which stages are present
/// (AA/DD/DU/UD), falling back to `UU`.
fn write_conflict(
    entry: &git2::StatusEntry<'_>,
    conflicts: &FxHashMap<String, ConflictEntry>,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
    null_terminate: bool,
) -> Result<(), io::Error> {
    let path = entry.path().unwrap_or("");
    let m_work = entry
        .index_to_workdir()
        .map_or(0u32, |d| u32::from(d.new_file().mode()));
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
    write!(
        out,
        "u {xy} N... {m1:06o} {m2:06o} {m3:06o} {m_work:06o} {h1} {h2} {h3} ",
    )?;
    rel.write_quoted(out, path, null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
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
    rel: &Relativizer<'_>,
    null_terminate: bool,
) -> Result<(), io::Error> {
    // `x`/`y` mirror git's XY notation; `c`/`m`/`u` mirror the
    // porcelain v2 `S<C><M><U>` sub-field positions.
    let (x, y) = submodule_xy(st);
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
    rel.write_quoted(out, path, null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}

/// Writes a submodule whose gitlink was removed from the index (via
/// `git rm`) as `1 D. S... 160000 0 0 <h_head> 0000... PATH`. The
/// workdir side is zeroed since the entry no longer exists in the
/// index either.
fn write_deleted_submodule(
    path: &str,
    h_head: git2::Oid,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
    null_terminate: bool,
) -> Result<(), io::Error> {
    write!(
        out,
        "1 D. S... {:06o} {:06o} {:06o} {h_head} {} ",
        0o160_000_u32,
        0u32,
        0u32,
        git2::Oid::zero(),
    )?;
    rel.write_quoted(out, path, null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}
