//! Porcelain v1 output format (terse `XY PATH` per entry).
//!
//! Per `git-status(1)`, each line is `XY PATH`, with `?? PATH` for
//! untracked, `!! PATH` for ignored, and `R<space> ORIG -> PATH`
//! (`XY PATH\0ORIG\0` under `-z`) for renames. The `--branch` flag
//! prepends a `## branch...upstream [ahead/behind]` header.

use git2::{Repository, Statuses};
use rustc_hash::FxHashMap;

use std::io::{self, Write};

use crate::StatusSummary;

use super::{
    StatusResult,
    conflict::{ConflictEntry, build_conflict_map},
    line_terminator,
    quote::{QuoteMode, write_path},
    unborn_branch_name,
};

/// Porcelain v1 uses `QuoteSpace` mode to match `git status --porcelain`,
/// which sets `QUOTE_PATH_QUOTE_SP` so paths containing spaces get quoted.
/// v1 emits repo-root-relative paths regardless of cwd, so it never goes
/// through `Relativizer`.
const QUOTE_MODE: QuoteMode = QuoteMode::QuoteSpace;

/// Renders the full porcelain v1 output to `out`: an optional
/// `## branch...` header followed by one `XY PATH` line per entry,
/// terminated by LF or NUL per `null_terminate`.
pub fn display_porcelain_v1(
    out: &mut impl Write,
    repo: &Repository,
    non_submod: &Statuses<'_>,
    submodule_statuses: &[(String, StatusSummary)],
    deleted_submodule_paths: &[String],
    null_terminate: bool,
    branch: bool,
) -> StatusResult<()> {
    if branch {
        write_branch_header(repo, out)?;
    }

    let index = repo.index()?;
    let conflicts = build_conflict_map(&index)?;

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
            write_conflict(&entry, &conflicts, out, null_terminate)?;
        } else if st.intersects(git2::Status::INDEX_RENAMED | git2::Status::WT_RENAMED) {
            write_renamed(&entry, out, null_terminate)?;
        } else {
            write_ordinary(&entry, out, null_terminate)?;
        }
    }

    for (path, st) in submodule_statuses {
        write_submodule(path, *st, out, null_terminate)?;
    }

    for path in deleted_submodule_paths {
        write_xy_path(out, "D ", path, null_terminate)?;
    }

    for entry in non_submod
        .iter()
        .filter(|e| e.status() == git2::Status::WT_NEW)
    {
        write_xy_path(out, "??", entry.path().unwrap_or(""), null_terminate)?;
    }

    for entry in non_submod
        .iter()
        .filter(|e| e.status().contains(git2::Status::IGNORED))
    {
        write_xy_path(out, "!!", entry.path().unwrap_or(""), null_terminate)?;
    }

    Ok(())
}

/// Maps a `git2::Status` to the XY index/worktree characters used in porcelain v1.
/// Differs from porcelain v2 by emitting a literal space for the unmodified state
/// instead of `.`, matching the v1 wire format.
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
        ' '
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
        ' '
    };
    (x, y)
}

/// Maps a `StatusSummary` to the XY characters for a submodule porcelain v1 entry.
fn submodule_xy(st: StatusSummary) -> (char, char) {
    let x = if st.contains(StatusSummary::STAGED_NEW) {
        'A'
    } else if st.contains(StatusSummary::STAGED) {
        'M'
    } else {
        ' '
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
        ' '
    };
    (x, y)
}

/// Writes the `## branch...upstream [ahead/behind]` header for porcelain v1.
fn write_branch_header(repo: &Repository, out: &mut impl Write) -> StatusResult<()> {
    let Ok(head) = repo.head() else {
        // Unborn HEAD (empty repo, no commits yet).
        let head_ref = repo.find_reference("HEAD").ok();
        let branch = head_ref
            .as_ref()
            .and_then(unborn_branch_name)
            .unwrap_or("(unknown)");
        writeln!(out, "## No commits yet on {branch}")?;
        return Ok(());
    };

    let branch_name = Some(&head)
        .filter(|h| h.is_branch())
        .and_then(|h| h.shorthand());

    let Some(name) = branch_name else {
        // Detached HEAD: `## HEAD (no branch)`
        writeln!(out, "## HEAD (no branch)")?;
        return Ok(());
    };

    let Ok(local) = repo.find_branch(name, git2::BranchType::Local) else {
        writeln!(out, "## {name}")?;
        return Ok(());
    };

    let Ok(upstream) = local.upstream() else {
        writeln!(out, "## {name}")?;
        return Ok(());
    };
    let Some(upstream_name) = upstream.get().shorthand() else {
        writeln!(out, "## {name}")?;
        return Ok(());
    };

    let counts = local
        .get()
        .peel_to_commit()
        .ok()
        .zip(upstream.get().peel_to_commit().ok())
        .and_then(|(l, u)| repo.graph_ahead_behind(l.id(), u.id()).ok());

    match counts {
        Some((ahead, behind)) if ahead != 0 || behind != 0 => writeln!(
            out,
            "## {name}...{upstream_name} [ahead {ahead}, behind {behind}]"
        )?,
        _ => writeln!(out, "## {name}...{upstream_name}")?,
    }
    Ok(())
}

/// Writes a porcelain v1 line of the form `XY PATH<term>`, where `xy`
/// is a pre-decided status code rather than something derived from a
/// `StatusEntry`. Used for the three entry kinds whose code is fixed by
/// the caller: `D ` for staged-deletion submodules, `??` for untracked,
/// and `!!` for ignored.
fn write_xy_path(
    out: &mut impl Write,
    xy: &str,
    path: &str,
    null_terminate: bool,
) -> Result<(), io::Error> {
    write!(out, "{xy} ")?;
    write_path(out, path, null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}

/// Writes a non-rename, non-conflict tracked entry as `XY PATH<term>`,
/// with `XY` derived from the entry's index/worktree status bits.
fn write_ordinary(
    entry: &git2::StatusEntry<'_>,
    out: &mut impl Write,
    null_terminate: bool,
) -> Result<(), io::Error> {
    let (x, y) = regular_xy(entry.status());
    write!(out, "{x}{y} ")?;
    write_path(out, entry.path().unwrap_or(""), null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}

/// Writes a rename entry. Without `-z`: `R<space> ORIG -> PATH\n`, with
/// each path quoted independently. With `-z`: `R<space> PATH\0ORIG\0`,
/// path first and no arrow (per `git-status(1)`'s `-z` rename form).
fn write_renamed(
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
    let old_path = path_str(delta.as_ref().and_then(|d| d.old_file().path()));
    let new_path = path_str(delta.as_ref().and_then(|d| d.new_file().path()));
    if null_terminate {
        // -z form: `XY PATH\0ORIG\0` (path first, no arrow). No quoting
        // applies under -z.
        write!(out, "{x}{y} {new_path}\0{old_path}\0")
    } else {
        // Each path is quoted independently.
        write!(out, "{x}{y} ")?;
        write_path(out, &old_path, false, QUOTE_MODE)?;
        out.write_all(b" -> ")?;
        write_path(out, &new_path, false, QUOTE_MODE)?;
        out.write_all(b"\n")
    }
}

/// Writes a conflicted entry as `XY PATH<term>`, with `XY` decoded from
/// the index's ancestor/ours/theirs presence: `AA` (both added), `DD`
/// (both deleted), `DU` (deleted by us), `UD` (deleted by them), `UU`
/// (both modified / fallback).
fn write_conflict(
    entry: &git2::StatusEntry<'_>,
    conflicts: &FxHashMap<String, ConflictEntry>,
    out: &mut impl Write,
    null_terminate: bool,
) -> Result<(), io::Error> {
    let path = entry.path().unwrap_or("");
    let xy = conflicts.get(path).map_or("UU", |c| {
        match (c.ancestor.is_some(), c.ours.is_some(), c.theirs.is_some()) {
            (false, true, true) => "AA",
            (true, false, false) => "DD",
            (true, false, true) => "DU",
            (true, true, false) => "UD",
            _ => "UU",
        }
    });
    write!(out, "{xy} ")?;
    write_path(out, path, null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}

/// Writes a submodule entry as `XY PATH<term>`, with `XY` derived from
/// the [`StatusSummary`] (staged-new / staged / dirty-content / deleted
/// workdir flags) via [`submodule_xy`].
fn write_submodule(
    path: &str,
    st: StatusSummary,
    out: &mut impl Write,
    null_terminate: bool,
) -> Result<(), io::Error> {
    let (x, y) = submodule_xy(st);
    write!(out, "{x}{y} ")?;
    write_path(out, path, null_terminate, QUOTE_MODE)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}
