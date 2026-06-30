//! Shared `XY PATH` line writer for porcelain v1 and short formats.
//!
//! Both emit a `## branch...` header (optional) followed by one
//! `XY PATH` line per entry. The two formats differ only along three
//! axes, captured in [`LineStyle`]:
//!
//! - Quoting mode: porcelain v1 uses `QuoteSpace`, short uses `Standard`.
//! - Relativization: porcelain v1 is always repo-root-relative; short is
//!   cwd-relative. Both go through `Relativizer` (porcelain v1 just
//!   constructs it with `cwd_rel = ""` so it's a no-op rewriter).
//! - Color: porcelain v1 is plain; short applies git's
//!   `WT_STATUS_{UPDATED,CHANGED,UNMERGED,UNTRACKED,...}` colors.

use git2::Repository;
use rustc_hash::FxHashMap;
use std::io::{self, Write};

use anstyle::Style;

use crate::{StatusSummary, paint::paint_into};

use super::{
    Divergence, PorcelainOpts, StatusEntries, StatusResult, UpstreamStatus,
    conflict::{ConflictEntry, build_conflict_map, path_within_any},
    interleave::SubRow,
    line_terminator,
    quote::QuoteMode,
    relativize::Relativizer,
    tracked::{
        SyntheticOrdinary, SyntheticRename, TrackedOrSubRow, TrackedRow, for_each_tracked_row,
        normalized_tracked_rows,
    },
    unborn_branch_name, upstream_status,
};

pub(super) struct LineStyle {
    pub quote_mode: QuoteMode,
    /// `None` for porcelain v1 (uncolored). `Some` for short.
    pub palette: Option<&'static Palette>,
    pub submodule: SubmoduleFormat,
}

/// How submodule Y characters are derived. Porcelain v1 collapses
/// `NEW_COMMITS` / `MODIFIED_CONTENT` / `UNTRACKED_CONTENT` into a
/// single 'M'; short distinguishes them as 'M' / 'm' / '?' so
/// submodule states are visually distinct from regular files.
#[derive(Clone, Copy)]
pub(super) enum SubmoduleFormat {
    Porcelain,
    Short,
}

/// Color slots mirroring git's `WT_STATUS_*` constants.
pub(super) struct Palette {
    pub local_branch: Style,
    pub remote_branch: Style,
    pub nobranch: Style,
    pub updated: Style,
    pub changed: Style,
    pub untracked: Style,
    pub unmerged: Style,
}

/// Renders the full output: optional `## branch...` header followed by
/// the five entry passes (tracked, submodules, deleted submodules,
/// untracked, ignored).
#[expect(clippy::too_many_lines)]
pub(super) fn display_xy_lines(
    out: &mut impl Write,
    repo: &Repository,
    entries: &StatusEntries<'_>,
    rel: &Relativizer<'_>,
    opts: PorcelainOpts,
    style: &LineStyle,
) -> StatusResult<()> {
    let PorcelainOpts {
        null_terminate,
        branch,
        ahead_behind,
        // `quote_path` already baked into `style.quote_mode`.
        quote_path: _,
        // Short / porcelain v1 don't emit a stash line.
        show_stash: _,
    } = opts;

    if branch {
        write_branch_header(repo, out, style, ahead_behind)?;
    }

    let index = repo.index()?;
    let conflicts = build_conflict_map(&index)?;

    // git emits tracked changes (including submodules) in one path-sorted stream,
    // then untracked, then ignored. The tracked file rows come pre-classified
    // (renames reconciled to match git) from `normalized_tracked_rows`; libgit2
    // excludes submodules from `non_submod`, so interleave the submodule rows by path.
    let tracked = normalized_tracked_rows(repo, entries);
    let mut submods: Vec<SubRow<'_>> = Vec::with_capacity(
        entries.submodules.len()
            + entries.deleted_submodules.len()
            + entries.renamed_submodules.len(),
    );
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

    for_each_tracked_row(tracked, submods, |row| match row {
        TrackedOrSubRow::File(TrackedRow::Entry(entry)) => {
            let st = entry.status();
            if st.contains(git2::Status::CONFLICTED) {
                write_conflict(&entry, &conflicts, out, rel, null_terminate, style)
            } else if st.intersects(git2::Status::INDEX_RENAMED | git2::Status::WT_RENAMED) {
                write_renamed(&entry, out, rel, null_terminate, style)
            } else {
                write_ordinary(&entry, out, rel, null_terminate, style)
            }
        }
        TrackedOrSubRow::File(TrackedRow::SyntheticOrdinary(row)) => {
            write_synthetic_ordinary_line(&row, out, rel, null_terminate, style)
        }
        TrackedOrSubRow::File(TrackedRow::SyntheticRename(row)) => {
            write_synthetic_rename_line(&row, out, rel, null_terminate, style)
        }
        TrackedOrSubRow::Sub(SubRow::Modified(path, st)) => {
            write_submodule(path, st, out, rel, null_terminate, style)
        }
        TrackedOrSubRow::Sub(SubRow::Deleted(path)) => {
            // `D ` (staged deletion of a submodule). X gets the staged color, Y is blank.
            let x = XyChar::new('D', style.palette.map(|p| p.updated));
            let y = XyChar::new(' ', None);
            write_xy_path(out, x, y, path.as_bytes(), rel, null_terminate, style)
        }
        TrackedOrSubRow::Sub(SubRow::Renamed(rename)) => {
            // `R ` (staged submodule rename). With -z the new and old paths
            // are NUL-separated; otherwise rendered as `old -> new`.
            let x = XyChar::new('R', style.palette.map(|p| p.updated));
            let y = XyChar::new(' ', None);
            write_xy_prefix(out, x, y)?;
            if null_terminate {
                write!(out, "{new}\0{old}\0", new = rename.new, old = rename.old)
            } else {
                write_path(out, rename.old.as_bytes(), rel, false, style)?;
                out.write_all(b" -> ")?;
                write_path(out, rename.new.as_bytes(), rel, false, style)?;
                out.write_all(b"\n")
            }
        }
    })?;

    for entry in entries
        .non_submod
        .iter()
        .filter(|e| e.status() == git2::Status::WT_NEW)
    {
        if path_within_any(entry.path_bytes(), entries.conflicted_paths) {
            continue; // libgit2's phantom untracked row for a conflicted submodule
        }
        let untracked = XyChar::new('?', style.palette.map(|p| p.untracked));
        write_xy_path(
            out,
            untracked,
            untracked,
            entry.path_bytes(),
            rel,
            null_terminate,
            style,
        )?;
    }

    for entry in entries
        .non_submod
        .iter()
        .filter(|e| e.status().contains(git2::Status::IGNORED))
    {
        let ignored = XyChar::new('!', None);
        write_xy_path(
            out,
            ignored,
            ignored,
            entry.path_bytes(),
            rel,
            null_terminate,
            style,
        )?;
    }

    Ok(())
}

/// Maps a `git2::Status` to its XY index/worktree characters. Space
/// (not `.`) for the unmodified slot, matching the v1/short wire format.
///
/// `RENAMED` is checked before `MODIFIED`: git2 sets both on a rename that
/// also changes content, and git renders that as `R` (the modification is
/// part of the rename), never `M`.
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
        ' '
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
        ' '
    };
    (x, y)
}

/// Maps a `StatusSummary` to the XY characters for a submodule entry,
/// per the given [`SubmoduleFormat`].
fn submodule_xy(st: StatusSummary, format: SubmoduleFormat) -> (char, char) {
    let x = if st.contains(StatusSummary::STAGED_NEW) {
        'A'
    } else if st.contains(StatusSummary::STAGED) {
        'M'
    } else {
        ' '
    };
    let y = if st.contains(StatusSummary::DELETED_WORKDIR) {
        'D'
    } else {
        match format {
            SubmoduleFormat::Porcelain => {
                if st.intersects(
                    StatusSummary::NEW_COMMITS
                        | StatusSummary::MODIFIED_CONTENT
                        | StatusSummary::UNTRACKED_CONTENT,
                ) {
                    'M'
                } else {
                    ' '
                }
            }
            SubmoduleFormat::Short => {
                if st.contains(StatusSummary::NEW_COMMITS) {
                    'M'
                } else if st.contains(StatusSummary::MODIFIED_CONTENT) {
                    'm'
                } else if st.contains(StatusSummary::UNTRACKED_CONTENT) {
                    '?'
                } else {
                    ' '
                }
            }
        }
    };
    (x, y)
}

/// A single X or Y character + the color slot it should render in.
/// Blank characters (`' '`) are never colored regardless of `color`.
#[derive(Clone, Copy)]
struct XyChar {
    ch: char,
    color: Option<Style>,
}

impl XyChar {
    const fn new(ch: char, color: Option<Style>) -> Self {
        Self { ch, color }
    }

    fn paint(self, out: &mut impl Write) -> io::Result<()> {
        let color = if self.ch == ' ' { None } else { self.color };
        match color {
            Some(s) => paint_into(out, s, |o| write!(o, "{}", self.ch)),
            None => write!(out, "{}", self.ch),
        }
    }
}

/// Writes the `XY ` prefix. The trailing space is plain.
fn write_xy_prefix(out: &mut impl Write, x: XyChar, y: XyChar) -> io::Result<()> {
    x.paint(out)?;
    y.paint(out)?;
    out.write_all(b" ")
}

/// Writes `path` using the style's quote mode + relativizer.
fn write_path(
    out: &mut impl Write,
    path: &[u8],
    rel: &Relativizer<'_>,
    null_terminate: bool,
    style: &LineStyle,
) -> io::Result<()> {
    rel.write_quoted(out, path, null_terminate, style.quote_mode)
}

/// Writes a line of the form `XY PATH<term>` with caller-supplied X/Y
/// characters. Used for the three entry kinds whose code is fixed:
/// `D ` for staged-deletion submodules, `??` for untracked, `!!` for
/// ignored.
fn write_xy_path(
    out: &mut impl Write,
    x: XyChar,
    y: XyChar,
    path: &[u8],
    rel: &Relativizer<'_>,
    null_terminate: bool,
    style: &LineStyle,
) -> io::Result<()> {
    write_xy_prefix(out, x, y)?;
    write_path(out, path, rel, null_terminate, style)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}

/// Color slots for an ordinary (non-conflict) tracked entry: X gets
/// `updated`, Y gets `changed`. Both `None` when no palette.
fn ordinary_colors(style: &LineStyle) -> (Option<Style>, Option<Style>) {
    style
        .palette
        .map_or((None, None), |p| (Some(p.updated), Some(p.changed)))
}

/// Writes a non-rename, non-conflict tracked entry as `XY PATH<term>`.
fn write_ordinary(
    entry: &git2::StatusEntry<'_>,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
    null_terminate: bool,
    style: &LineStyle,
) -> io::Result<()> {
    let (x, y) = regular_xy(entry.status());
    let (x_color, y_color) = ordinary_colors(style);
    write_xy_prefix(out, XyChar::new(x, x_color), XyChar::new(y, y_color))?;
    write_path(out, entry.path_bytes(), rel, null_terminate, style)?;
    out.write_all(line_terminator(null_terminate).as_bytes())
}

/// Writes a rename. Without `-z`: `XY <old> -> <new>`, each path quoted
/// independently. With `-z`: `XY <new>\0<old>\0` (per `git-status(1)`'s
/// `-z` rename form: path first, no arrow, no quoting).
fn write_renamed(
    entry: &git2::StatusEntry<'_>,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
    null_terminate: bool,
    style: &LineStyle,
) -> io::Result<()> {
    let st = entry.status();
    let (x, y) = regular_xy(st);
    let (x_color, y_color) = ordinary_colors(style);

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

    write_xy_prefix(out, XyChar::new(x, x_color), XyChar::new(y, y_color))?;
    if null_terminate {
        out.write_all(new_path)?;
        out.write_all(b"\0")?;
        out.write_all(old_path)?;
        out.write_all(b"\0")
    } else {
        write_path(out, old_path, rel, false, style)?;
        out.write_all(b" -> ")?;
        write_path(out, new_path, rel, false, style)?;
        out.write_all(b"\n")
    }
}

/// Maps porcelain-v2's `.` unmodified slot (used by the shared synthetic rows)
/// to the v1/short blank.
const fn blank_dot(ch: char) -> char {
    if ch == '.' { ' ' } else { ch }
}

/// Writes a synthetic ordinary row (a split or unpaired staged add/delete from
/// rename reconciliation) as `XY PATH`.
fn write_synthetic_ordinary_line(
    row: &SyntheticOrdinary,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
    null_terminate: bool,
    style: &LineStyle,
) -> io::Result<()> {
    let (x_color, y_color) = ordinary_colors(style);
    let x = XyChar::new(row.x, x_color);
    let y = XyChar::new(blank_dot(row.y), y_color);
    write_xy_path(out, x, y, &row.path, rel, null_terminate, style)
}

/// Writes a synthetic rename (a subspy-paired staged add/delete) the same way as
/// a libgit2 rename: `XY <old> -> <new>` (or `XY <new>\0<old>\0` under `-z`).
fn write_synthetic_rename_line(
    row: &SyntheticRename,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
    null_terminate: bool,
    style: &LineStyle,
) -> io::Result<()> {
    let (x_color, y_color) = ordinary_colors(style);
    write_xy_prefix(
        out,
        XyChar::new('R', x_color),
        XyChar::new(blank_dot(row.new.wt_y), y_color),
    )?;
    if null_terminate {
        out.write_all(&row.new.path)?;
        out.write_all(b"\0")?;
        out.write_all(&row.old.path)?;
        out.write_all(b"\0")
    } else {
        write_path(out, &row.old.path, rel, false, style)?;
        out.write_all(b" -> ")?;
        write_path(out, &row.new.path, rel, false, style)?;
        out.write_all(b"\n")
    }
}

/// Writes a conflicted entry as `XY PATH<term>`. `XY` is decoded from
/// the index's ancestor/ours/theirs presence: `AA` (both added), `DD`
/// (both deleted), `DU` (deleted by us), `UD` (deleted by them), `UU`
/// (both modified / fallback). Both characters get the `unmerged`
/// color slot.
fn write_conflict(
    entry: &git2::StatusEntry<'_>,
    conflicts: &FxHashMap<String, ConflictEntry>,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
    null_terminate: bool,
    style: &LineStyle,
) -> io::Result<()> {
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
    let mut chars = xy.chars();
    let color = style.palette.map(|p| p.unmerged);
    let x = XyChar::new(chars.next().unwrap(), color);
    let y = XyChar::new(chars.next().unwrap(), color);
    write_xy_path(out, x, y, entry.path_bytes(), rel, null_terminate, style)
}

/// Writes a submodule entry. XY derived from the [`StatusSummary`]
/// (staged-new / staged / dirty-content / deleted-workdir flags).
fn write_submodule(
    path: &str,
    st: StatusSummary,
    out: &mut impl Write,
    rel: &Relativizer<'_>,
    null_terminate: bool,
    style: &LineStyle,
) -> io::Result<()> {
    let (x, y) = submodule_xy(st, style.submodule);
    let (x_color, y_color) = ordinary_colors(style);
    write_xy_path(
        out,
        XyChar::new(x, x_color),
        XyChar::new(y, y_color),
        path.as_bytes(),
        rel,
        null_terminate,
        style,
    )
}

/// Writes the `## branch...upstream [ahead/behind]` header. Color is
/// applied to the local-branch name and the upstream name when a
/// palette is present. With `ahead_behind = false` and a diverged
/// upstream, emits `[different]` rather than the specific counts.
fn write_branch_header(
    repo: &Repository,
    out: &mut impl Write,
    style: &LineStyle,
    ahead_behind: bool,
) -> StatusResult<()> {
    let Ok(head) = repo.head() else {
        let head_ref = repo.find_reference("HEAD").ok();
        let branch = head_ref
            .as_ref()
            .and_then(unborn_branch_name)
            .unwrap_or("(unknown)");
        out.write_all(b"## No commits yet on ")?;
        paint_str(out, branch, style.palette.map(|p| p.local_branch))?;
        out.write_all(b"\n")?;
        return Ok(());
    };

    if !head.is_branch() {
        out.write_all(b"## ")?;
        paint_str(out, "HEAD (no branch)", style.palette.map(|p| p.nobranch))?;
        out.write_all(b"\n")?;
        return Ok(());
    }

    // Display path is lossy so a non-UTF-8 ref still renders something.
    // `find_branch` below needs the strict `&str` form -- if the shorthand
    // isn't valid UTF-8 we'll skip the upstream suffix instead.
    let branch_display = String::from_utf8_lossy(head.shorthand_bytes());
    out.write_all(b"## ")?;
    paint_str(out, &branch_display, style.palette.map(|p| p.local_branch))?;

    match upstream_status(repo, &head, ahead_behind)? {
        UpstreamStatus::None => {}
        UpstreamStatus::Gone { name } => {
            out.write_all(b"...")?;
            paint_str(out, &name, style.palette.map(|p| p.remote_branch))?;
            out.write_all(b" [gone]")?;
        }
        UpstreamStatus::Tracking { name, divergence } => {
            out.write_all(b"...")?;
            paint_str(out, &name, style.palette.map(|p| p.remote_branch))?;
            match divergence {
                Divergence::Counts(0, 0) => {}
                Divergence::Counts(a, 0) => write!(out, " [ahead {a}]")?,
                Divergence::Counts(0, b) => write!(out, " [behind {b}]")?,
                Divergence::Counts(a, b) => write!(out, " [ahead {a}, behind {b}]")?,
                Divergence::Skipped => write!(out, " [different]")?,
            }
        }
    }
    out.write_all(b"\n")?;
    Ok(())
}

/// Writes `s`, optionally wrapped in a color span.
fn paint_str(out: &mut impl Write, s: &str, color: Option<Style>) -> io::Result<()> {
    match color {
        Some(style) => paint_into(out, style, |o| o.write_all(s.as_bytes())),
        None => out.write_all(s.as_bytes()),
    }
}
