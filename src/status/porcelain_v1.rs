//! Porcelain v1 output format (terse `XY PATH` per entry).
//!
//! Per `git-status(1)`, each line is `XY PATH`, with `?? PATH` for
//! untracked, `!! PATH` for ignored, and `R<space> ORIG -> PATH`
//! (`XY PATH\0ORIG\0` under `-z`) for renames. The `--branch` flag
//! prepends a `## branch...upstream [ahead/behind]` header.
//!
//! v1 is repo-root-relative and uncolored. The actual line-writing is
//! shared with the short format via [`xy_line`]; this module is a thin
//! wrapper that picks `QuoteSpace` quoting, no palette, and a no-op
//! `Relativizer::new("")`.

use git2::Repository;

use std::io::Write;

use super::{
    PorcelainOpts, StatusEntries, StatusResult,
    quote::QuoteMode,
    relativize::Relativizer,
    xy_line::{LineStyle, display_xy_lines},
};

const V1_STYLE: LineStyle = LineStyle {
    quote_mode: QuoteMode::QuoteSpace,
    palette: None,
};

/// Renders the full porcelain v1 output to `out`.
pub fn display_porcelain_v1(
    out: &mut impl Write,
    repo: &Repository,
    entries: &StatusEntries<'_>,
    opts: PorcelainOpts,
) -> StatusResult<()> {
    let rel = Relativizer::new("");
    display_xy_lines(out, repo, entries, &rel, opts, &V1_STYLE)
}
