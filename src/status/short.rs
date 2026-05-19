//! Short output format (`git status -s` / `--short`).
//!
//! Same `XY PATH` line shape as porcelain v1, but with cwd-relative
//! paths, `Standard` quoting (matching `core.quotePath=true`), and
//! colors matching git's `WT_STATUS_*` palette. The actual line
//! writing is shared with porcelain v1 via [`xy_line`].

use git2::Repository;
use std::io::Write;

use crate::paint::{GREEN, RED};

use super::{
    PorcelainOpts, StatusEntries, StatusResult,
    quote::QuoteMode,
    relativize::Relativizer,
    xy_line::{LineStyle, Palette, SubmoduleFormat, display_xy_lines},
};

/// Color slots used by `git status -s`. Names mirror git's `WT_STATUS_*`
/// constants; values match git's defaults (green for staged / local
/// branch, red for everything else).
const SHORT_PALETTE: Palette = Palette {
    local_branch: GREEN,
    remote_branch: RED,
    nobranch: RED,
    updated: GREEN,
    changed: RED,
    untracked: RED,
    unmerged: RED,
};

/// Renders the full short output to `out`.
pub fn display_short(
    out: &mut impl Write,
    repo: &Repository,
    entries: &StatusEntries<'_>,
    rel: &Relativizer<'_>,
    opts: PorcelainOpts,
) -> StatusResult<()> {
    let style = LineStyle {
        quote_mode: QuoteMode {
            quote_path: opts.quote_path,
            ..QuoteMode::STANDARD
        },
        palette: Some(&SHORT_PALETTE),
        submodule: SubmoduleFormat::Short,
    };
    display_xy_lines(out, repo, entries, rel, opts, &style)
}
