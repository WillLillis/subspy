//! Output-format verification tests. Each submodule exercises a specific
//! renderer (long / porcelain v1 / porcelain v2 / short) and asserts its
//! output against an external reference - either a committed snapshot
//! (long, short) or a live `git status` invocation (porcelain).

mod config;
mod fixtures;
mod long;
mod porcelain;
mod short;

use git2::Repository;

use crate::{StatusSummary, cli::ProjectPath, git::path::GitPath};

use super::{
    AssembleOutcome, OutputOpts, Relativizer, StatusEntries, StatusResult, StatusScope,
    assemble_status_scoped,
};

/// Whole-repository status for the renderer tests, with warnings discarded.
fn assemble_status<R>(
    project: &ProjectPath,
    opts: OutputOpts,
    submodule_statuses: impl FnOnce() -> StatusResult<Vec<(GitPath, StatusSummary)>>,
    render: impl FnOnce(&Repository, &StatusEntries<'_>, &Relativizer<'_>) -> StatusResult<R>,
) -> StatusResult<R> {
    match assemble_status_scoped(
        project,
        opts,
        StatusScope::All,
        false,
        submodule_statuses,
        render,
    )? {
        AssembleOutcome::Rendered(rendered, _) => Ok(rendered),
        AssembleOutcome::Declined(_) => {
            unreachable!("whole-repository status requests cannot decline")
        }
    }
}
