//! The `reindex` subcommand: triggers a full status recomputation on
//! the watch server.

use std::path::Path;

use thiserror::Error;

use crate::connection::{IpcError, client::request_reindex};

pub type ReindexResult<T> = Result<T, ReindexError>;

#[derive(Debug, Error)]
pub enum ReindexError {
    #[error(transparent)]
    Ipc(#[from] IpcError),
}

/// Issues a reindex request to the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if connecting to the server, encoding the request,
/// or receiving the response fails.
pub fn reindex(
    root_path: &Path,
    replace_watchers: bool,
    display_progress: bool,
) -> ReindexResult<()> {
    Ok(request_reindex(
        root_path,
        replace_watchers,
        display_progress,
    )?)
}
