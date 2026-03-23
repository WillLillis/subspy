use std::path::Path;

use thiserror::Error;

use crate::connection::client::request_reindex;

pub type ReindexResult<T> = Result<T, ReindexError>;

#[derive(Debug, Error)]
pub enum ReindexError {
    #[error(transparent)]
    BincodeEncode(#[from] bincode::error::EncodeError),
    #[error(transparent)]
    BincodeDecode(#[from] bincode::error::DecodeError),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    VersionMismatch(#[from] crate::connection::VersionMismatchError),
}

/// Issues a reindex request to the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if any failure occurs.
pub fn reindex(
    root_path: &Path,
    replace_watchers: bool,
    display_progress: bool,
) -> ReindexResult<()> {
    request_reindex(root_path, replace_watchers, display_progress)
}
