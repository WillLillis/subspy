//! The `stop` subcommand: sends a shutdown request to the watch server.

use std::path::Path;

use thiserror::Error;

use crate::connection::client::request_shutdown;

pub type ShutdownResult<T> = Result<T, ShutdownError>;

#[derive(Debug, Error)]
pub enum ShutdownError {
    #[error(transparent)]
    BincodeEncode(#[from] bincode::error::EncodeError),
    #[error(transparent)]
    BincodeDecode(#[from] bincode::error::DecodeError),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    VersionMismatch(#[from] crate::connection::VersionMismatchError),
}

/// Issues a shutdown request to the watch server for `root_path`
///
/// # Errors
///
/// Returns `Err` if any failure occurs.
pub fn shutdown(root_path: &Path) -> ShutdownResult<()> {
    request_shutdown(root_path)
}
