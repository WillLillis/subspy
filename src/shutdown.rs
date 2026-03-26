//! The `stop` subcommand: sends a shutdown request to the watch server.

use std::path::Path;

use thiserror::Error;

use crate::connection::{IpcError, client::request_shutdown};

pub type ShutdownResult<T> = Result<T, ShutdownError>;

#[derive(Debug, Error)]
pub enum ShutdownError {
    #[error(transparent)]
    Ipc(#[from] IpcError),
}

/// Issues a shutdown request to the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if connecting to the server, encoding the request,
/// or receiving the acknowledgement fails.
pub fn shutdown(root_path: &Path) -> ShutdownResult<()> {
    Ok(request_shutdown(root_path)?)
}
