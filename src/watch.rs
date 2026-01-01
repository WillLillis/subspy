use std::path::Path;

use thiserror::Error;

use crate::connection::watch_server::watch;

pub type WatchResult<T> = Result<T, WatchError>;

#[derive(Error, Debug)]
pub enum WatchError {
    #[error(transparent)]
    BincodeEncode(#[from] bincode::error::EncodeError),
    #[error(transparent)]
    BincodeDecode(#[from] bincode::error::DecodeError),
    #[error(transparent)]
    FileWatch(#[from] notify::Error),
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    Receive(#[from] crossbeam_channel::RecvError),
}

/// Watches the repository at `path`
///
/// # Errors
///
/// Returns `Err` if watching fails.
pub fn watch_project(path: &Path) -> WatchResult<()> {
    watch(path)
}
