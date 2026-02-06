use std::path::{Path, PathBuf};

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
    #[error(transparent)]
    LockFileAcquire(#[from] LockFileError),
}

#[derive(Debug, Error)]
pub struct LockFileError {
    error: std::io::Error,
    path: PathBuf,
}

impl std::fmt::Display for LockFileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Failed to acquire lock file at {}: {}",
            self.path.display(),
            self.error
        )
    }
}

impl LockFileError {
    #[must_use]
    pub const fn new(path: PathBuf, error: std::io::Error) -> Self {
        Self { error, path }
    }
}

/// Watches the repository at `path`
///
/// # Errors
///
/// Returns `Err` if watching fails.
pub fn watch_project(path: &Path) -> WatchResult<()> {
    watch(path)
}
