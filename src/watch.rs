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
pub fn watch_project(path: &Path, display_progress: bool) -> WatchResult<()> {
    watch(path, display_progress)
}

/// Spawns the watch server as a fully detached background process for `path`.
///
/// The server is started by re-invoking the current executable with
/// `start <path> --foreground`.
///
/// # Errors
///
/// Returns `std::io::Error` if the current executable path cannot be determined
/// or the child process cannot be spawned.
pub fn spawn_daemon(path: &Path, log_level: Option<&str>) -> std::io::Result<()> {
    let exe = std::env::current_exe()?;
    let mut cmd = std::process::Command::new(exe);
    cmd.arg("start")
        .arg(path)
        .arg("--foreground")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if let Some(level) = log_level {
        cmd.args(["--log-level", level]);
    }

    #[cfg(target_os = "windows")]
    {
        use std::os::windows::process::CommandExt as _;
        // https://learn.microsoft.com/en-us/windows/win32/procthread/process-creation-flags#flags
        // The new process does not inherit its parent's console
        const DETACHED_PROCESS: u32 = 0x0000_0008;
        // The new process is the root process of a new process group...If this flag is specified,
        // CTRL+C signals will be disabled for all processes within the new process group.
        const CREATE_NEW_PROCESS_GROUP: u32 = 0x0000_0200;
        cmd.creation_flags(DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP);
    }

    cmd.spawn()?;
    Ok(())
}
