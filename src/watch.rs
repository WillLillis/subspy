//! Daemon lifecycle: spawning the background watch server process
//! and lock file management.

use std::{
    fs,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use log::error;
use notify::{RecursiveMode, Watcher as _};
use thiserror::Error;

use crate::connection::{IpcError, watch_server::ServerWatcher};

pub type WatchResult<T> = Result<T, WatchError>;

#[derive(Error, Debug)]
pub enum WatchError {
    #[error(transparent)]
    BincodeEncode(#[from] bincode::error::EncodeError),
    #[error(transparent)]
    BincodeDecode(#[from] bincode::error::DecodeError),
    #[error(transparent)]
    Ipc(#[from] IpcError),
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
    #[error("{} is not a submodule gitlink (its gitdir is not under .git/modules/)", .0.display())]
    NotSubmoduleGitlink(PathBuf),
    #[error("submodule name in {} is not valid UTF-8: {error}", path.display())]
    NonUtf8SubmoduleName {
        path: PathBuf,
        error: std::str::Utf8Error,
    },
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

const LOCKFILE_TIMEOUT: Duration = Duration::from_secs(10);

/// Creates a lock file at `path` that is removed on drop.
pub struct LockFileGuard<'a> {
    path: &'a Path,
}

/// Attempts to create the lock file atomically. Returns:
/// - `Ok(Some(guard))` if the file was created successfully
/// - `Ok(None)` if the file already exists (caller should retry)
/// - `Err(...)` if creation failed for another reason
fn try_create_lock(path: &Path) -> Result<Option<LockFileGuard<'_>>, LockFileError> {
    match fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
    {
        Ok(_) => Ok(Some(LockFileGuard { path })),
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => Ok(None),
        Err(e) => Err(LockFileError::new(path.to_path_buf(), e)),
    }
}

impl<'a> LockFileGuard<'a> {
    /// Creates a lock file at `path`. If it already exists, watches the
    /// parent directory for filesystem events and retries on each event.
    ///
    /// # Errors
    ///
    /// Returns `LockFileError` if the lock cannot be acquired within the
    /// timeout or the file cannot be created.
    ///
    /// # Panics
    ///
    /// Panics if `path` does not have a parent. This condition should never be reached.
    pub fn acquire(path: &'a Path) -> Result<Self, LockFileError> {
        // Fast path: lock file doesn't exist yet
        if let Some(guard) = try_create_lock(path)? {
            return Ok(guard);
        }

        // Contended: watch the parent directory for the lock file's removal.
        // We watch the parent (not the file itself) because notify has
        // platform-specific issues when a watched file is deleted.
        let deadline = Instant::now() + LOCKFILE_TIMEOUT;
        let lock_dir = path.parent().unwrap();

        let (tx, watcher_rx) = crossbeam_channel::unbounded();
        let log_path = lock_dir.to_path_buf();
        let mut watcher = ServerWatcher::new(
            move |res: Result<notify::Event, notify::Error>| {
                if let Err(e) = tx.send(res) {
                    error!(
                        "Lock file watcher for {} failed to send: {e}",
                        log_path.display()
                    );
                }
            },
            notify::Config::default(),
        )
        .map_err(|e| LockFileError::new(lock_dir.to_path_buf(), std::io::Error::other(e)))?;

        watcher
            .watch(lock_dir.as_ref(), RecursiveMode::NonRecursive)
            .map_err(|e| LockFileError::new(lock_dir.to_path_buf(), std::io::Error::other(e)))?;

        // Retry in case the lock was released while setting up the watcher
        if let Some(guard) = try_create_lock(path)? {
            return Ok(guard);
        }

        loop {
            match watcher_rx.recv_deadline(deadline) {
                Ok(Ok(event)) => {
                    if event.paths.iter().any(|p| p.eq(path))
                        && let Some(guard) = try_create_lock(path)?
                    {
                        return Ok(guard);
                    }
                }
                Ok(Err(e)) => error!("Lock file watcher error: {e}"),
                Err(crossbeam_channel::RecvTimeoutError::Timeout) => {
                    return Err(LockFileError::new(
                        path.to_path_buf(),
                        std::io::Error::new(
                            std::io::ErrorKind::TimedOut,
                            "timed out waiting for lock file",
                        ),
                    ));
                }
                Err(crossbeam_channel::RecvTimeoutError::Disconnected) => {
                    return Err(LockFileError::new(
                        lock_dir.to_path_buf(),
                        std::io::Error::other("lock file watcher disconnected"),
                    ));
                }
            }
        }
    }
}

impl Drop for LockFileGuard<'_> {
    fn drop(&mut self) {
        if let Err(e) = fs::remove_file(self.path) {
            error!(
                "Failed to release lock file at {}: {e}",
                self.path.display()
            );
        }
    }
}

/// Spawns the watch server as a fully detached background process for `path`.
///
/// The server is started by re-invoking the current executable with
/// `--subspy-internal start <path> --foreground`. The sentinel makes the
/// receiving process run subspy's CLI even when `current_exe()` resolves
/// to the `subspy-git` shim.
///
/// # Errors
///
/// Returns `std::io::Error` if the current executable path cannot be determined
/// or the child process cannot be spawned.
pub fn spawn_daemon(path: &Path, log_level: Option<&str>) -> std::io::Result<()> {
    let exe = std::env::current_exe()?;
    let mut cmd = build_daemon_command(&exe, path, log_level);
    crate::proc::configure_detached_daemon(&mut cmd);
    cmd.spawn()?;
    Ok(())
}

/// Builds the argv-pinned `Command` for the daemon child. Prepends
/// [`INTERNAL_FLAG`] so the receiving process runs subspy's CLI even
/// if `current_exe()` resolved to the `subspy-git` shim.
///
/// [`INTERNAL_FLAG`]: crate::entry::INTERNAL_FLAG
fn build_daemon_command(
    exe: &Path,
    repo_path: &Path,
    log_level: Option<&str>,
) -> std::process::Command {
    let mut cmd = std::process::Command::new(exe);
    cmd.arg(crate::entry::INTERNAL_FLAG)
        .arg("start")
        .arg(repo_path)
        .arg("--foreground")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if let Some(level) = log_level {
        cmd.args(["--log-level", level]);
    }
    cmd
}

#[cfg(test)]
mod daemon_command_tests {
    use super::build_daemon_command;
    use crate::entry::INTERNAL_FLAG;
    use std::ffi::OsStr;
    use std::path::Path;

    #[test]
    fn argv_starts_with_internal_flag_then_start_path_foreground() {
        let cmd = build_daemon_command(Path::new("/path/to/subspy"), Path::new("/repo/root"), None);
        let args: Vec<Option<&str>> = cmd.get_args().map(OsStr::to_str).collect();
        assert_eq!(args[0], Some(INTERNAL_FLAG));
        assert_eq!(args[1], Some("start"));
        assert_eq!(args[2], Some("/repo/root"));
        assert_eq!(args[3], Some("--foreground"));
        assert_eq!(args.len(), 4, "no extra args when log_level is None");
    }

    #[test]
    fn log_level_appended_when_provided() {
        let cmd = build_daemon_command(Path::new("/exe"), Path::new("/repo"), Some("debug"));
        let args: Vec<Option<&str>> = cmd.get_args().map(OsStr::to_str).collect();
        assert_eq!(args.last().copied().flatten(), Some("debug"));
        assert_eq!(args[args.len() - 2], Some("--log-level"));
    }
}
