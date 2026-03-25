//! Daemon lifecycle: spawning the background watch server process,
//! lock file management, and the top-level `watch` entry point.

use std::{
    fs,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use crossbeam_channel::TryRecvError;
use log::{error, trace};
use notify::{RecursiveMode, Watcher as _};
use thiserror::Error;

use crate::connection::watch_server::{ServerWatcher, watch};

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

/// Creates a cancellation pair for cooperative task cancellation.
///
/// The [`CancelHandle`] is held by the canceller (e.g. the task tracker).
/// The [`CancelToken`] is given to the cancellable task. Dropping the handle
/// disconnects the internal channel, which the token detects instantly via
/// [`CancelToken::is_cancelled`] or through `crossbeam_channel::Select`.
#[must_use]
pub fn cancel_pair() -> (CancelHandle, CancelToken) {
    let (tx, rx) = crossbeam_channel::bounded(0);
    (CancelHandle(tx), CancelToken(rx))
}

/// The canceller's end. Drop or call [`cancel`](Self::cancel) to signal
/// cancellation. The inner sender is never used directly; its `Drop` impl
/// disconnects the channel.
pub struct CancelHandle(#[expect(dead_code)] crossbeam_channel::Sender<()>);

impl CancelHandle {
    /// Signals cancellation by disconnecting the channel.
    pub fn cancel(self) {
        // Dropping self disconnects the sender, which the CancelToken detects.
    }
}

/// The cancellable task's end. Check [`is_cancelled`](Self::is_cancelled) or
/// use [`receiver`](Self::receiver) in a `crossbeam_channel::Select` to
/// detect cancellation without polling.
pub struct CancelToken(crossbeam_channel::Receiver<()>);

impl CancelToken {
    /// Returns `true` if the corresponding [`CancelHandle`] has been dropped.
    #[must_use]
    pub fn is_cancelled(&self) -> bool {
        matches!(self.0.try_recv(), Err(TryRecvError::Disconnected))
    }

    /// Returns the underlying receiver for use in `crossbeam_channel::Select`.
    #[must_use]
    pub const fn receiver(&self) -> &crossbeam_channel::Receiver<()> {
        &self.0
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
/// - `Err(...)` if creation failed for another reason or was cancelled
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
    /// If `cancel` is provided, the wait is aborted when the corresponding
    /// [`CancelHandle`] is dropped.
    ///
    /// # Errors
    ///
    /// Returns `LockFileError` if the lock cannot be acquired within the
    /// timeout, the wait is cancelled, or the file cannot be created.
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

        let deadline = Instant::now() + LOCKFILE_TIMEOUT;
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
        trace!("Releasing lock file at path: {}", self.path.display());
        if let Err(e) = fs::remove_file(self.path) {
            error!(
                "Failed to release lock file at {}: {e}",
                self.path.display()
            );
        }
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
