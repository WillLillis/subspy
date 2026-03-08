//! Client-server implementation
use core::hash::{Hash as _, Hasher as _};
use std::{
    io::{BufReader, Read, Write as _},
    path::Path,
    sync::{Mutex, MutexGuard, TryLockError},
    time::{Duration, Instant},
};

use bincode::{BorrowDecode, Encode};
use interprocess::local_socket::{
    GenericFilePath, GenericNamespaced, Listener, ListenerOptions, Name, NameType as _, Stream,
    ToFsName as _, ToNsName as _,
};

use crate::{FullRepoStatus, StatusSummary};

pub mod client;
mod client_handler;
pub mod watch_server;

/// Common bincode configuration used to encode/decode messages between the client and server
pub const BINCODE_CFG: bincode::config::Configuration = bincode::config::standard().with_no_limit();

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ClientMessage {
    Reindex { pid: u32, replace_watchers: bool },
    Shutdown,
    Status(u32),
    Debug,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ServerMessage {
    Status(Box<FullRepoStatus>),
    Indexing { curr: u32, total: u32 },
    ShutdownAck,
    DebugInfo(DebugState),
}

/// Diagnostic snapshot of the watch server's internal state
#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub struct DebugState {
    pub server_pid: u32,
    pub rayon_threads: u32,
    pub progress_subscribers: Option<Vec<u32>>,
    pub watcher_count: u32,
    pub watched_paths: Vec<(String, String, u32)>,
    pub skip_set: Vec<String>,
    pub root_rebasing: bool,
    pub root_path: String,
    pub submodule_statuses: Option<Vec<(String, StatusSummary)>>,
    /// In-flight rayon tasks: `(relative_path, state)` where state is "active" or "dirty"
    pub in_flight: Option<Vec<(String, String)>>,
    /// Progress queues keyed by client PID: `(pid, [(curr, total)])`
    #[expect(clippy::type_complexity)]
    pub progress_queues: Option<Vec<(u32, Vec<(u32, u32)>)>>,
    /// The last watcher error that triggered a reindex, if any
    pub last_watcher_error: Option<String>,
}

/// Writes all of `msg` to `conn`, followed by `MSG_DELIM`
///
/// # Errors
///
/// Returns `std::io::Error` if writing to `conn` fails
#[inline]
pub fn write_full_message(conn: &mut BufReader<Stream>, msg: &[u8]) -> std::io::Result<()> {
    let len_bytes = (msg.len() as u32).to_le_bytes();
    conn.get_mut().write_all(&len_bytes)?;
    conn.get_mut().write_all(msg)?;

    Ok(())
}

/// Reads from `conn` into `buffer` until the delimiter `MSG_DELIM` is found.
/// `buffer` is cleared immediately. After reading, `MSG_DELIM` is stripped from `buffer`
/// before returning.
///
/// # Errors
///
/// Returns `std::io::Error` if reading fails
pub fn read_full_message(
    conn: &mut BufReader<Stream>,
    buffer: &mut Vec<u8>,
) -> std::io::Result<()> {
    buffer.clear();

    let msg_len = {
        let mut len_buf = [0u8; 4];
        conn.read_exact(&mut len_buf)?;
        u32::from_le_bytes(len_buf) as usize
    };

    let additional_size = msg_len.saturating_sub(buffer.capacity());
    buffer.reserve_exact(additional_size);
    // `buffer` length is set to 0, so resizing fills it with 0s
    buffer.resize(msg_len, 0);
    conn.read_exact(buffer)?;

    Ok(())
}

/// Returns the `interprocess::local_socket::name::Name` used to communicate between
/// the watch server and request clients for a given git project at `path`.
///
/// # Errors
///
/// Returns `std::io::Error` if socket name isn't supported by the given platform
pub fn ipc_name(path: &Path) -> std::io::Result<Name<'_>> {
    let mut hasher = std::hash::DefaultHasher::new();
    path.hash(&mut hasher);
    let hash = hasher.finish();
    let base_name = hash.to_string();
    if GenericNamespaced::is_supported() {
        format!("{base_name}.sock").to_ns_name::<GenericNamespaced>()
    } else {
        format!("/tmp/{base_name}.sock").to_fs_name::<GenericFilePath>()
    }
}

/// Creates a new listener for incoming client connections to the watch server for `root_dir`.
///
/// # Errors
///
/// Returns `std::io::Error` if the ipc name or listener cannot be created
pub fn create_listener(root_dir: &Path) -> std::io::Result<Listener> {
    let name = ipc_name(root_dir)?;
    let opts = ListenerOptions::new().name(name);
    let listener = match opts.create_sync() {
        Err(e) if e.kind() == std::io::ErrorKind::AddrInUse => Err(std::io::Error::new(
            std::io::ErrorKind::AddrInUse,
            format!(
                "Could not start watch server because the socket file is occupied. Is there already a watcher placed on {}?",
                root_dir.display()
            ),
        ))?,
        x => x?,
    };

    Ok(listener)
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

/// Attempts to acquire `mutex` without blocking.
///
/// # Panics
///
/// Panics if `mutex` has been poisoned
fn try_lock<T>(mutex: &Mutex<T>) -> Option<MutexGuard<'_, T>> {
    try_lock_for(mutex, Duration::ZERO)
}

/// Attempts to acquire `mutex` within `timeout`, polling with `try_lock`.
/// Returns `None` if the timeout elapses without acquiring the lock.
///
/// # Panics
///
/// Panics if `mutex` has been poisoned
#[inline]
fn try_lock_for<T>(mutex: &Mutex<T>, timeout: Duration) -> Option<MutexGuard<'_, T>> {
    let start = Instant::now();
    loop {
        match mutex.try_lock() {
            Ok(guard) => return Some(guard),
            Err(TryLockError::WouldBlock) => {
                if start.elapsed() >= timeout {
                    return None;
                }
                std::thread::yield_now();
            }
            Err(TryLockError::Poisoned(_)) => panic!("Mutex poisoned"),
        }
    }
}
