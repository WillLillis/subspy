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
use rustc_hash::FxHasher;
use thiserror::Error;

use crate::StatusSummary;

pub mod client;
mod client_handler;
pub mod watch_server;

/// Common bincode configuration used to encode/decode messages between the client and server
pub const BINCODE_CFG: bincode::config::Configuration<
    bincode::config::LittleEndian,
    bincode::config::Fixint,
> = bincode::config::standard()
    .with_fixed_int_encoding()
    .with_no_limit();

/// IPC protocol version. Bump when the wire format changes.
pub const IPC_VERSION: u8 = 0;

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub struct ClientRequest {
    pub version: u8,
    pub message: ClientMessage,
}

impl ClientRequest {
    #[must_use]
    pub const fn new(message: ClientMessage) -> Self {
        Self {
            version: IPC_VERSION,
            message,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ClientMessage {
    Reindex { pid: u32, replace_watchers: bool },
    Shutdown,
    Status(u32),
    Debug,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ServerMessage {
    Status(Vec<(String, StatusSummary)>),
    Indexing { curr: u32, total: u32 },
    ShutdownAck,
    DebugInfo(Box<DebugState>),
    VersionMismatch { server_version: u8 },
}

/// Error returned when the client and server IPC versions do not match.
#[derive(Clone, Debug, Error)]
pub struct VersionMismatchError {
    pub client_version: u8,
    pub server_version: u8,
}

impl std::fmt::Display for VersionMismatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "IPC version mismatch: client is version {}, server is version {}.\n\
             Stop the server with `subspy stop` (or kill the process) and retry.",
            self.client_version, self.server_version,
        )
    }
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
    pub socket_name: String,
    pub submodule_statuses: Option<Vec<(String, StatusSummary)>>,
    /// In-flight rayon tasks: `(relative_path, state)` where state is "active" or "dirty"
    pub in_flight: Option<Vec<(String, String)>>,
    /// Progress queues keyed by client PID: `(pid, [(curr, total)])`
    #[expect(clippy::type_complexity)]
    pub progress_queues: Option<Vec<(u32, Vec<(u32, u32)>)>>,
    /// The last watcher error that triggered a reindex, if any
    pub last_watcher_error: Option<String>,
}

/// Writes all of `msg` to `conn`, prepended by the length as a LE u32.
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

/// Reads from `conn` into `buffer` expecting the message length as a LE u32 first.
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
    let name = ipc_name_string(path);
    if GenericNamespaced::is_supported() {
        name.to_ns_name::<GenericNamespaced>()
    } else {
        name.to_fs_name::<GenericFilePath>()
    }
}

/// Returns the raw socket name string for a given repository path.
#[must_use]
pub fn ipc_name_string(path: &Path) -> String {
    let mut hasher = FxHasher::default();
    path.hash(&mut hasher);
    let hash = hasher.finish();
    if GenericNamespaced::is_supported() {
        format!("{hash}.sock")
    } else {
        format!("/tmp/{hash}.sock")
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
