//! Client-server implementation
use core::hash::{Hash as _, Hasher as _};
use std::{
    io::{BufReader, Read, Write as _},
    path::Path,
};

use bincode::{BorrowDecode, Encode};
use interprocess::local_socket::{
    GenericFilePath, GenericNamespaced, Listener, ListenerOptions, Name, NameType as _, Stream,
    ToFsName as _, ToNsName as _,
};

use crate::StatusSummary;

pub mod client;
pub mod watch_server;

/// Common bincode configuration used to encode/decode messages between the client and server
pub const BINCODE_CFG: bincode::config::Configuration = bincode::config::standard().with_no_limit();

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ClientMessage {
    Reindex(u32),
    Shutdown,
    Status(u32),
    Debug,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ServerMessage {
    Status(Vec<(String, StatusSummary)>),
    Indexing { curr: u32, total: u32 },
    ShutdownAck,
    DebugInfo(DebugState),
}

/// Diagnostic snapshot of the watch server's internal state
#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub struct DebugState {
    pub server_pid: u32,
    pub rayon_threads: u32,
    pub progress_subscribers: Vec<u32>,
    pub watcher_count: u32,
    pub watched_paths: Vec<(String, String)>,
    pub skip_set: Vec<String>,
    pub root_rebasing: bool,
    pub root_path: String,
    pub submodule_statuses: Vec<(String, StatusSummary)>,
    /// In-flight rayon tasks: `(relative_path, state)` where state is "active" or "dirty"
    pub in_flight: Vec<(String, String)>,
    /// Progress queues keyed by client PID: `(pid, [(curr, total)])`
    pub progress_queues: Vec<(u32, Vec<(u32, u32)>)>,
}

/// Writes all of `msg` to `conn`, followed by `MSG_DELIM`
///
/// # Errors
///
/// Returns `std::io::Error` if writing to `conn` fails
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
