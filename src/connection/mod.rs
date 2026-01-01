//! Client-server implementation
use std::{
    hash::{Hash as _, Hasher as _},
    io::{BufRead as _, BufReader, Write as _},
    path::{Path, PathBuf},
};

use bincode::{BorrowDecode, Encode};
use interprocess::local_socket::{
    GenericFilePath, GenericNamespaced, Listener, ListenerOptions, Name, NameType as _, Stream,
    ToFsName as _, ToNsName as _,
};

use crate::{DOT_GIT, StatusSummary, reindex::REINDEX_FILE_PREFIX, shutdown::SHUTDOWN_FILE_PREFIX};

pub mod client;
pub mod watch_server;

pub const BINCODE_CFG: bincode::config::Configuration = bincode::config::standard().with_no_limit();

const MSG_DELIM: [u8; 4] = [u8::MAX, u8::MAX, u8::MAX, u8::MAX];

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ClientMessage {
    Reindex(u32),
    Status(u32),
    Shutdown(u32),
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ServerMessage {
    Status(Vec<(String, StatusSummary)>),
    Indexing { curr: u32, total: u32 },
}

/// Writes all of `msg` to `conn`, followed by `MSG_DELIM`
///
/// # Errors
///
/// Returns `std::io::Error` if writing to `conn` fails
pub fn write_full_message(conn: &mut BufReader<Stream>, msg: &[u8]) -> std::io::Result<()> {
    conn.get_mut().write_all(msg)?;
    conn.get_mut().write_all(&MSG_DELIM)?;

    Ok(())
}

/// Checks whether `msg` ends with `MSG_DELIM`
fn has_delimiter(msg: &[u8]) -> bool {
    let len = msg.len();
    if len <= MSG_DELIM.len() {
        return false;
    }

    [
        msg.get(len - 4).copied(),
        msg.get(len - 3).copied(),
        msg.get(len - 2).copied(),
        msg.get(len - 1).copied(),
    ] == [
        Some(MSG_DELIM[0]),
        Some(MSG_DELIM[1]),
        Some(MSG_DELIM[2]),
        Some(MSG_DELIM[3]),
    ]
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
    while !has_delimiter(buffer) {
        conn.read_until(u8::MAX, buffer)?;
    }

    for _ in 0..MSG_DELIM.len() {
        buffer.pop();
    }

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

/// Returns reindex sentinel file path for the repository at `root_dir`.
#[must_use]
pub fn get_reindex_file_path(root_dir: &Path, client_pid: u32) -> PathBuf {
    let mut reindex_path = root_dir.to_path_buf();
    reindex_path.push(DOT_GIT);
    let reindex_file_name = format!("{REINDEX_FILE_PREFIX}{client_pid}");
    reindex_path.push(reindex_file_name);
    reindex_path
}

/// Returns shutdown sentinel file path for the repository at `root_dir`.
#[must_use]
pub fn get_shutdown_file_path(root_dir: &Path, client_pid: u32) -> PathBuf {
    let mut reindex_path = root_dir.to_path_buf();
    let reindex_file_name = format!("{SHUTDOWN_FILE_PREFIX}{client_pid}");
    reindex_path.push(reindex_file_name);
    reindex_path
}
