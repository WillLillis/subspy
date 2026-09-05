//! Platform-specific IPC sockets and length-prefixed message framing: the
//! transport that moves framed messages in and out over the local socket.

use core::hash::{Hash as _, Hasher as _};
use std::{
    ffi::{OsStr, OsString},
    io::{BufReader, Read, Write as _},
    path::Path,
    time::Duration,
};

use bincode::Encode;
#[cfg(not(target_os = "windows"))]
use interprocess::local_socket::{
    GenericFilePath, GenericNamespaced, ListenerOptions, Name, ToFsName as _, ToNsName as _,
};
use rustc_hash::FxHasher;

use super::{BINCODE_CFG, IpcResult};

pub(super) const SOCKET_NAME_PREFIX: &str = "subspy-";
pub(super) const SOCKET_NAME_SUFFIX: &str = ".sock";

// Platform-specific IPC stream and listener types.
//
// On Unix, we use interprocess's local sockets (Unix domain sockets).
// On Windows, interprocess only supports named pipes, which lack native
// read timeouts (SO_RCVTIMEO). We use uds_windows instead, which provides
// AF_UNIX sockets with full timeout support.
//
// Once std gains Unix domain socket support on Windows (rust-lang/rust#56533),
// interprocess can adopt it (kotauskas/interprocess#45) and we can drop
// uds_windows in favor of a single interprocess backend on all platforms.
#[cfg(not(target_os = "windows"))]
pub type IpcStream = interprocess::local_socket::Stream;
#[cfg(target_os = "windows")]
pub type IpcStream = uds_windows::UnixStream;

#[cfg(not(target_os = "windows"))]
pub type IpcListener = interprocess::local_socket::Listener;
#[cfg(target_os = "windows")]
pub type IpcListener = uds_windows::UnixListener;

/// Whether IPC uses filesystem sockets that need manual cleanup.
///
/// Only Linux and Android have an abstract namespace, where the kernel drops the
/// socket when the owning process exits. Everywhere else a socket is a file in
/// the temp directory that outlives a crashed server.
#[must_use]
pub const fn uses_filesystem_sockets() -> bool {
    cfg!(not(any(target_os = "linux", target_os = "android")))
}

/// Returns `true` if the error indicates no server is listening.
///
/// Covers the common cases: no socket exists (`NotFound`), server not
/// accepting (`ConnectionRefused`), and stale/dead sockets that produce
/// `ConnectionReset` or `ConnectionAborted`. On Windows, `WSAEINVAL`
/// (error 10022) from a stale `AF_UNIX` socket file is also treated as
/// retryable.
#[inline]
#[must_use]
pub fn server_not_started(error: &std::io::Error) -> bool {
    if matches!(
        error.kind(),
        std::io::ErrorKind::ConnectionRefused
            | std::io::ErrorKind::NotFound
            | std::io::ErrorKind::ConnectionReset
            | std::io::ErrorKind::ConnectionAborted
    ) {
        return true;
    }

    #[cfg(target_os = "windows")]
    {
        const WSAEINVAL: i32 = 10022;
        if error.raw_os_error() == Some(WSAEINVAL) {
            return true;
        }
    }

    false
}

/// Sets the receive timeout on the IPC stream.
///
/// # Errors
///
/// Returns `std::io::Error` if the timeout cannot be set.
#[cfg(not(target_os = "windows"))]
pub fn set_recv_timeout(stream: &IpcStream, timeout: Option<Duration>) -> std::io::Result<()> {
    use interprocess::local_socket::traits::Stream as _;
    stream.set_recv_timeout(timeout)
}

/// Sets the receive timeout on the IPC stream.
///
/// # Errors
///
/// Returns `std::io::Error` if the timeout cannot be set.
#[cfg(target_os = "windows")]
pub fn set_recv_timeout(stream: &IpcStream, timeout: Option<Duration>) -> std::io::Result<()> {
    stream.set_read_timeout(timeout)
}

/// Size of the LE u32 length prefix prepended to every IPC message.
pub(super) const MSG_PREFIX_LEN: usize = size_of::<u32>();

/// Maximum encoded size of a fixed-size IPC message stored in a stack buffer.
/// The largest is `ServerMessage::Indexing { u32, u32 }` at 12 bytes.
pub(super) const MAX_FIXED_MSG_LEN: usize = 12;

/// Stack buffer size for [`write_full_message_fixed`]'s single-write fast path.
const INLINE_WRITE_BUF_LEN: usize = MSG_PREFIX_LEN + MAX_FIXED_MSG_LEN;

/// Encodes `msg` into `buf` with a LE u32 length prefix and writes the
/// entire framed message to `conn` in a single `write_all` call.
///
/// `buf` is cleared and reused to avoid allocating on every call. The
/// length prefix is reserved up front, the message is encoded after it,
/// and the prefix is backfilled before writing.
///
/// # Errors
///
/// Returns `Err` if bincode encoding or writing to `conn` fails.
pub fn encode_and_write(
    conn: &mut BufReader<IpcStream>,
    msg: impl Encode,
    buf: &mut Vec<u8>,
) -> IpcResult<()> {
    buf.clear();
    buf.extend_from_slice(&[0u8; MSG_PREFIX_LEN]);
    let msg_len = bincode::encode_into_std_write(msg, buf, BINCODE_CFG)? as u32;
    buf[..MSG_PREFIX_LEN].copy_from_slice(&msg_len.to_le_bytes());
    conn.get_mut().write_all(buf)?;
    Ok(())
}

/// Writes a fixed-size `msg` to `conn`, prepended by the length as a LE u32.
///
/// The length prefix and body are combined into a single `write_all` call
/// via a stack buffer.
///
/// # Errors
///
/// Returns `std::io::Error` if writing to `conn` fails.
///
/// # Panics
///
/// Debug-panics if `msg` exceeds [`MAX_FIXED_MSG_LEN`] bytes.
#[inline]
pub fn write_full_message_fixed(
    conn: &mut BufReader<IpcStream>,
    msg: &[u8],
) -> std::io::Result<()> {
    debug_assert!(
        msg.len() <= MAX_FIXED_MSG_LEN,
        "Message length {} exceeds MAX_FIXED_MSG_LEN ({MAX_FIXED_MSG_LEN})",
        msg.len(),
    );
    let len_bytes = (msg.len() as u32).to_le_bytes();
    let mut buf = [0u8; INLINE_WRITE_BUF_LEN];
    buf[..MSG_PREFIX_LEN].copy_from_slice(&len_bytes);
    buf[MSG_PREFIX_LEN..MSG_PREFIX_LEN + msg.len()].copy_from_slice(msg);
    conn.get_mut().write_all(&buf[..MSG_PREFIX_LEN + msg.len()])
}

/// Reads a length-prefixed message into a stack buffer of size `N`.
///
/// Returns the payload length in bytes. The caller caller accesses it
/// through `&buffer[..len]`.
///
/// # Errors
///
/// Returns [`std::io::Error`] if reading fails.
///
/// # Panics
///
/// Debug-panics if the incoming message length exceeds `N`.
pub fn read_full_message_fixed<const N: usize>(
    conn: &mut BufReader<IpcStream>,
    buffer: &mut [u8; N],
) -> std::io::Result<usize> {
    let mut len_buf = [0u8; 4];
    conn.read_exact(&mut len_buf)?;
    let msg_len = u32::from_le_bytes(len_buf) as usize;
    debug_assert!(
        msg_len <= N,
        "Message length {msg_len} exceeds buffer size {N}"
    );
    conn.read_exact(&mut buffer[..msg_len])?;
    Ok(msg_len)
}

/// Reads from `conn` into `buffer` expecting the message length as a LE u32 first.
///
/// The caller is responsible for setting any socket timeout via
/// [`set_recv_timeout`] before calling this function.
///
/// # Errors
///
/// Returns `std::io::Error` if reading fails or the timeout elapses.
pub fn read_full_message(
    conn: &mut BufReader<IpcStream>,
    buffer: &mut Vec<u8>,
) -> std::io::Result<()> {
    buffer.clear();
    let msg_len = {
        let mut len_buf = [0u8; 4];
        conn.read_exact(&mut len_buf)?;
        u32::from_le_bytes(len_buf) as usize
    };
    // SAFETY: `read_exact` will fill exactly `msg_len` bytes, so there's no
    // risk of reading uninitialized memory. We set the length first so
    // `read_exact` can write directly into the buffer without a redundant
    // zero-fill from `resize`.
    #[expect(
        clippy::uninit_vec,
        reason = "read_exact fills the buffer before it's read"
    )]
    {
        buffer.reserve(msg_len);
        unsafe {
            buffer.set_len(msg_len);
        };
    }
    conn.read_exact(buffer)
}

/// Returns the socket path used for IPC on the current platform.
///
/// On Unix with namespace support, returns a short name like `subspy-{hash}.sock`.
/// On Unix without namespace support or on Windows, returns a filesystem path
/// like `{tmpdir}/subspy-{hash}.sock`.
#[must_use]
pub fn ipc_socket_path(path: &Path) -> OsString {
    let mut hasher = FxHasher::default();
    path.hash(&mut hasher);
    let hash = hasher.finish();

    if !uses_filesystem_sockets() {
        return socket_name(hash).into();
    }

    let mut sock_path = std::env::temp_dir();
    sock_path.push(socket_name(hash));
    sock_path.into_os_string()
}

fn socket_name(hash: u64) -> String {
    format!("{SOCKET_NAME_PREFIX}{hash}{SOCKET_NAME_SUFFIX}")
}

/// Converts a socket path string into an `interprocess` `Name`.
#[cfg(not(target_os = "windows"))]
fn ipc_name(sock_path: &OsStr) -> std::io::Result<Name<'_>> {
    if uses_filesystem_sockets() {
        sock_path.to_fs_name::<GenericFilePath>()
    } else {
        sock_path.to_ns_name::<GenericNamespaced>()
    }
}

/// Connects to the IPC socket at the given socket path (as returned by
/// [`ipc_socket_path`]).
///
/// # Errors
///
/// Returns `std::io::Error` if the connection cannot be established.
pub fn ipc_connect(sock_path: &OsStr) -> std::io::Result<IpcStream> {
    #[cfg(not(target_os = "windows"))]
    {
        use interprocess::local_socket::traits::Stream as _;
        let name = ipc_name(sock_path)?;
        IpcStream::connect(name)
    }
    #[cfg(target_os = "windows")]
    {
        IpcStream::connect(sock_path)
    }
}

/// Creates a new listener for incoming client connections to the watch server for `root_dir`.
///
/// On platforms using filesystem sockets (Windows, or Unix without namespace
/// support), a stale socket file from a crashed server is detected and removed
/// automatically.
///
/// # Errors
///
/// Returns `std::io::Error` if the listener cannot be created.
pub fn create_listener(root_dir: &Path) -> std::io::Result<IpcListener> {
    let sock_path = ipc_socket_path(root_dir);
    let addr_in_use_err = || {
        std::io::Error::new(
            std::io::ErrorKind::AddrInUse,
            format!(
                "Could not start watch server because the socket file is occupied. \
                 Is there already a watcher placed on {}?",
                root_dir.display()
            ),
        )
    };

    #[cfg(not(target_os = "windows"))]
    {
        let name = ipc_name(&sock_path)?;
        let opts = ListenerOptions::new().name(name);
        match opts.create_sync() {
            Ok(listener) => Ok(listener),
            Err(e) if e.kind() == std::io::ErrorKind::AddrInUse => {
                if uses_filesystem_sockets()
                    && ipc_connect(&sock_path).is_err_and(|error| server_not_started(&error))
                    && std::fs::remove_file(&sock_path).is_ok()
                {
                    let name = ipc_name(&sock_path)?;
                    Ok(ListenerOptions::new().name(name).create_sync()?)
                } else {
                    Err(addr_in_use_err())
                }
            }
            Err(e) => Err(e),
        }
    }
    #[cfg(target_os = "windows")]
    {
        match uds_windows::UnixListener::bind(&sock_path) {
            Ok(listener) => Ok(listener),
            Err(e) if e.kind() == std::io::ErrorKind::AddrInUse => {
                if uses_filesystem_sockets()
                    && ipc_connect(&sock_path).is_err_and(|error| server_not_started(&error))
                    && std::fs::remove_file(&sock_path).is_ok()
                {
                    Ok(uds_windows::UnixListener::bind(&sock_path)?)
                } else {
                    Err(addr_in_use_err())
                }
            }
            Err(e) => Err(e),
        }
    }
}

/// Removes the socket file for `root_dir` if it exists on the filesystem.
/// No-op on platforms using abstract/namespaced sockets.
pub fn cleanup_socket(root_dir: &Path) {
    if !uses_filesystem_sockets() {
        return;
    }
    let sock_path = ipc_socket_path(root_dir);
    let _ = std::fs::remove_file(&sock_path);
}
