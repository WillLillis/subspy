//! IPC types, message framing, and socket management shared between the
//! watch server and its clients.
use core::hash::{Hash as _, Hasher as _};
use std::{
    io::{BufReader, Read, Write as _},
    path::Path,
    sync::{Mutex, MutexGuard, TryLockError},
    time::{Duration, Instant},
};

use bincode::{BorrowDecode, Encode};
#[cfg(not(target_os = "windows"))]
use interprocess::local_socket::{
    GenericFilePath, GenericNamespaced, ListenerOptions, Name, NameType as _, ToFsName as _,
    ToNsName as _,
};
use rustc_hash::FxHasher;
use thiserror::Error;

use crate::StatusSummary;

pub mod client;
mod client_handler;
pub mod watch_server;

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
    Status {
        statuses: Vec<(String, StatusSummary)>,
        total: u32,
    },
    Indexing {
        curr: u32,
        total: u32,
    },
    ShutdownAck,
    DebugInfo(Box<DebugState>),
    VersionMismatch {
        server_version: u8,
    },
}

/// Errors that can occur during client-server IPC communication.
#[derive(Debug, Error)]
pub enum IpcError {
    #[error(transparent)]
    BincodeEncode(#[from] bincode::error::EncodeError),
    #[error(transparent)]
    BincodeDecode(#[from] bincode::error::DecodeError),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    VersionMismatch(#[from] VersionMismatchError),
}

pub type IpcResult<T> = Result<T, IpcError>;

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
    /// In-flight rayon tasks: `(relative_path, state)` where state is
    /// "active", "active (cancelling)", "dirty", or "dirty (cancelling)"
    pub in_flight: Option<Vec<(String, String)>>,
    /// Progress queues keyed by client PID: `(pid, [(curr, total)])`
    #[expect(clippy::type_complexity)]
    pub progress_queues: Option<Vec<(u32, Vec<(u32, u32)>)>>,
    /// The last watcher error that triggered a reindex, if any
    pub last_watcher_error: Option<String>,
    /// Non-recursive tripwire watches on submodule ancestor directories:
    /// `(watch_path, pending_event_count)`.
    pub tripwires: Vec<(String, u32)>,
}

/// Returns `true` if IPC uses filesystem sockets that need manual cleanup.
#[cfg(target_os = "windows")]
#[must_use]
pub const fn uses_filesystem_sockets() -> bool {
    true // uds_windows always uses filesystem sockets
}

/// Returns `true` if IPC uses filesystem sockets that need manual cleanup.
#[cfg(not(target_os = "windows"))]
#[must_use]
pub fn uses_filesystem_sockets() -> bool {
    !GenericNamespaced::is_supported()
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

/// Maximum encoded size of any fixed-size IPC message (i.e. messages that
/// use stack buffers rather than `Vec`s). Currently the largest is
/// `ServerMessage::Indexing { u32, u32 }` at 12 bytes.
///
/// [`write_full_message`] uses this to combine the length prefix and body
/// into a single `write_all` call, requiring one syscall instead of two.
const MAX_FIXED_MSG_LEN: usize = 12;

/// Stack buffer size for [`write_full_message`]'s single-write fast path.
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
/// Returns the number of bytes in the message (not including the prefix).
/// The caller should use `&buffer[..len]` to access the message.
///
/// # Errors
///
/// Returns `std::io::Error` if reading fails.
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
/// On Unix with namespace support, returns a short name like `{hash}.sock`.
/// On Unix without namespace support or on Windows, returns a filesystem
/// path like `/tmp/{hash}.sock` or `%TEMP%\{hash}.sock`.
#[must_use]
pub fn ipc_socket_path(path: &Path) -> String {
    let mut hasher = FxHasher::default();
    path.hash(&mut hasher);
    let hash = hasher.finish();

    #[cfg(not(target_os = "windows"))]
    if GenericNamespaced::is_supported() {
        return format!("{hash}.sock");
    }

    #[cfg(target_os = "windows")]
    {
        let temp = std::env::temp_dir();
        format!("{}\\{hash}.sock", temp.display())
    }

    #[cfg(not(target_os = "windows"))]
    format!("/tmp/{hash}.sock")
}

/// Converts a socket path string into an `interprocess` `Name`.
#[cfg(not(target_os = "windows"))]
fn ipc_name(sock_path: &str) -> std::io::Result<Name<'_>> {
    if GenericNamespaced::is_supported() {
        sock_path.to_string().to_ns_name::<GenericNamespaced>()
    } else {
        sock_path.to_string().to_fs_name::<GenericFilePath>()
    }
}

/// Connects to the IPC socket at the given socket path (as returned by
/// [`ipc_socket_path`]).
///
/// # Errors
///
/// Returns `std::io::Error` if the connection cannot be established.
pub fn ipc_connect(sock_path: &str) -> std::io::Result<IpcStream> {
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
                    && ipc_connect(&sock_path).is_err()
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
                    && ipc_connect(&sock_path).is_err()
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_variant_sizes() {
        let cases: &[(&str, Vec<u8>)] = &[
            (
                "ServerMessage::ShutdownAck",
                bincode::encode_to_vec(ServerMessage::ShutdownAck, BINCODE_CFG).unwrap(),
            ),
            (
                "ClientMessage::Shutdown",
                bincode::encode_to_vec(ClientMessage::Shutdown, BINCODE_CFG).unwrap(),
            ),
            (
                "ClientMessage::Debug",
                bincode::encode_to_vec(ClientMessage::Debug, BINCODE_CFG).unwrap(),
            ),
        ];

        for (name, encoded) in cases {
            assert_eq!(
                encoded.len(),
                4,
                "Expected {name} to encode to 4 bytes, got {} bytes",
                encoded.len(),
            );
        }
    }

    /// Verifies that the worst-case encoded sizes of `ClientRequest` and
    /// `ServerMessage::Indexing` / `VersionMismatch` fit within the stack
    /// buffers used to encode/decode them in `client.rs` and `client_handler.rs`.
    #[test]
    fn max_message_sizes() {
        // ClientRequest wrapping Reindex with max u32 is the largest request
        let reindex_max = bincode::encode_to_vec(
            ClientRequest::new(ClientMessage::Reindex {
                pid: u32::MAX,
                replace_watchers: true,
            }),
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            reindex_max.len() <= 10,
            "ClientRequest(Reindex(u32::MAX, true)) encoded to {} bytes, exceeds buffer size of 10",
            reindex_max.len(),
        );

        // ClientRequest wrapping Status with max u32
        let status_max = bincode::encode_to_vec(
            ClientRequest::new(ClientMessage::Status(u32::MAX)),
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            status_max.len() <= 10,
            "ClientRequest(Status(u32::MAX)) encoded to {} bytes, exceeds buffer size of 10",
            status_max.len(),
        );

        // ServerMessage::Indexing with max values (used in try_send_progress_update)
        let indexing_max = bincode::encode_to_vec(
            ServerMessage::Indexing {
                curr: u32::MAX,
                total: u32::MAX,
            },
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            indexing_max.len() <= 12,
            "ServerMessage::Indexing(u32::MAX, u32::MAX) encoded to {} bytes, exceeds buffer size of 12",
            indexing_max.len(),
        );

        // ServerMessage::VersionMismatch with max u8
        let mismatch_max = bincode::encode_to_vec(
            ServerMessage::VersionMismatch {
                server_version: u8::MAX,
            },
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            mismatch_max.len() <= 5,
            "ServerMessage::VersionMismatch(u8::MAX) encoded to {} bytes, exceeds buffer size of 5",
            mismatch_max.len(),
        );
    }

    /// Asserts that every fixed-size IPC message fits within
    /// [`MAX_FIXED_MSG_LEN`], ensuring [`write_full_message`] uses the
    /// single-write fast path for all of them.
    #[test]
    fn fixed_messages_fit_inline_write_buffer() {
        use crate::connection::MAX_FIXED_MSG_LEN;

        let fixed_messages: &[(&str, Vec<u8>)] = &[
            (
                "ClientRequest(Reindex)",
                bincode::encode_to_vec(
                    ClientRequest::new(ClientMessage::Reindex {
                        pid: u32::MAX,
                        replace_watchers: true,
                    }),
                    BINCODE_CFG,
                )
                .unwrap(),
            ),
            (
                "ClientRequest(Shutdown)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Shutdown), BINCODE_CFG)
                    .unwrap(),
            ),
            (
                "ClientRequest(Status)",
                bincode::encode_to_vec(
                    ClientRequest::new(ClientMessage::Status(u32::MAX)),
                    BINCODE_CFG,
                )
                .unwrap(),
            ),
            (
                "ClientRequest(Debug)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Debug), BINCODE_CFG)
                    .unwrap(),
            ),
            (
                "ServerMessage::Indexing",
                bincode::encode_to_vec(
                    ServerMessage::Indexing {
                        curr: u32::MAX,
                        total: u32::MAX,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
            ),
            (
                "ServerMessage::ShutdownAck",
                bincode::encode_to_vec(ServerMessage::ShutdownAck, BINCODE_CFG).unwrap(),
            ),
            (
                "ServerMessage::VersionMismatch",
                bincode::encode_to_vec(
                    ServerMessage::VersionMismatch {
                        server_version: u8::MAX,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
            ),
        ];

        for (name, encoded) in fixed_messages {
            assert!(
                encoded.len() <= MAX_FIXED_MSG_LEN,
                "{name} encoded to {} bytes, exceeds MAX_FIXED_MSG_LEN ({MAX_FIXED_MSG_LEN}). \
                 Increase the constant or the message will use two syscalls.",
                encoded.len(),
            );
        }
    }

    #[test]
    fn client_request_round_trip() {
        let request = ClientRequest::new(ClientMessage::Status(42));
        let encoded = bincode::encode_to_vec(&request, BINCODE_CFG).unwrap();
        let (decoded, _): (ClientRequest, usize) =
            bincode::borrow_decode_from_slice(&encoded, BINCODE_CFG).unwrap();
        assert_eq!(request, decoded);
    }

    #[test]
    fn version_mismatch_round_trip() {
        let msg = ServerMessage::VersionMismatch { server_version: 7 };
        let encoded = bincode::encode_to_vec(&msg, BINCODE_CFG).unwrap();
        let (decoded, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&encoded, BINCODE_CFG).unwrap();
        assert_eq!(msg, decoded);
    }

    /// Hardcoded byte sequences for every IPC message variant. If any of these
    /// change, the wire format has broken: bump `IPC_VERSION` and update the
    /// expected byte slices to match the actual bytes shown in the failure output.
    #[test]
    #[allow(clippy::too_many_lines)]
    fn wire_format_stability() {
        use crate::{StatusSummary, connection::DebugState};

        let cases: &[(&str, Vec<u8>, &[u8])] = &[
            // -- ClientRequest variants --
            (
                "ClientRequest(Reindex { pid: 1, replace_watchers: false })",
                bincode::encode_to_vec(
                    ClientRequest::new(ClientMessage::Reindex {
                        pid: 1,
                        replace_watchers: false,
                    }),
                    BINCODE_CFG,
                )
                .unwrap(),
                // version(0) | variant(0,0,0,0) | pid(1,0,0,0) | bool(0)
                &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
            ),
            (
                "ClientRequest(Shutdown)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Shutdown), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(1,0,0,0)
                &[0, 1, 0, 0, 0],
            ),
            (
                "ClientRequest(Status(42))",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Status(42)), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(2,0,0,0) | pid(42,0,0,0)
                &[0, 2, 0, 0, 0, 42, 0, 0, 0],
            ),
            (
                "ClientRequest(Debug)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Debug), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(3,0,0,0)
                &[0, 3, 0, 0, 0],
            ),
            // -- ServerMessage variants --
            (
                "ServerMessage::Status(empty, total=0)",
                bincode::encode_to_vec(
                    ServerMessage::Status {
                        statuses: vec![],
                        total: 0,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(0,0,0,0) | vec_len(0,0,0,0,0,0,0,0) | total(0,0,0,0)
                &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            ),
            (
                "ServerMessage::Status(one entry, total=3)",
                bincode::encode_to_vec(
                    ServerMessage::Status {
                        statuses: vec![("sub".to_string(), StatusSummary::MODIFIED_CONTENT)],
                        total: 3,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(0,0,0,0) | vec_len(1,0,0,0,0,0,0,0)
                // | str_len(3,0,0,0,0,0,0,0) | "sub" | flags(1)
                // | total(3,0,0,0)
                &[
                    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, b's', b'u', b'b',
                    1, 3, 0, 0, 0,
                ],
            ),
            (
                "ServerMessage::Indexing { curr: 5, total: 10 }",
                bincode::encode_to_vec(ServerMessage::Indexing { curr: 5, total: 10 }, BINCODE_CFG)
                    .unwrap(),
                // variant(1,0,0,0) | curr(5,0,0,0) | total(10,0,0,0)
                &[1, 0, 0, 0, 5, 0, 0, 0, 10, 0, 0, 0],
            ),
            (
                "ServerMessage::ShutdownAck",
                bincode::encode_to_vec(ServerMessage::ShutdownAck, BINCODE_CFG).unwrap(),
                // variant(2,0,0,0)
                &[2, 0, 0, 0],
            ),
            (
                "ServerMessage::DebugInfo(empty)",
                bincode::encode_to_vec(
                    ServerMessage::DebugInfo(Box::new(DebugState {
                        server_pid: 0,
                        rayon_threads: 0,
                        progress_subscribers: None,
                        watcher_count: 0,
                        watched_paths: vec![],
                        skip_set: vec![],
                        root_rebasing: false,
                        root_path: String::new(),
                        socket_name: String::new(),
                        submodule_statuses: None,
                        in_flight: None,
                        progress_queues: None,
                        last_watcher_error: None,
                        tripwires: vec![],
                    })),
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(3,0,0,0)
                // | server_pid(0,0,0,0) | rayon_threads(0,0,0,0)
                // | progress_subscribers:None(0)
                // | watcher_count(0,0,0,0)
                // | watched_paths:empty(0,0,0,0,0,0,0,0)
                // | skip_set:empty(0,0,0,0,0,0,0,0)
                // | root_rebasing:false(0)
                // | root_path:""(0,0,0,0,0,0,0,0)
                // | socket_name:""(0,0,0,0,0,0,0,0)
                // | submodule_statuses:None(0)
                // | in_flight:None(0) | progress_queues:None(0)
                // | last_watcher_error:None(0)
                // | tripwires:empty(0,0,0,0,0,0,0,0)
                &[
                    3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "ServerMessage::VersionMismatch { server_version: 0 }",
                bincode::encode_to_vec(
                    ServerMessage::VersionMismatch { server_version: 0 },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(4,0,0,0) | version(0)
                &[4, 0, 0, 0, 0],
            ),
        ];

        for (name, actual, expected) in cases {
            assert_eq!(
                actual, expected,
                "Wire format changed for {name}! \
                 If this is intentional, bump IPC_VERSION and update the expected bytes."
            );
        }
    }
}
