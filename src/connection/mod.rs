//! Shared IPC plumbing for the client/server connection.
//!
//! The `protocol` submodule holds the message types, `transport` holds the
//! sockets and length-prefixed framing, and this module keeps the `IpcError`
//! hierarchy, the shared bincode config, and small lock helpers. `protocol`
//! and `transport` are re-exported here so callers use stable `connection::X`
//! paths.

use std::{
    sync::{Mutex, MutexGuard, TryLockError},
    time::{Duration, Instant},
};

use thiserror::Error;

pub mod client;
mod client_handler;
mod protocol;
mod transport;
pub mod watch_server;

pub use protocol::{ClientMessage, ClientRequest, DebugState, ServerMessage};
pub use transport::{
    IpcListener, IpcStream, cleanup_socket, create_listener, encode_and_write, ipc_connect,
    ipc_socket_path, read_full_message, read_full_message_fixed, set_recv_timeout,
    uses_filesystem_sockets, write_full_message_fixed,
};
/// Common bincode configuration used to encode/decode messages between the client and server
pub const BINCODE_CFG: bincode::config::Configuration<
    bincode::config::LittleEndian,
    bincode::config::Fixint,
> = bincode::config::standard()
    .with_fixed_int_encoding()
    .with_no_limit();

/// IPC protocol version. Bump when the wire format changes.
pub const IPC_VERSION: u8 = 0;

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
