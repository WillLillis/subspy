//! The `stop` subcommand: sends shutdown requests to watch servers.

use std::{ffi::OsStr, path::Path};

use thiserror::Error;

use crate::{
    connection::{
        IpcError, ServerMessage,
        client::{request_shutdown, request_shutdown_endpoint},
        discover_ipc_endpoints, ipc_connect, peer_pid, server_not_started, uses_filesystem_sockets,
    },
    proc::{Pid, terminate_process},
};

pub type ShutdownResult<T> = Result<T, ShutdownError>;

#[derive(Debug, Error)]
pub enum ShutdownError {
    #[error(transparent)]
    Ipc(#[from] IpcError),
    #[error("could not enumerate watch server sockets: {0}")]
    Discovery(#[source] std::io::Error),
    #[error("{failed} watch server(s) could not be stopped")]
    Incomplete { failed: usize },
}

/// How [`stop_endpoint`] stopped the server at an endpoint.
enum Stopped {
    /// The server acknowledged the shutdown request.
    ShutDown,
    /// Nothing listened on the socket file, so it was removed.
    StaleSocketRemoved,
    /// The server did not acknowledge the shutdown request, so its process was
    /// terminated.
    Terminated { pid: Pid },
}

/// Why [`stop_endpoint`] could not stop the server at an endpoint.
#[derive(Debug, Error)]
enum StopError {
    #[error(transparent)]
    Connect(std::io::Error),
    #[error("could not remove the socket: {0}")]
    RemoveSocket(#[source] std::io::Error),
    #[error("the server's process could not be identified: {0}")]
    PeerPid(#[source] std::io::Error),
    #[error("the platform does not report the server's process ID")]
    PeerPidUnavailable,
    #[error("terminating the server (pid {pid}) failed: {error}")]
    Terminate {
        pid: Pid,
        #[source]
        error: std::io::Error,
    },
}

/// Issues a shutdown request to the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if connecting to the server, encoding the request,
/// or receiving the acknowledgement fails.
pub fn shutdown(root_path: &Path) -> ShutdownResult<()> {
    Ok(request_shutdown(root_path)?)
}

/// Stops every watch server discoverable on this machine.
///
/// Servers that do not acknowledge shutdown are terminated. On platforms
/// whose sockets are files, stale sockets are removed.
///
/// # Errors
///
/// Returns `Err` if the socket namespace cannot be enumerated, or if any
/// endpoint cannot be stopped or cleaned up.
pub fn shutdown_all() -> ShutdownResult<()> {
    let endpoints = discover_ipc_endpoints().map_err(ShutdownError::Discovery)?;
    let mut failed = 0usize;

    for endpoint in &endpoints {
        let name = Path::new(endpoint).display();
        match stop_endpoint(endpoint) {
            Ok(Stopped::ShutDown) => println!("Successfully shutdown watch server at {name}"),
            Ok(Stopped::StaleSocketRemoved) => println!("Removed stale socket {name}"),
            Ok(Stopped::Terminated { pid }) => {
                println!("Terminated watch server (pid {pid}) at {name}");
            }
            Err(error) => {
                failed += 1;
                eprintln!("{name}: {error}");
            }
        }
    }

    if failed > 0 {
        return Err(ShutdownError::Incomplete { failed });
    }
    if endpoints.is_empty() {
        println!("No watch servers found");
    }
    Ok(())
}

/// Stops the server listening on `endpoint`.
///
/// The server is asked to shut down. One that answers with anything but an
/// acknowledgement, or not at all, is terminated instead. On platforms whose
/// sockets are files, a socket nothing listens on is removed.
fn stop_endpoint(endpoint: &OsStr) -> Result<Stopped, StopError> {
    let conn = match ipc_connect(endpoint) {
        Ok(conn) => conn,
        Err(error) if uses_filesystem_sockets() && server_not_started(&error) => {
            remove_socket(endpoint)?;
            return Ok(Stopped::StaleSocketRemoved);
        }
        Err(error) => return Err(StopError::Connect(error)),
    };
    let pid = peer_pid(&conn);

    let response = request_shutdown_endpoint(conn);
    if matches!(&response, Ok(ServerMessage::ShutdownAck)) {
        return Ok(Stopped::ShutDown);
    }
    log::warn!(
        "shutdown request to {} was not acknowledged: {response:?}",
        endpoint.display()
    );
    let pid = match pid {
        Ok(Some(pid)) => pid,
        Ok(None) => return Err(StopError::PeerPidUnavailable),
        Err(error) => return Err(StopError::PeerPid(error)),
    };
    if let Err(error) = terminate_process(pid) {
        return Err(StopError::Terminate { pid, error });
    }
    if uses_filesystem_sockets() {
        remove_socket(endpoint)?;
    }
    Ok(Stopped::Terminated { pid })
}

/// Removes the socket file at `endpoint`. One that is already gone counts as
/// removed.
fn remove_socket(endpoint: &OsStr) -> Result<(), StopError> {
    match std::fs::remove_file(endpoint) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(StopError::RemoveSocket(error)),
    }
}
