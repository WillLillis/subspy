//! The `stop` subcommand: sends shutdown requests to watch servers.

use std::path::Path;

use thiserror::Error;

use crate::connection::{
    IpcError, ServerMessage, ShutdownEndpointError,
    client::{request_shutdown, request_shutdown_endpoint},
    discover_ipc_endpoints, server_not_started, uses_filesystem_sockets,
};

pub type ShutdownResult<T> = Result<T, ShutdownError>;

#[derive(Debug, Error)]
pub enum ShutdownError {
    #[error(transparent)]
    Ipc(#[from] IpcError),
    #[error("could not enumerate watch server sockets: {0}")]
    Discovery(#[source] std::io::Error),
    #[error("{failed} watch server(s) did not shut down")]
    Incomplete { failed: usize },
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

/// Requests shutdown from every watch server discoverable on this machine.
///
/// On platforms whose sockets are files, an unreachable endpoint is assumed
/// to be a leftover from a crashed server.
///
/// # Errors
///
/// Returns `Err` if the socket namespace cannot be enumerated, or if any live
/// server failed to shut down.
pub fn shutdown_all() -> ShutdownResult<()> {
    let endpoints = discover_ipc_endpoints().map_err(ShutdownError::Discovery)?;
    let mut failed = 0usize;

    for endpoint in &endpoints {
        let name = Path::new(endpoint).display();
        match request_shutdown_endpoint(endpoint) {
            Ok(ServerMessage::ShutdownAck) => {
                println!("Successfully shutdown watch server at {name}");
            }
            Ok(other) => {
                failed += 1;
                eprintln!("{name}: unexpected response to shutdown: {other:?}");
            }
            Err(ShutdownEndpointError::Connect(error))
                if uses_filesystem_sockets() && server_not_started(&error) =>
            {
                eprintln!("{name}: stale or unreachable socket ({error})");
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
