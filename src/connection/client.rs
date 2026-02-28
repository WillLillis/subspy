use std::{io::BufReader, path::Path};

use interprocess::local_socket::{Stream, traits::Stream as _};
use log::error;

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, DebugState, ServerMessage, ipc_name, read_full_message,
        write_full_message,
    },
    create_progress_bar,
    debug::DebugResult,
    reindex::ReindexResult,
    shutdown::ShutdownResult,
    status::StatusResult,
};

/// Sends a reindex request to the watch server for `root_path`
///
/// # Errors
///
/// Returns `Err` if client-server communication or bincode encoding fails.
pub fn request_reindex(root_path: &Path) -> ReindexResult<()> {
    let name = ipc_name(root_path)?;

    let conn = Stream::connect(name)?;
    let mut conn = BufReader::new(conn);
    let client_pid = std::process::id();
    let status_req = ClientMessage::Reindex(client_pid);
    let mut msg = [0; 6]; // 1 byte variant index + up to 5 bytes varint u32
    let msg_len = bincode::encode_into_slice(&status_req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    let progress_bar = create_progress_bar(0, "Reindexing in progress...");
    let mut buffer = Vec::with_capacity(1024);
    loop {
        if let Err(e) = read_full_message(&mut conn, &mut buffer) {
            error!("Error occurred while reindexing: {e}");
            break;
        }
        let Ok((ServerMessage::Indexing { curr, total }, _)): Result<(ServerMessage, usize), _> =
            bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)
        else {
            break;
        };
        progress_bar.set_position(u64::from(curr));
        progress_bar.set_length(u64::from(total));
        if curr == total {
            break;
        }
    }

    progress_bar.finish_with_message("Reindex complete");

    Ok(())
}

/// Sends a shutdown request to the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if client-server communication or bincode encoding/decoding fails.
pub fn request_shutdown(root_path: &Path) -> ShutdownResult<()> {
    let name = ipc_name(root_path)?;
    let conn = Stream::connect(name)?;
    let mut conn = BufReader::new(conn);
    let status_req = ClientMessage::Shutdown;
    let mut msg = [0; 1]; // unit variant: 1 byte for variant index
    let msg_len = bincode::encode_into_slice(&status_req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    // Wait for the watch server to acknowledge the shutdown
    let mut buffer = Vec::with_capacity(1024);
    read_full_message(&mut conn, &mut buffer)?;
    let (resp, _): (ServerMessage, usize) =
        bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)?;

    match resp {
        ServerMessage::ShutdownAck => {
            println!(
                "Successfully shutdown watch server for {}",
                root_path.display()
            );
        }
        other => error!("Unexpected response from server during shutdown: {other:?}"),
    }

    Ok(())
}

/// Requests the statuses of the submodules within `path` from the watch server
///
/// # Errors
///
/// Returns error if the ipc channel cannot be created, or communication over said channel fails
///
/// # Panics
///
/// Panics if a malformed response from the watch server is received
pub fn request_status(root_path: &Path) -> StatusResult<Vec<(String, StatusSummary)>> {
    let name = ipc_name(root_path)?;

    let conn = Stream::connect(name)?;
    let mut conn = BufReader::new(conn);
    let status_req = ClientMessage::Status(std::process::id());
    let mut req_msg = [0; 6]; // statically determined an upper bound of 6 bytes
    let req_msg_len = bincode::encode_into_slice(&status_req, &mut req_msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &req_msg[..req_msg_len])?;

    let progress_bar = create_progress_bar(0, "Indexing in progress...");
    // TODO: Get some impirical data on the actual buffer size we need
    let mut buffer = Vec::with_capacity(1024);
    loop {
        read_full_message(&mut conn, &mut buffer)?;

        let (resp_msg, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)?;
        match resp_msg {
            ServerMessage::Status(items) => {
                progress_bar.finish_and_clear();
                return Ok(items);
            }
            ServerMessage::Indexing { curr, total } => {
                progress_bar.set_length(u64::from(total));
                progress_bar.set_position(u64::from(curr));
            }
            other => {
                error!("Unexpected response from server during status request: {other:?}");
            }
        }
        buffer.clear();
    }
}

/// Requests a debug state snapshot from the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if client-server communication or bincode encoding/decoding fails.
pub fn request_debug(root_path: &Path) -> DebugResult<DebugState> {
    let name = ipc_name(root_path)?;
    let conn = Stream::connect(name)?;
    let mut conn = BufReader::new(conn);
    let req = ClientMessage::Debug;
    let mut msg = [0; 1]; // unit variant: 1 byte for variant index
    let msg_len = bincode::encode_into_slice(&req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    let mut buffer = Vec::with_capacity(1024);
    read_full_message(&mut conn, &mut buffer)?;
    let (resp, _): (ServerMessage, usize) =
        bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)?;

    match resp {
        ServerMessage::DebugInfo(state) => Ok(state),
        other => {
            error!("Unexpected response from server during debug request: {other:?}");
            Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Unexpected response from server",
            ))?
        }
    }
}
