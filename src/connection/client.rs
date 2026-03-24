//! Client-side IPC: connecting to the watch server, sending requests,
//! and reading responses.

use std::{
    io::{BufReader, Read},
    path::Path,
    time::{Duration, Instant},
};

use indicatif::{ProgressBar, ProgressStyle};
use log::error;

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ClientRequest, DebugState, IPC_VERSION, IpcStream,
        ServerMessage, VersionMismatchError, ipc_connect, ipc_socket_path, read_full_message,
        write_full_message,
    },
    create_progress_bar,
    debug::DebugResult,
    reindex::ReindexResult,
    shutdown::ShutdownResult,
    status::StatusResult,
    watch::spawn_daemon,
};

/// Sends a reindex request to the watch server for `root_path`
///
/// # Errors
///
/// Returns `Err` if client-server communication or bincode encoding fails.
pub fn request_reindex(
    root_path: &Path,
    replace_watchers: bool,
    display_progress: bool,
) -> ReindexResult<()> {
    let sock_path = ipc_socket_path(root_path);
    let conn = ipc_connect(&sock_path)?;
    let mut conn = BufReader::new(conn);
    let client_pid = std::process::id();
    let req = ClientRequest::new(ClientMessage::Reindex {
        pid: client_pid,
        replace_watchers,
    });
    // 1 byte version + 4 byte variant index + 4 byte u32 pid + 1 byte bool (fixint)
    let mut msg = [0; 10];
    let msg_len = bincode::encode_into_slice(&req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    let progress_bar =
        display_progress.then(|| create_progress_bar(0, "Reindexing in progress..."));
    // Indexing { u32, u32 } = 12 bytes fixint, so use a stack buffer.
    let mut len_buf = [0u8; 4];
    let mut buffer = [0u8; 12];
    // TODO: This would be better as a `try` block if that's ever stabilized
    let result = loop {
        if let Err(e) = conn.read_exact(&mut len_buf) {
            break Err(e.into());
        }
        let msg_len = u32::from_le_bytes(len_buf) as usize;
        debug_assert!(
            msg_len <= buffer.len(),
            "Server message length {msg_len} exceeds buffer size"
        );
        if let Err(e) = conn.read_exact(&mut buffer[..msg_len]) {
            break Err(e.into());
        }
        match bincode::borrow_decode_from_slice::<ServerMessage, _>(&buffer[..msg_len], BINCODE_CFG)
        {
            Err(e) => break Err(e.into()),
            Ok((ServerMessage::VersionMismatch { server_version }, _)) => {
                break Err(VersionMismatchError {
                    client_version: IPC_VERSION,
                    server_version,
                }
                .into());
            }
            Ok((ServerMessage::Indexing { curr, total }, _)) => {
                if let Some(pb) = &progress_bar {
                    pb.set_position(u64::from(curr));
                    pb.set_length(u64::from(total));
                }
                if curr == total {
                    break Ok(());
                }
            }
            Ok(_) => break Ok(()),
        }
    };

    if let Some(pb) = &progress_bar {
        if result.is_ok() {
            pb.finish_with_message("Reindex complete");
        } else {
            pb.abandon();
        }
    }

    result
}

/// Sends a shutdown request to the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if client-server communication or bincode encoding/decoding fails.
pub fn request_shutdown(root_path: &Path) -> ShutdownResult<()> {
    let sock_path = ipc_socket_path(root_path);
    let conn = ipc_connect(&sock_path)?;
    let mut conn = BufReader::new(conn);
    let req = ClientRequest::new(ClientMessage::Shutdown);
    let mut msg = [0; 5]; // 1 byte version + 4 byte variant index (fixint)
    let msg_len = bincode::encode_into_slice(&req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    // Wait for the watch server to acknowledge the shutdown.
    // VersionMismatch { u8 } = 5 bytes is the largest possible response.
    let mut len_buf = [0u8; 4];
    conn.read_exact(&mut len_buf)?;
    let msg_len = u32::from_le_bytes(len_buf) as usize;
    let mut buffer = [0u8; 5];
    debug_assert!(
        msg_len <= buffer.len(),
        "Server message length {msg_len} exceeds buffer size"
    );
    conn.read_exact(&mut buffer[..msg_len])?;
    let (resp, _): (ServerMessage, usize) =
        bincode::borrow_decode_from_slice(&buffer[..msg_len], BINCODE_CFG)?;

    match resp {
        ServerMessage::ShutdownAck => {
            println!(
                "Successfully shutdown watch server for {}",
                root_path.display()
            );
        }
        ServerMessage::VersionMismatch { server_version } => {
            Err(VersionMismatchError {
                client_version: IPC_VERSION,
                server_version,
            })?;
        }
        other => error!("Unexpected response from server during shutdown: {other:?}"),
    }

    Ok(())
}

/// Connects to the watch server for `root_path`, starting one if necessary.
///
/// On the happy path (server already running), this is a single connect
/// call with no overhead. If the connection fails with `ConnectionRefused` or
/// `NotFound`, a new server is spawned and the connection is retried until
/// it succeeds, the user terminates the program, or 10 seconds pass.
fn connect_to_server(root_path: &Path) -> StatusResult<BufReader<IpcStream>> {
    let sock_path = ipc_socket_path(root_path);
    match ipc_connect(&sock_path) {
        Ok(conn) => return Ok(BufReader::new(conn)),
        Err(e) if server_not_started(&e) => {}
        Err(e) => Err(e)?,
    }

    spawn_daemon(root_path, None)?;

    #[allow(clippy::literal_string_with_formatting_args)]
    let spinner = ProgressBar::new_spinner()
        .with_style(ProgressStyle::with_template("{spinner} {msg}").unwrap());
    spinner.set_message("Starting watch server...");
    spinner.enable_steady_tick(Duration::from_millis(80));

    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        match ipc_connect(&sock_path) {
            Ok(conn) => {
                spinner.finish_and_clear();
                return Ok(BufReader::new(conn));
            }
            Err(e) if server_not_started(&e) => {
                if Instant::now() >= deadline {
                    spinner.abandon_with_message(
                        "Watch server failed to start within 10s".to_string(),
                    );
                    Err(e)?;
                }
            }
            Err(e) => {
                spinner.abandon_with_message("Failed to connect to watch server".to_string());
                Err(e)?;
            }
        }
        std::thread::yield_now();
    }
}

#[inline]
#[must_use]
pub fn server_not_started(e: &std::io::Error) -> bool {
    matches!(
        e.kind(),
        std::io::ErrorKind::ConnectionRefused | std::io::ErrorKind::NotFound
    )
}

/// Sends a status request to the watch server for `root_path`.
///
/// Connects to the server (spawning if needed) and sends a `ClientMessage::Status`
/// request. Returns the live connection so that the caller can perform other work
/// before reading the response with [`recv_status_response`].
///
/// # Errors
///
/// Returns error if the ipc channel cannot be created or the request cannot be sent.
pub fn send_status_request(root_path: &Path) -> StatusResult<BufReader<IpcStream>> {
    let mut conn = connect_to_server(root_path)?;
    let req = ClientRequest::new(ClientMessage::Status(std::process::id()));
    let mut req_msg = [0; 9]; // 1 byte version + 4 byte variant index + 4 byte u32 pid (fixint)
    let req_msg_len = bincode::encode_into_slice(&req, &mut req_msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &req_msg[..req_msg_len])?;
    Ok(conn)
}

/// Drains any `Indexing` progress messages from `conn` (updating the progress bar if
/// `display_progress` is true), and returns the final `Status` payload.
///
/// # Errors
///
/// Returns error if communication over the channel fails or an unexpected message
/// is received.
pub fn recv_status_response(
    conn: &mut BufReader<IpcStream>,
    display_progress: bool,
) -> StatusResult<(Vec<(String, StatusSummary)>, u32)> {
    let progress_bar = display_progress.then(|| create_progress_bar(0, "Indexing in progress..."));
    let mut buffer = Vec::with_capacity(4096); // empirically ~2 KiB on a test repo
    // TODO: This would be better as a `try` block if that's ever stabilized
    let result = loop {
        if let Err(e) = read_full_message(conn, &mut buffer, None) {
            break Err(e.into());
        }

        let resp_msg =
            match bincode::borrow_decode_from_slice::<ServerMessage, _>(&buffer, BINCODE_CFG) {
                Ok((msg, _)) => msg,
                Err(e) => break Err(e.into()),
            };
        match resp_msg {
            ServerMessage::Status { statuses, total } => break Ok((statuses, total)),
            ServerMessage::Indexing { curr, total } => {
                if let Some(pb) = &progress_bar {
                    pb.set_length(u64::from(total));
                    pb.set_position(u64::from(curr));
                }
            }
            ServerMessage::VersionMismatch { server_version } => {
                break Err(VersionMismatchError {
                    client_version: IPC_VERSION,
                    server_version,
                }
                .into());
            }
            other => {
                break Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("Unexpected response from server during status request: {other:?}"),
                )
                .into());
            }
        }
        buffer.clear();
    };

    if let Some(pb) = &progress_bar {
        if result.is_ok() {
            pb.finish_and_clear();
        } else {
            pb.abandon();
        }
    }

    result
}

/// Requests a debug state snapshot from the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if client-server communication or bincode encoding/decoding fails.
pub fn request_debug(root_path: &Path) -> DebugResult<DebugState> {
    let sock_path = ipc_socket_path(root_path);
    let conn = ipc_connect(&sock_path)?;
    let mut conn = BufReader::new(conn);
    let req = ClientRequest::new(ClientMessage::Debug);
    let mut msg = [0; 5]; // 1 byte version + 4 byte variant index (fixint)
    let msg_len = bincode::encode_into_slice(&req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    let mut buffer = Vec::with_capacity(1024);
    read_full_message(&mut conn, &mut buffer, None)?;
    let (resp, _): (ServerMessage, usize) =
        bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)?;

    match resp {
        ServerMessage::DebugInfo(state) => Ok(*state),
        ServerMessage::VersionMismatch { server_version } => Err(VersionMismatchError {
            client_version: IPC_VERSION,
            server_version,
        })?,
        other => {
            error!("Unexpected response from server during debug request: {other:?}");
            Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Unexpected response from server",
            ))?
        }
    }
}
