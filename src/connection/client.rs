//! Client-side IPC: connecting to the watch server, sending requests,
//! and reading responses.

use std::{
    io::BufReader,
    path::Path,
    time::{Duration, Instant},
};

use indicatif::{ProgressBar, ProgressStyle};

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ClientRequest, DebugState, IPC_VERSION, IpcError, IpcResult,
        IpcStream, ServerMessage, VersionMismatchError, ipc_connect, ipc_socket_path,
        protocol::{DEBUG_REQUEST, SHUTDOWN_REQUEST},
        read_full_message, read_full_message_fixed, server_not_started, write_full_message_fixed,
    },
    create_progress_bar,
    git::path::GitPath,
    watch::spawn_daemon,
};

/// Sends a reindex request to the watch server for `root_path`
///
/// # Errors
///
/// Returns `Err` if client-server communication or bincode encoding fails or an
/// unexpected message is received, and [`IpcError::IndexingFailed`] when the
/// server's indexing pass fails.
pub fn request_reindex(root_path: &Path, display_progress: bool) -> IpcResult<()> {
    let sock_path = ipc_socket_path(root_path);
    let conn = ipc_connect(&sock_path)?;
    let mut conn = BufReader::new(conn);
    let client_pid = std::process::id();
    let req = ClientRequest::new(ClientMessage::Reindex { pid: client_pid });
    // 1 byte version + 4 byte variant index + 4 byte u32 pid (fixint)
    let mut msg = [0; 9];
    let msg_len = bincode::encode_into_slice(&req, &mut msg, BINCODE_CFG)?;
    write_full_message_fixed(&mut conn, &msg[..msg_len])?;

    let mut progress_bar = None;
    // Indexing { u32, u32 } = 12 bytes fixint, so use a stack buffer.
    let mut buffer = [0u8; 12];
    // TODO: This would be better as a `try` block if that's ever stabilized
    let result = loop {
        let msg_len = match read_full_message_fixed(&mut conn, &mut buffer) {
            Ok(n) => n,
            Err(e) => break Err(e),
        };
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
                if display_progress {
                    let pb = progress_bar
                        .get_or_insert_with(|| create_progress_bar(0, "Reindexing in progress..."));
                    pb.set_length(u64::from(total));
                    pb.set_position(u64::from(curr));
                }
                if curr == total {
                    break Ok(());
                }
            }
            Ok((ServerMessage::IndexingFailed, _)) => break Err(IpcError::IndexingFailed),
            Ok((other, _)) => break Err(IpcError::UnexpectedResponse(other)),
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

/// Sends a shutdown request over `conn` and returns the server's response.
///
/// # Errors
///
/// Returns `Err` if the exchange fails, or if encoding or decoding fails.
pub fn request_shutdown(conn: IpcStream) -> IpcResult<ServerMessage> {
    let mut conn = BufReader::new(conn);
    write_full_message_fixed(&mut conn, &SHUTDOWN_REQUEST)?;

    // VersionMismatch { u8 } = 5 bytes is the largest possible response.
    let mut buffer = [0u8; 5];
    let msg_len = read_full_message_fixed(&mut conn, &mut buffer)?;
    let (resp, _): (ServerMessage, usize) =
        bincode::borrow_decode_from_slice(&buffer[..msg_len], BINCODE_CFG)?;

    Ok(resp)
}

/// How long [`connect_to_server`] waits for a freshly-spawned daemon to
/// accept connections before giving up. Empirically matches `prompt`'s
/// per-call budget and is long enough for normal cold starts (sub-100ms
/// in practice) with headroom for slow disks.
const COLD_START_DEADLINE: Duration = Duration::from_secs(1);

/// Connects to the watch server for `root_path`, starting one if necessary.
///
/// On the happy path (server already running), this is a single connect
/// call with no overhead. If the connection fails with `ConnectionRefused`
/// or `NotFound`, a new server is spawned and the connection is retried
/// until it succeeds, the user terminates the program, or
/// [`COLD_START_DEADLINE`] passes.
fn connect_to_server(root_path: &Path, display_progress: bool) -> IpcResult<BufReader<IpcStream>> {
    let sock_path = ipc_socket_path(root_path);
    match ipc_connect(&sock_path) {
        Ok(conn) => return Ok(BufReader::new(conn)),
        Err(e) if server_not_started(&e) => {}
        Err(e) => Err(e)?,
    }

    spawn_daemon(root_path, None)?;

    // Build the spinner only for terminal callers because its steady tick spawns
    // a drawing thread.
    let spinner = display_progress.then(|| {
        #[allow(clippy::literal_string_with_formatting_args)]
        let s = ProgressBar::new_spinner()
            .with_style(ProgressStyle::with_template("{spinner} {msg}").unwrap());
        s.set_message("Starting watch server...");
        s.enable_steady_tick(Duration::from_millis(80));
        s
    });

    let deadline = Instant::now() + COLD_START_DEADLINE;
    loop {
        match ipc_connect(&sock_path) {
            Ok(conn) => {
                if let Some(s) = &spinner {
                    s.finish_and_clear();
                }
                return Ok(BufReader::new(conn));
            }
            Err(e) if server_not_started(&e) => {
                if Instant::now() >= deadline {
                    if let Some(s) = &spinner {
                        s.abandon_with_message(format!(
                            "Watch server failed to start within {}s",
                            COLD_START_DEADLINE.as_secs(),
                        ));
                    }
                    Err(e)?;
                }
            }
            Err(e) => {
                if let Some(s) = &spinner {
                    s.abandon_with_message("Failed to connect to watch server".to_string());
                }
                Err(e)?;
            }
        }
        std::thread::yield_now();
    }
}

/// Sends a status request to the watch server for `root_path`.
///
/// Connects to the server (spawning if needed) and sends a `ClientMessage::Status`
/// request. Returns the live connection so that the caller can perform other work
/// before reading the response with [`recv_status_response`]. `display_progress`
/// gates the cold-start spinner shown while a freshly spawned server starts up
/// (off for non-terminal callers).
///
/// # Errors
///
/// Returns `Err` if the ipc channel cannot be created or the request cannot be sent.
pub fn send_status_request(
    root_path: &Path,
    display_progress: bool,
) -> IpcResult<BufReader<IpcStream>> {
    let mut conn = connect_to_server(root_path, display_progress)?;
    let req = ClientRequest::new(ClientMessage::Status(std::process::id()));
    let mut req_msg = [0; 9]; // 1 byte version + 4 byte variant index + 4 byte u32 pid (fixint)
    let req_msg_len = bincode::encode_into_slice(&req, &mut req_msg, BINCODE_CFG)?;
    write_full_message_fixed(&mut conn, &req_msg[..req_msg_len])?;
    Ok(conn)
}

/// Drains any `Indexing` progress messages from `conn` (updating the progress bar if
/// `display_progress` is true), and returns the final `Status` payload.
///
/// # Errors
///
/// Returns `Err` if communication over the channel fails or an unexpected message
/// is received, and [`IpcError::IndexingFailed`] when the server has no indexed state
/// to serve.
pub fn recv_status_response(
    conn: &mut BufReader<IpcStream>,
    display_progress: bool,
) -> IpcResult<(Vec<(GitPath, StatusSummary)>, u32)> {
    let mut progress_bar = None;
    let mut buffer = Vec::with_capacity(4096); // empirically ~2 KiB on a test repo
    // TODO: This would be better as a `try` block if that's ever stabilized
    let result = loop {
        if let Err(e) = read_full_message(conn, &mut buffer) {
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
                if display_progress {
                    // Created on the first update, so a request that fails before
                    // any update draws no bar.
                    let pb = progress_bar
                        .get_or_insert_with(|| create_progress_bar(0, "Indexing in progress..."));
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
            ServerMessage::IndexingFailed => break Err(IpcError::IndexingFailed),
            other => break Err(IpcError::UnexpectedResponse(other)),
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
/// Returns `Err` if client-server communication or bincode encoding/decoding fails
/// or an unexpected message is received.
pub fn request_debug(root_path: &Path) -> IpcResult<DebugState> {
    let sock_path = ipc_socket_path(root_path);
    let conn = ipc_connect(&sock_path)?;
    let mut conn = BufReader::new(conn);
    write_full_message_fixed(&mut conn, &DEBUG_REQUEST)?;

    let mut buffer = Vec::with_capacity(1024);
    read_full_message(&mut conn, &mut buffer)?;
    let (resp, _): (ServerMessage, usize) =
        bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)?;

    match resp {
        ServerMessage::DebugInfo(state) => Ok(*state),
        ServerMessage::VersionMismatch { server_version } => Err(VersionMismatchError {
            client_version: IPC_VERSION,
            server_version,
        })?,
        other => Err(IpcError::UnexpectedResponse(other)),
    }
}
