use std::{
    io::{BufReader, Read},
    path::Path,
    time::Duration,
};

use indicatif::{ProgressBar, ProgressStyle};
use interprocess::local_socket::{Stream, traits::Stream as _};
use log::error;

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, DebugState, ServerMessage, ipc_name, read_full_message,
        spawn_daemon, write_full_message,
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
pub fn request_reindex(
    root_path: &Path,
    replace_watchers: bool,
    display_progress: bool,
) -> ReindexResult<()> {
    let name = ipc_name(root_path)?;

    let conn = Stream::connect(name)?;
    let mut conn = BufReader::new(conn);
    let client_pid = std::process::id();
    let status_req = ClientMessage::Reindex {
        pid: client_pid,
        replace_watchers,
    };
    let mut msg = [0; 9]; // 4 byte variant index + 4 byte u32 pid + 1 byte bool (fixint)
    let msg_len = bincode::encode_into_slice(&status_req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    let progress_bar =
        display_progress.then(|| create_progress_bar(0, "Reindexing in progress..."));
    // Indexing { u32, u32 } = 12 bytes fixint, so use a stack buffer.
    let mut len_buf = [0u8; 4];
    let mut buffer = [0u8; 12];
    loop {
        conn.read_exact(&mut len_buf)?;
        let msg_len = u32::from_le_bytes(len_buf) as usize;
        conn.read_exact(&mut buffer[..msg_len])?;
        let Ok((ServerMessage::Indexing { curr, total }, _)): Result<(ServerMessage, usize), _> =
            bincode::borrow_decode_from_slice(&buffer[..msg_len], BINCODE_CFG)
        else {
            break;
        };
        if let Some(pb) = &progress_bar {
            pb.set_position(u64::from(curr));
            pb.set_length(u64::from(total));
        }
        if curr == total {
            break;
        }
    }

    if let Some(pb) = &progress_bar {
        pb.finish_with_message("Reindex complete");
    }

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
    let mut msg = [0; 4]; // unit variant: 4 byte variant index (fixint)
    let msg_len = bincode::encode_into_slice(&status_req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    // Wait for the watch server to acknowledge the shutdown.
    // ShutdownAck is 4 bytes (fixint variant index only), so use a stack buffer.
    let mut len_buf = [0u8; 4];
    conn.read_exact(&mut len_buf)?;
    let msg_len = u32::from_le_bytes(len_buf) as usize;
    let mut buffer = [0u8; 4];
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
        other => error!("Unexpected response from server during shutdown: {other:?}"),
    }

    Ok(())
}

/// Connects to the watch server for `root_path`, starting one if necessary.
///
/// On the happy path (server already running), this is a single `Stream::connect`
/// call with no overhead. If the connection fails with `ConnectionRefused` or
/// `NotFound`, a new server is spawned and the connection is retried until
/// it succeeds or the user terminates the program.
fn connect_to_server(root_path: &Path) -> StatusResult<BufReader<Stream>> {
    let name = ipc_name(root_path)?;
    match Stream::connect(name) {
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

    let name = ipc_name(root_path)?;
    loop {
        match Stream::connect(name.clone()) {
            Ok(conn) => {
                spinner.finish_and_clear();
                return Ok(BufReader::new(conn));
            }
            Err(e) if server_not_started(&e) => {}
            Err(e) => {
                spinner.abandon_with_message("Failed to connect to watch server".to_string());
                Err(e)?;
            }
        }
        std::thread::yield_now();
    }
}

#[inline]
fn server_not_started(e: &std::io::Error) -> bool {
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
pub fn send_status_request(root_path: &Path) -> StatusResult<BufReader<Stream>> {
    let mut conn = connect_to_server(root_path)?;
    let status_req = ClientMessage::Status(std::process::id());
    let mut req_msg = [0; 8]; // 4 byte variant index + 4 byte u32 pid (fixint)
    let req_msg_len = bincode::encode_into_slice(&status_req, &mut req_msg, BINCODE_CFG)?;
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
    conn: &mut BufReader<Stream>,
    display_progress: bool,
) -> StatusResult<Vec<(String, StatusSummary)>> {
    let progress_bar = display_progress.then(|| create_progress_bar(0, "Indexing in progress..."));
    let mut buffer = Vec::with_capacity(4096); // empirically ~2 KiB on a test repo
    loop {
        read_full_message(conn, &mut buffer)?;

        let (resp_msg, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)?;
        match resp_msg {
            ServerMessage::Status(items) => {
                if let Some(pb) = &progress_bar {
                    pb.finish_and_clear();
                }
                return Ok(items);
            }
            ServerMessage::Indexing { curr, total } => {
                if let Some(pb) = &progress_bar {
                    pb.set_length(u64::from(total));
                    pb.set_position(u64::from(curr));
                }
            }
            other => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("Unexpected response from server during status request: {other:?}"),
            ))?,
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
    let mut msg = [0; 4]; // unit variant: 4 byte variant index (fixint)
    let msg_len = bincode::encode_into_slice(&req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    let mut buffer = Vec::with_capacity(1024);
    read_full_message(&mut conn, &mut buffer)?;
    let (resp, _): (ServerMessage, usize) =
        bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)?;

    match resp {
        ServerMessage::DebugInfo(state) => Ok(*state),
        other => {
            error!("Unexpected response from server during debug request: {other:?}");
            Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Unexpected response from server",
            ))?
        }
    }
}
