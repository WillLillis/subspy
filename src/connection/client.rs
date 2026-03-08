use std::{io::BufReader, path::Path, time::Duration};

use indicatif::{ProgressBar, ProgressStyle};
use interprocess::local_socket::{Stream, traits::Stream as _};
use log::error;

use crate::{
    FullRepoStatus,
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
    let mut msg = [0; 7]; // 1 byte variant index + up to 5 bytes varint u32 + 1 byte bool
    let msg_len = bincode::encode_into_slice(&status_req, &mut msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg[..msg_len])?;

    let progress_bar =
        display_progress.then(|| create_progress_bar(0, "Reindexing in progress..."));
    let mut buffer = Vec::with_capacity(1024);
    loop {
        read_full_message(&mut conn, &mut buffer)?;
        let Ok((ServerMessage::Indexing { curr, total }, _)): Result<(ServerMessage, usize), _> =
            bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)
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

/// Requests the full repository status from the watch server for `root_path`.
///
/// # Errors
///
/// Returns error if the ipc channel cannot be created, or communication over said channel fails
///
/// # Panics
///
/// Panics if a malformed response from the watch server is received
pub fn request_status(
    root_path: &Path,
    display_progress: bool,
) -> StatusResult<FullRepoStatus> {
    let mut conn = connect_to_server(root_path)?;
    let status_req = ClientMessage::Status(std::process::id());
    let mut req_msg = [0; 6]; // statically determined an upper bound of 6 bytes
    let req_msg_len = bincode::encode_into_slice(&status_req, &mut req_msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &req_msg[..req_msg_len])?;

    let progress_bar = display_progress.then(|| create_progress_bar(0, "Indexing in progress..."));
    let mut buffer = Vec::with_capacity(4096);
    loop {
        read_full_message(&mut conn, &mut buffer)?;

        let (resp_msg, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG)?;
        match resp_msg {
            ServerMessage::Status(full_status) => {
                if let Some(pb) = &progress_bar {
                    pb.finish_and_clear();
                }
                return Ok(*full_status);
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
