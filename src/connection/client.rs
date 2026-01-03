use std::{io::BufReader, path::Path};

use interprocess::local_socket::{Stream, traits::Stream as _};
use log::error;
use notify::{EventKind, RecommendedWatcher, RecursiveMode, Watcher as _};

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ServerMessage, get_reindex_file_path, get_shutdown_file_path,
        ipc_name, read_full_message, write_full_message,
    },
    create_progress_bar,
    reindex::ReindexResult,
    shutdown::{ShutdownError, ShutdownResult},
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
    let msg = bincode::encode_to_vec(status_req, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg)?;

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

    // NOTE: If this file is immediately removed after creation by the server,
    // the watcher doesn't pick up its creation. To get around this, we remove
    // the file here after we know it's already served its purpose.
    let reindex_file_path = get_reindex_file_path(root_path, client_pid);
    if let Err(e) = std::fs::remove_file(&reindex_file_path) {
        error!(
            "Failed to remove reindex sentinel file {} -- {e}",
            reindex_file_path.display()
        );
    }

    Ok(())
}

/// Sends a shutdown request to the watch server for `root_path`.
///
/// # Errors
///
/// Returns `Err` if client-server communication fails, a watcher cannot be created
/// on the shutdown sentinel file, or if bincode fails to encode a message.
pub fn request_shutdown(root_path: &Path) -> ShutdownResult<()> {
    let name = ipc_name(root_path)?;

    let conn = Stream::connect(name)?;
    let mut conn = BufReader::new(conn);
    let pid = std::process::id();
    let status_req = ClientMessage::Shutdown(pid);
    let msg = bincode::encode_to_vec(status_req, BINCODE_CFG)?;
    write_full_message(&mut conn, &msg)?;

    let shutdown_file_path = get_shutdown_file_path(root_path, pid);

    let (tx, rx) = crossbeam_channel::unbounded();
    let log_full_path = root_path.to_path_buf();
    let mut watcher = RecommendedWatcher::new(
        move |res: Result<notify::Event, _>| {
            if let Err(e) = tx.send(res) {
                error!(
                    "Watcher for {} failed to send -- {e}",
                    log_full_path.display()
                );
            }
        },
        notify::Config::default(),
    )?;
    watcher.watch(&shutdown_file_path, RecursiveMode::NonRecursive)?;

    'outer: loop {
        let event = rx.recv()?.map_err(ShutdownError::Watch)?;
        if matches!(event.kind, EventKind::Remove(_))
            && event.paths.iter().any(|p| p.eq(&shutdown_file_path))
        {
            println!(
                "Successfully shutdown watch server for {}",
                root_path.display()
            );
            break 'outer;
        }
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
    let req_msg = bincode::encode_to_vec(status_req, BINCODE_CFG)?;
    write_full_message(&mut conn, &req_msg)?;

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
        }
        buffer.clear();
    }
}
