use std::{
    cell::RefCell,
    collections::{BTreeMap, VecDeque},
    io::{BufReader, Read as _},
    sync::{Arc, MutexGuard},
};

use bincode::{BorrowDecode, Encode};
use interprocess::local_socket::Stream;
use log::{error, info};

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ClientRequest, IPC_VERSION, ServerMessage, write_full_message,
    },
    watch::WatchResult,
};

use super::{
    try_lock,
    watch_server::{ControlMessage, ProgressMap, ProgressSubscribers, StatusMap},
};

thread_local! {
    static ENCODE_BUF: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

#[derive(Debug, Clone, Copy, Encode, BorrowDecode)]
pub struct ProgressUpdate {
    pub curr: u32,
    pub total: u32,
}

impl ProgressUpdate {
    #[must_use]
    pub const fn new(curr: u32, total: u32) -> Self {
        Self { curr, total }
    }
}

/// Pushes `progress_val` to the progress queue for every registered subscriber.
///
/// # Panics
///
/// Panics if either mutex has been poisoned
#[inline]
#[expect(clippy::significant_drop_tightening)]
pub(super) fn broadcast_progress(
    subscribers: &ProgressSubscribers,
    progress: &ProgressMap,
    progress_val: ProgressUpdate,
) {
    let subs = subscribers.lock().expect("Subscribers mutex poisoned");
    // Avoid locking the progress queue for the common case of no active subscribers
    if subs.is_empty() {
        return;
    }
    let mut progress_guard = progress.lock().expect("Progress mutex poisoned");
    for &pid in subs.iter() {
        let queue = progress_guard.entry(pid).or_insert_with(|| {
            let ProgressUpdate { total: cap, .. } = progress_val;
            VecDeque::with_capacity(cap as usize + 1)
        });
        queue.push_back(progress_val);
    }
}

/// Handles an incoming client connection on a dedicated OS thread.
/// Errors are logged rather than propagated, since each connection is handled independently.
#[expect(
    clippy::needless_pass_by_value,
    reason = "owned values required for 'static std::thread::spawn closure"
)]
pub(super) fn handle_client_connection(
    conn: Stream,
    control_tx: crossbeam_channel::Sender<ControlMessage>,
    statuses: Arc<StatusMap>,
    progress: Arc<ProgressMap>,
    subscribers: Arc<ProgressSubscribers>,
) {
    if let Err(e) = dispatch_client_message(conn, &control_tx, &statuses, &progress, &subscribers) {
        error!("Failed to handle client connection: {e}");
    }
}

// NOTE: The logic in this function is kept separate from `handle_client_connection` purely to
// preserve `?` ergonomics.
fn dispatch_client_message(
    conn: Stream,
    control_tx: &crossbeam_channel::Sender<ControlMessage>,
    statuses: &StatusMap,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<()> {
    let mut conn = BufReader::new(conn);

    let msg_len = {
        let mut len_buf = [0u8; 4];
        conn.read_exact(&mut len_buf)?;
        u32::from_le_bytes(len_buf) as usize
    };
    // 1 byte version + 4 byte variant index + 4 byte u32 + 1 byte bool (fixint)
    let mut buffer = [0u8; 10];
    debug_assert!(
        msg_len <= buffer.len(),
        "Client request length {msg_len} exceeds buffer size"
    );
    conn.read_exact(&mut buffer[..msg_len])?;
    let (request, _): (ClientRequest, usize) =
        bincode::borrow_decode_from_slice(&buffer[..msg_len], BINCODE_CFG)?;
    info!("Received client request: {request:?}");

    if request.version != IPC_VERSION {
        error!(
            "Version mismatch: client={}, server={}",
            request.version, IPC_VERSION
        );
        let resp = ServerMessage::VersionMismatch {
            server_version: IPC_VERSION,
        };
        // VersionMismatch: 4 byte variant index + 1 byte u8 (fixint)
        let mut resp_buf = [0u8; 5];
        let resp_len = bincode::encode_into_slice(resp, &mut resp_buf, BINCODE_CFG)?;
        write_full_message(&mut conn, &resp_buf[..resp_len])?;
        return Ok(());
    }

    match request.message {
        ClientMessage::Reindex {
            pid,
            replace_watchers,
        } => {
            subscribers
                .lock()
                .expect("Subscribers mutex poisoned")
                .insert(pid);
            control_tx
                .send(ControlMessage::Reindex { replace_watchers })
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
            handle_reindex_request(conn, pid, progress, subscribers)?;
        }
        ClientMessage::Status(client_pid) => {
            handle_status_request(conn, client_pid, statuses, progress, subscribers)?;
        }
        ClientMessage::Shutdown => {
            control_tx
                .send(ControlMessage::Shutdown { conn })
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
        }
        ClientMessage::Debug => {
            control_tx
                .send(ControlMessage::Debug { conn })
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
        }
    }

    Ok(())
}

/// Handles a client's request for submodule statuses.
fn handle_status_request(
    mut conn: BufReader<Stream>,
    client_pid: u32,
    statuses: &StatusMap,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<()> {
    subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .insert(client_pid);
    let result = get_status_guard_with_progress(&mut conn, client_pid, statuses, progress);
    _ = subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .remove(&client_pid);
    _ = progress.lock().expect("Mutex poisoned").remove(&client_pid);
    let guard = result?;

    let mut status_out = Vec::with_capacity(guard.len());
    for (submod_path, status) in guard.iter().filter(|(_, st)| **st != StatusSummary::CLEAN) {
        status_out.push((submod_path.clone(), *status));
    }
    drop(guard);

    let msg = ServerMessage::Status(status_out);
    ENCODE_BUF.with_borrow_mut(|buf| -> WatchResult<()> {
        buf.clear();
        bincode::encode_into_std_write(msg, buf, BINCODE_CFG)?;
        write_full_message(&mut conn, buf)?;
        Ok(())
    })?;

    Ok(())
}

/// Handles a client's request to reindex the watch server. The reindex signal has already
/// been sent to the main event loop via the control channel; this function handles sending
/// progress updates back to the client over the IPC connection.
fn handle_reindex_request(
    mut conn: BufReader<Stream>,
    client_pid: u32,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<()> {
    let result = loop {
        match try_send_progress_update(&mut conn, client_pid, progress) {
            Ok(true) => break Ok(()),
            Ok(false) => std::thread::yield_now(),
            Err(e) => break Err(e),
        }
    };

    _ = subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .remove(&client_pid);
    _ = progress.lock().expect("Mutex poisoned").remove(&client_pid);

    result
}

/// Attempts to send an index progress message to `conn` for `client_pid`.
/// Return indicates whether indexing is determined to be complete (a message
/// is sent where `curr == total`)
///
/// # Errors
///
/// Returns `Err` if `bincode` encoding or writing to `conn` fails
fn try_send_progress_update(
    conn: &mut BufReader<Stream>,
    client_pid: u32,
    progress: &ProgressMap,
) -> WatchResult<bool> {
    let Some(mut progress_queue) = try_lock(progress) else {
        return Ok(false);
    };
    let Some(queue) = progress_queue.get_mut(&client_pid) else {
        return Ok(false);
    };
    let Some(ProgressUpdate { curr, total }) = queue.pop_front() else {
        return Ok(false);
    };
    drop(progress_queue);

    let progress = ServerMessage::Indexing { curr, total };
    // 4 byte variant index + 4 byte u32 curr + 4 byte u32 total (fixint)
    let mut progress_msg = [0; 12];
    let progress_msg_len = bincode::encode_into_slice(progress, &mut progress_msg, BINCODE_CFG)?;
    write_full_message(conn, &progress_msg[..progress_msg_len])?;

    Ok(curr == total)
}

/// Acquires the `statuses` guard. Every time the lock cannot be acquired
/// (because it is currently locked by an indexing operation in the main loop), an attempt
/// is made to send a progress update to the client.
fn get_status_guard_with_progress<'a>(
    conn: &mut BufReader<Stream>,
    client_pid: u32,
    statuses: &'a StatusMap,
    progress: &ProgressMap,
) -> WatchResult<MutexGuard<'a, BTreeMap<String, StatusSummary>>> {
    loop {
        if let Some(g) = try_lock(statuses) {
            return Ok(g);
        }
        if !try_send_progress_update(conn, client_pid, progress)? {
            std::thread::yield_now();
        }
    }
}
