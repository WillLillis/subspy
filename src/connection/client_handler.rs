use std::{
    collections::{BTreeMap, VecDeque},
    io::BufReader,
    sync::{Mutex, MutexGuard, TryLockError},
};

use bincode::{BorrowDecode, Encode};
use interprocess::local_socket::Stream;
use log::info;

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ServerMessage, read_full_message, write_full_message,
    },
    watch::WatchResult,
};

use super::watch_server::{ControlMessage, ProgressMap, ProgressSubscribers, StatusMap};

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

/// Attempts to acquire `mutex`.
///
/// # Panics
///
/// Panics if `mutex` has been poisoned
fn try_acquire<T>(mutex: &Mutex<T>) -> Option<MutexGuard<'_, T>> {
    match mutex.try_lock() {
        Ok(guard) => Some(guard),
        Err(TryLockError::WouldBlock) => None,
        Err(TryLockError::Poisoned(_)) => panic!("Mutex poisoned"),
    }
}

/// Pushes `progress_val` to the progress queue for every registered subscriber.
///
/// # Panics
///
/// Panics if either mutex has been poisoned
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

/// Handles incoming client connections. Returns whether the listener received a shutdown command
///
/// # Errors
///
/// Returns `Err` if the client message couldn't be read, decoded, or handled.
pub(super) fn handle_client_connection(
    conn: Stream,
    buffer: &mut Vec<u8>,
    control_tx: &crossbeam_channel::Sender<ControlMessage>,
    statuses: &StatusMap,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<bool> {
    let mut conn = BufReader::new(conn);

    read_full_message(&mut conn, buffer)?;
    let (msg, _): (ClientMessage, usize) = bincode::borrow_decode_from_slice(buffer, BINCODE_CFG)?;
    info!("Received client message: {msg:?}");

    match msg {
        ClientMessage::Reindex(client_pid) => {
            subscribers
                .lock()
                .expect("Subscribers mutex poisoned")
                .insert(client_pid);
            control_tx
                .send(ControlMessage::Reindex)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
            handle_reindex_request(conn, client_pid, progress, subscribers)?;
        }
        ClientMessage::Status(client_pid) => {
            handle_status_request(conn, client_pid, statuses, progress, subscribers)?;
        }
        ClientMessage::Shutdown => {
            control_tx
                .send(ControlMessage::Shutdown { conn })
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
            return Ok(true);
        }
        ClientMessage::Debug => {
            control_tx
                .send(ControlMessage::Debug { conn })
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
        }
    }

    Ok(false)
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
    let guard = get_status_guard_with_progress(&mut conn, client_pid, statuses, progress)?;
    _ = subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .remove(&client_pid);
    _ = progress.lock().expect("Mutex poisoned").remove(&client_pid);

    let mut status_out = Vec::with_capacity(guard.len());
    for (submod_path, status) in guard.iter().filter(|(_, st)| **st != StatusSummary::CLEAN) {
        status_out.push((submod_path.clone(), *status));
    }
    drop(guard);

    let msg = ServerMessage::Status(status_out);
    let serialized = bincode::encode_to_vec(msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &serialized)?;

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
    loop {
        if try_send_progress_update(&mut conn, client_pid, progress)? {
            break;
        }
        std::thread::yield_now();
    }

    _ = subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .remove(&client_pid);
    _ = progress.lock().expect("Mutex poisoned").remove(&client_pid);

    Ok(())
}

/// Attempts to send an index progress message to `conn` for `client_pid`.
/// Return indicates whether indexing is determined to be complete (a message
/// is received where `current_idx == length`)
///
/// # Errors
///
/// Returns `Err` if `bincode` encoding or writing to `conn` fails
fn try_send_progress_update(
    conn: &mut BufReader<Stream>,
    client_pid: u32,
    progress: &ProgressMap,
) -> WatchResult<bool> {
    let Some(mut progress_queue) = try_acquire(progress) else {
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
    let mut progress_msg = [0; 10]; // statically determined an upper bound of 10 bytes
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
        if let Some(g) = try_acquire(statuses) {
            return Ok(g);
        }
        if !try_send_progress_update(conn, client_pid, progress)? {
            std::thread::yield_now();
        }
    }
}
