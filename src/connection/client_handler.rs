//! Server-side client connection handling: message dispatch, status
//! responses, progress broadcasting, and reindex coordination.

use std::{
    cell::RefCell,
    collections::{BTreeMap, VecDeque},
    io::{BufReader, Write as _},
    sync::{Arc, MutexGuard},
};

use super::IpcStream;
use bincode::{BorrowDecode, Encode};
use log::{error, info};

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ClientRequest, IPC_VERSION, MSG_PREFIX_LEN, ServerMessage,
        read_full_message_fixed, write_full_message_fixed,
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
pub(super) struct ProgressUpdate {
    pub(super) curr: u32,
    pub(super) total: u32,
}

impl ProgressUpdate {
    #[must_use]
    pub(super) const fn new(curr: u32, total: u32) -> Self {
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
    conn: IpcStream,
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
    conn: IpcStream,
    control_tx: &crossbeam_channel::Sender<ControlMessage>,
    statuses: &StatusMap,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<()> {
    let mut conn = BufReader::new(conn);

    // 1 byte version + 4 byte variant index + 4 byte u32 + 1 byte bool (fixint)
    let mut buffer = [0u8; 10];
    let msg_len = read_full_message_fixed(&mut conn, &mut buffer)?;
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
        write_full_message_fixed(&mut conn, &resp_buf[..resp_len])?;
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
    mut conn: BufReader<IpcStream>,
    client_pid: u32,
    statuses: &StatusMap,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<()> {
    // Fast path: status map available immediately (no indexing in progress).
    // Skip the 3 mutex lock/unlock pairs for progress subscriber management.
    if let Some(guard) = try_lock(statuses) {
        return ENCODE_BUF.with_borrow_mut(|buf| -> WatchResult<()> {
            encode_status_response(&mut conn, &guard, buf)?;
            Ok(())
        });
    }

    // Slow path: indexing in progress, subscribe for progress updates.
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

    ENCODE_BUF.with_borrow_mut(|buf| -> WatchResult<()> {
        encode_status_response(&mut conn, &guard, buf)?;
        Ok(())
    })?;
    drop(guard);

    Ok(())
}

/// Encodes a `ServerMessage::Status` response directly from the status map guard,
/// avoiding String clones by writing borrowed `&str` keys into the buffer.
///
/// The wire format matches the derived `Encode` for `ServerMessage::Status`:
/// `variant(u32) | vec_len(u64) | [str_len(u64) + str_bytes + status(u8)]... | total(u32)`
///
/// # Errors
///
/// Returns `Err` if writing to `conn` fails.
fn encode_status_response(
    conn: &mut BufReader<IpcStream>,
    guard: &MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    buf: &mut Vec<u8>,
) -> WatchResult<()> {
    encode_status_into(guard, buf);
    conn.get_mut().write_all(buf)?;
    Ok(())
}

/// Encodes a length-prefixed `ServerMessage::Status` into `buf` directly from
/// the status map, avoiding String clones.
///
/// The payload after the length prefix is byte-identical to bincode's derived
/// `Encode` for `ServerMessage::Status { statuses, total }`.
fn encode_status_into(map: &BTreeMap<String, StatusSummary>, buf: &mut Vec<u8>) {
    let total = map.len() as u32;

    buf.clear();
    buf.extend_from_slice(&[0u8; MSG_PREFIX_LEN]); // length prefix placeholder

    // variant discriminant: Status = 0
    buf.extend_from_slice(&0u32.to_le_bytes());
    // vec length placeholder (backfilled after the loop)
    let vec_len_offset = buf.len();
    buf.extend_from_slice(&[0u8; size_of::<usize>()]);

    // entries (single pass: count + encode)
    let mut dirty_count: usize = 0;
    for (path, status) in map {
        if *status == StatusSummary::clean() {
            continue;
        }
        dirty_count += 1;
        buf.extend_from_slice(&path.len().to_le_bytes());
        buf.extend_from_slice(path.as_bytes());
        buf.push(status.bits());
    }

    // Backfill vec length
    buf[vec_len_offset..vec_len_offset + size_of::<usize>()]
        .copy_from_slice(&dirty_count.to_le_bytes());
    // total submodule count
    buf.extend_from_slice(&total.to_le_bytes());

    // Backfill the length prefix
    let msg_len = (buf.len() - MSG_PREFIX_LEN) as u32;
    buf[..MSG_PREFIX_LEN].copy_from_slice(&msg_len.to_le_bytes());
}

/// Handles a client's request to reindex the watch server. The reindex signal has already
/// been sent to the main event loop via the control channel; this function handles sending
/// progress updates back to the client over the IPC connection.
fn handle_reindex_request(
    mut conn: BufReader<IpcStream>,
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
    conn: &mut BufReader<IpcStream>,
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
    write_full_message_fixed(conn, &progress_msg[..progress_msg_len])?;

    Ok(curr == total)
}

/// Acquires the `statuses` guard. Every time the lock cannot be acquired
/// (because it is currently locked by an indexing operation in the main loop), an attempt
/// is made to send a progress update to the client.
fn get_status_guard_with_progress<'a>(
    conn: &mut BufReader<IpcStream>,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::connection::BINCODE_CFG;

    /// Builds a reference encoding using bincode's derived Encode, and compares
    /// it against our manual `encode_status_into`.
    fn assert_encoding_matches(map: &BTreeMap<String, StatusSummary>) {
        // Manual encoding
        let mut manual_buf = Vec::new();
        encode_status_into(map, &mut manual_buf);

        // Derived encoding: replicate the old clone+encode path
        let total = map.len() as u32;
        let status_out: Vec<(String, StatusSummary)> = map
            .iter()
            .filter(|(_, st)| **st != StatusSummary::clean())
            .map(|(path, st)| (path.clone(), *st))
            .collect();
        let msg = ServerMessage::Status {
            statuses: status_out,
            total,
        };
        let derived_payload = bincode::encode_to_vec(&msg, BINCODE_CFG).unwrap();

        // manual_buf has a 4-byte length prefix; derived_payload does not
        let manual_payload = &manual_buf[MSG_PREFIX_LEN..];
        assert_eq!(
            manual_payload,
            &derived_payload[..],
            "manual encoding does not match derived encoding"
        );

        // Verify the length prefix is correct
        let prefix = u32::from_le_bytes(manual_buf[..MSG_PREFIX_LEN].try_into().unwrap()) as usize;
        assert_eq!(prefix, manual_payload.len());
    }

    #[test]
    fn encode_empty_map() {
        assert_encoding_matches(&BTreeMap::new());
    }

    #[test]
    fn encode_all_clean() {
        let mut map = BTreeMap::new();
        map.insert("sub_a".to_string(), StatusSummary::clean());
        map.insert("sub_b".to_string(), StatusSummary::clean());
        assert_encoding_matches(&map);
    }

    #[test]
    fn encode_all_dirty() {
        let mut map = BTreeMap::new();
        map.insert("sub_a".to_string(), StatusSummary::MODIFIED_CONTENT);
        map.insert("sub_b".to_string(), StatusSummary::UNTRACKED_CONTENT);
        map.insert("sub_c".to_string(), StatusSummary::NEW_COMMITS);
        assert_encoding_matches(&map);
    }

    #[test]
    fn encode_mixed_clean_and_dirty() {
        let mut map = BTreeMap::new();
        map.insert("clean_one".to_string(), StatusSummary::clean());
        map.insert("dirty_one".to_string(), StatusSummary::MODIFIED_CONTENT);
        map.insert("clean_two".to_string(), StatusSummary::clean());
        map.insert(
            "dirty_two".to_string(),
            StatusSummary::STAGED | StatusSummary::NEW_COMMITS,
        );
        assert_encoding_matches(&map);
    }

    #[test]
    fn encode_combined_flags() {
        let mut map = BTreeMap::new();
        map.insert(
            "libs/system".to_string(),
            StatusSummary::MODIFIED_CONTENT
                | StatusSummary::UNTRACKED_CONTENT
                | StatusSummary::NEW_COMMITS,
        );
        assert_encoding_matches(&map);
    }
}
