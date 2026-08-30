//! Progress-update vocabulary shared between the watch server (which
//! broadcasts indexing progress) and the client handler (which drains queued
//! updates to subscribed clients).

use std::{collections::VecDeque, sync::Mutex};

use bincode::{BorrowDecode, Encode};
use rustc_hash::{FxHashMap, FxHashSet};

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

/// Progress update queues keyed by client PID.
pub(super) type ProgressMap = Mutex<FxHashMap<u32, VecDeque<ProgressUpdate>>>;

/// Client PIDs subscribed to indexing progress updates.
pub(super) type ProgressSubscribers = Mutex<FxHashSet<u32>>;

/// Pushes `progress_val` to the progress queue for every registered subscriber.
///
/// # Panics
///
/// Panics if either mutex has been poisoned.
#[inline]
#[expect(clippy::significant_drop_tightening)]
pub(super) fn broadcast_progress(
    subscribers: &ProgressSubscribers,
    progress: &ProgressMap,
    progress_val: ProgressUpdate,
) {
    let subs = subscribers.lock().expect("Subscribers mutex poisoned");
    // Lock the progress queues only when active subscribers exist.
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
