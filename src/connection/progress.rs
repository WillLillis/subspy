//! Progress-update vocabulary shared between the watch server (which
//! broadcasts indexing progress) and the client handler (which forwards the
//! pending update to subscribed clients).

use std::sync::{
    Mutex,
    atomic::{AtomicU32, Ordering},
};

use bincode::{BorrowDecode, Encode};
use rustc_hash::FxHashMap;

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

/// What an indexing pass tells its subscribers.
#[derive(Debug, Clone, Copy)]
pub(super) enum ProgressEvent {
    Update(ProgressUpdate),
    /// The pass failed, so no further update for it will come.
    Failed,
}

/// Client PIDs subscribed to indexing progress, each holding the event it has
/// not read yet.
pub(super) type ProgressSubscribers = Mutex<FxHashMap<u32, Option<ProgressEvent>>>;

/// Makes `progress_val` the pending update for every subscriber, replacing
/// whatever each had not yet read.
///
/// # Panics
///
/// Panics if the mutex has been poisoned.
#[inline]
pub(super) fn broadcast_progress(subscribers: &ProgressSubscribers, progress_val: ProgressUpdate) {
    broadcast(subscribers, ProgressEvent::Update(progress_val));
}

/// Records one more completed item in `completed` and makes the new count the
/// pending update for every subscriber.
///
/// # Panics
///
/// Panics if the mutex has been poisoned.
pub(super) fn advance_progress(
    subscribers: &ProgressSubscribers,
    completed: &AtomicU32,
    total: u32,
) {
    let mut subscribers = subscribers.lock().expect("Subscribers mutex poisoned");
    let curr = completed.fetch_add(1, Ordering::Relaxed) + 1;
    for pending in subscribers.values_mut() {
        *pending = Some(ProgressEvent::Update(ProgressUpdate::new(curr, total)));
    }
}

/// Tells every subscriber that the indexing pass it waited on failed, replacing
/// whatever each had not yet read.
///
/// # Panics
///
/// Panics if the mutex has been poisoned.
pub(super) fn broadcast_indexing_failed(subscribers: &ProgressSubscribers) {
    broadcast(subscribers, ProgressEvent::Failed);
}

fn broadcast(subscribers: &ProgressSubscribers, event: ProgressEvent) {
    for pending in subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .values_mut()
    {
        *pending = Some(event);
    }
}
