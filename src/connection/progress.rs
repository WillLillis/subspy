//! Progress-update vocabulary shared between the watch server (which
//! broadcasts indexing progress) and the client handler (which forwards the
//! pending update to subscribed clients).

use std::sync::Mutex;

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

/// Client PIDs subscribed to indexing progress, each holding the update it has
/// not read yet.
pub(super) type ProgressSubscribers = Mutex<FxHashMap<u32, Option<ProgressUpdate>>>;

/// Makes `progress_val` the pending update for every subscriber, replacing
/// whatever each had not yet read.
///
/// # Panics
///
/// Panics if the mutex has been poisoned.
#[inline]
pub(super) fn broadcast_progress(subscribers: &ProgressSubscribers, progress_val: ProgressUpdate) {
    for pending in subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .values_mut()
    {
        *pending = Some(progress_val);
    }
}
