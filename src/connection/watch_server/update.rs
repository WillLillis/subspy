use std::sync::{
    Arc, Condvar, Mutex,
    atomic::{AtomicBool, Ordering},
};

use git2::Repository;
use log::error;
use rustc_hash::FxHashMap;

use crate::{StatusSummary, bitset::BitSet, connection::watch_server::WatchServer};

use super::trace::{spawn_submod_task, wtrace};

/// An in-flight rayon task for a submodule status read. Setting the cancel
/// flag signals the task to stop.
pub(super) struct InFlightTask {
    pub cancel: Arc<AtomicBool>,
    /// When `true`, new events arrived while processing and the task should
    /// re-read status when done rather than completing.
    pub dirty: bool,
}

/// Tracks which submodule watcher indices have in-flight rayon tasks.
#[derive(Default)]
pub(super) struct InFlightTracker {
    pub tasks: FxHashMap<usize, InFlightTask>,
}

/// Signals cancellation to all in-flight rayon tasks, then blocks until
/// they have all completed.
pub(super) fn wait_for_in_flight(state: &(Mutex<InFlightTracker>, Condvar)) {
    let (mutex, condvar) = state;
    let mut guard = mutex.lock().expect("InFlightTracker mutex poisoned");
    for task in guard.tasks.values() {
        task.cancel.store(true, Ordering::Relaxed);
    }
    // Tasks remove themselves from the tracker as they exit; wait for stragglers
    // that haven't observed cancellation yet.
    while !guard.tasks.is_empty() {
        guard = condvar.wait(guard).expect("InFlightTracker mutex poisoned");
    }
    drop(guard);
}

/// Signals cancellation to the in-flight rayon task for `index`, if one exists.
pub(super) fn cancel_submod_update(index: usize, state: &(Mutex<InFlightTracker>, Condvar)) {
    let tracker = state.0.lock().expect("InFlightTracker mutex poisoned");
    if let Some(task) = tracker.tasks.get(&index) {
        task.cancel.store(true, Ordering::Relaxed);
    }
}

impl WatchServer {
    /// Attempts to spawn a rayon task to update the status of the submodule at watcher `index`.
    ///
    /// If the submodule is already being processed, marks it as dirty so the in-flight task
    /// will re-check after completing. Otherwise, inserts into the processing set and spawns
    /// a rayon task that loops until no more dirty events are pending.
    ///
    /// Any previous entry for `index` in `pending_lock_retries` is cleared, since the new
    /// task supersedes the old retry request.
    #[allow(clippy::too_many_lines)]
    pub(super) fn try_spawn_submod_update(
        &self,
        index: usize,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
        pending_lock_retries: &Arc<Mutex<BitSet>>,
    ) {
        pending_lock_retries
            .lock()
            .expect("pending_lock_retries mutex poisoned")
            .remove(index);

        let mut tracker = in_flight.0.lock().expect("InFlightTracker mutex poisoned");
        if let Some(task) = tracker.tasks.get_mut(&index) {
            // Already in-flight, mark dirty so the task re-checks when done.
            task.dirty = true;
            return;
        }
        let cancel = Arc::new(AtomicBool::new(false));
        tracker.tasks.insert(
            index,
            InFlightTask {
                cancel: Arc::clone(&cancel),
                dirty: false,
            },
        );
        drop(tracker);

        let watcher = &self.watchers[index];
        let relative_path = watcher.relative_path.clone();

        let in_flight = Arc::clone(in_flight);
        let statuses = Arc::clone(&self.submod_statuses);
        // cloning the `Arc` here should be cheaper than the `PathBuf` in `self.root_path`.
        let root_path = Arc::clone(&self.root_path_shared);
        let pending_retries = Arc::clone(pending_lock_retries);

        spawn_submod_task(move || {
            // ## Lock-free submodule status reads
            //
            // No `index.lock` is acquired here. `submodule_status()` is a
            // read-only operation. It never calls `git_index_write()` in
            // libgit2 (the `GIT_DIFF_UPDATE_INDEX` flag is never set in the
            // submodule status path). Git's atomic rename pattern
            // (`index.lock`->`index`) guarantees the index file is always
            // in a consistent state for readers. Acquiring `index.lock`
            // would block concurrent git operations (commit, rebase, add,
            // etc.) that need the same lock for writing.
            //
            // ## Retry strategy for transient read failures
            //
            // If the index is transiently missing (between git deleting
            // the old file and renaming `index.lock`->`index`), the read
            // fails. Three retry paths cover all timing scenarios:
            //
            // 1. **Dirty retry (event loop already processed the rename)**:
            //    This task runs concurrently with the event loop. If the
            //    rename event arrives while we're in-flight, the event loop
            //    calls `try_spawn_submod_update` which marks us `Dirty`.
            //    After the failed read we fall through to the Dirty check,
            //    see the flag, and loop back to retry. The index is
            //    guaranteed to exist by now since the rename completed.
            //
            // 2. **New task (task exits before rename event arrives)**:
            //    If we exit before the event loop processes the rename, we
            //    remove ourselves from `InFlightTracker`. When the rename
            //    event arrives it fires `SubmoduleGitOperation`, which
            //    calls `try_spawn_submod_update`. Since we're gone, it
            //    spawns a fresh task that reads successfully.
            //
            // 3. **`SubmoduleLockRelease` safety net (abort / no rename)**:
            //    If git aborts (deletes `index.lock` without renaming), no
            //    `SubmoduleGitOperation` fires. Instead, the `Remove
            //    index.lock` event is classified as `SubmoduleLockRelease`.
            //    On exit without a Dirty retry, we insert our watcher index
            //    into `pending_retries`. The `SubmoduleLockRelease` handler
            //    checks this set and re-fires the status read. (On Linux,
            //    `Modify(Name(From)) index.lock` is also classified as
            //    `SubmoduleLockRelease` for rename events where only the
            //    source path is reported.)
            let mut cleaned_up = false;
            loop {
                if cancel.load(Ordering::Relaxed) {
                    break;
                }

                // Open a fresh Repository on every iteration. git2 caches
                // the index and refdb in-memory after first access, so
                // reusing a handle across dirty retries would read stale
                // data when the index changed between iterations (e.g.
                // rapid `git add` calls staging different gitlinks).
                // Opening is cheap (config + refdb setup, no heavy I/O).
                let repo = match Repository::open(&root_path) {
                    Ok(r) => r,
                    Err(e) => {
                        error!("Failed to open repository for submodule update: {e}");
                        break;
                    }
                };

                let read_ok =
                    match repo.submodule_status(&relative_path, git2::SubmoduleIgnore::None) {
                        Ok(st) => {
                            let submod_status: StatusSummary = st.into();
                            wtrace!(|s| ReReadOk {
                                rel: s.intern_str(&relative_path),
                                status: submod_status,
                            });
                            if !cancel.load(Ordering::Relaxed) {
                                let mut guard = statuses.lock().expect("StatusMap mutex poisoned");
                                if let Some(entry) = guard.get_mut(relative_path.as_str()) {
                                    *entry = submod_status;
                                } else {
                                    guard.insert(relative_path.clone(), submod_status);
                                }
                            }
                            true
                        }
                        #[cfg_attr(not(trace_events), allow(unused_variables))]
                        Err(e) => {
                            wtrace!(|s| ReReadFailed {
                                rel: s.intern_str(&relative_path),
                                code: e.code(),
                                class: e.class(),
                                msg: s.intern_str(e.message()),
                            });
                            false
                        }
                    };

                // Handle pending_retries before acquiring the tracker lock.
                // This preserves lock ordering (pending_retries->tracker),
                // matching `try_spawn_submod_update` to avoid deadlocks.
                if !read_ok && !cancel.load(Ordering::Relaxed) {
                    pending_retries
                        .lock()
                        .expect("pending_retries mutex poisoned")
                        .insert(index);
                } else {
                    // Clear any stale entry from a previous failed iteration
                    pending_retries
                        .lock()
                        .expect("pending_retries mutex poisoned")
                        .remove(index);
                }

                // Dirty check + task removal under a single lock hold.
                //
                // This is critical: if these were separate critical sections,
                // the event loop could mark the task Dirty in the gap between
                // the check and the removal. The task would then remove
                // itself without re-reading, silently dropping the event.
                let (mutex, _) = &*in_flight;
                let mut tracker = mutex.lock().expect("InFlightTracker mutex poisoned");
                if let Some(task @ InFlightTask { dirty: true, .. }) = tracker.tasks.get_mut(&index)
                {
                    // Another event arrived while we were processing,
                    // clear the flag and re-check.
                    task.dirty = false;
                    continue;
                }
                tracker.tasks.remove(&index);
                drop(tracker);
                cleaned_up = true;
                break;
            }

            // Early exits (cancellation, repo-open failure) skip the
            // atomic dirty-check-and-remove above. Clean up the tracker
            // entry so `wait_for_in_flight` doesn't block indefinitely.
            if !cleaned_up {
                let (mutex, _) = &*in_flight;
                let mut tracker = mutex.lock().expect("InFlightTracker mutex poisoned");
                tracker.tasks.remove(&index);
                drop(tracker);
            }
            let (_, condvar) = &*in_flight;
            condvar.notify_one();
        });
    }
}
