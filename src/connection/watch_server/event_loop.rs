use std::{
    io::BufReader,
    ops::Bound,
    path::Path,
    sync::{Arc, Condvar, Mutex},
    time::{Duration, Instant},
};

use log::error;
use notify::{EventKind, event::ModifyKind};

use crate::{
    StatusSummary,
    bitset::BitSet,
    connection::{
        IpcStream,
        watch_server::{
            ControlMessage, DOT_GITMODULES_WATCHER_IDX, EventType, InFlightTracker,
            ROOT_WATCHER_COUNT, WatchList, WatchListItem, WatchServer,
            update::{cancel_submod_update, wait_for_in_flight},
        },
    },
    watch::WatchResult,
};

/// Fallback timeout for triggering a reindex after `.gitmodules` changes when
/// no subsequent git operation produces a root event (e.g. `git submodule add`
/// without a follow-up `git commit`).
const REINDEX_DEBOUNCE: Duration = Duration::from_millis(200);

/// Reason `handle_events` exited its select loop
pub(super) enum HandleEventsExit {
    /// A reindex was required due to a root git operation or rebase event
    ReindexEvent,
    /// A reindex was requested by a client
    ReindexRequest { replace_watchers: bool },
    /// A shutdown was requested by a client
    Shutdown { conn: BufReader<IpcStream> },
    /// A filesystem watcher at `index` reported an error
    WatcherError { index: usize },
}

/// The source a `crossbeam_channel::Select` operation came from.
#[derive(Clone, Copy)]
enum SelectSource {
    /// A filesystem `watchers` entry (a root watcher or a submodule watcher),
    /// carrying its index into `watchers`.
    Watcher(usize),
    /// A `tripwires` entry, carrying its index into `tripwires`.
    Tripwire(usize),
    /// The control channel from the listener thread.
    Control,
}

/// Deferral state for `.gitmodules` changes within [`GitmodulesTracker`].
#[derive(Clone, Copy)]
enum GitmodulesDeferral {
    /// No `.gitmodules` change is pending.
    Idle,
    /// `.gitmodules` changed; waiting for the first root event from the
    /// same git operation.
    Pending,
    /// First root event consumed. Stores the tracker cookie (if any) to
    /// skip subsequent events from the same rename operation.
    Consumed(Option<usize>),
}

/// Tracks deferred reindex state after `.gitmodules` changes.
///
/// When `.gitmodules` is modified, we can't reindex immediately because the
/// git operation (e.g. `git submodule add`, `git rm -f`) also produces index
/// rename events as part of the same command. Triggering a reindex on those
/// would acquire `index.lock` before the git operation completes, causing git
/// to fail.
///
/// This state machine:
/// 1. Records that a watcher update is needed ([`Self::on_gitmodules_changed`])
/// 2. Skips events from the same git operation (via matching tracker cookie)
/// 3. Resets a debounce deadline on events from subsequent operations
/// 4. Falls back to a deadline-based reindex if no further root events arrive
#[derive(Clone, Copy)]
pub(super) struct GitmodulesTracker {
    state: GitmodulesDeferral,
    /// Fallback deadline: if no subsequent root event arrives before this
    /// instant, `handle_events` returns `ReindexEvent`.
    deadline: Option<Instant>,
}

impl GitmodulesTracker {
    #[inline]
    pub(super) const fn new() -> Self {
        Self {
            state: GitmodulesDeferral::Idle,
            deadline: None,
        }
    }

    /// Returns the current reindex deadline, if any.
    #[inline]
    pub(super) const fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// Called when `.gitmodules` itself changes. Resets the tracker to begin
    /// deferring the reindex until a subsequent operation completes.
    #[inline]
    pub(super) const fn on_gitmodules_changed(&mut self) {
        self.state = GitmodulesDeferral::Pending;
        self.deadline = None;
    }

    /// Called when a non-`.gitmodules` root git event arrives. Updates the
    /// deferral state based on whether the event belongs to the same git
    /// operation that modified `.gitmodules`.
    #[inline]
    pub(super) fn on_root_event(&mut self, event: &notify::Event) {
        match self.state {
            GitmodulesDeferral::Idle => {}
            GitmodulesDeferral::Pending => {
                // First root event after .gitmodules changed-> this is the
                // index rename from the same git operation. Record its
                // tracker cookie and start a debounce timer as a fallback
                // (in case no subsequent git command produces a root event,
                // e.g. `git submodule add` without a follow-up `git commit`).
                self.state = GitmodulesDeferral::Consumed(event.attrs.tracker());
                self.deadline = Some(Instant::now() + REINDEX_DEBOUNCE);
            }
            GitmodulesDeferral::Consumed(Some(cookie)) if event.attrs.tracker() == Some(cookie) => {
                // Same rename operation (matching tracker cookie)-> skip.
            }
            GitmodulesDeferral::Consumed(_) => {
                // Event from a subsequent git operation. Reset the debounce
                // timer rather than reindexing immediately: the operation
                // may still be in progress (e.g. `git commit` has renamed
                // the index but has not yet updated the branch ref).
                self.deadline = Some(Instant::now() + REINDEX_DEBOUNCE);
            }
        }
    }
}

impl WatchServer {
    /// The "meat" of the logic for the watch server. Handles incoming watcher events and updates
    /// server state accordingly. This function will only exit if a reindex is required or
    /// requested, a shutdown is received via the control channel, or if a watcher error occurs.
    #[expect(clippy::too_many_lines)]
    pub(super) fn handle_events(&mut self) -> WatchResult<HandleEventsExit> {
        let mut sel = crossbeam_channel::Select::new();
        register_select(&mut sel, &self.watchers, &self.tripwires, &self.control_rx);

        // Shared state for parallel submodule status updates
        let in_flight: Arc<(Mutex<InFlightTracker>, Condvar)> =
            Arc::new((Mutex::new(InFlightTracker::default()), Condvar::new()));
        // Watcher indices whose rayon task failed a non-blocking lock acquisition.
        // When the corresponding `index.lock` is removed (lock released), the event
        // loop re-fires the status read.
        let pending_lock_retries: Arc<Mutex<BitSet>> =
            Arc::new(Mutex::new(BitSet::with_capacity(self.watchers.len())));
        let mut gitmodules = GitmodulesTracker::new();

        loop {
            #[allow(clippy::single_match_else)]
            let oper = if let Some(deadline) = gitmodules.deadline() {
                match sel.select_deadline(deadline) {
                    Ok(oper) => oper,
                    Err(_) => {
                        // No new events within the debounce window-> trigger
                        // the deferred reindex.
                        wtrace!("reindex debounce expired -> reindexing");
                        wait_for_in_flight(&in_flight);
                        return Ok(HandleEventsExit::ReindexEvent);
                    }
                }
            } else {
                sel.select()
            };
            // Decode which receiver fired. The `Control` and `Tripwire` arms fully
            // handle their event, while the Watcher arm yields the watcher index for
            // the match below.
            let index = match select_source(oper.index(), self.watchers.len(), self.tripwires.len())
            {
                SelectSource::Control => match oper.recv(&self.control_rx)? {
                    ControlMessage::Reindex { replace_watchers } => {
                        wait_for_in_flight(&in_flight);
                        return Ok(HandleEventsExit::ReindexRequest { replace_watchers });
                    }
                    ControlMessage::Shutdown { conn } => {
                        wait_for_in_flight(&in_flight);
                        return Ok(HandleEventsExit::Shutdown { conn });
                    }
                    ControlMessage::Debug { mut conn } => {
                        self.handle_debug_request(&mut conn, &in_flight);
                        continue;
                    }
                },
                SelectSource::Tripwire(tripwire) => {
                    match oper.recv(&self.tripwires[tripwire].receiver)? {
                        Ok(event) => {
                            if self.handle_tripwire_event(&event, &in_flight, &pending_lock_retries)
                            {
                                wait_for_in_flight(&in_flight);
                                return Ok(HandleEventsExit::ReindexEvent);
                            }
                        }
                        Err(e) => {
                            wait_for_in_flight(&in_flight);
                            error!("Tripwire watcher error -- {e}");
                            return Ok(HandleEventsExit::ReindexEvent);
                        }
                    }
                    continue;
                }
                SelectSource::Watcher(index) => index,
            };

            match oper.recv(&self.watchers[index].receiver)? {
                Ok(event) => match self.classify_and_trace_event(&event, index) {
                    Some(EventType::RootGitOperation) => {
                        if index == DOT_GITMODULES_WATCHER_IDX {
                            // .gitmodules changed, defer reindex. Don't
                            // spawn submodule tasks here: individual
                            // submodule statuses aren't affected until the
                            // reindex runs, and the git operation that
                            // modified .gitmodules will produce its own
                            // root events (index rename, etc.) that spawn
                            // tasks independently.
                            gitmodules.on_gitmodules_changed();
                            wtrace!(".gitmodules changed -> deferring reindex");
                        } else {
                            gitmodules.on_root_event(&event);
                            wtrace!(
                                "root git op -> reindex deadline {:?}",
                                gitmodules.deadline()
                            );
                            for i in ROOT_WATCHER_COUNT..self.watchers.len() {
                                if !self.skip_set.contains(i) {
                                    self.try_spawn_submod_update(
                                        i,
                                        &in_flight,
                                        &pending_lock_retries,
                                    );
                                }
                            }
                        }
                    }
                    Some(EventType::RootRebaseStart) => {
                        self.root_rebasing = true;
                    }
                    Some(EventType::RootRebaseEnd) => {
                        wait_for_in_flight(&in_flight);
                        self.root_rebasing = false;
                        return Ok(HandleEventsExit::ReindexEvent);
                    }
                    Some(EventType::SubmoduleChange) if !self.skip_set.contains(index) => {
                        self.try_spawn_submod_update(index, &in_flight, &pending_lock_retries);
                    }
                    Some(EventType::SubmoduleGitOperation) => {
                        if let Some(i) = self.submod_for_event(&event)
                            && !self.skip_set.contains(i)
                        {
                            self.try_spawn_submod_update(i, &in_flight, &pending_lock_retries);
                        }
                    }
                    // Rebases generate an incredible volume of events, and during such an
                    // operation git continually acquires and releases `index.lock`. This,
                    // paired with the changes to the submodule's source files leads to too much
                    // contention for `index.lock`, which leads to the rebase failing partway
                    // through when git fails to acquire `index.lock`. Instead, we pause
                    // updating the relevant submodule until the rebase is completed.
                    Some(EventType::SubmoduleRebaseStart) => {
                        if let Some(i) = self.submod_for_event(&event) {
                            cancel_submod_update(i, &in_flight);
                            self.skip_set.insert(i);
                            self.submod_statuses.lock().expect("Mutex poisoned").insert(
                                self.watchers[i].relative_path.clone(),
                                StatusSummary::NEW_COMMITS,
                            );
                        }
                    }
                    Some(EventType::SubmoduleRebaseEnd) => {
                        if let Some(i) = self.submod_for_event(&event) {
                            self.skip_set.remove(i);
                            self.try_spawn_submod_update(i, &in_flight, &pending_lock_retries);
                        }
                    }
                    Some(EventType::SubmoduleLockRelease) => {
                        if let Some(i) = self.submod_for_event(&event)
                            && !self.skip_set.contains(i)
                            && pending_lock_retries
                                .lock()
                                .expect("pending_lock_retries mutex poisoned")
                                .remove(i)
                        {
                            self.try_spawn_submod_update(i, &in_flight, &pending_lock_retries);
                        }
                    }
                    Some(EventType::SubmoduleChange) | None => {}
                },
                Err(e) => {
                    wait_for_in_flight(&in_flight);
                    return Ok(self.handle_watcher_error(index, &e));
                }
            }
        }
    }

    /// Logs a watcher error and records it in `last_watcher_error`.
    fn handle_watcher_error(&mut self, index: usize, error: &notify::Error) -> HandleEventsExit {
        let msg = format!(
            "Watcher error for {}: {error}",
            self.watchers[index].relative_path
        );
        error!("{msg}\nReindexing to reset watchers...");
        self.last_watcher_error = Some(msg);
        HandleEventsExit::WatcherError { index }
    }

    /// Routes a tripwire event (a structural change to a submodule ancestor
    /// directory) to the affected submodules. Returns `true` if a reindex is
    /// needed to re-arm watches.
    ///
    /// A `Remove` of a directory at/under which submodules live means those
    /// submodules' workdirs are gone -> re-read them so they flip to
    /// `DELETED_WORKDIR` (their own recursive watches just died silently). A
    /// `Create` or rename (`Modify(Name)`) means a directory reappeared or moved
    /// -> a full reindex re-places the now-dead recursive watch.
    ///
    /// On macOS things are less clear. `FSEvents` event flags are advisory hints,
    /// not a reliable log (Apple's guidance is to reconcile against the real
    /// filesystem), so a `rm -rf` was seen on CI to surface as a `Create` for the
    /// now-gone dir. The reindex it triggers re-reads actual state and tolerates
    /// an absent workdir. Events with no submodule at/under the path are repo-root
    /// churn, ignored.
    fn handle_tripwire_event(
        &self,
        event: &notify::Event,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
        pending_lock_retries: &Arc<Mutex<BitSet>>,
    ) -> bool {
        let reindex_kind = matches!(
            event.kind,
            EventKind::Create(_) | EventKind::Modify(ModifyKind::Name(_))
        );
        let remove_kind = matches!(event.kind, EventKind::Remove(_));
        if !reindex_kind && !remove_kind {
            return false;
        }

        let mut needs_reindex = false;
        for path in &event.paths {
            // Tripwire dirs are all under the root, so events on them are too;
            // strip the root prefix to look up against the relative keys.
            let Ok(rel) = path.strip_prefix(&self.root_path) else {
                continue;
            };
            // Every submodule at or under `rel` (a prefix range over the sorted
            // map). An empty range is ordinary repo-root churn and a no-op.
            for (_, &idx) in self
                .workdir_to_index
                .range::<Path, _>((Bound::Included(rel), Bound::Unbounded))
                .take_while(|(k, _)| k.starts_with(rel))
            {
                wtrace!(
                    "tripwire {:?} {rel:?} -> submod[{idx}] (reindex={reindex_kind})",
                    event.kind,
                );
                if reindex_kind {
                    // A single affected submodule is enough to decide a reindex.
                    needs_reindex = true;
                    break;
                }
                if !self.skip_set.contains(idx) {
                    self.try_spawn_submod_update(idx, in_flight, pending_lock_retries);
                }
            }
        }
        needs_reindex
    }

    /// Finds the watcher index of the submodule whose `.git/modules` path matches the event.
    /// Walks ancestor paths of each event path and checks the `modules_path_to_index` map.
    #[inline]
    pub(super) fn submod_for_event(&self, event: &notify::Event) -> Option<usize> {
        event.paths.iter().find_map(|p| {
            p.ancestors()
                .find_map(|ancestor| self.modules_path_to_index.get(ancestor))
                .copied()
        })
    }
}

/// Decodes a `crossbeam_channel::Select` index back into its [`SelectSource`].
///
/// `handle_events` registers receivers in a fixed order: `n_watchers`
/// watchers, then `n_tripwires` tripwires, then the single control channel.
const fn select_source(index: usize, n_watchers: usize, n_tripwires: usize) -> SelectSource {
    if index < n_watchers {
        SelectSource::Watcher(index)
    } else if index < n_watchers + n_tripwires {
        SelectSource::Tripwire(index - n_watchers)
    } else {
        SelectSource::Control
    }
}

/// Registers every receiver on `sel` in the canonical order [`select_source`]
/// decodes: all `watchers`, then all `tripwires`, then the control channel.
pub(super) fn register_select<'a>(
    sel: &mut crossbeam_channel::Select<'a>,
    watchers: &'a WatchList,
    tripwires: &'a WatchList,
    control_rx: &'a crossbeam_channel::Receiver<ControlMessage>,
) {
    for WatchListItem { receiver, .. } in watchers {
        sel.recv(receiver);
    }
    for WatchListItem { receiver, .. } in tripwires {
        sel.recv(receiver);
    }
    sel.recv(control_rx);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn select_source_decodes_index_bands() {
        // `handle_events` registers receivers as: watchers, then tripwires, then
        // the control channel. For 2 watchers + 1 tripwire that is watchers
        // [0, 1], tripwire [2], control [3].
        assert!(matches!(select_source(0, 2, 1), SelectSource::Watcher(0)));
        assert!(matches!(select_source(1, 2, 1), SelectSource::Watcher(1)));
        assert!(matches!(select_source(2, 2, 1), SelectSource::Tripwire(0)));
        assert!(matches!(select_source(3, 2, 1), SelectSource::Control));

        // No tripwires: the control channel sits immediately after the watchers.
        assert!(matches!(select_source(2, 2, 0), SelectSource::Control));

        // The tripwire band is reported as a 0-based index local to `tripwires`.
        assert!(matches!(select_source(2, 2, 3), SelectSource::Tripwire(0)));
        assert!(matches!(select_source(4, 2, 3), SelectSource::Tripwire(2)));
        assert!(matches!(select_source(5, 2, 3), SelectSource::Control));
    }
}
