use std::{
    io::BufReader,
    ops::Bound,
    path::Path,
    sync::{Arc, Condvar, Mutex},
};

use log::error;
use notify::{EventKind, event::ModifyKind};

use super::debounce::{DebounceKind, ReindexDebounce, earliest_deadline};
use super::trace::wtrace;

use crate::{
    StatusSummary,
    bitset::BitSet,
    connection::{
        IpcStream,
        watch_server::{
            ControlMessage, DOT_GITMODULES_WATCHER_IDX, EventType, InFlightTracker,
            ROOT_WATCHER_COUNT, StatusMap, WatchList, WatchListItem, WatchServer,
            update::{cancel_submod_update, wait_for_in_flight},
        },
    },
    watch::WatchResult,
};

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
        // Two debounced reindex deadlines. `gitmodules` is armed by a
        // `.gitmodules` change and bumped by subsequent root git events.
        // `structural` is armed when a tripwire sees a submodule workdir
        // (re)appear, and bumped by later tripwire and root-watcher events, so
        // its reindex reads the settled state once the restoring operation's
        // burst dies down rather than racing a half-finished one.
        // `earliest_deadline` collapses the two for the select below.
        let mut gitmodules = ReindexDebounce::new(DebounceKind::Gitmodules);
        let mut structural = ReindexDebounce::new(DebounceKind::Structural);

        loop {
            #[allow(clippy::single_match_else)]
            let oper = if let Some(deadline) =
                earliest_deadline(gitmodules.deadline(), structural.deadline())
            {
                match sel.select_deadline(deadline) {
                    Ok(oper) => oper,
                    Err(_) => {
                        // No new events within the debounce window-> trigger
                        // the deferred reindex.
                        wtrace!(ReindexExpired);
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
                            // A structural change (workdir appearing/disappearing) needs
                            // a reindex to re-arm watches; any other tripwire event seen
                            // while one is already pending just pushes the window out.
                            let needs_reindex = self.handle_tripwire_event(
                                &event,
                                &in_flight,
                                &pending_lock_retries,
                            );
                            if needs_reindex {
                                structural.arm();
                            } else {
                                structural.bump();
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
                Ok(event) => {
                    // Of the watcher events, only the root `.git/`and `.gitmodules` ones
                    // extend a pending structural reindex (tripwire events arm and bump
                    // it too, above). A restoring git op churns `.git/modules/<name>`
                    // (config.lock, index.lock, the index rename), which the recursive
                    // `.git` watcher sees. Bumping on that defers the reindex until the op
                    // releases `index.lock` rather than contending with it. A submodule's
                    // own watcher can't witness its workdir reappearing (it's dead until
                    // the reindex re-arms it), so submodule watchers don't extend the
                    // window. No-op when unarmed.
                    if index < ROOT_WATCHER_COUNT {
                        structural.bump();
                    }
                    match self.classify_and_trace_event(&event, index) {
                        Some(EventType::RootGitOperation) => {
                            if index == DOT_GITMODULES_WATCHER_IDX {
                                // .gitmodules changed, defer reindex. Don't
                                // spawn submodule tasks here: individual
                                // submodule statuses aren't affected until the
                                // reindex runs, and the git operation that
                                // modified .gitmodules will produce its own
                                // root events (index rename, etc.) that spawn
                                // tasks independently.
                                gitmodules.arm();
                            } else {
                                gitmodules.bump();
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
                                && lock_release_needs_reread(
                                    i,
                                    &pending_lock_retries,
                                    &self.submod_statuses,
                                    &self.watchers[i].relative_path,
                                )
                            {
                                self.try_spawn_submod_update(i, &in_flight, &pending_lock_retries);
                            }
                        }
                        Some(EventType::SubmoduleChange) | None => {}
                    }
                }
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
                wtrace!(|s| TripwireFired {
                    kind: event.kind,
                    rel: s.intern_path(rel),
                    idx,
                    reindex: reindex_kind,
                });
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

/// Whether a `SubmoduleLockRelease` for watcher `index` should trigger a status
/// re-read, consuming any pending lock-retry request for it.
///
/// Re-reads when either:
/// - a prior lock-free read failed and registered a retry in
///   `pending_lock_retries` (the incremental path's safety net), or
/// - the submodule's cached status is `LOCK_FAILURE` -- e.g. a full reindex
///   timed out acquiring this submodule's `index.lock` (a stale lock), recorded
///   `LOCK_FAILURE`, and never entered `pending_lock_retries`. The lock now
///   being gone (the op finished/aborted, or the user cleared the stale lock)
///   means a lock-free re-read will now succeed.
///
/// The two locks are taken in separate statements, never held simultaneously.
fn lock_release_needs_reread(
    index: usize,
    pending_lock_retries: &Mutex<BitSet>,
    submod_statuses: &StatusMap,
    relative_path: &str,
) -> bool {
    // Always consume any registered retry request, matching the prior inline
    // `pending_lock_retries.remove(i)`; `remove` returns whether it was set.
    let pending = pending_lock_retries
        .lock()
        .expect("pending_lock_retries mutex poisoned")
        .remove(index);
    let lock_failed = submod_statuses
        .lock()
        .expect("StatusMap mutex poisoned")
        .get(relative_path)
        .is_some_and(|s| s.contains(StatusSummary::LOCK_FAILURE));
    pending || lock_failed
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

    // -- lock_release_needs_reread --

    use std::collections::BTreeMap;

    #[test]
    fn lock_release_rereads_on_pending_retry() {
        // Existing behavior: a registered retry (the incremental path's safety
        // net) triggers a re-read, and is consumed so it can't re-fire.
        let mut set = BitSet::with_capacity(4);
        set.insert(2);
        let pending = Mutex::new(set);
        let statuses: StatusMap = Mutex::new(BTreeMap::new());
        assert!(lock_release_needs_reread(2, &pending, &statuses, "sub"));
        assert!(
            !lock_release_needs_reread(2, &pending, &statuses, "sub"),
            "the pending retry must be consumed by the first call"
        );
    }

    #[test]
    fn lock_release_rereads_on_cached_lock_failure() {
        // The fix: a reindex that recorded LOCK_FAILURE (and so never entered
        // `pending_lock_retries`) still gets re-read when the lock is released --
        // e.g. the user clears a stale `index.lock`. Without this, the submodule
        // would stay LOCK_FAILURE until some unrelated event touched it.
        let pending = Mutex::new(BitSet::with_capacity(4));
        let statuses: StatusMap = Mutex::new(BTreeMap::from([(
            "sub".to_string(),
            StatusSummary::LOCK_FAILURE,
        )]));
        assert!(lock_release_needs_reread(0, &pending, &statuses, "sub"));
    }

    #[test]
    fn lock_release_skips_clean_dirty_or_absent() {
        // No spurious re-read: a clean or ordinarily-dirty cached status (or no
        // entry at all) with no pending retry must not re-fire on every
        // `index.lock` removal.
        let pending = Mutex::new(BitSet::with_capacity(4));
        let statuses: StatusMap = Mutex::new(BTreeMap::from([
            ("clean".to_string(), StatusSummary::clean()),
            ("dirty".to_string(), StatusSummary::UNTRACKED_CONTENT),
        ]));
        assert!(!lock_release_needs_reread(0, &pending, &statuses, "clean"));
        assert!(!lock_release_needs_reread(0, &pending, &statuses, "dirty"));
        assert!(!lock_release_needs_reread(
            0, &pending, &statuses, "missing"
        ));
    }
}
