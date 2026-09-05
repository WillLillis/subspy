use std::{
    io::BufReader,
    ops::Bound,
    path::Path,
    sync::{Arc, Condvar, Mutex},
    time::Instant,
};

use log::error;
use notify::{EventKind, event::ModifyKind};

use super::classify::event_is_idle_activity;
use super::debounce::{DebounceKind, ReindexDebounce};
use super::trace::wtrace;

use crate::{
    bitset::BitSet,
    connection::{
        IpcStream,
        watch_server::{
            ControlMessage, DOT_GITMODULES_WATCHER_IDX, EventType, InFlightTracker,
            ROOT_WATCHER_COUNT, WatchEntry, WatchServer, update::wait_for_in_flight,
        },
    },
    watch::WatchResult,
};

/// Reason `handle_events` exited its select loop
pub(super) enum HandleEventsExit {
    /// The hot watcher set has been idle long enough to park.
    Park,
    /// The parked-state watcher observed filesystem activity.
    Wake,
    /// The parked-state watcher reported an error.
    IdleWatcherError,
    /// A filesystem event requires a reindex.
    ReindexEvent,
    /// A reindex was requested by a client.
    ReindexRequest { replace_watchers: bool },
    /// A shutdown was requested by a client.
    Shutdown { conn: BufReader<IpcStream> },
    /// A filesystem watcher at `index` reported an error.
    WatcherError { index: usize },
    /// A tripwire watcher at `index` reported an error.
    TripwireError { index: usize },
}

/// The source a [`crossbeam_channel::Select`] operation came from.
#[derive(Clone, Copy)]
enum SelectSource {
    /// Index of the selected filesystem watcher in [`WatchServer::watchers`].
    Watcher(usize),
    /// Index of the selected filesystem watcher in [`WatchServer::tripwires`].
    Tripwire(usize),
    /// The idle timer fired.
    Idle,
    /// A message on [`WatchServer::control_rx`] channel from the listener thread.
    Control,
}

impl WatchServer {
    /// The meat of the logic for the watch server. Handles incoming watcher events and updates
    /// server state accordingly. This function will exit if:
    ///     - a reindex is required by filesystem events
    ///     - a client message requesting a reindex is received
    ///     - a client message requesting a shutdown is received
    ///     - a watcher error is detected
    ///     - the idle timer expires
    #[expect(clippy::too_many_lines)]
    pub(super) fn handle_events(&mut self) -> WatchResult<HandleEventsExit> {
        // Shared state for parallel submodule status updates
        let in_flight: Arc<(Mutex<InFlightTracker>, Condvar)> =
            Arc::new((Mutex::new(InFlightTracker::default()), Condvar::new()));
        // Watcher indices whose latest submodule status read failed. A later lock
        // release retries the read unless another watcher event supersedes it.
        let pending_status_retries: Arc<Mutex<BitSet>> =
            Arc::new(Mutex::new(BitSet::with_capacity(self.watchers.len())));
        // Two debounced reindex deadlines. `gitmodules_debounce` is armed by a
        // `.gitmodules` change and bumped by subsequent root git events.
        // `tripwire_debounce` is armed when a tripwire sees a submodule workdir
        // (re)appear, and bumped by later tripwire and root-watcher events, so
        // its reindex reads the settled state once the restoring operation's
        // burst dies down.
        let mut gitmodules_debounce = ReindexDebounce::new(DebounceKind::Gitmodules);
        let mut tripwire_debounce = ReindexDebounce::new(DebounceKind::Structural);

        self.drain_pending_rescans(&in_flight, &pending_status_retries);

        let mut sel = crossbeam_channel::Select::new();
        register_select(
            &mut sel,
            &self.watchers,
            &self.tripwires,
            None,
            &self.control_rx,
        );
        let mut idle_deadline = Instant::now() + super::IDLE_SERVER_TIMEOUT;

        loop {
            let deadline = next_deadline(
                gitmodules_debounce.deadline(),
                tripwire_debounce.deadline(),
                idle_deadline,
            );
            let Ok(oper) = sel.select_deadline(deadline) else {
                let exit = deadline_expiry(
                    gitmodules_debounce.deadline(),
                    tripwire_debounce.deadline(),
                    idle_deadline,
                    Instant::now(),
                );
                if matches!(&exit, HandleEventsExit::Park) {
                    wtrace!(ReindexExpired);
                }
                wait_for_in_flight(&in_flight);
                return Ok(exit);
            };
            // Decode which receiver fired. The `Control` and `Tripwire` arms fully
            // handle their event, while the Watcher arm yields the watcher index for
            // the match below.
            let index = match select_source(
                oper.index(),
                self.watchers.len(),
                self.tripwires.len(),
                false,
            ) {
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
                        self.handle_debug_request(&mut conn, Some(&in_flight));
                        continue;
                    }
                },
                SelectSource::Tripwire(tripwire) => {
                    match oper.recv(&self.tripwires[tripwire].receiver)? {
                        Ok(event) => {
                            idle_deadline = Instant::now() + super::IDLE_SERVER_TIMEOUT;
                            // A structural change (workdir appearing/disappearing) needs
                            // a reindex to re-arm watches. Any other tripwire event seen
                            // while one is already pending just pushes the window out.
                            let needs_reindex = self.handle_tripwire_event(
                                &event,
                                &in_flight,
                                &pending_status_retries,
                            );
                            if needs_reindex {
                                tripwire_debounce.arm();
                            } else {
                                tripwire_debounce.bump();
                            }
                        }
                        Err(e) => {
                            wait_for_in_flight(&in_flight);
                            error!("Tripwire watcher error: {e}");
                            return Ok(HandleEventsExit::TripwireError { index: tripwire });
                        }
                    }
                    continue;
                }
                SelectSource::Watcher(index) => index,
                SelectSource::Idle => {
                    unreachable!("idle watcher is not registered in the hot event loop")
                }
            };

            match oper.recv(&self.watchers[index].receiver)? {
                Ok(event) => {
                    idle_deadline = Instant::now() + super::IDLE_SERVER_TIMEOUT;
                    // Of the watcher events, only the root `.git/` and `.gitmodules` ones
                    // extend a pending structural reindex (tripwire events arm and bump
                    // it too, above). A restoring git op churns `.git/modules/<name>`
                    // (config.lock, index.lock, the index rename), which the recursive
                    // `.git` watcher sees. Bumping on that defers the reindex until the op
                    // releases `index.lock` (rather than contending with it). A submodule's
                    // own watcher can't witness its workdir reappearing (it's dead until
                    // the reindex re-arms it), so submodule watchers don't extend the
                    // window. No-op when unarmed.
                    if index < ROOT_WATCHER_COUNT {
                        tripwire_debounce.bump();
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
                                gitmodules_debounce.arm();
                            } else {
                                gitmodules_debounce.bump();
                                for i in ROOT_WATCHER_COUNT..self.watchers.len() {
                                    self.try_spawn_submod_update(
                                        i,
                                        &in_flight,
                                        &pending_status_retries,
                                    );
                                }
                            }
                        }
                        Some(EventType::SubmoduleChange) => {
                            self.try_spawn_submod_update(
                                index,
                                &in_flight,
                                &pending_status_retries,
                            );
                        }
                        Some(EventType::SubmoduleGitOperation) => {
                            if let Some(i) = self.submod_for_event(&event) {
                                self.try_spawn_submod_update(
                                    i,
                                    &in_flight,
                                    &pending_status_retries,
                                );
                            } else {
                                // A relevant event under `.git/modules`, but no current route.
                                // This probably means the worktree/gitdir topology changed while
                                // watchers weren't active. Reconcile from disk after the burst.
                                tripwire_debounce.arm();
                            }
                        }
                        Some(EventType::SubmoduleLockRelease) => {
                            if let Some(i) = self.submod_for_event(&event) {
                                if lock_release_needs_reread(i, &pending_status_retries) {
                                    self.try_spawn_submod_update(
                                        i,
                                        &in_flight,
                                        &pending_status_retries,
                                    );
                                }
                            } else {
                                // A relevant event under `.git/modules`, but no current route.
                                // This probably means the worktree/gitdir topology changed while
                                // watchers weren't active. Reconcile from disk after the burst.
                                tripwire_debounce.arm();
                            }
                        }
                        None => {}
                    }
                }
                Err(e) => {
                    wait_for_in_flight(&in_flight);
                    return Ok(self.handle_watcher_error(index, &e));
                }
            }
        }
    }

    /// Waits for activity or control input while the hot watcher set is parked.
    pub(super) fn handle_parked(&self, idle_watcher: &WatchEntry) -> WatchResult<HandleEventsExit> {
        let mut sel = crossbeam_channel::Select::new();
        register_select(&mut sel, &[], &[], Some(idle_watcher), &self.control_rx);

        loop {
            let oper = sel.select();
            let source = select_source(oper.index(), 0, 0, true);
            match source {
                SelectSource::Idle => match oper.recv(&idle_watcher.receiver)? {
                    // Arming a recursive watch makes notify walk the tree, and
                    // its own `opendir` calls come back as one `Access(Open)`
                    // per directory (~9k on boost). Waking on those would
                    // re-park and re-arm forever, so the parked loop applies the
                    // same setup-noise filter as the park transition.
                    Ok(event) => {
                        if event_is_idle_activity(&event) {
                            return Ok(HandleEventsExit::Wake);
                        }
                    }
                    Err(error) => {
                        error!("Idle watcher error: {error}");
                        wtrace!(IdleWatcherError);
                        return Ok(HandleEventsExit::IdleWatcherError);
                    }
                },
                SelectSource::Control => match oper.recv(&self.control_rx)? {
                    ControlMessage::Reindex { .. } => {
                        return Ok(HandleEventsExit::Wake);
                    }
                    ControlMessage::Shutdown { conn } => {
                        return Ok(HandleEventsExit::Shutdown { conn });
                    }
                    ControlMessage::Debug { mut conn } => {
                        self.handle_debug_request(&mut conn, None);
                    }
                },
                SelectSource::Watcher(_) | SelectSource::Tripwire(_) => unreachable!(),
            }
        }
    }

    /// Logs a watcher error and records it in [`Self::last_watcher_error`].
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
    /// filesystem). For example, an `rm -rf` was seen on CI to surface as a `Create`
    /// for the now-gone dir. The reindex it triggers re-reads actual state and tolerates
    /// an absent workdir. Events with no submodule at/under the path are repo-root
    /// churn, ignored.
    fn handle_tripwire_event(
        &self,
        event: &notify::Event,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
        pending_status_retries: &Arc<Mutex<BitSet>>,
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
            // Tripwire dirs are all under the root, so events on them are too:
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
                self.try_spawn_submod_update(idx, in_flight, pending_status_retries);
            }
        }
        needs_reindex
    }

    /// Finds the watcher index of the submodule whose `.git/modules/` path matches the event.
    #[inline]
    pub(super) fn submod_for_event(&self, event: &notify::Event) -> Option<usize> {
        event.paths.iter().find_map(|p| {
            p.ancestors()
                .find_map(|ancestor| self.modules_path_to_index.get(ancestor))
                .copied()
        })
    }
}

/// A lock release is a chance to retry a failed status read. Consuming the entry
/// ensures that the release triggers at most one retry.
fn lock_release_needs_reread(index: usize, pending_status_retries: &Mutex<BitSet>) -> bool {
    pending_status_retries
        .lock()
        .expect("pending_status_retries mutex poisoned")
        .remove(index)
}

/// Chooses the next hot-loop deadline, giving reindex deadlines priority on ties.
fn next_deadline(gitmodules: Option<Instant>, tripwire: Option<Instant>, idle: Instant) -> Instant {
    let reindex = [gitmodules, tripwire].into_iter().flatten().min();

    match reindex {
        Some(deadline) if deadline <= idle => deadline,
        _ => idle,
    }
}

/// Converts an elapsed hot-loop deadline into the corresponding loop exit.
fn deadline_expiry(
    gitmodules: Option<Instant>,
    tripwire: Option<Instant>,
    idle: Instant,
    now: Instant,
) -> HandleEventsExit {
    let reindex_expired = [gitmodules, tripwire]
        .into_iter()
        .flatten()
        .any(|deadline| deadline <= now);

    if reindex_expired {
        HandleEventsExit::ReindexEvent
    } else {
        debug_assert!(idle <= now);
        HandleEventsExit::Park
    }
}

/// Decodes an index returned by a [`crossbeam_channel::Select`] configured by
/// [`register_select`].
///
/// The watcher band starts with the [`ROOT_WATCHER_COUNT`] root watchers,
/// followed by the submodule watchers (totalling `n_watchers`). Those indices pass
/// through unchanged. Tripwire indices are rebased by `n_watchers`, followed by
/// the control channel.
const fn select_source(
    index: usize,
    n_watchers: usize,
    n_tripwires: usize,
    has_idle: bool,
) -> SelectSource {
    if index < n_watchers {
        SelectSource::Watcher(index)
    } else if index < n_watchers + n_tripwires {
        SelectSource::Tripwire(index - n_watchers)
    } else if has_idle && index == n_watchers + n_tripwires {
        SelectSource::Idle
    } else {
        SelectSource::Control
    }
}

/// Registers every receiver on `sel` in the canonical order [`select_source`]
/// decodes. All `watchers`, then all `tripwires`, then the control channel.
pub(super) fn register_select<'a>(
    sel: &mut crossbeam_channel::Select<'a>,
    watchers: &'a [WatchEntry],
    tripwires: &'a [WatchEntry],
    idle_watcher: Option<&'a WatchEntry>,
    control_rx: &'a crossbeam_channel::Receiver<ControlMessage>,
) {
    for WatchEntry { receiver, .. } in watchers {
        sel.recv(receiver);
    }
    for WatchEntry { receiver, .. } in tripwires {
        sel.recv(receiver);
    }
    if let Some(WatchEntry { receiver, .. }) = idle_watcher {
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
        assert!(matches!(
            select_source(0, 2, 1, false),
            SelectSource::Watcher(0)
        ));
        assert!(matches!(
            select_source(1, 2, 1, false),
            SelectSource::Watcher(1)
        ));
        assert!(matches!(
            select_source(2, 2, 1, false),
            SelectSource::Tripwire(0)
        ));
        assert!(matches!(
            select_source(3, 2, 1, false),
            SelectSource::Control
        ));

        // No tripwires: the control channel sits immediately after the watchers.
        assert!(matches!(
            select_source(2, 2, 0, false),
            SelectSource::Control
        ));

        // The tripwire band is reported as a 0-based index local to `tripwires`.
        assert!(matches!(
            select_source(2, 2, 3, false),
            SelectSource::Tripwire(0)
        ));
        assert!(matches!(
            select_source(4, 2, 3, false),
            SelectSource::Tripwire(2)
        ));
        assert!(matches!(
            select_source(5, 2, 3, false),
            SelectSource::Control
        ));

        // With an idle watcher, it occupies the slot immediately before control.
        assert!(matches!(select_source(5, 2, 3, true), SelectSource::Idle));
        assert!(matches!(
            select_source(6, 2, 3, true),
            SelectSource::Control
        ));
    }
}
