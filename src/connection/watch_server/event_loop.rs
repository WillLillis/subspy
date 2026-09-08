use std::{
    io::BufReader,
    ops::Bound,
    path::Path,
    sync::{Arc, Condvar, Mutex},
    time::Instant,
};

use log::error;
use notify::{EventKind, event::ModifyKind};

use super::classify::{TreeAction, event_is_idle_activity};
use super::debounce::{DebounceKind, ReindexDebounce};
use super::trace::wtrace;

use crate::{
    bitset::BitSet,
    connection::{
        IpcStream,
        watch_server::{
            ControlMessage, EventType, InFlightTracker, SharedWatch, WatchServer, WatchSource,
            update::wait_for_in_flight,
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
    /// The shared watcher for `source` reported an error.
    WatcherError { source: WatchSource },
}

impl WatchServer {
    /// The meat of the logic for the watch server. Handles incoming watcher events and updates
    /// server state accordingly. This function will exit if:
    ///     - a reindex is required by filesystem events
    ///     - a client message requesting a reindex is received
    ///     - a client message requesting a shutdown is received
    ///     - a watcher error is detected
    ///     - the idle timer expires
    pub(super) fn handle_events(&mut self) -> WatchResult<HandleEventsExit> {
        // Shared state for parallel submodule status updates
        let in_flight: Arc<(Mutex<InFlightTracker>, Condvar)> =
            Arc::new((Mutex::new(InFlightTracker::default()), Condvar::new()));
        // Slots whose latest submodule status read failed. A later lock
        // release retries the read unless another watcher event supersedes it.
        let pending_status_retries: Arc<Mutex<BitSet>> =
            Arc::new(Mutex::new(BitSet::with_capacity(self.submodules.len())));
        // Two debounced reindex deadlines. `gitmodules_debounce` is armed by a
        // `.gitmodules` change and bumped by subsequent root git events.
        // `tripwire_debounce` is armed when a tripwire sees a submodule workdir
        // (re)appear, and bumped by later structural and git-watcher events, so
        // its reindex reads the settled state once the restoring operation's
        // burst dies down.
        let mut gitmodules_debounce = ReindexDebounce::new(DebounceKind::Gitmodules);
        let mut tripwire_debounce = ReindexDebounce::new(DebounceKind::Structural);

        self.drain_pending_rescans(&in_flight, &pending_status_retries);

        // Receiver clones keep the select arms free to call methods on `self`.
        let git_rx = self
            .git_watch
            .as_ref()
            .expect("git watch not placed")
            .receiver
            .clone();
        let tree_rx = self
            .tree_watch
            .as_ref()
            .expect("tree watch not placed")
            .receiver
            .clone();
        let control_rx = self.control_rx.clone();

        let mut idle_deadline = Instant::now() + super::IDLE_SERVER_TIMEOUT;

        loop {
            let deadline = next_deadline(
                gitmodules_debounce.deadline(),
                tripwire_debounce.deadline(),
                idle_deadline,
            );
            let timeout = deadline.saturating_duration_since(Instant::now());

            crossbeam_channel::select! {
                recv(git_rx) -> res => match res? {
                    Ok(event) => {
                        idle_deadline = Instant::now() + super::IDLE_SERVER_TIMEOUT;
                        self.handle_git_event(
                            &event,
                            &in_flight,
                            &pending_status_retries,
                            &mut gitmodules_debounce,
                            &mut tripwire_debounce,
                        );
                    }
                    Err(e) => {
                        wait_for_in_flight(&in_flight);
                        return Ok(self.handle_watcher_error(WatchSource::Git, &e));
                    }
                },
                recv(tree_rx) -> res => match res? {
                    Ok(event) => {
                        idle_deadline = Instant::now() + super::IDLE_SERVER_TIMEOUT;
                        self.handle_tree_event(
                            &event,
                            &in_flight,
                            &pending_status_retries,
                            &mut gitmodules_debounce,
                            &mut tripwire_debounce,
                        );
                    }
                    Err(e) => {
                        wait_for_in_flight(&in_flight);
                        return Ok(self.handle_watcher_error(WatchSource::Tree, &e));
                    }
                },
                recv(control_rx) -> msg => match msg? {
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
                    }
                },
                default(timeout) => {
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
                }
            }
        }
    }

    /// Waits for activity or control input while the hot watcher set is parked.
    pub(super) fn handle_parked(&self, idle_watch: &SharedWatch) -> WatchResult<HandleEventsExit> {
        let idle_rx = idle_watch.receiver.clone();
        let control_rx = self.control_rx.clone();

        loop {
            crossbeam_channel::select! {
                recv(idle_rx) -> res => match res? {
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
                recv(control_rx) -> msg => match msg? {
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
            }
        }
    }

    /// Handles one event from the git watcher.
    fn handle_git_event(
        &self,
        event: &notify::Event,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
        pending_status_retries: &Arc<Mutex<BitSet>>,
        gitmodules_debounce: &mut ReindexDebounce,
        tripwire_debounce: &mut ReindexDebounce,
    ) {
        // The kernel overflowed this instance's event queue and dropped events.
        // Which ones is unknowable, so schedule a replacing reindex once the
        // burst that overflowed the queue settles.
        if event.need_rescan() {
            wtrace!(RescanFlagged);
            tripwire_debounce.arm();
        }
        // Git-watcher events extend a pending structural reindex. A restoring
        // git op churns `.git/modules/<name>` (config.lock, index.lock, the
        // index rename), which this recursive watch sees. Bumping on that
        // defers the reindex until the op releases `index.lock` (rather than
        // contending with it). A submodule workdir can't witness its own
        // reappearance (its watch root is dead until the reindex re-arms it),
        // so workdir events don't extend the window. No-op when unarmed.
        tripwire_debounce.bump();
        match self.classify_and_trace_git_event(event) {
            Some(EventType::RootGitOperation) => {
                gitmodules_debounce.bump();
                for i in 0..self.submodules.len() {
                    self.try_spawn_submod_update(i, in_flight, pending_status_retries);
                }
            }
            Some(EventType::SubmoduleGitOperation) => {
                if let Some(i) = self.submod_for_event(event) {
                    self.try_spawn_submod_update(i, in_flight, pending_status_retries);
                } else {
                    // A relevant event under `.git/modules`, but no current route.
                    // This probably means the worktree/gitdir topology changed while
                    // watchers weren't active. Reconcile from disk after the burst.
                    tripwire_debounce.arm();
                }
            }
            Some(EventType::SubmoduleLockRelease) => {
                if let Some(i) = self.submod_for_event(event) {
                    if lock_release_needs_reread(i, pending_status_retries) {
                        self.try_spawn_submod_update(i, in_flight, pending_status_retries);
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

    /// Handles one event from the tree watcher by routing each of its paths:
    /// `.gitmodules` changes defer a reindex, paths inside a submodule workdir
    /// spawn that submodule's status re-read, and structural paths go through
    /// the tripwire logic. A single event can span classes (a rename between
    /// two submodules pairs both halves into one event on a shared instance),
    /// so every path routes independently and the debounce outcomes combine
    /// afterwards.
    fn handle_tree_event(
        &self,
        event: &notify::Event,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
        pending_status_retries: &Arc<Mutex<BitSet>>,
        gitmodules_debounce: &mut ReindexDebounce,
        tripwire_debounce: &mut ReindexDebounce,
    ) {
        // The kernel overflowed this instance's event queue and dropped events.
        // Which ones is unknowable, so schedule a replacing reindex once the
        // burst that overflowed the queue settles.
        if event.need_rescan() {
            wtrace!(RescanFlagged);
            tripwire_debounce.arm();
        }
        let mut gitmodules_changed = false;
        let mut structural_seen = false;
        let mut structural_reindex = false;
        for path in &event.paths {
            let action = self.classify_tree_path(path, event);
            wtrace!(|s| TreeRouted {
                kind: event.kind,
                path: s.intern_path(path),
                action,
            });
            match action {
                TreeAction::Gitmodules => gitmodules_changed = true,
                TreeAction::Submodule(slot) => {
                    self.try_spawn_submod_update(slot, in_flight, pending_status_retries);
                }
                TreeAction::Structural => {
                    structural_seen = true;
                    if let Ok(rel) = path.strip_prefix(&self.root_path)
                        && self.handle_structural_path(
                            rel,
                            event,
                            in_flight,
                            pending_status_retries,
                        )
                    {
                        structural_reindex = true;
                    }
                }
                TreeAction::Ignored => {}
            }
        }

        if gitmodules_changed {
            // .gitmodules changed, defer reindex. Don't spawn submodule
            // tasks here: individual submodule statuses aren't affected
            // until the reindex runs, and the git operation that modified
            // .gitmodules will produce its own root events (index rename,
            // etc.) that spawn tasks independently.
            gitmodules_debounce.arm();
        }
        // A structural change (workdir appearing or moving) needs a reindex to
        // re-arm watches. Other structural or `.gitmodules` activity seen while
        // one is already pending just pushes the window out.
        if structural_reindex {
            tripwire_debounce.arm();
        } else if structural_seen || gitmodules_changed {
            tripwire_debounce.bump();
        }
    }

    /// Applies tripwire logic to `rel`, a root-relative structural path outside
    /// every submodule workdir. Returns `true` if a reindex is needed to re-arm
    /// watches.
    ///
    /// A `Remove` of a directory at/under which submodules live means those
    /// submodules' workdirs are gone -> re-read them so they flip to
    /// `DELETED_WORKDIR` (their recursive watch roots just died silently). A
    /// `Create` or rename (`Modify(Name)`) means a directory reappeared or moved
    /// -> a full reindex re-places the now-dead watch root.
    ///
    /// On macOS things are less clear. `FSEvents` event flags are advisory hints,
    /// not a reliable log (Apple's guidance is to reconcile against the real
    /// filesystem). For example, an `rm -rf` was seen on CI to surface as a `Create`
    /// for the now-gone dir. The reindex it triggers re-reads actual state and tolerates
    /// an absent workdir. Events with no submodule at/under the path are repo-root
    /// churn, ignored.
    fn handle_structural_path(
        &self,
        rel: &Path,
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
                return true;
            }
            self.try_spawn_submod_update(idx, in_flight, pending_status_retries);
        }
        false
    }

    /// Logs a watcher error and records it in [`Self::last_watcher_error`].
    fn handle_watcher_error(
        &mut self,
        source: WatchSource,
        error: &notify::Error,
    ) -> HandleEventsExit {
        let msg = format!("{source:?} watcher error: {error}");
        error!("{msg}\nReindexing to reset watchers...");
        wtrace!(WatcherErrored { source });
        self.last_watcher_error = Some(msg);
        HandleEventsExit::WatcherError { source }
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
