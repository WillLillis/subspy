//! The watch server: monitors filesystem events on submodule working trees,
//! maintains a cached status map, and serves status queries over IPC.

use std::{
    collections::{BTreeMap, VecDeque},
    io::BufReader,
    path::{Path, PathBuf},
    sync::{
        Arc, Condvar, Mutex, MutexGuard,
        atomic::{AtomicBool, Ordering},
    },
    time::{Duration, Instant},
};

use rustc_hash::{FxHashMap, FxHashSet};

use git2::Repository;
#[cfg(not(target_os = "windows"))]
use interprocess::local_socket::traits::ListenerExt as _;
use log::{error, info, trace};
use notify::{
    Event, EventKind, Watcher,
    event::{AccessKind, AccessMode, ModifyKind},
};

use crate::{
    DOT_GIT, DOT_GITMODULES, StatusSummary,
    connection::{
        BINCODE_CFG, DebugState, IpcStream, ServerMessage, cleanup_socket, create_listener,
        ipc_socket_path, write_full_message,
    },
    create_progress_bar,
    git::parse_gitmodules,
    watch::{LockFileGuard, WatchResult},
};

use super::{
    client_handler::{ProgressUpdate, broadcast_progress, handle_client_connection},
    try_lock_for,
};

/// `.git/` and `.gitmodules`
const ROOT_WATCHER_COUNT: usize = 2;
// Root watch indices are stable across re-indexes
const DOT_GITMODULES_WATCHER_IDX: usize = 0;
const DOT_GIT_WATCHER_IDX: usize = 1;

const DEBUG_LOCK_TIMEOUT: Duration = Duration::from_secs(5);

/// Fallback timeout for triggering a reindex after `.gitmodules` changes when
/// no subsequent git operation produces a root event (e.g. `git submodule add`
/// without a follow-up `git commit`).
const REINDEX_DEBOUNCE: Duration = Duration::from_millis(200);

/// Type alias for the submodule status map mutex
pub(super) type StatusMap = Mutex<BTreeMap<String, StatusSummary>>;

/// Type alias for the progress queue mutex
pub(super) type ProgressMap = Mutex<FxHashMap<u32, VecDeque<ProgressUpdate>>>;

/// Set of client PIDs that should receive progress updates during indexing
pub(super) type ProgressSubscribers = Mutex<FxHashSet<u32>>;

/// Message receiver type for a watcher
type WatchReceiver = crossbeam_channel::Receiver<Result<notify::Event, notify::Error>>;

/// Watcher type alias
pub type ServerWatcher = notify::RecommendedWatcher;

/// Item watched by the server
#[derive(Debug)]
struct WatchListItem {
    watch_path: PathBuf,
    relative_path: String,
    receiver: WatchReceiver,
    watcher: ServerWatcher,
}

impl WatchListItem {
    const fn new(
        relative_path: String,
        watch_path: PathBuf,
        receiver: WatchReceiver,
        watcher: ServerWatcher,
    ) -> Self {
        Self {
            watch_path,
            relative_path,
            receiver,
            watcher,
        }
    }
}

type WatchList = Vec<WatchListItem>;

/// The primary state necessary to maintain a status watch over the repository at `root_path`
struct WatchServer {
    /// Filesystem watchers
    watchers: WatchList,
    /// Watcher indices of submodules to skip updating (due to being in a rebase)
    skip_set: FxHashSet<usize>,
    /// Whether a rebase is in progress in the root repository
    root_rebasing: bool,

    // NOTE: Commonly used paths are pre-computed and stored here to avoid redundant heap allocs
    // in hot loops
    /// Root path to the repository being watched
    root_path: PathBuf,
    /// `<root_path>/.git/index`
    root_index_path: PathBuf,
    /// `<root_path>/.git/HEAD`
    root_head_path: PathBuf,
    /// `<root_path>/.gitmodules`
    root_gitmodules_path: PathBuf,
    /// `<root_path>/.git`
    root_git_path: PathBuf,
    /// `<root_path>/.git/modules`
    root_modules_path: PathBuf,
    /// `<root_path>/.git/index.lock`
    root_lock_path: PathBuf,
    /// `<root_path>/.git/HEAD.lock`
    root_head_lock_path: PathBuf,
    /// `<root_path>/.git/refs/heads`
    root_refs_heads_path: PathBuf,

    /// Receiver for control messages from the listener thread
    control_rx: crossbeam_channel::Receiver<ControlMessage>,
    /// The main map of the server, associating submodule relative paths (from the repository's
    /// `.gitmodules` file) to the given submodule's summarized status.
    submod_statuses: Arc<StatusMap>,
    /// Associates a given client pid with a queue of indexing progress updates.
    progress_queue: Arc<ProgressMap>,
    /// Client PIDs that should receive progress updates during indexing.
    progress_subscribers: Arc<ProgressSubscribers>,
    /// The last watcher error that triggered a reindex, if any.
    last_watcher_error: Option<String>,
    /// Maps a submodule's `.git/modules/<name>` path to its watcher index.
    /// Used by `submod_for_event` to avoid a linear scan over all watchers.
    modules_path_to_index: FxHashMap<PathBuf, usize>,
}

/// Summarizes an event received from a watcher. Create with `get_event_type`
#[derive(Debug, Copy, Clone)]
enum EventType {
    /// Something changed in `.git/` or `.gitmodules` that may affect submodule statuses
    RootGitOperation,
    /// A change occurred in one of the watched submodule's source
    SubmoduleChange,
    /// A change occurred in one of the watched submodule's `.git/` subdirectory
    SubmoduleGitOperation,
    /// A submodule's `index.lock` was removed, indicating a git operation completed
    /// or was aborted. Used to re-fire deferred status reads.
    SubmoduleLockRelease,
    /// A rebase started within a submodule
    SubmoduleRebaseStart,
    /// A rebase ended within a submodule
    SubmoduleRebaseEnd,
    /// A rebase started within the root repository
    RootRebaseStart,
    /// A rebase ended within the root repository
    RootRebaseEnd,
}

/// Reason `handle_events` exited its select loop
enum HandleEventsExit {
    /// A reindex was required due to a root git operation or rebase event
    ReindexEvent,
    /// A reindex was requested by a client
    ReindexRequest { replace_watchers: bool },
    /// A shutdown was requested by a client
    Shutdown { conn: BufReader<IpcStream> },
    /// A filesystem watcher at `index` reported an error
    WatcherError { index: usize },
}

/// Control messages sent from the listener thread to the main event loop
pub(super) enum ControlMessage {
    Reindex { replace_watchers: bool },
    Shutdown { conn: BufReader<IpcStream> },
    Debug { conn: BufReader<IpcStream> },
}

/// An in-flight rayon task for a submodule status read. Setting the cancel
/// flag signals the task to stop.
struct InFlightTask {
    cancel: Arc<AtomicBool>,
    /// When `true`, new events arrived while processing and the task should
    /// re-read status when done rather than completing.
    dirty: bool,
}

/// Tracks which submodule watcher indices have in-flight rayon tasks.
#[derive(Default)]
struct InFlightTracker {
    tasks: FxHashMap<usize, InFlightTask>,
}

/// Signals cancellation to all in-flight rayon tasks, then blocks until
/// they have all completed.
fn wait_for_in_flight(state: &(Mutex<InFlightTracker>, Condvar)) {
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
fn cancel_submod_update(index: usize, state: &(Mutex<InFlightTracker>, Condvar)) {
    let tracker = state.0.lock().expect("InFlightTracker mutex poisoned");
    if let Some(task) = tracker.tasks.get(&index) {
        task.cancel.store(true, Ordering::Relaxed);
    }
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
struct GitmodulesTracker {
    state: GitmodulesDeferral,
    /// Fallback deadline: if no subsequent root event arrives before this
    /// instant, `handle_events` returns `ReindexEvent`.
    deadline: Option<Instant>,
}

impl GitmodulesTracker {
    #[inline]
    const fn new() -> Self {
        Self {
            state: GitmodulesDeferral::Idle,
            deadline: None,
        }
    }

    /// Returns the current reindex deadline, if any.
    #[inline]
    const fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// Called when `.gitmodules` itself changes. Resets the tracker to begin
    /// deferring the reindex until a subsequent operation completes.
    #[inline]
    const fn on_gitmodules_changed(&mut self) {
        self.state = GitmodulesDeferral::Pending;
        self.deadline = None;
    }

    /// Called when a non-`.gitmodules` root git event arrives. Updates the
    /// deferral state based on whether the event belongs to the same git
    /// operation that modified `.gitmodules`.
    #[inline]
    fn on_root_event(&mut self, event: &Event) {
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

/// Returns the converted `StatusSummary` status for the submodule at `relative_path` guarded by
/// `lock_path`. If the lock file at `lock_path` cannot be acquired, returns
/// `Ok(StatusSummary::LOCK_FAILURE)`.
fn get_submod_status(
    repo: &Repository,
    relative_path: &str,
    lock_path: &Path,
) -> WatchResult<StatusSummary> {
    let lock = LockFileGuard::acquire(lock_path);
    let status: StatusSummary = if lock.is_ok() {
        repo.submodule_status(relative_path, git2::SubmoduleIgnore::None)?
            .into()
    } else {
        // Pass failures to acquire the relevant `index.lock` file as pseudo
        // statuses so they can be displayed to the user to resolve.
        error!(
            "Failed to acquire lock file `{}` before retrieving status",
            lock_path.display()
        );
        StatusSummary::LOCK_FAILURE
    };
    // Explicitly drop `lock` as soon as possible, rather than at some point after the return
    drop(lock);
    Ok(status)
}

impl WatchServer {
    pub fn new(root_path: &Path, control_rx: crossbeam_channel::Receiver<ControlMessage>) -> Self {
        let root_git_path = root_path.join(DOT_GIT);
        let root_index_path = root_git_path.join("index");
        let root_head_path = root_git_path.join("HEAD");
        let root_gitmodules_path = root_path.join(DOT_GITMODULES);
        let root_modules_path = root_git_path.join("modules");
        let root_lock_path = root_git_path.join("index.lock");
        let root_head_lock_path = root_git_path.join("HEAD.lock");
        let root_refs_heads_path = root_git_path.join("refs").join("heads");

        Self {
            watchers: Vec::new(),
            skip_set: FxHashSet::default(),
            root_rebasing: false,
            root_path: root_path.to_path_buf(),
            root_index_path,
            root_head_path,
            root_gitmodules_path,
            root_git_path,
            root_modules_path,
            root_lock_path,
            root_head_lock_path,
            root_refs_heads_path,
            control_rx,
            submod_statuses: Arc::new(Mutex::new(BTreeMap::new())),
            progress_queue: Arc::new(Mutex::new(FxHashMap::default())),
            progress_subscribers: Arc::new(Mutex::new(FxHashSet::default())),
            last_watcher_error: None,
            modules_path_to_index: FxHashMap::default(),
        }
    }

    /// Spawns a detached listener thread to handle incoming client connections
    ///
    /// # Errors
    ///
    /// Returns `std::io::Error` if the thread cannot be created
    fn spawn_listener(
        &self,
        control_tx: crossbeam_channel::Sender<ControlMessage>,
    ) -> std::io::Result<()> {
        let listener = create_listener(&self.root_path)?;
        let statuses = Arc::clone(&self.submod_statuses);
        let progress = Arc::clone(&self.progress_queue);
        let subscribers = Arc::clone(&self.progress_subscribers);

        std::thread::Builder::new()
            .name("subspy_listener".to_string())
            .spawn(move || {
                // The listener thread runs until the process exits and is cleaned up by the OS
                for conn in listener.incoming().filter_map(|c| match c {
                    Ok(c) => Some(c),
                    Err(e) => {
                        error!("Incoming connection failed: {e}");
                        None
                    }
                }) {
                    let control_tx = control_tx.clone();
                    let statuses = Arc::clone(&statuses);
                    let progress = Arc::clone(&progress);
                    let subscribers = Arc::clone(&subscribers);
                    // Client handlers must NOT run on rayon's global thread pool. The
                    // main thread enters rayon's work-stealing loop during
                    // `par_iter().collect()` in `populate_status_map` while holding
                    // the status map lock. If the main thread picks up a spawned
                    // handler that spins waiting for that same lock, we deadlock.
                    std::thread::spawn(move || {
                        handle_client_connection(conn, control_tx, statuses, progress, subscribers);
                    });
                }
            })?;

        Ok(())
    }

    /// Places a watcher of type `mode` on `watch_path`. Returns the receiver and watcher.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if the watcher cannot be created
    fn place_watch(
        watch_path: impl AsRef<Path>,
        mode: notify::RecursiveMode,
    ) -> notify::Result<(WatchReceiver, ServerWatcher)> {
        let (tx, rx) = crossbeam_channel::unbounded();
        let log_full_path = watch_path.as_ref().to_path_buf();
        let mut watcher = ServerWatcher::new(
            move |res: Result<notify::Event, notify::Error>| {
                if let Err(e) = tx.send(res) {
                    error!(
                        "Watcher for {} failed to send -- {e}",
                        log_full_path.display()
                    );
                }
            },
            notify::Config::default(),
        )?;
        watcher.watch(watch_path.as_ref(), mode)?;

        Ok((rx, watcher))
    }

    /// Places watchers on the root path independent of the given repository's submodules
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if any watchers cannot be created
    fn place_root_watchers(&mut self) -> notify::Result<()> {
        let (rx, watcher) = match Self::place_watch(
            self.root_gitmodules_path.as_path(),
            notify::RecursiveMode::NonRecursive, // ignored
        ) {
            Ok((rx, watcher)) => (rx, watcher),
            Err(e) => {
                error!(
                    "Failed to place root watch at `{}` - {e}",
                    self.root_gitmodules_path.display()
                );
                Err(e)?
            }
        };
        self.watchers.push(WatchListItem::new(
            DOT_GITMODULES.to_owned(),
            self.root_gitmodules_path.clone(),
            rx,
            watcher,
        ));

        let (rx, watcher) = match Self::place_watch(
            self.root_git_path.as_path(),
            notify::RecursiveMode::Recursive,
        ) {
            Ok((rx, watcher)) => (rx, watcher),
            Err(e) => {
                error!(
                    "Failed to place root watch at `{}` - {e}",
                    self.root_git_path.display()
                );
                Err(e)?
            }
        };
        self.watchers.push(WatchListItem::new(
            DOT_GIT.to_owned(),
            self.root_git_path.clone(),
            rx,
            watcher,
        ));

        debug_assert_eq!(self.watchers.len(), ROOT_WATCHER_COUNT);
        Ok(())
    }

    /// Gathers the status for all submodules within the given repository. When
    /// `place_submod_watches` is true, also places watchers on their directories.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if any watchers cannot be created, or `git2::Error` if any
    /// git operation fails.
    #[allow(clippy::too_many_lines)]
    fn populate_status_map(
        &mut self,
        display_progress: bool,
        place_submod_watches: bool,
        mut status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        use std::sync::atomic::{AtomicU32, Ordering};

        use rayon::prelude::*;

        let gitmodule_entries = {
            let _lock = LockFileGuard::acquire(&self.root_lock_path)?;
            parse_gitmodules(&self.root_path)?
        };

        if gitmodule_entries.is_empty() {
            log::warn!(
                "No submodules found in {}",
                self.root_path.join(".gitmodules").display()
            );
        }

        self.root_rebasing = self.root_git_path.join("rebase-merge").exists();

        info!("Indexing project at {}", self.root_path.display());
        let n_submodules = gitmodule_entries.len() as u32;
        let progress_bar = display_progress
            .then(|| create_progress_bar(u64::from(n_submodules), "Indexing submodules"));

        broadcast_progress(
            &self.progress_subscribers,
            &self.progress_queue,
            ProgressUpdate::new(0, n_submodules),
        );

        let completed = AtomicU32::new(0);
        let root_path = &self.root_path;
        let progress_subscribers = &self.progress_subscribers;
        let progress_queue = &self.progress_queue;
        let tl_repo = thread_local::ThreadLocal::new();

        let results: Vec<_> = gitmodule_entries
            .into_par_iter()
            .map(|(_, relative_path, _)| {
                let sub_start = std::time::Instant::now();

                let full_path = root_path.join(&relative_path);

                // TODO: This would be better as a `try` block if that's ever stabilized
                // (https://github.com/rust-lang/rust/issues/31436)
                // (`.git/modules/` path, status, is in rebase)
                let inner: WatchResult<(PathBuf, StatusSummary, bool)> = (|| {
                    let repo = tl_repo.get_or_try(|| Repository::open(root_path))
                        .map_err(|e| {
                            error!("Failed to open repository while indexing {relative_path}: {e}");
                            e
                        })?;

                    let modules_path = match self.get_modules_path(&relative_path) {
                        Ok(p) => p,
                        Err(e) => {
                            error!(
                                "Failed to get modules path for submodule {relative_path} - {e}, skipping...",
                            );
                            Err(e)?
                        }
                    };
                    // This is definitely a race condition, and is not meant to catch "active"
                    // rebases while the status map is being populated. Instead, the intention is
                    // for "stalled" rebases (i.e. that has hit a conflict that must be manually
                    // resolved) so that we can properly skip updating this submodule until its
                    // rebase has been completed.
                    let is_in_rebase = modules_path.join("rebase-merge").exists();

                    let status = if is_in_rebase {
                        StatusSummary::NEW_COMMITS
                    } else {
                        match get_submod_status(
                            repo,
                            &relative_path,
                            &modules_path.join("index.lock"),
                        ) {
                            Ok(st) => st,
                            Err(e) => {
                                error!("Failed to get {relative_path} status while populating status map: {e}");
                                Err(e)?
                            }
                        }
                    };

                    Ok((modules_path, status, is_in_rebase))
                })();

                let count = completed.fetch_add(1, Ordering::Relaxed) + 1;
                broadcast_progress(
                    progress_subscribers,
                    progress_queue,
                    ProgressUpdate::new(count, n_submodules),
                );
                if let Some(pb) = &progress_bar {
                    pb.inc(1);
                }
                trace!(
                    "Indexed {} in {}ms ({})",
                    full_path.display(),
                    sub_start.elapsed().as_millis(),
                    if inner.is_ok() { "ok" } else { "error" },
                );

                (relative_path, full_path, inner)
            })
            .collect();

        status_guard.clear();
        self.skip_set.clear();
        if place_submod_watches {
            self.modules_path_to_index.clear();
        }
        // Every submodule occupies a slot in this loop regardless of whether
        // its status read succeeded. This keeps `index` (= ROOT_WATCHER_COUNT + i)
        // aligned with watcher positions across calls: rayon preserves order for
        // indexed iterators, and `parse_gitmodules()` returns a consistent order.
        // Skipping failed submodules would shift subsequent indices and misalign
        // skip_set / modules_path_to_index with the watcher array.
        for (i, (relative_path, full_path, inner)) in results.into_iter().enumerate() {
            let index = ROOT_WATCHER_COUNT + i;
            // Only populate status/skip_set/modules_path_to_index on success.
            // Failed submodules get no status entry but still reserve a watcher
            // slot — the watcher will generate events that trigger re-reads via
            // try_spawn_submod_update, so the status will eventually converge.
            if let Ok((modules_path, status, is_in_rebase)) = inner {
                status_guard.insert(relative_path.clone(), status);
                if is_in_rebase {
                    self.skip_set.insert(index);
                }
                if place_submod_watches {
                    self.modules_path_to_index.insert(modules_path, index);
                }
            }
            if place_submod_watches {
                let (rx, watcher) =
                    Self::place_watch(&full_path, notify::RecursiveMode::Recursive)?;
                self.watchers
                    .push(WatchListItem::new(relative_path, full_path, rx, watcher));
            }
        }
        drop(status_guard);

        if let Some(pb) = &progress_bar {
            pb.finish();
        }

        Ok(())
    }

    /// Gathers a snapshot of the server's internal state for diagnostic purposes.
    fn gather_debug_state(&self, in_flight: &(Mutex<InFlightTracker>, Condvar)) -> DebugState {
        let watched_paths: Vec<(String, String, u32)> = self
            .watchers
            .iter()
            .map(|w| {
                (
                    w.relative_path.clone(),
                    w.watch_path.display().to_string(),
                    w.receiver.len() as u32,
                )
            })
            .collect();

        let skip_set: Vec<String> = self
            .skip_set
            .iter()
            .filter_map(|&idx| self.watchers.get(idx).map(|w| w.relative_path.clone()))
            .collect();

        let submodule_statuses = try_lock_for(&self.submod_statuses, DEBUG_LOCK_TIMEOUT)
            .map(|guard| guard.iter().map(|(k, v)| (k.clone(), *v)).collect());

        let in_flight_tasks = try_lock_for(&in_flight.0, DEBUG_LOCK_TIMEOUT).map(|guard| {
            guard
                .tasks
                .iter()
                .map(|(idx, state)| {
                    let rel_path = self
                        .watchers
                        .get(*idx)
                        .map_or("(unknown)", |w| w.relative_path.as_str());
                    let state_str = if state.dirty { "dirty" } else { "active" };
                    (rel_path.to_owned(), state_str.to_owned())
                })
                .collect()
        });

        let progress_queues = try_lock_for(&self.progress_queue, DEBUG_LOCK_TIMEOUT).map(|guard| {
            guard
                .iter()
                .map(|(pid, queue)| {
                    let updates: Vec<(u32, u32)> =
                        queue.iter().map(|p| (p.curr, p.total)).collect();
                    (*pid, updates)
                })
                .collect()
        });

        let progress_subscribers = try_lock_for(&self.progress_subscribers, DEBUG_LOCK_TIMEOUT)
            .map(|guard| guard.iter().copied().collect());

        DebugState {
            server_pid: std::process::id(),
            rayon_threads: rayon::current_num_threads() as u32,
            progress_subscribers,
            watcher_count: self.watchers.len() as u32,
            watched_paths,
            skip_set,
            root_rebasing: self.root_rebasing,
            root_path: self.root_path.display().to_string(),
            socket_name: ipc_socket_path(&self.root_path),
            submodule_statuses,
            in_flight: in_flight_tasks,
            progress_queues,
            last_watcher_error: self.last_watcher_error.clone(),
        }
    }

    /// Sends a shutdown acknowledgment to the client over the IPC connection.
    fn signal_shutdown(mut conn: BufReader<IpcStream>) {
        let mut buf = [0; 4]; // unit variant: 4 byte variant index (fixint)
        match bincode::encode_into_slice(ServerMessage::ShutdownAck, &mut buf, BINCODE_CFG) {
            Ok(_) => {
                if let Err(e) = write_full_message(&mut conn, &buf) {
                    error!("Failed to send shutdown ack -- {e}");
                }
            }
            Err(e) => {
                error!("Failed to encode shutdown ack -- {e}");
            }
        }
    }

    /// The main watch loop for the server. Will loop until a client shutdown request is received
    /// or an error is encountered.
    ///
    /// `status_guard` is a pre-acquired lock on the status map, ensuring clients
    /// block until initial indexing completes.
    #[expect(clippy::significant_drop_tightening)]
    fn watch(
        &mut self,
        display_progress: bool,
        status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        // Place watches on `.git/` and `.gitmodules`. These watches will live for the entirety of
        // the watch server's execution, unless a root watcher error requires replacement.
        self.place_root_watchers()?;

        // Initial indexing with the pre-acquired guard.
        self.populate_status_map(display_progress, true, status_guard)?;
        let mut exit_reason = self.handle_events()?;

        // Subsequent reindex iterations
        let status_lock = Arc::clone(&self.submod_statuses);
        loop {
            let new_submod_watches = match exit_reason {
                HandleEventsExit::ReindexEvent => {
                    self.watchers.truncate(ROOT_WATCHER_COUNT);
                    true
                }
                HandleEventsExit::Shutdown { .. } => break,
                HandleEventsExit::ReindexRequest { replace_watchers } => {
                    if replace_watchers {
                        self.watchers.clear();
                        self.place_root_watchers()?;
                    }
                    replace_watchers
                }
                HandleEventsExit::WatcherError { index } => {
                    if index < ROOT_WATCHER_COUNT {
                        // Root watcher errors require a full reindex since the
                        // submodule set may have changed
                        self.watchers.clear();
                        self.place_root_watchers()?;
                        true
                    } else {
                        let (new_rx, new_watcher) = Self::place_watch(
                            &self.watchers[index].watch_path,
                            notify::RecursiveMode::Recursive,
                        )?;
                        self.watchers[index].watcher = new_watcher;
                        self.watchers[index].receiver = new_rx;
                        false
                    }
                }
            };

            let status_guard = status_lock.lock().expect("Mutex poisoned");
            self.populate_status_map(false, new_submod_watches, status_guard)?;

            exit_reason = self.handle_events()?;
        }

        if let HandleEventsExit::Shutdown { conn } = exit_reason {
            Self::signal_shutdown(conn);
        }

        Ok(())
    }

    /// Helper to determine whether `paths` contains the `rebase-merge` path as
    /// a child of `prefix`
    #[inline]
    fn has_rebase_marker_path(paths: &[PathBuf], prefix: &Path) -> bool {
        paths
            .iter()
            .any(|p| p.starts_with(prefix) && p.file_name().is_some_and(|n| n.eq("rebase-merge")))
    }

    #[inline]
    fn is_submod_rebase_start_event(&self, event: &Event) -> bool {
        // NOTE: We could add an additional check here that the `rebase-merge` path is a directory,
        // but git shouldn't create a file with that name so it's fine
        matches!(event.kind, EventKind::Create(_))
            && Self::has_rebase_marker_path(&event.paths, &self.root_modules_path)
    }

    #[inline]
    fn is_submod_rebase_end_event(&self, event: &Event) -> bool {
        matches!(event.kind, EventKind::Remove(_))
            && Self::has_rebase_marker_path(&event.paths, &self.root_modules_path)
    }

    /// Finds the watcher index of the submodule whose `.git/modules` path matches the event.
    /// Walks ancestor paths of each event path and checks the `modules_path_to_index` map.
    #[inline]
    fn submod_for_event(&self, event: &Event) -> Option<usize> {
        event.paths.iter().find_map(|p| {
            p.ancestors()
                .find_map(|ancestor| self.modules_path_to_index.get(ancestor))
                .copied()
        })
    }

    #[inline]
    fn is_root_rebase_start_event(&self, event: &Event) -> bool {
        matches!(event.kind, EventKind::Create(_))
            && Self::has_rebase_marker_path(&event.paths, &self.root_git_path)
    }

    #[inline]
    fn is_root_rebase_end_event(&self, event: &Event) -> bool {
        matches!(event.kind, EventKind::Remove(_))
            && Self::has_rebase_marker_path(&event.paths, &self.root_git_path)
    }

    // NOTE: There's an interesting edge case here. In _theory_, all we need to do is respond
    // to changes to `.git/index`. However, when a new commit/branch is checked out, the files
    // within the repo are modified _before_ `.git/HEAD` is, and `.git/index` is modified
    // sometime before `HEAD` as well. This leads to a race condition where the watch server
    // re-indexes a submodule after `.git/index` (or one of the actual source files) was
    // modified, only sees the modified files (and _not_ the changed `HEAD`, since it hasn't
    // been updated yet), and "correctly" gets the status from `git2` as "modified content" when
    // in reality it should be "new commits". By also triggering on modifications to
    // `.git/HEAD`, we mitigate this race condition and get the correct status eventually.
    #[inline]
    fn is_index_or_head_path(p: &Path) -> bool {
        // NOTE: We don't check if `p.is_file()` here, as git sometimes deletes `index` before
        // renaming `index.lock`->`index`. If it doesn't exist at the time of the check, we'll get
        // an "incorrect" false. We _could_ check via the metadata and handle errors that way, but
        // in reality this should be just fine.
        p.file_name()
            .is_some_and(|name| name.eq("index") || name.eq("HEAD"))
    }

    /// Returns `true` if `p` is a branch ref path under a known submodule's
    /// `.git/modules/<name>/refs/heads/`. Uses `modules_path_to_index` to
    /// correctly handle multi-component submodule names (e.g. `libs/foo`).
    ///
    /// Detecting branch ref renames in submodules is critical for `git commit`:
    /// the ref update is the most reliable post-commit signal. Without it, the
    /// server can get stuck reporting pre-commit status (e.g. stale
    /// `MODIFIED_CONTENT` from staged changes that were just committed).
    fn is_submod_refs_heads(&self, p: &Path) -> bool {
        // Cheap pre-filter: if the path doesn't contain a "refs" component it
        // can't be a refs/heads update.  This avoids the expensive ancestor
        // walk + HashMap lookups for the vast majority of .git/modules events
        // (object files, pack files, logs, etc.).
        if !p.components().any(|c| c.as_os_str() == "refs") {
            return false;
        }
        p.ancestors().any(|ancestor| {
            self.modules_path_to_index.contains_key(ancestor)
                && p.strip_prefix(ancestor).is_ok_and(|rel| {
                    let mut c = rel.components();
                    c.next().is_some_and(|a| a.as_os_str() == "refs")
                        && c.next().is_some_and(|b| b.as_os_str() == "heads")
                })
        })
    }

    /// Converts a watcher event to a relevant `EventType`, if possible
    fn get_event_type(&self, event: &Event, watcher_idx: usize) -> Option<EventType> {
        if !event_is_relevant(event) {
            // File renames within submodule source trees are legitimate changes, but we
            // can't allow Modify(Name) events through globally because git's
            // `index.lock` -> `index` rename would trigger spurious reindexes.
            //
            // However, renames under `.git/modules/` _are_ meaningful, e.g. a
            // `git add` inside a submodule produces only a `MOVED_TO index` event
            // on Linux (inotify), and without this carve-out it would be silently
            // dropped. Root index renames (`index.lock`->`index`) also need
            // detection so that operations like `git add <submodule>` in the
            // parent repo are visible.
            let is_git_dir_rename = watcher_idx == DOT_GIT_WATCHER_IDX
                && matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
                && event.paths.iter().any(|p| {
                    (p.starts_with(&self.root_modules_path)
                        && (p.file_name().is_some_and(|n| {
                            n.to_str().is_some_and(|name| {
                                matches!(name, "index" | "index.lock" | "HEAD" | "HEAD.lock")
                            })
                        }) || self.is_submod_refs_heads(p)))
                        || p.eq(&self.root_index_path)
                        || p.eq(&self.root_lock_path)
                        || p.eq(&self.root_head_path)
                        || p.eq(&self.root_head_lock_path)
                        || p.starts_with(&self.root_refs_heads_path)
                });
            if !is_git_dir_rename {
                // Root watches are kept at indices 0 and 1
                let is_root_watcher = watcher_idx < ROOT_WATCHER_COUNT;
                if is_root_watcher || !matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
                {
                    return None;
                }
            }
        }

        if watcher_idx == DOT_GIT_WATCHER_IDX {
            if event
                .paths
                .iter()
                .any(|p| p.starts_with(&self.root_modules_path))
            {
                if event.paths.iter().any(|p| {
                    Self::is_index_or_head_path(p)
                        || self.is_submod_refs_heads(p)
                        // On Linux, inotify may only report the MOVED_FROM
                        // half of a `.lock` → target rename. The filename is
                        // "index.lock"/"HEAD.lock" rather than "index"/"HEAD",
                        // so `is_index_or_head_path` misses it. Treat a
                        // rename of these lock files as a completed git
                        // operation so the server re-reads submodule status.
                        || (matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
                            && p.file_name()
                                .is_some_and(|n| n == "index.lock" || n == "HEAD.lock"))
                }) {
                    // NOTE: We don't take the same `Remove` defensive measures for submodule
                    // `index`/`HEAD` operations as we do with the root repository. This is because
                    // the event loop continues to run (as opposed to breaking out for a reindex),
                    // so the rebase start event is caught in time.
                    Some(EventType::SubmoduleGitOperation)
                } else if self.is_submod_rebase_start_event(event) {
                    Some(EventType::SubmoduleRebaseStart)
                } else if self.is_submod_rebase_end_event(event) {
                    Some(EventType::SubmoduleRebaseEnd)
                } else if matches!(event.kind, EventKind::Remove(_))
                    && event
                        .paths
                        .iter()
                        .any(|p| p.file_name().is_some_and(|n| n == "index.lock"))
                {
                    Some(EventType::SubmoduleLockRelease)
                } else {
                    None
                }
            } else if event.paths.iter().any(|p| {
                p.eq(&self.root_index_path)
                    || p.eq(&self.root_head_path)
                    || p.starts_with(&self.root_refs_heads_path)
            }) {
                // Git's atomic update pattern for `index`, `HEAD`, and branch
                // refs: write to the `.lock` file, delete the original, rename
                // `.lock`-> target. The `Remove` event for the transient
                // deletion is ignored, acting on it would race with the
                // immediately following rename. All other events (writes,
                // renames) are classified as `RootGitOperation` and handled in
                // the event loop by spawning lock-free rayon tasks to re-check
                // submodule statuses.
                //
                // Detecting HEAD changes is critical for `git checkout`:
                // the index is updated before HEAD, so rayon tasks spawned
                // from the index rename may read status against the stale
                // HEAD (producing STAGED | NEW_COMMITS). When the HEAD
                // rename fires shortly after, it triggers a second round of
                // rayon tasks that correct the status.
                //
                // Detecting branch ref changes (under `refs/heads/`) is
                // critical for `git commit`: the index rename fires first,
                // but HEAD still points at the old commit, so rayon tasks
                // see a stale INDEX_MODIFIED (STAGED). The branch ref
                // rename fires shortly after and triggers a corrective
                // round.
                if matches!(event.kind, EventKind::Remove(_)) {
                    None
                } else {
                    Some(EventType::RootGitOperation)
                }
            } else if self.is_root_rebase_start_event(event) {
                Some(EventType::RootRebaseStart)
            } else if self.is_root_rebase_end_event(event) {
                Some(EventType::RootRebaseEnd)
            } else {
                None
            }
        } else if watcher_idx == DOT_GITMODULES_WATCHER_IDX {
            Some(EventType::RootGitOperation)
        } else {
            Some(EventType::SubmoduleChange)
        }
    }

    /// Returns the path to the submodule's `.git/modules/` entry (e.g.
    /// `.git/modules/libs/foo` for a submodule at `libs/foo`).
    fn get_modules_path(&self, submod_rel_path: &str) -> WatchResult<PathBuf> {
        // NOTE: There is a hypothetical bug here where if two submodules were renamed
        // to each other's names _and_ their `.git/modules` entries weren't updated (i.e.,
        // only the relative path in each submodule's `.git` file), the two paths
        // will be swapped. This is highly unlikely to cause a bug in real use, and until
        // it's proven to I would prefer to not pessimize the common case with a full read
        // and parse of the `.git` file.
        let alleged_submod_path = self.root_modules_path.join(submod_rel_path);
        if alleged_submod_path.exists() {
            return Ok(alleged_submod_path);
        }

        // The submodule was renamed at some point but its `.git` directory inside
        // `.git/modules` wasn't updated, so we have to read the submodule's `.git`
        // file to get the _actual_ relative path
        let dot_git_path = self.root_path.join(submod_rel_path).join(DOT_GIT);
        let dot_git_contents = std::fs::read_to_string(&dot_git_path)?;
        let actual_rel_path = dot_git_contents
            .strip_prefix("gitdir: ")
            .ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!(
                        "Expected {} to start with \"gitdir: \"",
                        dot_git_path.display()
                    ),
                )
            })?
            .trim();
        Ok(dunce::canonicalize(
            self.root_path.join(submod_rel_path).join(actual_rel_path),
        )?)
    }

    /// Attempts to spawn a rayon task to update the status of the submodule at watcher `index`.
    ///
    /// If the submodule is already being processed, marks it as dirty so the in-flight task
    /// will re-check after completing. Otherwise, inserts into the processing set and spawns
    /// a rayon task that loops until no more dirty events are pending.
    ///
    /// Any previous entry for `index` in `pending_lock_retries` is cleared, since the new
    /// task supersedes the old retry request.
    #[allow(clippy::too_many_lines)]
    fn try_spawn_submod_update(
        &self,
        index: usize,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
        pending_lock_retries: &Arc<Mutex<FxHashSet<usize>>>,
    ) {
        pending_lock_retries
            .lock()
            .expect("pending_lock_retries mutex poisoned")
            .remove(&index);

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
        let root_path = self.root_path.clone();
        let pending_retries = Arc::clone(pending_lock_retries);

        rayon::spawn(move || {
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
            // NOTE: The assert that exists in git2 around
            // `git_submodule_lookup` is specific to
            // `Repository::submodules()`, NOT `submodule_status()`. The
            // former is separately guarded by the root lock in
            // `populate_status_map()`. A missing index during
            // `submodule_status()` returns a git2 error, not a panic.
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
                        Err(e) => {
                            if !cancel.load(Ordering::Relaxed) {
                                trace!(
                                    "Transient read failure for {relative_path}, \
                                     will retry if dirty -- {e}",
                                );
                            }
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
                        .remove(&index);
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

    /// Handles a debug request from a client by serializing and sending the current server state.
    #[cold]
    fn handle_debug_request(
        &self,
        conn: &mut BufReader<IpcStream>,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
    ) {
        let state = self.gather_debug_state(in_flight);
        let msg = ServerMessage::DebugInfo(Box::new(state));
        match bincode::encode_to_vec(msg, BINCODE_CFG) {
            Ok(serialized) => {
                if let Err(e) = write_full_message(conn, &serialized) {
                    error!("Failed to send debug state -- {e}");
                }
            }
            Err(e) => {
                error!("Failed to encode debug state -- {e}");
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

    /// The "meat" of the logic for the watch server. Handles incoming watcher events and updates
    /// server state accordingly. This function will only exit if a reindex is required or
    /// requested, a shutdown is received via the control channel, or if a watcher error occurs.
    #[allow(clippy::too_many_lines)]
    fn handle_events(&mut self) -> WatchResult<HandleEventsExit> {
        let mut sel = crossbeam_channel::Select::new();
        // filesystem watchers
        for WatchListItem { receiver, .. } in &self.watchers {
            sel.recv(receiver);
        }
        // handles client requests from the listener thread
        let control_idx = sel.recv(&self.control_rx);

        // Shared state for parallel submodule status updates
        let in_flight: Arc<(Mutex<InFlightTracker>, Condvar)> =
            Arc::new((Mutex::new(InFlightTracker::default()), Condvar::new()));
        // Watcher indices whose rayon task failed a non-blocking lock acquisition.
        // When the corresponding `index.lock` is removed (lock released), the event
        // loop re-fires the status read.
        let pending_lock_retries: Arc<Mutex<FxHashSet<usize>>> =
            Arc::new(Mutex::new(FxHashSet::default()));
        let mut gitmodules = GitmodulesTracker::new();

        loop {
            #[allow(clippy::single_match_else)]
            let oper = if let Some(deadline) = gitmodules.deadline() {
                match sel.select_deadline(deadline) {
                    Ok(oper) => oper,
                    Err(_) => {
                        // No new events within the debounce window-> trigger
                        // the deferred reindex.
                        wait_for_in_flight(&in_flight);
                        return Ok(HandleEventsExit::ReindexEvent);
                    }
                }
            } else {
                sel.select()
            };
            let index = oper.index();

            if index == control_idx {
                match oper.recv(&self.control_rx)? {
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
                }
            }
            match oper.recv(&self.watchers[index].receiver)? {
                Ok(event) => match self.get_event_type(&event, index) {
                    Some(EventType::RootGitOperation) => {
                        if !self.root_rebasing {
                            if index == DOT_GITMODULES_WATCHER_IDX {
                                gitmodules.on_gitmodules_changed();
                            } else {
                                gitmodules.on_root_event(&event);
                            }
                            for i in ROOT_WATCHER_COUNT..self.watchers.len() {
                                if !self.skip_set.contains(&i) {
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
                    Some(EventType::SubmoduleChange) => {
                        if !self.skip_set.contains(&index) {
                            self.try_spawn_submod_update(index, &in_flight, &pending_lock_retries);
                        }
                    }
                    Some(EventType::SubmoduleGitOperation) => {
                        if let Some(i) = self.submod_for_event(&event)
                            && !self.skip_set.contains(&i)
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
                            self.skip_set.remove(&i);
                            self.try_spawn_submod_update(i, &in_flight, &pending_lock_retries);
                        }
                    }
                    Some(EventType::SubmoduleLockRelease) => {
                        if let Some(i) = self.submod_for_event(&event)
                            && !self.skip_set.contains(&i)
                            && pending_lock_retries
                                .lock()
                                .expect("pending_lock_retries mutex poisoned")
                                .remove(&i)
                        {
                            self.try_spawn_submod_update(i, &in_flight, &pending_lock_retries);
                        }
                    }
                    None => {}
                },
                Err(e) => {
                    wait_for_in_flight(&in_flight);
                    return Ok(self.handle_watcher_error(index, &e));
                }
            }
        }
    }
}

/// Determines whether `event` is relevant by its `kind`. Relevant events include writes
/// and deletions.
const fn event_is_relevant(event: &Event) -> bool {
    matches!(
        event.kind,
        EventKind::Remove(_)
            | EventKind::Access(AccessKind::Close(AccessMode::Write))
            | EventKind::Create(_)
            // Windows and macOS don't produce `Close(Write)`; file modifications
            // are reported as `Modify(...)` instead.
            | EventKind::Modify(ModifyKind::Any | ModifyKind::Data(_))
    )
}

/// Runs the watch server for the repository at `root_dir`
///
/// # Errors
///
/// Returns `Err` if communication with a client or interacting with the repository fails
///
/// # Panics
///
/// Panics if the `SUBMOD_STATUSES` mutex is poisoned.
#[expect(clippy::significant_drop_tightening)]
pub fn watch(root_dir: &Path, display_progress: bool) -> WatchResult<()> {
    let (control_tx, control_rx) = crossbeam_channel::unbounded();
    let mut server = WatchServer::new(root_dir, control_rx);

    // Lock status map before accepting connections so clients block (with
    // progress updates) until initial indexing completes instead of reading
    // an empty map.
    let status_lock = Arc::clone(&server.submod_statuses);
    let status_guard = status_lock.lock().expect("Mutex poisoned");

    server.spawn_listener(control_tx)?;
    let result = server.watch(display_progress, status_guard);
    // Socket file cleanup can't be tied to IpcListener's Drop because the
    // listener is moved into a background thread with no shutdown signal,
    // which it runs until the OS tears down the process. Instead we clean
    // up here after the server loop returns. Crashes that skip this are
    // handled by create_listener's stale socket recovery on next startup.
    cleanup_socket(root_dir);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::connection::{ClientMessage, ClientRequest};

    #[test]
    fn unit_variant_sizes() {
        let cases: &[(&str, Vec<u8>)] = &[
            (
                "ServerMessage::ShutdownAck",
                bincode::encode_to_vec(ServerMessage::ShutdownAck, BINCODE_CFG).unwrap(),
            ),
            (
                "ClientMessage::Shutdown",
                bincode::encode_to_vec(ClientMessage::Shutdown, BINCODE_CFG).unwrap(),
            ),
            (
                "ClientMessage::Debug",
                bincode::encode_to_vec(ClientMessage::Debug, BINCODE_CFG).unwrap(),
            ),
        ];

        for (name, encoded) in cases {
            assert_eq!(
                encoded.len(),
                4,
                "Expected {name} to encode to 4 bytes, got {} bytes",
                encoded.len(),
            );
        }
    }

    /// Verifies that the worst-case encoded sizes of `ClientRequest` and
    /// `ServerMessage::Indexing` / `VersionMismatch` fit within the stack
    /// buffers used to encode/decode them in `client.rs` and `client_handler.rs`.
    #[test]
    fn max_message_sizes() {
        // ClientRequest wrapping Reindex with max u32 is the largest request
        let reindex_max = bincode::encode_to_vec(
            ClientRequest::new(ClientMessage::Reindex {
                pid: u32::MAX,
                replace_watchers: true,
            }),
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            reindex_max.len() <= 10,
            "ClientRequest(Reindex(u32::MAX, true)) encoded to {} bytes, exceeds buffer size of 10",
            reindex_max.len(),
        );

        // ClientRequest wrapping Status with max u32
        let status_max = bincode::encode_to_vec(
            ClientRequest::new(ClientMessage::Status(u32::MAX)),
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            status_max.len() <= 10,
            "ClientRequest(Status(u32::MAX)) encoded to {} bytes, exceeds buffer size of 10",
            status_max.len(),
        );

        // ServerMessage::Indexing with max values (used in try_send_progress_update)
        let indexing_max = bincode::encode_to_vec(
            ServerMessage::Indexing {
                curr: u32::MAX,
                total: u32::MAX,
            },
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            indexing_max.len() <= 12,
            "ServerMessage::Indexing(u32::MAX, u32::MAX) encoded to {} bytes, exceeds buffer size of 12",
            indexing_max.len(),
        );

        // ServerMessage::VersionMismatch with max u8
        let mismatch_max = bincode::encode_to_vec(
            ServerMessage::VersionMismatch {
                server_version: u8::MAX,
            },
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            mismatch_max.len() <= 5,
            "ServerMessage::VersionMismatch(u8::MAX) encoded to {} bytes, exceeds buffer size of 5",
            mismatch_max.len(),
        );
    }

    #[test]
    fn client_request_round_trip() {
        let request = ClientRequest::new(ClientMessage::Status(42));
        let encoded = bincode::encode_to_vec(&request, BINCODE_CFG).unwrap();
        let (decoded, _): (ClientRequest, usize) =
            bincode::borrow_decode_from_slice(&encoded, BINCODE_CFG).unwrap();
        assert_eq!(request, decoded);
    }

    #[test]
    fn version_mismatch_round_trip() {
        let msg = ServerMessage::VersionMismatch { server_version: 7 };
        let encoded = bincode::encode_to_vec(&msg, BINCODE_CFG).unwrap();
        let (decoded, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&encoded, BINCODE_CFG).unwrap();
        assert_eq!(msg, decoded);
    }

    /// Hardcoded byte sequences for every IPC message variant. If any of these
    /// change, the wire format has broken: bump `IPC_VERSION` and update the
    /// expected byte slices to match the actual bytes shown in the failure output.
    #[test]
    #[allow(clippy::too_many_lines)]
    fn wire_format_stability() {
        use crate::{StatusSummary, connection::DebugState};

        let cases: &[(&str, Vec<u8>, &[u8])] = &[
            // -- ClientRequest variants --
            (
                "ClientRequest(Reindex { pid: 1, replace_watchers: false })",
                bincode::encode_to_vec(
                    ClientRequest::new(ClientMessage::Reindex {
                        pid: 1,
                        replace_watchers: false,
                    }),
                    BINCODE_CFG,
                )
                .unwrap(),
                // version(0) | variant(0,0,0,0) | pid(1,0,0,0) | bool(0)
                &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
            ),
            (
                "ClientRequest(Shutdown)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Shutdown), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(1,0,0,0)
                &[0, 1, 0, 0, 0],
            ),
            (
                "ClientRequest(Status(42))",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Status(42)), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(2,0,0,0) | pid(42,0,0,0)
                &[0, 2, 0, 0, 0, 42, 0, 0, 0],
            ),
            (
                "ClientRequest(Debug)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Debug), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(3,0,0,0)
                &[0, 3, 0, 0, 0],
            ),
            // -- ServerMessage variants --
            (
                "ServerMessage::Status(empty, total=0)",
                bincode::encode_to_vec(
                    ServerMessage::Status {
                        statuses: vec![],
                        total: 0,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(0,0,0,0) | vec_len(0,0,0,0,0,0,0,0) | total(0,0,0,0)
                &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            ),
            (
                "ServerMessage::Status(one entry, total=3)",
                bincode::encode_to_vec(
                    ServerMessage::Status {
                        statuses: vec![("sub".to_string(), StatusSummary::MODIFIED_CONTENT)],
                        total: 3,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(0,0,0,0) | vec_len(1,0,0,0,0,0,0,0)
                // | str_len(3,0,0,0,0,0,0,0) | "sub" | flags(1,0,0,0)
                // | total(3,0,0,0)
                &[
                    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, b's', b'u', b'b',
                    1, 0, 0, 0, 3, 0, 0, 0,
                ],
            ),
            (
                "ServerMessage::Indexing { curr: 5, total: 10 }",
                bincode::encode_to_vec(ServerMessage::Indexing { curr: 5, total: 10 }, BINCODE_CFG)
                    .unwrap(),
                // variant(1,0,0,0) | curr(5,0,0,0) | total(10,0,0,0)
                &[1, 0, 0, 0, 5, 0, 0, 0, 10, 0, 0, 0],
            ),
            (
                "ServerMessage::ShutdownAck",
                bincode::encode_to_vec(ServerMessage::ShutdownAck, BINCODE_CFG).unwrap(),
                // variant(2,0,0,0)
                &[2, 0, 0, 0],
            ),
            (
                "ServerMessage::DebugInfo(empty)",
                bincode::encode_to_vec(
                    ServerMessage::DebugInfo(Box::new(DebugState {
                        server_pid: 0,
                        rayon_threads: 0,
                        progress_subscribers: None,
                        watcher_count: 0,
                        watched_paths: vec![],
                        skip_set: vec![],
                        root_rebasing: false,
                        root_path: String::new(),
                        socket_name: String::new(),
                        submodule_statuses: None,
                        in_flight: None,
                        progress_queues: None,
                        last_watcher_error: None,
                    })),
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(3,0,0,0)
                // | server_pid(0,0,0,0) | rayon_threads(0,0,0,0)
                // | progress_subscribers:None(0)
                // | watcher_count(0,0,0,0)
                // | watched_paths:empty(0,0,0,0,0,0,0,0)
                // | skip_set:empty(0,0,0,0,0,0,0,0)
                // | root_rebasing:false(0)
                // | root_path:""(0,0,0,0,0,0,0,0)
                // | socket_name:""(0,0,0,0,0,0,0,0)
                // | submodule_statuses:None(0)
                // | in_flight:None(0) | progress_queues:None(0)
                // | last_watcher_error:None(0)
                &[
                    3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0,
                ],
            ),
            (
                "ServerMessage::VersionMismatch { server_version: 0 }",
                bincode::encode_to_vec(
                    ServerMessage::VersionMismatch { server_version: 0 },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(4,0,0,0) | version(0)
                &[4, 0, 0, 0, 0],
            ),
        ];

        for (name, actual, expected) in cases {
            assert_eq!(
                actual, expected,
                "Wire format changed for {name}! \
                 If this is intentional, bump IPC_VERSION and update the expected bytes."
            );
        }
    }

    // -- is_index_or_head_path --

    #[test]
    fn is_index_or_head_matches_index() {
        assert!(WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/index"
        )));
    }

    #[test]
    fn is_index_or_head_matches_head() {
        assert!(WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/HEAD"
        )));
    }

    #[test]
    fn is_index_or_head_rejects_index_lock() {
        assert!(!WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/index.lock"
        )));
    }

    #[test]
    fn is_index_or_head_rejects_head_lock() {
        assert!(!WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/HEAD.lock"
        )));
    }

    #[test]
    fn is_index_or_head_rejects_other() {
        assert!(!WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/config"
        )));
    }

    // -- has_rebase_marker_path --

    #[test]
    fn has_rebase_marker_under_prefix() {
        let paths = vec![PathBuf::from(".git/modules/sub/rebase-merge")];
        assert!(WatchServer::has_rebase_marker_path(
            &paths,
            Path::new(".git/modules")
        ));
    }

    #[test]
    fn has_rebase_marker_wrong_prefix() {
        let paths = vec![PathBuf::from("/other/path/rebase-merge")];
        assert!(!WatchServer::has_rebase_marker_path(
            &paths,
            Path::new(".git/modules")
        ));
    }

    #[test]
    fn has_rebase_marker_wrong_filename() {
        let paths = vec![PathBuf::from(".git/modules/sub/rebase-apply")];
        assert!(!WatchServer::has_rebase_marker_path(
            &paths,
            Path::new(".git/modules")
        ));
    }

    #[test]
    fn has_rebase_marker_empty_paths() {
        let paths: Vec<PathBuf> = vec![];
        assert!(!WatchServer::has_rebase_marker_path(
            &paths,
            Path::new(".git/modules")
        ));
    }
}
