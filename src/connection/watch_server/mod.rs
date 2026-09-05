//! The watch server: monitors filesystem events on submodule working trees,
//! maintains a cached status map, and serves status queries over IPC.

mod classify;
mod debounce;
mod debug;
mod event_loop;
mod indexing;
mod layout;
mod placement;
mod update;

// Expose trace capture to the external test harness when enabled.
#[cfg(trace_events)]
pub mod trace;
#[cfg(not(trace_events))]
mod trace;

use std::{
    collections::BTreeMap,
    io::BufReader,
    path::{Path, PathBuf},
    sync::{
        Arc, Mutex, MutexGuard,
        atomic::{AtomicBool, Ordering},
    },
    thread::JoinHandle,
    time::Duration,
};

use rustc_hash::{FxHashMap, FxHashSet};

#[cfg(not(target_os = "windows"))]
use interprocess::local_socket::traits::ListenerExt as _;
use log::error;

use crate::{
    DOT_GITMODULES, StatusSummary,
    bitset::BitSet,
    connection::{
        IpcStream, cleanup_socket, create_listener, ipc_connect, ipc_socket_path,
        protocol::SHUTDOWN_ACK, write_full_message_fixed,
    },
    watch::WatchResult,
};

use classify::{EventType, event_is_relevant};
use event_loop::HandleEventsExit;
use layout::GitLayout;
use update::InFlightTracker;

use super::client_handler::handle_client_connection;
use super::progress::{ProgressMap, ProgressSubscribers};

/// `.git/` and `.gitmodules`
const ROOT_WATCHER_COUNT: usize = 2;
const DOT_GITMODULES_WATCHER_IDX: usize = 0;
const DOT_GIT_WATCHER_IDX: usize = 1;
const IDLE_SERVER_TIMEOUT: Duration = Duration::from_secs(60);

/// The submodule status map
pub(super) type StatusMap = Mutex<BTreeMap<String, StatusSummary>>;

/// Message receiver type for a watcher
type WatchReceiver = crossbeam_channel::Receiver<Result<notify::Event, notify::Error>>;

/// Filesystem watcher type
pub type ServerWatcher = notify::RecommendedWatcher;

/// A filesystem watcher and the metadata used to route its events.
#[derive(Debug)]
struct WatchEntry {
    watch_path: PathBuf,
    relative_path: String,
    receiver: WatchReceiver,
    watcher: ServerWatcher,
}

impl WatchEntry {
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

/// The state necessary to maintain a status watch for the working tree at `root_path`
struct WatchServer {
    /// Filesystem watchers, one per submodule (plus the two root watchers).
    watchers: Vec<WatchEntry>,
    /// Non-recursive "tripwire" watches on the ancestor directories of every
    /// submodule, up to and including the repo root. A submodule's own watcher
    /// dies silently when its directory is deleted, so these surviving parent
    /// watches are what detect a submodule workdir being deleted or restored.
    /// Rebuilt alongside `watchers` whenever submodule watches are (re)placed.
    tripwires: Vec<WatchEntry>,
    /// Maps each submodule's **root-relative** working-directory path to its
    /// watcher index, sorted so a tripwire event on a directory `P` can find
    /// every submodule at or under `P` via a prefix range. Keys are relative so
    /// these comparisons start at the distinguishing component instead of re-walking
    /// the identical repo-root prefix.
    workdir_to_index: BTreeMap<PathBuf, usize>,
    /// Submodule watcher indices needing a re-read, drained by the event loop
    /// ([`Self::handle_events`]) on its next turn.
    ///
    /// A reindex that replaces the submodule watchers marks every submodule, because
    /// those watchers are armed _after_ [`Self::populate_status_map`] reads statuses,
    /// and whatever the previous watchers had queued is dropped with them. This
    /// causes a replacing reindex to publish stale status, so they must be refreshed
    /// to converge to a correct answer.
    pending_rescan: BitSet,

    // Cache paths used in hot loops to avoid repeated `PathBuf` allocations.
    /// Root path to the working tree being watched
    root_path: PathBuf,
    /// Shared handle to `root_path` for rayon tasks. Duplicated as an `Arc`
    /// so that `try_spawn_submod_update` can move a cheap refcount bump into
    /// `'static` closures instead of cloning the `PathBuf` on every spawn.
    root_path_shared: Arc<Path>,
    /// `<git_dir>/index`
    root_index_path: PathBuf,
    /// `<git_dir>/HEAD`
    root_head_path: PathBuf,
    /// `<root_path>/.gitmodules` (a tracked file in the working tree)
    root_gitmodules_path: PathBuf,
    /// `<git_dir>`, the per-worktree git directory and recursive watch target
    root_git_path: PathBuf,
    /// `<git_dir>/modules`, containing this working tree's submodule gitdirs
    root_modules_path: PathBuf,
    /// `<git_dir>/index.lock`
    root_lock_path: PathBuf,
    /// `<git_dir>/HEAD.lock`
    root_head_lock_path: PathBuf,
    /// `<common_dir>/refs/heads`, containing branch refs shared by linked worktrees
    root_refs_heads_path: PathBuf,

    /// Receiver for control messages from the listener thread
    control_rx: crossbeam_channel::Receiver<ControlMessage>,
    /// Maps root-relative submodule paths from `.gitmodules` to cached statuses.
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

/// Control messages sent from the listener thread to the main event loop
pub(super) enum ControlMessage {
    Reindex { replace_watchers: bool },
    Shutdown { conn: BufReader<IpcStream> },
    Debug { conn: BufReader<IpcStream> },
}

impl WatchServer {
    /// Builds a server for the working tree at `root_path` with its already
    /// resolved [`GitLayout`].
    pub fn new(
        root_path: &Path,
        layout: &GitLayout,
        control_rx: crossbeam_channel::Receiver<ControlMessage>,
    ) -> Self {
        let root_git_path = layout.git_dir().to_path_buf();
        let root_index_path = layout.index();
        let root_head_path = layout.head();
        let root_gitmodules_path = root_path.join(DOT_GITMODULES);
        let root_modules_path = layout.modules();
        let root_lock_path = layout.index_lock();
        let root_head_lock_path = layout.head_lock();
        let root_refs_heads_path = layout.refs_heads();

        Self {
            watchers: Vec::new(),
            tripwires: Vec::new(),
            workdir_to_index: BTreeMap::new(),
            pending_rescan: BitSet::with_capacity(0),
            root_path: root_path.to_path_buf(),
            root_path_shared: Arc::from(root_path),
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

    /// Spawns the listener thread that accepts incoming client connections.
    ///
    /// Returns a shutdown flag and the thread's `JoinHandle`. To stop the listener,
    /// [`Self::watch`] sets the flag and connects once to the socket. The flag is
    /// checked after each `accept`, so the thread sees the flag and returns, ready
    /// to be joined.
    ///
    /// # Errors
    ///
    /// Returns [`std::io::Error`] if the thread cannot be created.
    fn spawn_listener(
        &self,
        control_tx: crossbeam_channel::Sender<ControlMessage>,
    ) -> std::io::Result<(Arc<AtomicBool>, JoinHandle<()>)> {
        let listener = create_listener(&self.root_path)?;
        let statuses = Arc::clone(&self.submod_statuses);
        let progress = Arc::clone(&self.progress_queue);
        let subscribers = Arc::clone(&self.progress_subscribers);
        let shutdown = Arc::new(AtomicBool::new(false));
        let listener_shutdown = Arc::clone(&shutdown);

        let handle = std::thread::Builder::new()
            .name("subspy_listener".to_string())
            .spawn(move || {
                for conn in listener.incoming().filter_map(|c| match c {
                    Ok(c) => Some(c),
                    Err(e) => {
                        error!("Incoming connection failed: {e}");
                        None
                    }
                }) {
                    // When set, this is the shutdown self-connection from `WatchServer::watch`.
                    if listener_shutdown.load(Ordering::Acquire) {
                        break;
                    }
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

        Ok((shutdown, handle))
    }

    /// Tries to send a shutdown acknowledgment to the client over the IPC connection.
    /// Failures are logged but not propagated.
    fn signal_shutdown(mut conn: BufReader<IpcStream>) {
        if let Err(e) = write_full_message_fixed(&mut conn, &SHUTDOWN_ACK) {
            error!("Failed to send shutdown ack: {e}");
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
                HandleEventsExit::Park => {
                    let idle_watcher = self.place_idle_watcher()?;

                    // Arming the idle watcher above walks the tree, and inotify
                    // delivers each of those `opendir` calls to every watch on
                    // the same directory - including the hot watchers, which are
                    // still armed. Filtering by relevance keeps that self-inflicted
                    // `Access(Open)` burst from reading as real activity. A
                    // watcher error still counts: the hot loop reindexes on those.
                    let hot_activity =
                        self.watchers
                            .iter()
                            .chain(self.tripwires.iter())
                            .any(|entry| {
                                entry
                                    .receiver
                                    .try_iter()
                                    .any(|res| res.map_or(true, |event| event_is_relevant(&event)))
                            });

                    if hot_activity {
                        // The timeout raced with filesystem activity. Preserve the hot
                        // state and use the existing reindex path.
                        self.watchers.truncate(ROOT_WATCHER_COUNT);
                        true
                    } else {
                        self.watchers.clear();
                        self.tripwires.clear();
                        self.pending_rescan.clear_and_resize(0);
                        self.workdir_to_index.clear();
                        self.modules_path_to_index.clear();
                        // Indexing spreads allocations across glibc's per-thread
                        // arenas, and `free` returns blocks to the arena rather
                        // than to the OS. Dropping the watchers doesn't release
                        // that, so without this a parked server measures larger
                        // than a hot one.
                        // SAFETY: `malloc_trim` takes glibc's arena locks itself
                        // and is safe to call from any thread.
                        #[cfg(all(target_os = "linux", target_env = "gnu"))]
                        unsafe {
                            libc::malloc_trim(0);
                        }
                        exit_reason = self.handle_parked(&idle_watcher)?;
                        continue;
                    }
                }
                HandleEventsExit::Wake => {
                    self.watchers.clear();
                    self.tripwires.clear();
                    self.place_root_watchers()?;
                    true
                }
                HandleEventsExit::IdleWatcherError => {
                    let idle_watcher = self.place_idle_watcher()?;
                    exit_reason = self.handle_parked(&idle_watcher)?;
                    continue;
                }
                HandleEventsExit::ReindexEvent => {
                    self.watchers.truncate(ROOT_WATCHER_COUNT);
                    true
                }
                HandleEventsExit::Shutdown { .. } => break,
                HandleEventsExit::ReindexRequest { replace_watchers } => {
                    if replace_watchers {
                        self.watchers.clear();
                        self.tripwires.clear();
                        self.place_root_watchers()?;
                    }
                    replace_watchers
                }
                HandleEventsExit::WatcherError { index } => {
                    if index < ROOT_WATCHER_COUNT {
                        // Root watcher errors require a full reindex since the
                        // submodule set may have changed.
                        self.watchers.clear();
                        self.place_root_watchers()?;
                        true
                    } else {
                        let (new_rx, new_watcher) =
                            Self::place_submodule_watch(&self.watchers[index].watch_path)?;
                        self.watchers[index].watcher = new_watcher;
                        self.watchers[index].receiver = new_rx;
                        false
                    }
                }
                HandleEventsExit::TripwireError { index } => {
                    self.tripwires.remove(index);
                    self.watchers.truncate(ROOT_WATCHER_COUNT);
                    true
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
}

/// Runs the watch server for the working tree at `root_dir`.
///
/// `root_dir` must be canonicalized.
///
/// # Errors
///
/// Returns `Err` if resolving or reading the reposiory, setting up IPC or filesystem
/// watchers, receiving watcher events, or spawning the listener thread fails.
///
/// # Panics
///
/// Panics if the submodule status map mutex is poisoned.
#[expect(clippy::significant_drop_tightening)]
pub fn watch(root_dir: &Path, display_progress: bool) -> WatchResult<()> {
    let (control_tx, control_rx) = crossbeam_channel::unbounded();
    // Resolve the git-dir layout once up front. Linked worktree keeps their
    // index, HEAD, and modules in `.git/worktrees/<name>/`.
    let layout = GitLayout::resolve(root_dir)?;
    let mut server = WatchServer::new(root_dir, &layout, control_rx);

    // Lock the status map before accepting connections so clients wait (with
    // progress updates) until initial indexing completes.
    let status_lock = Arc::clone(&server.submod_statuses);
    let status_guard = status_lock.lock().expect("Mutex poisoned");

    let (listener_shutdown, listener_handle) = server.spawn_listener(control_tx)?;
    let result = server.watch(display_progress, status_guard);

    // Stop the listener thread: set the flag, then connect once to wake its
    // parked `accept` so it observes the flag and returns, and join it.
    listener_shutdown.store(true, Ordering::Release);
    let _ = ipc_connect(&ipc_socket_path(root_dir));
    let _ = listener_handle.join();

    // Clean up the socket after the listener thread exits. `create_listener`
    // removes any stale socket left by a crash on the next startup.
    cleanup_socket(root_dir);
    result
}
