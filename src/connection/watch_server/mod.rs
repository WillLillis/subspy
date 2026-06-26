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

// Defines the `wtrace!` macro (imported by path where used) plus the trace
// capture machinery. `pub` only under `--cfg trace_events`, where
// `capture_for`/`dump_for` are reachable by the test harness; a normal build
// keeps it private, adding no public surface.
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

use classify::EventType;
use event_loop::HandleEventsExit;
use layout::GitLayout;
use update::InFlightTracker;

use super::client_handler::handle_client_connection;
use super::progress::{ProgressMap, ProgressSubscribers};

/// `.git/` and `.gitmodules`
const ROOT_WATCHER_COUNT: usize = 2;
// Root watch indices are stable across re-indexes
const DOT_GITMODULES_WATCHER_IDX: usize = 0;
const DOT_GIT_WATCHER_IDX: usize = 1;

/// Type alias for the submodule status map mutex
pub(super) type StatusMap = Mutex<BTreeMap<String, StatusSummary>>;

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
    /// Filesystem watchers, one per submodule (plus the two root watchers).
    watchers: WatchList,
    /// Non-recursive "tripwire" watches on the ancestor directories of every
    /// submodule, up to and including the repo root. A submodule's own watcher
    /// dies silently when its directory is `rm -rf`'d, so these surviving parent
    /// watches are what detect a submodule workdir being deleted or restored.
    /// Rebuilt alongside `watchers` whenever submodule watches are (re)placed.
    tripwires: WatchList,
    /// Maps each submodule's **root-relative** working-directory path to its
    /// watcher index, sorted so a tripwire event on a directory `P` can find
    /// every submodule at or under `P` via a prefix range. Keys are relative so
    /// these comparisons start at the distinguishing component instead of re-walking
    /// the identical repo-root prefix.
    workdir_to_index: BTreeMap<PathBuf, usize>,
    /// Watcher indices of submodules to skip updating (due to being in a rebase)
    skip_set: BitSet,
    /// Whether a rebase is in progress in the root repository
    root_rebasing: bool,

    // NOTE: Commonly used paths are pre-computed and stored here to avoid redundant heap allocs
    // in hot loops. They are derived from the repository's resolved `GitLayout`
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
    /// `<git_dir>` -- the per-worktree git dir (`Repository::path`); the
    /// recursive watch target
    root_git_path: PathBuf,
    /// `<git_dir>/modules` -- this working tree's submodule gitdirs
    root_modules_path: PathBuf,
    /// `<git_dir>/index.lock`
    root_lock_path: PathBuf,
    /// `<git_dir>/HEAD.lock`
    root_head_lock_path: PathBuf,
    /// `<common_dir>/refs/heads` -- branch refs, shared across linked worktrees
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

/// Control messages sent from the listener thread to the main event loop
pub(super) enum ControlMessage {
    Reindex { replace_watchers: bool },
    Shutdown { conn: BufReader<IpcStream> },
    Debug { conn: BufReader<IpcStream> },
}

impl WatchServer {
    /// Builds a server for the working tree at `root_path` with its already
    /// resolved [`GitLayout`]. Splitting resolution (fallible, opens the repo)
    /// from construction keeps `new` infallible and lets the per-worktree git
    /// dir differ from the shared common dir (see [`GitLayout`]).
    pub fn new(
        root_path: &Path,
        layout: &GitLayout,
        control_rx: crossbeam_channel::Receiver<ControlMessage>,
    ) -> Self {
        // Per-worktree paths come from the git dir; only refs are shared, so
        // `root_refs_heads_path` is anchored on the common dir.
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
            skip_set: BitSet::with_capacity(0),
            root_rebasing: false,
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
    /// Returns a shutdown flag and the thread's `JoinHandle`. To stop the
    /// listener, [`watch`] sets the flag and connects once to the socket: the
    /// flag is checked after each `accept`, and the self-connection wakes the
    /// otherwise-parked `accept` so the thread sees the flag and returns, ready
    /// to be joined.
    ///
    /// # Errors
    ///
    /// Returns `std::io::Error` if the thread cannot be created
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
                    // When set, this `conn` is the shutdown self-connection from
                    // `watch`.
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

    /// Sends a shutdown acknowledgment to the client over the IPC connection.
    fn signal_shutdown(mut conn: BufReader<IpcStream>) {
        if let Err(e) = write_full_message_fixed(&mut conn, &SHUTDOWN_ACK) {
            error!("Failed to send shutdown ack -- {e}");
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
                        let (new_rx, new_watcher) =
                            Self::place_submodule_watch(&self.watchers[index].watch_path)?;
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
}

/// Runs the watch server for the repository at `root_dir`.
///
/// `root_dir` must be canonicalized.
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
    // Resolve the git-dir layout once up front: a linked worktree keeps its
    // index/HEAD/modules in `.git/worktrees/<name>/`, not `<root>/.git`.
    let layout = GitLayout::resolve(root_dir)?;
    let mut server = WatchServer::new(root_dir, &layout, control_rx);

    // Lock status map before accepting connections so clients block (with
    // progress updates) until initial indexing completes instead of reading
    // an empty map.
    let status_lock = Arc::clone(&server.submod_statuses);
    let status_guard = status_lock.lock().expect("Mutex poisoned");

    let (listener_shutdown, listener_handle) = server.spawn_listener(control_tx)?;
    let result = server.watch(display_progress, status_guard);

    // Stop the listener thread: set the flag, then connect once to wake its
    // parked `accept` so it observes the flag and returns, and join it.
    listener_shutdown.store(true, Ordering::Release);
    let _ = ipc_connect(&ipc_socket_path(root_dir));
    let _ = listener_handle.join();

    // Socket file cleanup can't be tied to IpcListener's Drop because the
    // listener is moved into a background thread. Crashes that skip this are
    // handled by create_listener's stale socket recovery on next startup.
    cleanup_socket(root_dir);
    result
}
