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

use rustc_hash::FxHashMap;

#[cfg(not(target_os = "windows"))]
use interprocess::local_socket::traits::ListenerExt as _;
use log::{error, warn};

use crate::{
    DOT_GITMODULES, StatusSummary,
    bitset::BitSet,
    connection::{
        IpcStream, cleanup_socket, create_listener, ipc_connect, ipc_socket_path,
        protocol::SHUTDOWN_ACK, write_full_message_fixed,
    },
    git::parse_gitmodules,
    watch::WatchResult,
};

use classify::{EventType, event_is_idle_activity};
use event_loop::HandleEventsExit;
use layout::GitLayout;
use trace::wtrace;
use update::InFlightTracker;

use super::client_handler::handle_client_connection;
use super::progress::ProgressSubscribers;

const IDLE_SERVER_TIMEOUT: Duration = Duration::from_secs(60);

/// The submodule status map
pub(super) type StatusMap = Mutex<BTreeMap<String, StatusSummary>>;

/// Message receiver type for a watcher
type WatchReceiver = crossbeam_channel::Receiver<Result<notify::Event, notify::Error>>;

/// Filesystem watcher type
pub type ServerWatcher = notify::RecommendedWatcher;

/// A shared filesystem watcher instance and the receiver its events arrive on.
/// One instance hosts many watch roots; events are routed by path.
#[derive(Debug)]
struct SharedWatch {
    receiver: WatchReceiver,
    watcher: ServerWatcher,
}

/// The shared watcher instance an event or error came from.
#[derive(Clone, Copy, Debug)]
pub(super) enum WatchSource {
    /// The git-side instance: the git directory, plus shared refs for linked
    /// worktrees.
    Git,
    /// The tree-side instance: the repository root, submodule workdirs, and
    /// tripwires.
    Tree,
}

/// One watched submodule: the routing metadata for a `.gitmodules` entry.
#[derive(Debug)]
struct SubmoduleSlot {
    /// Root-relative workdir path from `.gitmodules`, also the status-map key.
    relative_path: String,
    /// Absolute workdir path, a recursive watch root on the tree watcher.
    workdir_path: PathBuf,
}

/// The state necessary to maintain a status watch for the working tree at `root_path`
struct WatchServer {
    /// The git-side watcher instance: a recursive watch on the git directory,
    /// plus the shared refs directory when a linked worktree keeps it outside.
    /// `None` while parked.
    git_watch: Option<SharedWatch>,
    /// The tree-side watcher instance, hosting the always-on non-recursive
    /// repository-root watch (which covers `.gitmodules` and doubles as the
    /// root-level tripwire), one recursive watch root per submodule workdir,
    /// and the non-recursive ancestor tripwires. `None` while parked.
    tree_watch: Option<SharedWatch>,
    /// Watched submodules by slot index. Slot `i` corresponds to entry `i` in
    /// every index-keyed structure (`pending_rescan`, in-flight tasks, and the
    /// values of the `*_to_index` maps).
    submodules: Vec<SubmoduleSlot>,
    /// Root-relative ancestor directories of every submodule, watched
    /// non-recursively on the tree watcher. A submodule's own watch root dies
    /// silently when its directory is deleted, so these surviving parent
    /// watches are what detect a submodule workdir being deleted or restored.
    /// Rebuilt alongside the tree watcher whenever submodule watch roots are
    /// (re)placed.
    tripwires: Vec<PathBuf>,
    /// Maps each submodule's **root-relative** working-directory path to its
    /// slot index, sorted so a structural event on a directory `P` can find
    /// every submodule at or under `P` via a prefix range, and an event path
    /// inside a workdir can find its slot via the greatest key at or before
    /// it. Keys are relative so these comparisons start at the distinguishing
    /// component instead of re-walking the identical repo-root prefix.
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
    /// `<root_path>/.gitmodules.lock`, the staging file git renames over
    /// `.gitmodules`
    root_gitmodules_lock_path: PathBuf,
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
    /// Client PIDs that should receive progress updates during indexing, each
    /// holding the update it has not read yet.
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
        let root_gitmodules_lock_path = root_path.join(".gitmodules.lock");
        let root_modules_path = layout.modules();
        let root_lock_path = layout.index_lock();
        let root_head_lock_path = layout.head_lock();
        let root_refs_heads_path = layout.refs_heads();

        Self {
            git_watch: None,
            tree_watch: None,
            submodules: Vec::new(),
            tripwires: Vec::new(),
            workdir_to_index: BTreeMap::new(),
            pending_rescan: BitSet::with_capacity(0),
            root_path: root_path.to_path_buf(),
            root_path_shared: Arc::from(root_path),
            root_index_path,
            root_head_path,
            root_gitmodules_path,
            root_gitmodules_lock_path,
            root_git_path,
            root_modules_path,
            root_lock_path,
            root_head_lock_path,
            root_refs_heads_path,
            control_rx,
            submod_statuses: Arc::new(Mutex::new(BTreeMap::new())),
            progress_subscribers: Arc::new(Mutex::new(FxHashMap::default())),
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
                    let subscribers = Arc::clone(&subscribers);
                    // Client handlers must NOT run on rayon's global thread pool. The
                    // main thread enters rayon's work-stealing loop during
                    // `par_iter().collect()` in `populate_status_map` while holding
                    // the status map lock. If the main thread picks up a spawned
                    // handler that spins waiting for that same lock, we deadlock.
                    std::thread::spawn(move || {
                        handle_client_connection(conn, control_tx, statuses, subscribers);
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
    fn watch(
        &mut self,
        display_progress: bool,
        status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        // Place the two shared watcher instances. The git watch lives for the
        // entirety of the server's hot execution unless a watcher error requires
        // replacement. The tree watch is rebuilt by every reindex that re-places
        // submodule watch roots.
        self.place_git_watch()?;
        self.place_tree_watch()?;

        // Initial indexing with the pre-acquired guard. With no last good
        // state to fall back on, a `.gitmodules` parse failure is fatal here:
        // staying up with an empty map would render every submodule as clean.
        let entries = parse_gitmodules(&self.root_path)?;
        self.populate_status_map(entries, display_progress, true, status_guard)?;
        let mut exit_reason = self.handle_events()?;

        // Subsequent reindex iterations
        let status_lock = Arc::clone(&self.submod_statuses);
        loop {
            // Parse before touching any watcher. A broken `.gitmodules` (a
            // conflicted merge writes conflict markers into it, a mid-edit
            // save can leave invalid syntax) must not cost the healthy
            // watches: the server keeps serving the last indexed state, and
            // recovery is event-driven because the root watch reports the
            // next `.gitmodules` rewrite, which schedules the reindex that
            // reads the fixed file. A missing file parses as no entries.
            let parsed = parse_gitmodules(&self.root_path);
            let new_submod_watches = match exit_reason {
                HandleEventsExit::Park => {
                    let idle_watch = self.place_idle_watch()?;

                    // Arming the idle watcher above walks the tree, and inotify
                    // delivers each of those `opendir` calls to every watch on
                    // the same directory - including the hot watchers, which are
                    // still armed. Filtering by relevance keeps that self-inflicted
                    // `Access(Open)` burst from reading as real activity. A
                    // watcher error still counts: the hot loop reindexes on those.
                    let hot_activity = [&self.git_watch, &self.tree_watch]
                        .into_iter()
                        .flatten()
                        .any(|watch| {
                            watch.receiver.try_iter().any(|res| {
                                res.map_or(true, |event| event_is_idle_activity(&event))
                            })
                        });

                    if hot_activity {
                        // The timeout raced with filesystem activity. Keep the
                        // git watch and rebuild the tree watch through the
                        // existing reindex path.
                        if parsed.is_ok() {
                            self.place_tree_watch()?;
                        }
                        true
                    } else {
                        self.git_watch = None;
                        self.tree_watch = None;
                        self.submodules.clear();
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
                        exit_reason = self.handle_parked(&idle_watch)?;
                        continue;
                    }
                }
                HandleEventsExit::Wake => {
                    // A parked server holds no watches, so both instances are
                    // rebuilt even when the parse failed: without the root
                    // watch, the rewrite that recovers `.gitmodules` would go
                    // unseen.
                    self.place_git_watch()?;
                    self.place_tree_watch()?;
                    true
                }
                HandleEventsExit::IdleWatcherError => {
                    let idle_watch = self.place_idle_watch()?;
                    exit_reason = self.handle_parked(&idle_watch)?;
                    continue;
                }
                HandleEventsExit::ReindexEvent => {
                    if parsed.is_ok() {
                        self.place_tree_watch()?;
                    }
                    true
                }
                HandleEventsExit::Shutdown { .. } => break,
                HandleEventsExit::ReindexRequest { replace_watchers } => {
                    if replace_watchers && parsed.is_ok() {
                        self.place_git_watch()?;
                        self.place_tree_watch()?;
                    }
                    replace_watchers
                }
                HandleEventsExit::WatcherError { source } => {
                    // Watches may have died with the failing instance, and the
                    // submodule set may have changed while coverage was degraded,
                    // so rebuild and reindex. A tree-side failure keeps the
                    // healthy git watch. The rebuild happens even when the
                    // parse failed: a dead instance delivers no events,
                    // including the `.gitmodules` rewrite that would recover it.
                    if matches!(source, WatchSource::Git) {
                        self.place_git_watch()?;
                    }
                    self.place_tree_watch()?;
                    true
                }
            };

            match parsed {
                Ok(entries) => {
                    // A non-replacing pass reuses the live submodule slots,
                    // which is only sound while the parsed entries still line
                    // up with them one to one: retry marks and event routing
                    // key on slot indices. When `.gitmodules` changed the set
                    // (or its order) since the slots were built, upgrade to a
                    // replacing pass.
                    let place_watches = if new_submod_watches {
                        true
                    } else if self.slots_match(&entries) {
                        false
                    } else {
                        self.place_tree_watch()?;
                        true
                    };
                    let status_guard = status_lock.lock().expect("Mutex poisoned");
                    self.populate_status_map(entries, false, place_watches, status_guard)?;
                }
                Err(e) => {
                    warn!(".gitmodules failed to parse, keeping the last indexed state: {e}");
                    wtrace!(|s| GitmodulesParseFailed {
                        error: s.intern_str(&e.to_string())
                    });
                }
            }

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
