use std::{
    collections::{BTreeMap, HashMap, HashSet, VecDeque},
    fs,
    io::BufReader,
    path::{Path, PathBuf},
    sync::{
        Arc, Condvar, Mutex, MutexGuard, TryLockError,
        atomic::{AtomicBool, Ordering},
    },
    time::{Duration, Instant},
};

use bincode::{BorrowDecode, Encode};
use git2::Repository;
use interprocess::local_socket::{Stream, traits::ListenerExt as _};
use log::{error, info, trace};
use notify::{
    Event, EventKind, Watcher,
    event::{AccessKind, AccessMode, ModifyKind},
};

use crate::{
    DOT_GIT, DOT_GITMODULES, StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, DebugState, ServerMessage, create_listener, read_full_message,
        write_full_message,
    },
    create_progress_bar,
    watch::{LockFileError, WatchError, WatchResult},
};

/// `.git/` and `.gitmodules`
const ROOT_WATCHER_COUNT: usize = 2;

const MAX_LOCKFILE_BACKOFF: Duration = Duration::from_millis(100);
const LOCKFILE_TIMEOUT: Duration = Duration::from_secs(10);

/// Type alias for the submodule status map mutex
type StatusMap = Mutex<BTreeMap<String, StatusSummary>>;

/// Type alias for the progress queue mutex
type ProgressMap = Mutex<HashMap<u32, VecDeque<ProgressUpdate>>>;

/// Set of client PIDs that should receive progress updates during indexing
type ProgressSubscribers = Mutex<HashSet<u32>>;

/// Message receiver type for a watcher
type WatchReceiver = crossbeam_channel::Receiver<Result<notify::Event, notify::Error>>;

/// Watcher type alias
type ServerWatcher = notify::RecommendedWatcher;

/// Item watched by the server
#[derive(Debug)]
struct WatchListItem {
    // need to hang onto the watched path to `unwatch` later
    watch_path: PathBuf,
    relative_path: String,
    /// Cached path to the submodule's `index.lock` file. `None` for root watchers.
    lock_file_path: Option<PathBuf>,
    receiver: WatchReceiver,
    watcher: ServerWatcher,
}

impl WatchListItem {
    const fn new(
        relative_path: String,
        watch_path: PathBuf,
        lock_file_path: Option<PathBuf>,
        receiver: WatchReceiver,
        watcher: ServerWatcher,
    ) -> Self {
        Self {
            watch_path,
            relative_path,
            lock_file_path,
            receiver,
            watcher,
        }
    }
}

type WatchList = Vec<WatchListItem>;

/// The primary state necessary to maintain a status watch over the repository at `root_path`
struct WatchServer {
    /// Whether the server should continue to watch the repository at `root_path`
    do_watch: bool,
    /// Filesystem watchers
    watchers: WatchList,
    /// Which submodules to skip indexing
    skip_set: HashSet<String>,
    /// Whether a rebase is in progress in the root repository
    root_rebasing: bool,

    // NOTE: Commonly used paths are pre-computed and stored here to avoid redundant heap allocs
    // in hot loops
    /// Root path to the repository being watched
    root_path: PathBuf,
    /// `<root_path>/.git/index`
    root_index_path: PathBuf,
    /// `<root_path>/.gitmodules`
    root_gitmodules_path: PathBuf,
    /// `<root_path>/.git`
    root_git_path: PathBuf,
    /// `<root_path>/.git/modules`
    root_modules_path: PathBuf,
    /// `<root_path>/.git/index.lock`
    root_lock_path: PathBuf,

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
}

/// Summarizes an event received from a watcher. Create with `get_event_type`
#[derive(Debug, Copy, Clone)]
enum EventType {
    /// Something changed in `.git/` or `.gitmodules`, reindex needed
    RootGitOperation,
    /// A change occurred in one of the watched submodules's source
    SubmoduleChange,
    /// A change occurred in oen of the watched submodule's `.git/` subdirectory
    SubmoduleGitOperation,
    /// A rebase started within a submodule
    SubmoduleRebaseStart,
    /// A rebase ended within a submodule
    SubmoduleRebaseEnd,
    /// A rebase started within the root repository
    RootRebaseStart,
    /// A rebase ended within the root repository
    RootRebaseEnd,
}

/// Control messages sent from the listener thread to the main event loop
enum ControlMessage {
    Reindex,
    Shutdown { conn: BufReader<Stream> },
    Debug { conn: BufReader<Stream> },
}

/// RAII guard that acquires a lock file on creation and removes it on drop.
struct LockFileGuard<'a> {
    path: &'a Path,
}

impl<'a> LockFileGuard<'a> {
    fn acquire(path: &'a Path, cancel: Option<&AtomicBool>) -> WatchResult<Self> {
        trace!("Acquiring lock file at path: {}", path.display());
        let start = Instant::now();
        let mut backoff = Duration::from_millis(1);

        loop {
            match fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(path)
            {
                Ok(_) => break,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                    if start.elapsed() >= LOCKFILE_TIMEOUT
                        || cancel.is_some_and(|c| c.load(Ordering::Relaxed))
                    {
                        Err(WatchError::LockFileAcquire(LockFileError::new(
                            path.to_path_buf(),
                            e,
                        )))?;
                    }
                    trace!("Lock file {} already exists, waiting...", path.display());
                    std::thread::sleep(backoff);
                    backoff = (backoff * 2).min(MAX_LOCKFILE_BACKOFF);
                }
                Err(e) => Err(WatchError::LockFileAcquire(LockFileError::new(
                    path.to_path_buf(),
                    e,
                )))?,
            }
        }

        trace!("Acquired lock file at path: {}", path.display());
        Ok(Self { path })
    }
}

impl Drop for LockFileGuard<'_> {
    fn drop(&mut self) {
        trace!("Releasing lock file at path: {}", self.path.display());
        if let Err(e) = fs::remove_file(self.path) {
            error!(
                "Failed to release lock file at {}: {e}",
                self.path.display()
            );
        }
    }
}

/// State of an in-flight rayon task for a status reindex.
/// The inner `Arc<AtomicBool>` is the cancellation flag shared with the task.
enum TaskState {
    /// Running normally.
    Active(Arc<AtomicBool>),
    /// Running, but new events arrived while processing, so the task should re-check when done.
    Dirty(Arc<AtomicBool>),
}

impl TaskState {
    const fn cancellation_flag(&self) -> &Arc<AtomicBool> {
        match self {
            Self::Active(c) | Self::Dirty(c) => c,
        }
    }
}

/// Tracks which submodule watcher indices have in-flight rayon tasks.
struct InFlightTracker {
    tasks: HashMap<usize, TaskState>,
}

impl InFlightTracker {
    fn new() -> Self {
        Self {
            tasks: HashMap::new(),
        }
    }
}

/// Signals cancellation to all in-flight rayon tasks, then blocks until they have
/// all completed.
fn wait_for_in_flight(state: &(Mutex<InFlightTracker>, Condvar)) {
    let (mutex, condvar) = state;
    let mut guard = mutex.lock().expect("InFlightTracker mutex poisoned");
    for task in guard.tasks.values() {
        task.cancellation_flag().store(true, Ordering::Relaxed);
    }
    while !guard.tasks.is_empty() {
        guard = condvar.wait(guard).expect("InFlightTracker mutex poisoned");
    }
    drop(guard);
}

/// Signals cancellation to the in-flight rayon task for `index`, if one exists.
/// Also clears the dirty flag so the task doesn't re-check after cancellation.
fn cancel_submod_update(index: usize, state: &(Mutex<InFlightTracker>, Condvar)) {
    let tracker = state.0.lock().expect("InFlightTracker mutex poisoned");
    if let Some(task) = tracker.tasks.get(&index) {
        task.cancellation_flag().store(true, Ordering::Relaxed);
    }
}

/// Returns the converted `StatusSummary` status for the submodule at `relative_path` guarded by
/// `lock_path`. If the lock file at `lock_path` cannot be acquired, returns
/// `Ok(StatusSummary::LOCK_FAILURE)`.
fn get_submod_status(
    repo: &Repository,
    relative_path: &str,
    lock_path: &Path,
    cancel: Option<&AtomicBool>,
) -> WatchResult<StatusSummary> {
    let lock = LockFileGuard::acquire(lock_path, cancel);
    let status: StatusSummary = match lock {
        Ok(ref _lock) => repo
            .submodule_status(relative_path, git2::SubmoduleIgnore::None)?
            .into(),
        Err(WatchError::LockFileAcquire(_)) => {
            // Pass failures to acquire the relevant `index.lock` file as pseudo
            // statuses so they can be displayed to the user to resolve.
            error!(
                "Failed to acquire lock file `{}` before retrieving status",
                lock_path.display()
            );
            StatusSummary::LOCK_FAILURE
        }
        Err(e) => return Err(e)?,
    };
    // Explicitly drop `lock` as soon as possible, rather than at some point after the return
    drop(lock);
    Ok(status)
}

impl WatchServer {
    pub fn new(root_path: &Path, control_rx: crossbeam_channel::Receiver<ControlMessage>) -> Self {
        let root_index_path = root_path.join(DOT_GIT).join("index");
        let root_gitmodules_path = root_path.join(DOT_GITMODULES);
        let root_git_path = root_path.join(DOT_GIT);
        let root_modules_path = root_path.join(DOT_GIT).join("modules");
        let root_lock_path = root_path.join(DOT_GIT).join("index.lock");

        Self {
            do_watch: true,
            watchers: Vec::new(),
            skip_set: HashSet::new(),
            root_rebasing: false,
            root_path: root_path.to_path_buf(),
            root_index_path,
            root_gitmodules_path,
            root_git_path,
            root_modules_path,
            root_lock_path,
            control_rx,
            submod_statuses: Arc::new(Mutex::new(BTreeMap::new())),
            progress_queue: Arc::new(Mutex::new(HashMap::new())),
            progress_subscribers: Arc::new(Mutex::new(HashSet::new())),
            last_watcher_error: None,
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
                let mut buffer = Vec::with_capacity(1024);
                for conn in listener.incoming().filter_map(|c| match c {
                    Ok(c) => Some(c),
                    Err(e) => {
                        error!("Incoming connection failed: {e}");
                        None
                    }
                }) {
                    if handle_client_connection(
                        conn,
                        &mut buffer,
                        &control_tx,
                        &statuses,
                        &progress,
                        &subscribers,
                    )? {
                        break;
                    }
                }

                WatchResult::Ok(())
            })?;

        Ok(())
    }

    /// Stop all non-root watchers in `self.watchers`, clearing them from the list
    fn clear_watchers(&mut self) {
        for WatchListItem {
            mut watcher,
            watch_path,
            ..
        } in self.watchers.drain(ROOT_WATCHER_COUNT..)
        {
            if let Err(e) = watcher.unwatch(&watch_path) {
                error!(
                    "Failed to stop watcher for path {} -- {e}",
                    watch_path.display()
                );
            }
        }
    }

    /// Places a watcher of type `mode` on `watch_path`. The watcher created is stored in
    /// `self.watchers` along with `rel_path`. Returns the watcher and its transmitter.
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
        trace!("Placed watch: {}", watch_path.as_ref().display());

        Ok((rx, watcher))
    }

    /// Places watchers on the root path independent of the given repository's submodules
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if any watchers cannot be created
    fn place_root_watches(&mut self) -> notify::Result<()> {
        let (rx, watcher) = Self::place_watch(
            self.root_gitmodules_path.as_path(),
            notify::RecursiveMode::NonRecursive, // ignored
        )?;
        self.watchers.push(WatchListItem::new(
            DOT_GITMODULES.to_owned(),
            self.root_gitmodules_path.clone(),
            None,
            rx,
            watcher,
        ));

        let (rx, watcher) = Self::place_watch(
            self.root_git_path.as_path(),
            notify::RecursiveMode::Recursive,
        )?;
        self.watchers.push(WatchListItem::new(
            DOT_GIT.to_owned(),
            self.root_git_path.clone(),
            None,
            rx,
            watcher,
        ));

        debug_assert_eq!(self.watchers.len(), ROOT_WATCHER_COUNT);
        Ok(())
    }

    /// Gathers the status for all submodules within the given repository, places watchers
    /// on their directories, and places those watchers in `self.watchers`.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if any watchers cannot be created, or `git2::Error` if any
    /// git operation fails.
    #[allow(clippy::too_many_lines)]
    fn populate_status_map(
        &mut self,
        repo: &Repository,
        display_progress: bool,
        mut status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        use std::sync::atomic::{AtomicU32, Ordering};

        use rayon::prelude::*;

        // A race condition can occur if certain git operations (i.e. rebase) are performed
        // while the server is (re)indexing. git2's `Repository::submodules` function contains
        // an assert for its inner call to `git_submodule_lookup`, which triggers for a non-zero
        // return code.
        let submodules = {
            let _lock = LockFileGuard::acquire(&self.root_lock_path, None)?;
            repo.submodules()?
        };

        self.root_rebasing = self.root_git_path.join("rebase-merge").exists();

        info!("Indexing project at {}", self.root_path.display());
        let submod_info: Vec<_> = submodules
            .iter()
            .map(|submod| {
                let rel_path = submod.path();
                let git_path_str = rel_path
                    .to_str()
                    .expect("Submodule path contains invalid UTF-8");

                #[cfg(target_os = "windows")]
                let relative_path = git_path_str.replace('/', "\\");
                #[cfg(not(target_os = "windows"))]
                let relative_path = git_path_str.to_owned();

                let full_path = self.root_path.join(rel_path);

                (relative_path, full_path)
            })
            .collect();

        let n_submodules = submod_info.len() as u32;
        let progress_bar = display_progress.then_some(create_progress_bar(
            u64::from(n_submodules),
            "Indexing submodules",
        ));

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

        let results: WatchResult<Vec<_>> = submod_info
            .into_par_iter()
            .map(|(relative_path, full_path)| {
                let sub_start = std::time::Instant::now();
                let repo = tl_repo.get_or_try(|| Repository::open(root_path))?;

                let lock_path = match self.get_index_lock_path(&relative_path) {
                    Ok(p) => p,
                    Err(e) => {
                        error!(
                            "Failed to get lock file path for submodule {relative_path} - {e}, skipping...",
                        );
                        Err(e)?
                    }
                };
                // This is definitely a race condition, and is not meant to catch "active" rebases
                // while the status map is being populated. Instead, the intention is for "stalled"
                // rebases (i.e. that has hit a conflict that must be manually resolved) so that we
                // can properly skip updateing this submodule until its rebase has been completed.
                let is_in_rebase = lock_path.parent().unwrap().join("rebase-merge").exists();

                #[cfg(target_os = "windows")]
                let relative_path = relative_path.replace('\\', "/");

                let status = if is_in_rebase {
                    StatusSummary::NEW_COMMITS
                } else {
                    get_submod_status(repo, &relative_path, &lock_path, None)?
                };

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
                    "Indexed {} ({:?}) in {}ms",
                    full_path.display(),
                    status,
                    sub_start.elapsed().as_millis(),
                );

                Ok((relative_path, full_path, lock_path, status, is_in_rebase))
            })
            .collect();
        let results = results?;

        status_guard.clear();
        for (relative_path, full_path, lock_path, status, is_in_rebase) in results {
            status_guard.insert(relative_path.clone(), status);
            let (rx, watcher) = Self::place_watch(&full_path, notify::RecursiveMode::Recursive)?;
            if is_in_rebase {
                self.skip_set.insert(relative_path.clone());
            }
            self.watchers.push(WatchListItem::new(
                relative_path,
                full_path,
                Some(lock_path),
                rx,
                watcher,
            ));
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

        let skip_set: Vec<String> = self.skip_set.iter().cloned().collect();

        let submodule_statuses: Vec<(String, StatusSummary)> = self
            .submod_statuses
            .lock()
            .expect("StatusMap mutex poisoned")
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        let in_flight_tasks: Vec<(String, String)> = in_flight
            .0
            .lock()
            .unwrap()
            .tasks
            .iter()
            .map(|(idx, state)| {
                let rel_path = self
                    .watchers
                    .get(*idx)
                    .map_or("(unknown)", |w| w.relative_path.as_str());
                let cancelled = state.cancellation_flag().load(Ordering::Relaxed);
                let state_str = match (state, cancelled) {
                    (TaskState::Active(_), false) => "active",
                    (TaskState::Active(_), true) => "active (cancelling)",
                    (TaskState::Dirty(_), false) => "dirty",
                    (TaskState::Dirty(_), true) => "dirty (cancelling)",
                };
                (rel_path.to_owned(), state_str.to_owned())
            })
            .collect();

        let progress_queues: Vec<(u32, Vec<(u32, u32)>)> = self
            .progress_queue
            .lock()
            .expect("ProgressQueue mutex poisoned")
            .iter()
            .map(|(pid, queue)| {
                let updates: Vec<(u32, u32)> = queue.iter().map(|p| (p.curr, p.total)).collect();
                (*pid, updates)
            })
            .collect();

        let progress_subscribers: Vec<u32> = self
            .progress_subscribers
            .lock()
            .expect("Subscribers mutex poisoned")
            .iter()
            .copied()
            .collect();

        DebugState {
            server_pid: std::process::id(),
            rayon_threads: rayon::current_num_threads() as u32,
            progress_subscribers,
            watcher_count: self.watchers.len() as u32,
            watched_paths,
            skip_set,
            root_rebasing: self.root_rebasing,
            root_path: self.root_path.display().to_string(),
            submodule_statuses,
            in_flight: in_flight_tasks,
            progress_queues,
            last_watcher_error: self.last_watcher_error.clone(),
        }
    }

    /// Sends a shutdown acknowledgment to the client over the IPC connection.
    fn signal_shutdown(shutdown_conn: Option<BufReader<Stream>>) {
        if let Some(mut conn) = shutdown_conn {
            let mut buf = [0; 1]; // unit variant: 1 byte for variant index
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
    }

    /// The main watch loop for the server. Will loop until a client shutdown request is received
    /// or an error is encountered.
    ///
    /// `status_guard` is a pre-acquired lock on the status map, ensuring clients
    /// block until initial indexing completes.
    #[expect(clippy::significant_drop_tightening)]
    fn watch(
        &mut self,
        status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        // Place watches on `.git/` and `.gitmodules`. These watches will live for the entirety of
        // the watch server's execution.
        self.place_root_watches()?;

        // Initial indexing with the pre-acquired guard
        let repo = Repository::open(&self.root_path)?;
        self.populate_status_map(&repo, true, status_guard)?;
        // If a shutdown was requested, holds the requesting client's IPC connection
        let mut shutdown_conn = self.handle_events()?;

        // Subsequent reindex iterations
        let status_lock = Arc::clone(&self.submod_statuses);
        loop {
            self.clear_watchers();
            if !self.do_watch {
                break;
            }

            let status_guard = status_lock.lock().expect("Mutex poisoned");
            let repo = Repository::open(&self.root_path)?;
            self.populate_status_map(&repo, false, status_guard)?;

            shutdown_conn = self.handle_events()?;
        }

        Self::signal_shutdown(shutdown_conn);

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
    // to changes to `.git/index`. However, when a new commit/branch is checked ou, the files
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
        !p.is_dir()
            && p.file_name()
                .is_some_and(|name| name.eq("index") || name.eq("HEAD"))
    }

    /// Converts a watcher's event and relative path to a relevant `EventType`, if possible
    fn get_event_type(&self, event: &Event, rel_path: &str) -> Option<EventType> {
        if !event_is_relevant(event) {
            // File renames within submodule source trees are legitimate changes, but we
            // can't allow Modify(Name) events through globally because git's
            // `index.lock` -> `index` rename would trigger spurious reindexes.
            let is_root_watcher = rel_path.eq(DOT_GIT) || rel_path.eq(DOT_GITMODULES);
            if is_root_watcher || !matches!(event.kind, EventKind::Modify(ModifyKind::Name(_))) {
                return None;
            }
        }

        if rel_path.eq(DOT_GIT) {
            if event
                .paths
                .iter()
                .any(|p| p.starts_with(&self.root_modules_path))
            {
                if event.paths.iter().any(|p| Self::is_index_or_head_path(p)) {
                    if matches!(event.kind, EventKind::Remove(_)) {
                        None
                    } else {
                        Some(EventType::SubmoduleGitOperation)
                    }
                } else if self.is_submod_rebase_start_event(event) {
                    Some(EventType::SubmoduleRebaseStart)
                } else if self.is_submod_rebase_end_event(event) {
                    Some(EventType::SubmoduleRebaseEnd)
                } else {
                    None
                }
            } else if event.paths.iter().any(|p| p.eq(&self.root_index_path)) {
                // HACK: When `git rebase ...` is issued, git will begin by acquiring `index.lock`,
                // gathering some information about the current index (looking at all of the repo's
                // submodules, why isn't the index considered up to date at this point?), writing
                // the new `index` contents to `index.lock`, _deleting_ `index`, and renaming
                // `index.lock` to `index`. Immediately after, the `.git/rebase-merge` directory is
                // created, signaling the start of a rebase. Because these `index` operations happen
                // before we can detect the rebase, they trigger a root reindex and cause the rebase
                // to fail because git fails to acquire the `index.lock` file (why release it in the
                // first place?). As a workaround, we simply ignore these events and trigger a root
                // reindex after the rebase is completed. If git applies this pattern for other
                // operations that I haven't tested, we may be in trouble. So far though, this
                // approach seems to be ok.
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
        } else if rel_path.eq(DOT_GITMODULES) {
            Some(EventType::RootGitOperation)
        } else {
            Some(EventType::SubmoduleChange)
        }
    }

    /// Returns the path to the `index.lock` file for a submodule
    fn get_index_lock_path(&self, submod_rel_path: &str) -> WatchResult<PathBuf> {
        // NOTE: There is a hypothetical bug here where if two submodules were renamed
        // to eachother's names _and_ their `.git/modules` entries weren't updates (i.e.,
        // only the relative path in each submodule's `.git` file), the two lock paths
        // will be swapped. This is highly unlikely to cuase a bug in real use, and until
        // its proven to I would prefer to not pessimize the common case with a full read
        // and parse of the `.git` file.
        let alleged_submod_path = self.root_modules_path.join(submod_rel_path);
        if alleged_submod_path.exists() {
            return Ok(alleged_submod_path.join("index.lock"));
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
        let full_submod_path =
            dunce::canonicalize(self.root_path.join(submod_rel_path).join(actual_rel_path))?;
        Ok(full_submod_path.join("index.lock"))
    }

    /// Attempts to spawn a rayon task to update the status of the submodule at watcher `index`.
    ///
    /// If the submodule is already being processed, marks it as dirty so the in-flight task
    /// will re-check after completing. Otherwise, inserts into the processing set and spawns
    /// a rayon task that loops until no more dirty events are pending.
    fn try_spawn_submod_update(
        &self,
        index: usize,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
        tl_repo: &Arc<thread_local::ThreadLocal<Repository>>,
    ) {
        let cancel = Arc::new(AtomicBool::new(false));
        {
            let mut tracker = in_flight.0.lock().expect("InFlightTracker mutex poisoned");
            if let Some(task) = tracker.tasks.get_mut(&index) {
                // Already in-flight, mark dirty so the task re-checks when done.
                let existing_cancel = task.cancellation_flag().clone();
                *task = TaskState::Dirty(existing_cancel);
                return;
            }
            tracker
                .tasks
                .insert(index, TaskState::Active(Arc::clone(&cancel)));
        }

        let watcher = &self.watchers[index];
        let relative_path = watcher.relative_path.clone();
        let lock_file_path = watcher.lock_file_path.as_ref().unwrap_or_else(|| {
            panic!(
                "Submodule event for watcher with no cached lock file path\n -- watcher path: {}",
                watcher.watch_path.display()
            );
        }).clone();

        let in_flight = Arc::clone(in_flight);
        let statuses = Arc::clone(&self.submod_statuses);
        let tl_repo = Arc::clone(tl_repo);
        let root_path = self.root_path.clone();

        rayon::spawn(move || {
            let repo = match tl_repo.get_or_try(|| Repository::open(&root_path)) {
                Ok(r) => r,
                Err(e) => {
                    error!("Failed to open repository for submodule update: {e}");
                    let (mutex, condvar) = &*in_flight;
                    mutex
                        .lock()
                        .expect("InFlightTracker mutex poisoned")
                        .tasks
                        .remove(&index);
                    condvar.notify_one();
                    return;
                }
            };

            loop {
                if cancel.load(Ordering::Relaxed) {
                    break;
                }

                match get_submod_status(repo, &relative_path, &lock_file_path, Some(&cancel)) {
                    Ok(submod_status) => {
                        if !cancel.load(Ordering::Relaxed) {
                            let mut guard = statuses.lock().expect("StatusMap mutex poisoned");
                            if let Some(st) = guard.get_mut(relative_path.as_str()) {
                                *st = submod_status;
                            } else {
                                guard.insert(relative_path.clone(), submod_status);
                            }
                        }
                    }
                    Err(e) => {
                        if !cancel.load(Ordering::Relaxed) {
                            error!(
                                "Failed to get submodule status for path: {relative_path} -- {e}",
                            );
                        }
                    }
                }

                let (mutex, condvar) = &*in_flight;
                let mut tracker = mutex.lock().expect("InFlightTracker mutex poisoned");
                if let Some(task) = tracker.tasks.get_mut(&index)
                    && matches!(task, TaskState::Dirty(_))
                {
                    // Another event arrived while we were processing, demote back
                    // to Active and re-check.
                    let cancel = task.cancellation_flag().clone();
                    *task = TaskState::Active(cancel);
                    continue;
                }
                tracker.tasks.remove(&index);
                drop(tracker);
                condvar.notify_one();
                break;
            }
        });
    }

    /// The "meat" of the logic for the watch server. Handles incoming watcher events and updates
    /// server state accordingly. This function will only exit if a reindex is required or
    /// requested, a shutdown is received via the control channel, or if an error occurs.
    ///
    /// Returns `Some(conn)` if a shutdown was requested, where `conn` is the client's IPC
    /// connection to send the acknowledgment through.
    #[allow(clippy::too_many_lines)]
    fn handle_events(&mut self) -> WatchResult<Option<BufReader<Stream>>> {
        let mut sel = crossbeam_channel::Select::new();
        // filesystem watchers
        for WatchListItem { receiver, .. } in &self.watchers {
            sel.recv(receiver);
        }
        // handles client requests from the listener thread
        let control_idx = sel.recv(&self.control_rx);

        // Shared state for parallel submodule status updates
        let in_flight: Arc<(Mutex<InFlightTracker>, Condvar)> =
            Arc::new((Mutex::new(InFlightTracker::new()), Condvar::new()));
        let tl_repo: Arc<thread_local::ThreadLocal<Repository>> =
            Arc::new(thread_local::ThreadLocal::new());

        loop {
            let oper = sel.select();
            let index = oper.index();

            if index == control_idx {
                match oper.recv(&self.control_rx)? {
                    ControlMessage::Reindex => {
                        wait_for_in_flight(&in_flight);
                        return Ok(None);
                    }
                    ControlMessage::Shutdown { conn } => {
                        self.do_watch = false;
                        wait_for_in_flight(&in_flight);
                        return Ok(Some(conn));
                    }
                    ControlMessage::Debug { mut conn } => {
                        let state = self.gather_debug_state(&in_flight);
                        let msg = ServerMessage::DebugInfo(state);
                        match bincode::encode_to_vec(msg, BINCODE_CFG) {
                            Ok(serialized) => {
                                if let Err(e) = write_full_message(&mut conn, &serialized) {
                                    error!("Failed to send debug state -- {e}");
                                }
                            }
                            Err(e) => {
                                error!("Failed to encode debug state -- {e}");
                            }
                        }
                        continue;
                    }
                }
            }
            match oper.recv(&self.watchers[index].receiver)? {
                Ok(event) => {
                    let rel_path = self.watchers[index].relative_path.as_str();
                    match self.get_event_type(&event, rel_path) {
                        Some(EventType::RootGitOperation) => {
                            if !self.root_rebasing {
                                wait_for_in_flight(&in_flight);
                                break;
                            }
                        }
                        Some(EventType::RootRebaseStart) => {
                            self.root_rebasing = true;
                        }
                        Some(EventType::RootRebaseEnd) => {
                            wait_for_in_flight(&in_flight);
                            self.root_rebasing = false;
                            break;
                        }
                        Some(EventType::SubmoduleChange) => {
                            if !self.skip_set.contains(rel_path) {
                                self.try_spawn_submod_update(index, &in_flight, &tl_repo);
                            }
                        }
                        Some(EventType::SubmoduleGitOperation) => {
                            for (i, watcher) in self.watchers.iter().enumerate() {
                                let Some(submod_modules_path) =
                                    watcher.lock_file_path.as_ref().and_then(|p| p.parent())
                                else {
                                    continue;
                                };
                                if event
                                    .paths
                                    .iter()
                                    .any(|p| p.starts_with(submod_modules_path))
                                {
                                    if !self.skip_set.contains(&watcher.relative_path) {
                                        self.try_spawn_submod_update(i, &in_flight, &tl_repo);
                                    }
                                    break;
                                }
                            }
                        }
                        // Rebases generate an incredible volume of events, and during such an
                        // operation git continually acquires and releases `index.lock`. This,
                        // paired with the changes to the submodule's source files leads to too much
                        // contention for `index.lock`, which leads to the rebase failing partway
                        // through when git fails to acquire `index.lock`. Instead, we pause
                        // updating the relevant submodule until the rebase is completed.
                        Some(EventType::SubmoduleRebaseStart) => {
                            for (i, watcher) in self.watchers.iter().enumerate() {
                                let Some(submod_modules_path) =
                                    watcher.lock_file_path.as_ref().and_then(|p| p.parent())
                                else {
                                    continue;
                                };
                                if event
                                    .paths
                                    .iter()
                                    .any(|p| p.starts_with(submod_modules_path))
                                {
                                    cancel_submod_update(i, &in_flight);
                                    self.skip_set.insert(watcher.relative_path.clone());
                                    self.submod_statuses.lock().expect("Mutex poisoned").insert(
                                        watcher.relative_path.clone(),
                                        StatusSummary::NEW_COMMITS,
                                    );
                                    break;
                                }
                            }
                        }
                        Some(EventType::SubmoduleRebaseEnd) => {
                            for (i, watcher) in self.watchers.iter().enumerate() {
                                let Some(submod_modules_path) =
                                    watcher.lock_file_path.as_ref().and_then(|p| p.parent())
                                else {
                                    continue;
                                };
                                if event
                                    .paths
                                    .iter()
                                    .any(|p| p.starts_with(submod_modules_path))
                                {
                                    self.skip_set.remove(&watcher.relative_path);
                                    self.try_spawn_submod_update(i, &in_flight, &tl_repo);
                                    break;
                                }
                            }
                        }
                        None => {}
                    }
                }
                Err(e) => {
                    let msg = format!(
                        "Watcher error for {}: {e}",
                        self.watchers[index].relative_path
                    );
                    error!("{msg}\nReindexing to reset watchers...");
                    self.last_watcher_error = Some(msg);
                    wait_for_in_flight(&in_flight);
                    break;
                }
            }
        }

        Ok(None)
    }
}

#[derive(Debug, Clone, Copy, Encode, BorrowDecode)]
pub struct ProgressUpdate {
    pub curr: u32,
    pub total: u32,
}

impl ProgressUpdate {
    #[must_use]
    pub const fn new(curr: u32, total: u32) -> Self {
        Self { curr, total }
    }
}

/// Attempts to acquire `mutex`.
///
/// # Panics
///
/// Panics if `mutex` has been poisoned
fn try_acquire<T>(mutex: &Mutex<T>) -> Option<MutexGuard<'_, T>> {
    match mutex.try_lock() {
        Ok(g) => Some(g),
        Err(TryLockError::WouldBlock) => None,
        Err(TryLockError::Poisoned(_)) => panic!("Mutex poisoned"),
    }
}

/// Pushes `progress_val` to the progress queue for every registered subscriber.
///
/// # Panics
///
/// Panics if either mutex has been poisoned
#[expect(clippy::significant_drop_tightening)]
fn broadcast_progress(
    subscribers: &ProgressSubscribers,
    progress: &ProgressMap,
    progress_val: ProgressUpdate,
) {
    let subs = subscribers.lock().expect("Subscribers mutex poisoned");
    // Avoid locking the progress queue for the common case of no active subscribers
    if subs.is_empty() {
        return;
    }
    let mut progress_guard = progress.lock().expect("Progress mutex poisoned");
    for &pid in subs.iter() {
        let queue = progress_guard.entry(pid).or_insert_with(|| {
            let ProgressUpdate { total: cap, .. } = progress_val;
            VecDeque::with_capacity(cap as usize + 1)
        });
        queue.push_back(progress_val);
    }
}

/// Handles incoming client connections. Returns whether the listener received a shutdown command
///
/// # Errors
///
/// Returns `Err` if the client message couldn't be read, decoded, or handled.
fn handle_client_connection(
    conn: Stream,
    buffer: &mut Vec<u8>,
    control_tx: &crossbeam_channel::Sender<ControlMessage>,
    statuses: &StatusMap,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<bool> {
    let mut conn = BufReader::new(conn);

    read_full_message(&mut conn, buffer)?;
    let (msg, _): (ClientMessage, usize) = bincode::borrow_decode_from_slice(buffer, BINCODE_CFG)?;
    info!("Received client message: {msg:?}");

    match msg {
        ClientMessage::Reindex(client_pid) => {
            subscribers
                .lock()
                .expect("Subscribers mutex poisoned")
                .insert(client_pid);
            control_tx
                .send(ControlMessage::Reindex)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
            handle_reindex_request(conn, client_pid, progress, subscribers)?;
        }
        ClientMessage::Status(client_pid) => {
            handle_status_request(conn, client_pid, statuses, progress, subscribers)?;
        }
        ClientMessage::Shutdown => {
            control_tx
                .send(ControlMessage::Shutdown { conn })
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
            return Ok(true);
        }
        ClientMessage::Debug => {
            control_tx
                .send(ControlMessage::Debug { conn })
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::BrokenPipe, e.to_string()))?;
        }
    }

    Ok(false)
}

/// Handles a client's request for submodule statuses.
fn handle_status_request(
    mut conn: BufReader<Stream>,
    client_pid: u32,
    statuses: &StatusMap,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<()> {
    subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .insert(client_pid);
    let guard = get_status_guard_with_progress(&mut conn, client_pid, statuses, progress)?;
    _ = subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .remove(&client_pid);
    _ = progress.lock().expect("Mutex poisoned").remove(&client_pid);

    let mut status_out = Vec::with_capacity(guard.len());
    for (submod_path, status) in guard.iter().filter(|(_, st)| **st != StatusSummary::CLEAN) {
        status_out.push((submod_path.clone(), *status));
    }
    drop(guard);

    let msg = ServerMessage::Status(status_out);
    let serialized = bincode::encode_to_vec(msg, BINCODE_CFG)?;
    write_full_message(&mut conn, &serialized)?;

    Ok(())
}

/// Handles a client's request to reindex the watch server. The reindex signal has already
/// been sent to the main event loop via the control channel; this function handles sending
/// progress updates back to the client over the IPC connection.
fn handle_reindex_request(
    mut conn: BufReader<Stream>,
    client_pid: u32,
    progress: &ProgressMap,
    subscribers: &ProgressSubscribers,
) -> WatchResult<()> {
    loop {
        if try_send_progress_update(&mut conn, client_pid, progress)? {
            break;
        }
        std::thread::yield_now();
    }

    _ = subscribers
        .lock()
        .expect("Subscribers mutex poisoned")
        .remove(&client_pid);
    _ = progress.lock().expect("Mutex poisoned").remove(&client_pid);

    Ok(())
}

/// Attempts to send an index progress message to `conn` for `client_pid`.
/// Return indicates whether indexing is determined to be complete (a message
/// is received where `current_idx == length`)
///
/// # Errors
///
/// Returns `Err` if `bincode` encoding or writing to `conn` fails
fn try_send_progress_update(
    conn: &mut BufReader<Stream>,
    client_pid: u32,
    progress: &ProgressMap,
) -> WatchResult<bool> {
    let Some(mut progress_queue) = try_acquire(progress) else {
        return Ok(false);
    };
    let Some(queue) = progress_queue.get_mut(&client_pid) else {
        return Ok(false);
    };
    let Some(ProgressUpdate { curr, total }) = queue.pop_front() else {
        return Ok(false);
    };
    drop(progress_queue);

    let progress = ServerMessage::Indexing { curr, total };
    let mut progress_msg = [0; 10]; // statically determined an upper bound of 10 bytes
    let progress_msg_len = bincode::encode_into_slice(progress, &mut progress_msg, BINCODE_CFG)?;
    write_full_message(conn, &progress_msg[..progress_msg_len])?;

    Ok(curr == total)
}

/// Acquires the `statuses` guard. Every time the lock cannot be acquired
/// (because it is currently locked by an indexing operation in the main loop), an attempt
/// is made to send a progress update to the client.
fn get_status_guard_with_progress<'a>(
    conn: &mut BufReader<Stream>,
    client_pid: u32,
    statuses: &'a StatusMap,
    progress: &ProgressMap,
) -> WatchResult<MutexGuard<'a, BTreeMap<String, StatusSummary>>> {
    loop {
        if let Some(g) = try_acquire(statuses) {
            return Ok(g);
        }
        if !try_send_progress_update(conn, client_pid, progress)? {
            std::thread::yield_now();
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
pub fn watch(root_dir: &Path) -> WatchResult<()> {
    let (control_tx, control_rx) = crossbeam_channel::unbounded();
    let mut server = WatchServer::new(root_dir, control_rx);

    // Lock status map before accepting connections so clients block (with
    // progress updates) until initial indexing completes instead of reading
    // an empty map.
    let status_lock = Arc::clone(&server.submod_statuses);
    let status_guard = status_lock.lock().expect("Mutex poisoned");

    server.spawn_listener(control_tx)?;
    server.watch(status_guard)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn server_msg_unit_variants_fit_in_single_byte() {
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
                1,
                "Expected {name} to encode to 1 byte, got {} bytes",
                encoded.len(),
            );
        }
    }
}
