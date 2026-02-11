use std::{
    collections::{BTreeMap, HashMap, VecDeque},
    fs::{self, File},
    io::BufReader,
    path::{Path, PathBuf},
    sync::{LazyLock, Mutex, MutexGuard, TryLockError},
    time::{Duration, Instant},
};

use bincode::{BorrowDecode, Encode};
use git2::Repository;
use interprocess::local_socket::{Stream, traits::ListenerExt as _};
use log::{error, info, trace};
use notify::{
    Event, EventKind, Watcher,
    event::{AccessKind, AccessMode, CreateKind},
};

use crate::{
    DOT_GIT, DOT_GITMODULES, StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ServerMessage, create_listener, read_full_message,
        write_full_message,
    },
    create_progress_bar,
    watch::{LockFileError, WatchError, WatchResult},
};

const MAX_LOCKFILE_BACKOFF: Duration = Duration::from_millis(100);
const LOCKFILE_TIMEOUT: Duration = Duration::from_secs(30);

/// The main map of the server, associating submodule relative paths (from the repository's
/// `.gitmodules` file) to the given submodule's summarized status.
static SUBMOD_STATUSES: LazyLock<Mutex<BTreeMap<String, StatusSummary>>> =
    LazyLock::new(|| Mutex::new(BTreeMap::new()));

/// Associates a given client pid with a queue of indexing progress updates.
static PROGRESS_QUEUE: LazyLock<Mutex<HashMap<u32, VecDeque<ProgressUpdate>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Message receiver type for a debounced watcher
type WatchReceiver = crossbeam_channel::Receiver<Result<notify::Event, notify::Error>>;

/// Watcher type alias
type ServerWatcher = notify::RecommendedWatcher;

/// Item watched by the server
#[derive(Debug)]
struct WatchListItem {
    // need to hang onto the watched path to `unwatch` later
    pub watch_path: PathBuf,
    pub relative_path: String,
    pub receiver: WatchReceiver,
    pub watcher: ServerWatcher,
}

impl WatchListItem {
    #[expect(clippy::needless_pass_by_value)]
    fn new(
        rel_path: impl ToString,
        watch_path: PathBuf,
        receiver: WatchReceiver,
        watcher: ServerWatcher,
    ) -> Self {
        Self {
            relative_path: rel_path.to_string(),
            watch_path,
            receiver,
            watcher,
        }
    }
}

type WatchList = Vec<WatchListItem>;

/// The primary state necessary to maintain a status watch over the repository at `root_path`
struct WatchServer {
    /// Whether the server should continue to watch the repository at `root_path`
    pub do_watch: bool,
    /// The pid of the client who issued the latest reindex/shutdown request.
    pub client_pid: Option<u32>,
    /// Debounced watchers
    pub watchers: WatchList,
    /// Root path to the repository being watched
    pub root_path: PathBuf,
    /// `root_path`/.gitmodules
    pub gitmodules_path: PathBuf,
    /// `root_path`/.git
    pub dot_git_path: PathBuf,
    /// Receiver for control messages from the listener thread
    control_rx: crossbeam_channel::Receiver<ControlMessage>,
}

/// Summarizes an event received from a watcher. Create with `get_event_type`
#[derive(Debug, Copy, Clone)]
enum EventType {
    /// Something changed in `.git/` or `.gitmodules`, reindex needed
    GitOperation,
    /// A change occurred in one of the watched submodules
    SubmoduleChange,
}

/// Control messages sent from the listener thread to the main event loop
enum ControlMessage {
    Reindex { pid: u32 },
    Shutdown { pid: u32, conn: BufReader<Stream> },
}

fn acquire_lock_file(path: &Path) -> WatchResult<File> {
    trace!("Acquiring lock file at path: {}", path.display());
    let start = Instant::now();
    let mut backoff = Duration::from_millis(1);

    let lock_file = loop {
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
        {
            Ok(f) => break f,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                if start.elapsed() >= LOCKFILE_TIMEOUT {
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
    };

    trace!("Acquired lock file at path: {}", path.display());
    Ok(lock_file)
}

fn release_lock_file(path: &Path) -> WatchResult<()> {
    trace!("Releasing lock file at path: {}", path.display());
    fs::remove_file(path)?;
    trace!("Released lock file at path: {}", path.display());
    Ok(())
}

macro_rules! with_lock_file {
    ($lock_path:expr, $body:block) => {{
        let _lock_file = acquire_lock_file($lock_path)?;
        let result = $body;
        release_lock_file($lock_path)?;
        result
    }};
}

impl WatchServer {
    pub fn new(root_path: &Path, control_rx: crossbeam_channel::Receiver<ControlMessage>) -> Self {
        let gitmodules_path = root_path.to_path_buf().join(DOT_GITMODULES);
        let dot_git_path = root_path.to_path_buf().join(DOT_GIT);

        Self {
            do_watch: true,
            client_pid: None,
            watchers: Vec::new(),
            root_path: root_path.to_path_buf(),
            gitmodules_path,
            dot_git_path,
            control_rx,
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
                    if handle_client_connection(conn, &mut buffer, &control_tx)? {
                        break;
                    }
                }

                WatchResult::Ok(())
            })?;

        Ok(())
    }

    /// Stop all the watchers in `self.watchers`, clearing the list
    fn clear_watchers(&mut self) {
        for WatchListItem {
            mut watcher,
            watch_path,
            ..
        } in self.watchers.drain(..)
        {
            if let Err(e) = watcher.unwatch(&watch_path) {
                error!(
                    "Failed to stop watcher for path {} -- {e}",
                    watch_path.display()
                );
            }
        }
    }

    /// Places a debounced watch of type `mode` on `watch_path`. The watcher created is stored in
    /// `self.watchers` along with `rel_path`. Returns the watcher and its transmitter.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if the debouncer or watch cannot be created
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

    /// Places debounced watchers on the root path independent of the given repository's submodules
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if any debouncers or watchers cannot be created
    fn place_root_watches(&mut self) -> notify::Result<()> {
        let (rx, debouncer) = Self::place_watch(
            self.root_path.as_path(),
            notify::RecursiveMode::NonRecursive,
        )?;
        self.watchers.push(WatchListItem::new(
            DOT_GITMODULES,
            self.root_path.clone(),
            rx,
            debouncer,
        ));

        let (rx, debouncer) = Self::place_watch(
            self.dot_git_path.as_path(),
            notify::RecursiveMode::Recursive,
        )?;
        self.watchers.push(WatchListItem::new(
            DOT_GIT,
            self.dot_git_path.clone(),
            rx,
            debouncer,
        ));

        Ok(())
    }

    /// Gathers the status for all submodules within the given repository, places debounced watches on their
    /// directories, and places those watchers in `self.watchers`.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if any debouncers or watchers cannot be created, or `git2::Error`
    /// if any git operation fails.
    fn populate_status_map(
        &mut self,
        repo: &Repository,
        display_progress: bool,
    ) -> WatchResult<()> {
        use std::sync::atomic::{AtomicU32, Ordering};

        use rayon::prelude::*;

        // A race condition can occur if certain git operations (i.e. rebase) are performed
        // while the server is (re)indexing. git2's `Repository::submodules` function contains
        // an assert for its inner call to `git_submodule_lookup`, which triggers for a non-zero
        // return code.
        let lock_file_path = self.root_path.join(".git").join("index.lock");
        let submodules = with_lock_file!(&lock_file_path, { repo.submodules()? });

        info!("Indexing project at {}", self.root_path.display());
        let submod_info: Vec<_> = submodules
            .iter()
            .filter_map(|submod| {
                let rel_path = submod.path();
                let git_path = rel_path.to_str().unwrap().to_string();

                #[cfg(target_os = "windows")]
                let relative_path = rel_path.to_string_lossy().replace('/', "\\");
                #[cfg(not(target_os = "windows"))]
                let relative_path = git_path.clone();

                let full_path = self.root_path.join(rel_path);
                let lock_path = match self.get_index_lock_path(&git_path) {
                    Ok(p) => p,
                    Err(e) => {
                        error!(
                            "Failed to get lock file path for submodule {} - {e}, skipping...",
                            rel_path.display()
                        );
                        return None;
                    }
                };

                Some((git_path, relative_path, full_path, lock_path))
            })
            .collect();

        let n_submodules = submod_info.len() as u32;
        let progress_bar = display_progress.then_some(create_progress_bar(
            u64::from(n_submodules),
            "Indexing submodules",
        ));

        if let Some(id) = self.client_pid {
            update_progress(id, ProgressUpdate::new(0, n_submodules));
        }

        let completed = AtomicU32::new(0);
        let root_path = &self.root_path;
        let client_pid = self.client_pid;
        let tl_repo = thread_local::ThreadLocal::new();

        let results: WatchResult<Vec<_>> = submod_info
            .par_iter()
            .map(|(git_path, relative_path, full_path, lock_path)| {
                let sub_start = std::time::Instant::now();
                let repo = tl_repo.get_or_try(|| Repository::open(root_path))?;
                let status = with_lock_file!(lock_path, {
                    repo.submodule_status(git_path, git2::SubmoduleIgnore::None)?
                });
                let converted_status: StatusSummary = status.into();

                let count = completed.fetch_add(1, Ordering::Relaxed) + 1;
                if let Some(id) = client_pid {
                    update_progress(id, ProgressUpdate::new(count, n_submodules));
                }
                if let Some(pb) = &progress_bar {
                    pb.inc(1);
                }
                trace!(
                    "Indexed {} ({:?} -> {:?}) in {}ms",
                    full_path.display(),
                    status,
                    converted_status,
                    sub_start.elapsed().as_millis(),
                );

                Ok((relative_path.clone(), full_path.clone(), converted_status))
            })
            .collect();
        let results = results?;

        let mut new_statuses = BTreeMap::new();
        for (relative_path, _, status) in &results {
            new_statuses.insert(relative_path.clone(), *status);
        }

        let mut status_guard = SUBMOD_STATUSES.lock().expect("Mutex poisoned");
        *status_guard = new_statuses;
        drop(status_guard);

        for (map_key, full_path, _) in results {
            let (rx, debouncer) = Self::place_watch(&full_path, notify::RecursiveMode::Recursive)?;
            self.watchers
                .push(WatchListItem::new(map_key, full_path, rx, debouncer));
        }

        self.client_pid = None;
        if let Some(pb) = &progress_bar {
            pb.finish();
        }

        Ok(())
    }

    /// Sets up watchers and populates the status map
    fn setup(&mut self, repo: &Repository, display_progress: bool) -> WatchResult<()> {
        self.place_root_watches()?;
        self.populate_status_map(repo, display_progress)?;

        Ok(())
    }

    /// Sends a shutdown acknowledgment to the client over the IPC connection.
    fn signal_shutdown(shutdown_conn: Option<BufReader<Stream>>) {
        if let Some(mut conn) = shutdown_conn {
            let msg = ServerMessage::ShutdownAck;
            match bincode::encode_to_vec(msg, BINCODE_CFG) {
                Ok(serialized) => {
                    if let Err(e) = write_full_message(&mut conn, &serialized) {
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
    fn watch(&mut self) -> WatchResult<()> {
        // only display the progress bar on the first indexing
        let mut display_progress = true;
        // If a shutdown was requested, holds the requesting client's IPC connection
        let mut shutdown_conn = None;
        loop {
            self.clear_watchers();
            if !self.do_watch {
                break;
            }

            let repo = Repository::open(&self.root_path)?;
            self.setup(&repo, display_progress)?;
            display_progress = false;

            shutdown_conn = self.handle_events(&repo)?;
        }

        Self::signal_shutdown(shutdown_conn);

        Ok(())
    }

    /// Converts a debounced watcher's event and relative path to a relevant `EventType`,
    /// if possible
    fn get_event_type(&self, event: &Event, rel_path: &str) -> Option<EventType> {
        if !event_is_relevant(event) {
            return None;
        }

        if rel_path.eq(DOT_GITMODULES) || rel_path.eq(DOT_GIT) {
            if event.paths.iter().any(|p| {
                (p.starts_with(&self.dot_git_path) || p.eq(&self.gitmodules_path))
                    // Both git itself and subspy acquire various `index.lock` files to protect
                    // various operations. Acquiring such a lock does _not_ mean a reindex is
                    // necessary, it's just telling other git things "hey don't touch this right now".
                    // If something _does_ change that requires a reindex, another file will be
                    // modified which we will pick up on.
                    && p.file_name().is_none_or(|name| !name.eq("index.lock"))
            }) {
                Some(EventType::GitOperation)
            } else {
                None
            }
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
        let modules_path = self.root_path.join(".git").join("modules");
        let alleged_submod_path = modules_path.join(submod_rel_path);
        if alleged_submod_path.exists() {
            return Ok(alleged_submod_path.join("index.lock"));
        }

        // The submodule was renamed at some point but its `.git` directory inside
        // `.git/modules` wasn't updated, so we have to read the submodule's `.git`
        // file to get the _actual_ relative path
        let dot_git_path = self.root_path.join(submod_rel_path).join(".git");
        let dot_git_contents = std::fs::read_to_string(dot_git_path)?;
        assert!(dot_git_contents.starts_with("gitdir: "));
        let actual_rel_path = dot_git_contents["gitdir: ".len()..].trim();
        let full_submod_path =
            dunce::canonicalize(self.root_path.join(submod_rel_path).join(actual_rel_path))?;
        Ok(full_submod_path.join("index.lock"))
    }

    /// The "meat" of the logic for the watch server. Handles incoming watcher events and updates
    /// server state accordingly. This function will only exit if a reindex is required or
    /// requested, a shutdown is received via the control channel, or if an error occurs.
    ///
    /// Returns `Some(conn)` if a shutdown was requested, where `conn` is the client's IPC
    /// connection to send the acknowledgment through.
    fn handle_events(&mut self, repo: &Repository) -> WatchResult<Option<BufReader<Stream>>> {
        let mut sel = crossbeam_channel::Select::new();
        // filesystem watchers
        for WatchListItem { receiver, .. } in &self.watchers {
            sel.recv(receiver);
        }
        // handles client requests from the listener thread
        let control_idx = sel.recv(&self.control_rx);

        loop {
            let oper = sel.select(); // Blocks until any ready
            let index = oper.index(); // Which rx fired

            if index == control_idx {
                match oper.recv(&self.control_rx)? {
                    ControlMessage::Reindex { pid } => {
                        self.client_pid = Some(pid);
                        return Ok(None);
                    }
                    ControlMessage::Shutdown { pid, conn } => {
                        self.client_pid = Some(pid);
                        self.do_watch = false;
                        return Ok(Some(conn));
                    }
                }
            }
            match oper.recv(&self.watchers[index].receiver)? {
                Ok(event) => {
                    let rel_path = self.watchers[index].relative_path.as_str();
                    match self.get_event_type(&event, rel_path) {
                        Some(EventType::GitOperation) => break,
                        Some(EventType::SubmoduleChange) => {
                            let Ok(lock_file_path) = self.get_index_lock_path(rel_path) else {
                                error!(
                                    "Failed to get lock file path for submodule {rel_path}, skipping status update"
                                );
                                continue;
                            };
                            let status = with_lock_file!(&lock_file_path, {
                                repo.submodule_status(rel_path, git2::SubmoduleIgnore::None)
                            });
                            match status {
                                Ok(submod_status) => {
                                    SUBMOD_STATUSES
                                        .lock()
                                        .expect("Mutex poisoned")
                                        .entry(rel_path.to_string())
                                        .and_modify(|st| *st = submod_status.into())
                                        .or_insert_with(|| submod_status.into());
                                }
                                Err(e) => {
                                    error!(
                                        "Failed to get submodule status for path: {rel_path} -- {e}"
                                    );
                                }
                            }
                        }
                        None => {}
                    }
                }
                Err(e) => {
                    error!(
                        "Watcher error for submodule {}: {e}",
                        self.watchers[index].relative_path
                    );
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

/// Attempts to acquire `guard`.
///
/// # Panics
///
/// Panics if `guard`'s mutex has been poisoned
fn try_acquire<T>(guard: &'static LazyLock<Mutex<T>>) -> Option<std::sync::MutexGuard<'static, T>> {
    match guard.try_lock() {
        Ok(g) => Some(g),
        Err(TryLockError::WouldBlock) => None,
        Err(TryLockError::Poisoned(_)) => panic!("Mutex poisoned"),
    }
}

/// Adds `progress_val` to the queue in `PROGRESS_QUEUE` for `client_pid`
///
/// # Panics
///
/// Panics if the `PROGRESS_QUEUE` mutex has been poisoned
#[expect(clippy::significant_drop_tightening)] // false positive???
fn update_progress(client_pid: u32, progress_val: ProgressUpdate) {
    let mut progress_guard = PROGRESS_QUEUE.lock().expect("Progress mutex poisoned");
    let queue = progress_guard.entry(client_pid).or_default();
    queue.push_back(progress_val);
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
) -> WatchResult<bool> {
    let mut conn = BufReader::new(conn);

    read_full_message(&mut conn, buffer)?;
    let (msg, _): (ClientMessage, usize) = bincode::borrow_decode_from_slice(buffer, BINCODE_CFG)?;
    info!("Received client message: {msg:?}");

    match msg {
        ClientMessage::Reindex(client_pid) => {
            // Trigger the main loop to reindex
            if let Err(e) = control_tx.send(ControlMessage::Reindex { pid: client_pid }) {
                error!("Failed to send reindex control message -- {e}");
            }
            // Send progress updates to the client
            handle_reindex_request(conn, client_pid)?;
        }
        ClientMessage::Status(client_pid) => handle_status_request(conn, client_pid)?,
        ClientMessage::Shutdown(client_pid) => {
            if let Err(e) = control_tx.send(ControlMessage::Shutdown {
                pid: client_pid,
                conn,
            }) {
                error!("Failed to send shutdown control message -- {e}");
            }
            return Ok(true);
        }
    }

    Ok(false)
}

/// Handles a client's request for submodule statuses.
fn handle_status_request(mut conn: BufReader<Stream>, client_pid: u32) -> WatchResult<()> {
    let guard = get_status_guard_with_progress(&mut conn, client_pid)?;

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
fn handle_reindex_request(mut conn: BufReader<Stream>, client_pid: u32) -> WatchResult<()> {
    while !try_send_progress_update(&mut conn, client_pid)? {}

    _ = PROGRESS_QUEUE
        .lock()
        .expect("Mutex poisoned")
        .remove(&client_pid);

    Ok(())
}

/// Attempts to send an index progress message to `conn` for `client_pid`.
/// Return indicates whether indexing is determined to be complete (a message
/// is received where `current_idx == length`)
///
/// # Errors
///
/// Returns `Err` if `bincode` encoding or writing to `conn` fails
fn try_send_progress_update(conn: &mut BufReader<Stream>, client_pid: u32) -> WatchResult<bool> {
    let Some(mut progress_queue) = try_acquire(&PROGRESS_QUEUE) else {
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
    let progress_msg = bincode::encode_to_vec(progress, BINCODE_CFG)?;
    write_full_message(conn, &progress_msg)?;

    Ok(curr == total)
}

/// Acquires the `SUBMOD_STATUSES` guard. Every time the lock cannot be acquired
/// (because it is currently locked by an indexing operation in the main loop), an attempt
/// is made to send a progress update to the client.
fn get_status_guard_with_progress<'guard>(
    conn: &mut BufReader<Stream>,
    client_pid: u32,
) -> WatchResult<MutexGuard<'guard, BTreeMap<String, StatusSummary>>> {
    loop {
        if let Some(g) = try_acquire(&SUBMOD_STATUSES) {
            return Ok(g);
        }
        // TODO: Swallow errors here?
        try_send_progress_update(conn, client_pid)?;
    }
}

/// Determines whether `event` is relevant by its `kind`. Relevant events include writes
/// and deletions.
const fn event_is_relevant(event: &Event) -> bool {
    matches!(
        event.kind,
        EventKind::Remove(_)
            | EventKind::Access(AccessKind::Close(AccessMode::Write))
            // This is neeeded for newly created files on Windows only...
            | EventKind::Create(CreateKind::Any)
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
pub fn watch(root_dir: &Path) -> WatchResult<()> {
    let (control_tx, control_rx) = crossbeam_channel::unbounded();
    let mut server = WatchServer::new(root_dir, control_rx);
    server.spawn_listener(control_tx)?;
    server.watch()?;

    Ok(())
}
