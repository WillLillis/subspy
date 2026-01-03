use std::{
    collections::{BTreeMap, HashMap, VecDeque},
    io::BufReader,
    path::{Path, PathBuf},
    sync::{LazyLock, Mutex, MutexGuard, TryLockError},
    time::Duration,
};

use bincode::{BorrowDecode, Encode};
use git2::Repository;
use interprocess::local_socket::{Stream, traits::ListenerExt as _};
use log::{error, info};
use notify::{
    Event, EventKind,
    event::{AccessKind, AccessMode},
};
use notify_debouncer_full::new_debouncer;

use crate::{
    DOT_GIT, DOT_GITMODULES, StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, REINDEX_FILE_PREFIX, SHUTDOWN_FILE_PREFIX, ServerMessage,
        create_listener, get_reindex_file_path, get_shutdown_file_path, read_full_message,
        write_full_message,
    },
    create_progress_bar,
    watch::WatchResult,
};

/// The main map of the server, associating submodule relative paths (from the repository's
/// `.gitmodules` file) to the given submodule's summarized status.
static SUBMOD_STATUSES: LazyLock<Mutex<BTreeMap<String, StatusSummary>>> =
    LazyLock::new(|| Mutex::new(BTreeMap::new()));

/// Associates a given client pid with a queue of indexing progress updates.
static PROGRESS_QUEUE: LazyLock<Mutex<HashMap<u32, VecDeque<ProgressUpdate>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Message receiver type for a debounced watcher
type WatchReceiver = crossbeam_channel::Receiver<notify_debouncer_full::DebounceEventResult>;

/// Debounced watcher type
type DebouncedWatcher = notify_debouncer_full::Debouncer<
    notify::RecommendedWatcher,
    notify_debouncer_full::RecommendedCache,
>;

/// Item watched by the server
#[derive(Debug)]
struct WatchListItem {
    pub relative_path: String,
    pub receiver: WatchReceiver,
    pub watcher: DebouncedWatcher,
}

impl WatchListItem {
    #[expect(clippy::needless_pass_by_value)]
    fn new(rel_path: impl ToString, receiver: WatchReceiver, watcher: DebouncedWatcher) -> Self {
        Self {
            relative_path: rel_path.to_string(),
            receiver,
            watcher,
        }
    }
}

type WatchList = Vec<WatchListItem>;

/// The primary state necessary to maintain a status watch over the repository at `root_path`
#[derive(Debug)]
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
}

/// Summarizes an event received from a watcher. Create with `get_event_type`
#[derive(Debug, Copy, Clone)]
enum EventType {
    /// Client requested reindex of the entire repository
    ReindexRequest(u32),
    /// Client requested shutdown of the watch server
    ShutdownRequest(u32),
    /// Something changed in `.git/` or `.gitmodules`, reindex needed
    GitOperation,
    /// A change occurred in one of the watched submodules
    SubmoduleChange,
}

fn pid_from_event(event: &Event, filename_prefix: &str) -> Option<u32> {
    if let Some(name_path) = event.paths.iter().find(|p| {
        p.file_name()
            .is_some_and(|n| n.to_string_lossy().starts_with(filename_prefix))
    }) && let Ok(id) =
        name_path.file_name().unwrap().to_string_lossy()[filename_prefix.len()..].parse::<u32>()
    {
        Some(id)
    } else {
        None
    }
}

impl WatchServer {
    pub fn new(root_path: &Path) -> Self {
        let gitmodules_path = root_path.to_path_buf().join(DOT_GITMODULES);
        let dot_git_path = root_path.to_path_buf().join(DOT_GIT);

        Self {
            do_watch: true,
            client_pid: None,
            watchers: Vec::new(),
            root_path: root_path.to_path_buf(),
            gitmodules_path,
            dot_git_path,
        }
    }

    /// Spawns a detached listener thread to handle incoming client connections
    ///
    /// # Errors
    ///
    /// Returns `std::io::Error` if the thread cannot be created
    fn spawn_listener(&self) -> std::io::Result<()> {
        let path = self.root_path.clone();
        let listener = create_listener(path.as_path())?;
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
                    if handle_client_connection(conn, &mut buffer, path.as_path())? {
                        break;
                    }
                }

                WatchResult::Ok(())
            })?;

        Ok(())
    }

    /// Stop all the watchers in `self.watchers`, clearing the list
    fn clear_watchers(&mut self) {
        for WatchListItem { watcher, .. } in self.watchers.drain(..) {
            watcher.stop_nonblocking();
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
    ) -> notify::Result<(WatchReceiver, DebouncedWatcher)> {
        let (tx, rx) = crossbeam_channel::unbounded();
        let log_full_path = watch_path.as_ref().to_path_buf();
        let mut debouncer = new_debouncer(
            Duration::from_secs(1),
            None,
            move |res: notify_debouncer_full::DebounceEventResult| {
                if let Err(e) = tx.send(res) {
                    error!(
                        "Watcher for {} failed to send -- {e}",
                        log_full_path.display()
                    );
                }
            },
        )?;
        debouncer.watch(&watch_path, mode)?;
        info!("Placed watch: {}", watch_path.as_ref().display());

        Ok((rx, debouncer))
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
        self.watchers
            .push(WatchListItem::new(DOT_GITMODULES, rx, debouncer));

        let (rx, debouncer) = Self::place_watch(
            self.dot_git_path.as_path(),
            notify::RecursiveMode::Recursive,
        )?;
        self.watchers
            .push(WatchListItem::new(DOT_GIT, rx, debouncer));

        let (rx, debouncer) = Self::place_watch(
            self.root_path.as_path(),
            notify::RecursiveMode::NonRecursive,
        )?;
        self.watchers
            .push(WatchListItem::new(SHUTDOWN_FILE_PREFIX, rx, debouncer));

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
        let submodules = repo.submodules()?;
        info!("Indexing project at {}", self.root_path.display());
        let progress_bar = display_progress.then_some(create_progress_bar(
            submodules.len() as u64,
            "Indexing submodules",
        ));

        let mut status_guard = SUBMOD_STATUSES.lock().expect("Mutex poisoned");
        if let Some(id) = self.client_pid {
            update_progress(id, ProgressUpdate::new(0, submodules.len() as u32));
        }
        status_guard.clear();

        for (i, submod) in submodules.iter().enumerate() {
            let sub_start = std::time::Instant::now();
            let rel_path = submod.path().to_string_lossy().to_string();
            let submod_path = self.root_path.clone().join(submod.path());

            let status = repo
                .submodule_status(submod.path().to_str().unwrap(), git2::SubmoduleIgnore::None)?;
            let converted_status: StatusSummary = status.into();
            status_guard.insert(rel_path.clone(), converted_status);

            let (rx, debouncer) =
                Self::place_watch(&submod_path, notify::RecursiveMode::Recursive)?;
            self.watchers
                .push(WatchListItem::new(rel_path, rx, debouncer));

            if let Some(id) = self.client_pid {
                update_progress(
                    id,
                    ProgressUpdate::new(i as u32 + 1, submodules.len() as u32),
                );
            }
            if let Some(pb) = &progress_bar {
                pb.inc(1);
            }
            info!(
                "Indexed {} ({:?} -> {:?}) in {}ms",
                submod_path.display(),
                status,
                converted_status,
                sub_start.elapsed().as_millis(),
            );
        }
        drop(status_guard);

        self.client_pid = None;
        if let Some(pb) = &progress_bar {
            pb.finish();
            println!(
                "Indexing complete. If you haven't already, send this process to the background."
            );
        }

        Ok(())
    }

    /// Sets up watchers and populates the status map
    fn setup(&mut self, repo: &Repository, display_progress: bool) -> WatchResult<()> {
        self.place_root_watches()?;
        self.populate_status_map(repo, display_progress)?;

        Ok(())
    }

    /// Removes the sentinel shutdown file if it exists, signaling to the client that the watch
    /// server successfully shut down.
    fn signal_shutdown(&self) {
        if let Some(client_pid) = self.client_pid {
            let shutdown_path = get_shutdown_file_path(&self.root_path, client_pid);
            if let Err(e) = std::fs::remove_file(&shutdown_path) {
                error!(
                    "Failed to remove shutdown file {} -- {e}",
                    shutdown_path.display()
                );
            }
        }
    }

    /// The main watch loop for the server. Will loop until a client shutdown request is received
    /// or an error is encountered.
    fn watch(&mut self) -> WatchResult<()> {
        // only display the progress bar on the first indexing
        let mut display_progress = true;
        loop {
            self.clear_watchers();
            if !self.do_watch {
                break;
            }

            let repo = Repository::open(&self.root_path)?;
            self.setup(&repo, display_progress)?;
            display_progress = false;

            self.handle_events(&repo)?;
        }

        self.signal_shutdown();

        Ok(())
    }

    /// Converts a debounced watcher's event and relative path to a relevant `EventType`,
    /// if possible
    fn get_event_type(&self, event: &Event, rel_path: &str) -> Option<EventType> {
        if !event_is_relevant(event) {
            return None;
        }

        if rel_path.eq(DOT_GITMODULES) || rel_path.eq(DOT_GIT) {
            if event
                .paths
                .iter()
                .any(|p| p.starts_with(&self.dot_git_path) || p.eq(&self.gitmodules_path))
            {
                // if this event was triggered by a reindex request, grab
                // the client's pid
                pid_from_event(event, REINDEX_FILE_PREFIX)
                    // otherwise it's just some git operation, trigger a reindex
                    .map_or(Some(EventType::GitOperation), |pid| {
                        Some(EventType::ReindexRequest(pid))
                    })
            } else {
                None
            }
        } else if rel_path.eq(SHUTDOWN_FILE_PREFIX)
            && event.paths.iter().any(|p| {
                p.file_name().is_some_and(|n| {
                    n.to_str()
                        .is_some_and(|n| n.starts_with(SHUTDOWN_FILE_PREFIX))
                })
            })
        {
            pid_from_event(event, SHUTDOWN_FILE_PREFIX).map(EventType::ShutdownRequest)
        } else {
            Some(EventType::SubmoduleChange)
        }
    }

    /// The "meat" of the logic for the watch server. Handles incoming watcher events and updates
    /// server state accordingly. This function will only exit if a reindex is required or
    /// requested, or if an error occurs.
    fn handle_events(&mut self, repo: &Repository) -> WatchResult<()> {
        let mut sel = crossbeam_channel::Select::new();
        for WatchListItem { receiver, .. } in &self.watchers {
            sel.recv(receiver); // Register each recv op
        }

        'outer: loop {
            let oper = sel.select(); // Blocks until any ready
            let index = oper.index(); // Which rx fired

            match oper.recv(&self.watchers[index].receiver)? {
                Ok(events) => {
                    for event in events {
                        let rel_path = self.watchers[index].relative_path.as_str();
                        match self.get_event_type(&event, rel_path) {
                            Some(EventType::GitOperation) => break 'outer,
                            Some(EventType::ReindexRequest(id)) => {
                                self.client_pid = Some(id);
                                break 'outer;
                            }
                            Some(EventType::ShutdownRequest(id)) => {
                                self.client_pid = Some(id);
                                self.do_watch = false;
                                break 'outer;
                            }
                            Some(EventType::SubmoduleChange) => {
                                let submod_status = match repo
                                    .submodule_status(rel_path, git2::SubmoduleIgnore::None)
                                {
                                    Ok(st) => st,
                                    Err(e) => {
                                        error!(
                                            "Failed to get submodule status for path: {rel_path} -- {e}"
                                        );
                                        continue;
                                    }
                                };
                                SUBMOD_STATUSES
                                    .lock()
                                    .expect("Mutex poisoned")
                                    .entry(rel_path.to_string())
                                    .and_modify(|st| *st = submod_status.into())
                                    .or_insert_with(|| submod_status.into());
                                // Any events for this receiver will refer to the same submodule. Once
                                // we've triggered an update, any more will be redundant.
                                break;
                            }
                            None => {} // try the next one
                        }
                    }
                }
                Err(e) => {
                    error!(
                        "Watcher error for submodule {}: {:?}",
                        self.watchers[index].relative_path, e
                    );
                }
            }
        }

        Ok(())
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

/// Handles incoming client connections. Returns whether the listener recieved a shutdown command
///
/// # Errors
///
/// Returns `Err` if the client message couldn't be read, decoded, or handled.
fn handle_client_connection(conn: Stream, buffer: &mut Vec<u8>, path: &Path) -> WatchResult<bool> {
    let mut conn = BufReader::new(conn);
    info!("New client connection to server for {}", path.display());

    read_full_message(&mut conn, buffer)?;
    let (msg, _): (ClientMessage, usize) = bincode::borrow_decode_from_slice(buffer, BINCODE_CFG)?;

    match msg {
        ClientMessage::Reindex(client_pid) => handle_reindex_request(conn, path, client_pid)?,
        ClientMessage::Status(client_pid) => handle_status_request(conn, client_pid)?,
        ClientMessage::Shutdown(client_pid) => {
            handle_shutdown_request(path, client_pid);
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

/// Handles a client's request to shut down the watch server.
fn handle_shutdown_request(root_dir: &Path, client_pid: u32) {
    let shutdown_path = get_shutdown_file_path(root_dir, client_pid);
    if let Err(e) = std::fs::write(&shutdown_path, "it's so joever") {
        error!(
            "Failed to write to shutdown file '{}' -- {e}",
            shutdown_path.display()
        );
    }
}

/// Handles a client's request to reindex the watch server.
fn handle_reindex_request(
    mut conn: BufReader<Stream>,
    root_dir: &Path,
    client_pid: u32,
) -> WatchResult<()> {
    // changes to files within the `.git` directory trigger a full re-index, so we only need to
    // create a file inside `.git` for this to work.
    let reindex_path = get_reindex_file_path(root_dir, client_pid);
    std::fs::write(&reindex_path, "we're so back")?;
    // NOTE: If this file is immediately removed, the watcher doesn't pick up its creation. To get
    // around this, the responsibility for deletion falls on the client.

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
        EventKind::Remove(_) | EventKind::Access(AccessKind::Close(AccessMode::Write))
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
    let mut server = WatchServer::new(root_dir);
    server.spawn_listener()?;
    server.watch()?;

    Ok(())
}
