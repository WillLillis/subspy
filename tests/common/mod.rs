use std::{
    path::{Path, PathBuf},
    thread::JoinHandle,
    time::{Duration, Instant},
};

use git2::{Repository, Signature};
use tempfile::TempDir;

use subspy::{
    connection::client::{request_shutdown, request_status},
    connection::watch_server,
};

/// A temporary git repository with helpers for adding submodules.
pub struct TestRepo {
    _dir: TempDir,
    path: PathBuf,
    /// Keep remote TempDirs alive so submodule URLs remain valid.
    _remotes: Vec<TempDir>,
}

impl TestRepo {
    /// Creates a new temporary git repository with an initial commit.
    pub fn new() -> Self {
        let dir = TempDir::new().expect("Failed to create temp dir");
        let path = dunce::canonicalize(dir.path()).expect("Failed to canonicalize temp dir");
        let repo = Repository::init(&path).expect("Failed to init repo");

        // Create an initial commit so HEAD exists
        let sig = Signature::now("test", "test@test.com").unwrap();
        let tree_id = repo.index().unwrap().write_tree().unwrap();
        let tree = repo.find_tree(tree_id).unwrap();
        repo.commit(Some("HEAD"), &sig, &sig, "Initial commit", &tree, &[])
            .unwrap();

        Self {
            _dir: dir,
            path,
            _remotes: Vec::new(),
        }
    }

    /// Returns the canonicalized path to the repo root.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Opens the repository.
    pub fn repo(&self) -> Repository {
        Repository::open(&self.path).expect("Failed to open repo")
    }

    /// Adds a submodule to this repo. Creates a remote repo, clones it as
    /// a submodule, and commits the result. The submodule will contain one
    /// tracked file (`file.txt`).
    ///
    /// This must be called *before* starting the watch server — calling it
    /// with a running server will cause index lock contention.
    pub fn add_submodule(&mut self, name: &str) {
        // Create a non-bare "remote" repo with at least one commit.
        let remote_dir = TempDir::new().expect("Failed to create remote temp dir");
        let remote_path =
            dunce::canonicalize(remote_dir.path()).expect("Failed to canonicalize remote dir");
        let remote_repo = Repository::init(&remote_path).expect("Failed to init remote repo");

        let file_path = remote_path.join("file.txt");
        std::fs::write(&file_path, "initial content\n").unwrap();
        let mut index = remote_repo.index().unwrap();
        index.add_path(Path::new("file.txt")).unwrap();
        index.write().unwrap();
        let tree_id = index.write_tree().unwrap();
        let tree = remote_repo.find_tree(tree_id).unwrap();
        let sig = Signature::now("test", "test@test.com").unwrap();
        remote_repo
            .commit(Some("HEAD"), &sig, &sig, "Initial commit", &tree, &[])
            .unwrap();

        // Add submodule pointing to the remote
        let remote_url = format!("file://{}", remote_path.display());
        let repo = self.repo();
        let mut submodule = repo
            .submodule(&remote_url, Path::new(name), true)
            .expect("Failed to add submodule");

        // Clone the remote into the submodule's working directory
        let mut update_opts = git2::SubmoduleUpdateOptions::new();
        submodule
            .clone(Some(&mut update_opts))
            .expect("Failed to clone submodule");

        // Finalize
        submodule
            .add_finalize()
            .expect("Failed to finalize submodule");

        // Stage and commit the submodule addition
        let mut parent_index = repo.index().unwrap();
        parent_index
            .add_path(Path::new(".gitmodules"))
            .unwrap();
        parent_index.add_path(Path::new(name)).unwrap();
        parent_index.write().unwrap();
        let tree_id = parent_index.write_tree().unwrap();
        let tree = repo.find_tree(tree_id).unwrap();
        let sig = Signature::now("test", "test@test.com").unwrap();
        let head = repo.head().unwrap().peel_to_commit().unwrap();
        repo.commit(
            Some("HEAD"),
            &sig,
            &sig,
            &format!("Add submodule {name}"),
            &tree,
            &[&head],
        )
        .unwrap();

        self._remotes.push(remote_dir);
    }

    /// Returns the absolute path to a submodule's working directory.
    pub fn submodule_path(&self, name: &str) -> PathBuf {
        self.path.join(name)
    }
}

/// A handle to a watch server running in a background thread.
pub struct WatchServerHandle {
    path: PathBuf,
    thread: Option<JoinHandle<subspy::watch::WatchResult<()>>>,
}

impl WatchServerHandle {
    /// Starts the watch server for the repo at `path` in a background thread.
    pub fn start(path: &Path) -> Self {
        let path = path.to_path_buf();
        let thread_path = path.clone();
        let thread = std::thread::Builder::new()
            .name("test_watch_server".to_string())
            .spawn(move || watch_server::watch(&thread_path))
            .expect("Failed to spawn watch server thread");

        Self {
            path,
            thread: Some(thread),
        }
    }

    /// Polls `request_status()` until the server responds, with retries.
    pub fn wait_until_ready(&self) {
        let deadline = Instant::now() + Duration::from_secs(10);
        let interval = Duration::from_millis(100);

        while Instant::now() < deadline {
            if request_status(&self.path).is_ok() {
                return;
            }
            std::thread::sleep(interval);
        }
        panic!(
            "Watch server did not become ready within 10 seconds for {}",
            self.path.display()
        );
    }

    /// Shuts down the server and joins the thread, returning the server's result.
    pub fn shutdown(mut self) -> subspy::watch::WatchResult<()> {
        let _ = request_shutdown(&self.path);
        self.join_thread()
    }

    fn join_thread(&mut self) -> subspy::watch::WatchResult<()> {
        if let Some(handle) = self.thread.take() {
            handle.join().expect("Watch server thread panicked")
        } else {
            Ok(())
        }
    }
}

impl Drop for WatchServerHandle {
    fn drop(&mut self) {
        if self.thread.is_some() {
            // Best-effort shutdown
            let _ = request_shutdown(&self.path);
            let _ = self.join_thread();
        }
    }
}

/// Polls `condition` at `interval` until it returns `true`, or panics after `timeout`.
pub fn poll_until(timeout: Duration, interval: Duration, mut condition: impl FnMut() -> bool) {
    let deadline = Instant::now() + timeout;
    while Instant::now() < deadline {
        if condition() {
            return;
        }
        std::thread::sleep(interval);
    }
    panic!("poll_until timed out after {timeout:?}");
}
