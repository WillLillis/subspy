use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    thread::JoinHandle,
    time::{Duration, Instant},
};

use git2::{Repository, Signature};
use subspy::{
    StatusSummary,
    connection::watch_server::watch,
    connection::{
        client::{recv_status_response, request_reindex, request_shutdown, send_status_request},
        ipc_connect, ipc_socket_path,
    },
};
use tempfile::TempDir;

/// Default timeout for polling assertions.
pub const DEFAULT_TIMEOUT: Duration = Duration::from_secs(10);

/// Polling interval between status checks.
pub const POLL_INTERVAL: Duration = Duration::from_millis(100);

/// Builder for constructing a [`TestHarness`] with a specific repository layout.
pub struct HarnessBuilder {
    submodule_names: Vec<String>,
    start_server: bool,
}

impl HarnessBuilder {
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        Self {
            submodule_names: Vec::new(),
            start_server: true,
        }
    }

    /// Add a submodule with the given relative path name.
    pub fn submodule(mut self, name: &str) -> Self {
        self.submodule_names.push(name.to_string());
        self
    }

    /// Add N submodules named `sub_0`, `sub_1`, ..., `sub_{n-1}`.
    pub fn submodules(mut self, count: usize) -> Self {
        for i in 0..count {
            self.submodule_names.push(format!("sub_{i}"));
        }
        self
    }

    /// Do not start the watch server (useful for testing auto-start).
    pub const fn no_server(mut self) -> Self {
        self.start_server = false;
        self
    }

    /// Build the harness: create temp dir, init repos with submodules,
    /// optionally start the watch server, and wait for initial indexing.
    pub fn build(self) -> TestHarness {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let root_path = temp_dir.path().join("root_repo");
        std::fs::create_dir_all(&root_path).unwrap();

        let submodule_paths =
            init_repo_with_submodules(temp_dir.path(), &root_path, &self.submodule_names);

        let server_thread = if self.start_server {
            Some(start_watch_server(&root_path))
        } else {
            None
        };

        let harness = TestHarness {
            root_path,
            server_thread,
            submodule_paths,
            _temp_dir: temp_dir,
        };

        if self.start_server {
            harness.wait_for_server_ready();
        }

        harness
    }
}

/// An integration test harness that manages a real git repository with
/// submodules and an in-process watch server.
pub struct TestHarness {
    /// Path to the root repository.
    root_path: PathBuf,
    /// Background thread running `watch()`. `None` after shutdown.
    server_thread: Option<JoinHandle<()>>,
    /// Submodule relative name -> absolute workdir path.
    submodule_paths: HashMap<String, PathBuf>,
    /// Temp directory holding the entire test fixture. Must be the last field
    /// so it outlives the server thread during automatic field drops.
    _temp_dir: TempDir,
}

impl TestHarness {
    /// Returns the root repository path.
    pub fn root_path(&self) -> &Path {
        &self.root_path
    }

    /// Returns the working directory path for a submodule by relative name.
    pub fn submodule_path(&self, name: &str) -> &Path {
        self.submodule_paths
            .get(name)
            .unwrap_or_else(|| panic!("No submodule named '{name}'"))
    }

    /// Returns the names of all registered submodules.
    pub fn submodule_names(&self) -> impl Iterator<Item = &str> {
        self.submodule_paths.keys().map(String::as_str)
    }

    /// Create or overwrite a file inside a submodule.
    pub fn write_file(&self, submodule: &str, relative_path: &str, contents: &str) {
        let full = self.submodule_path(submodule).join(relative_path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&full, contents).unwrap();
    }

    /// Create or overwrite a file in the root repo (not in a submodule).
    pub fn write_root_file(&self, relative_path: &str, contents: &str) {
        let full = self.root_path.join(relative_path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&full, contents).unwrap();
    }

    /// Delete a file inside a submodule.
    pub fn remove_file(&self, submodule: &str, relative_path: &str) {
        let full = self.submodule_path(submodule).join(relative_path);
        std::fs::remove_file(&full).unwrap();
    }

    /// Stage and commit all changes in a submodule via `git add -A && git commit`.
    pub fn commit_in_submodule(&self, submodule: &str, message: &str) {
        let path = self.submodule_path(submodule);
        git(&["-C", &path.display().to_string(), "add", "-A"]);
        git(&["-C", &path.display().to_string(), "commit", "-m", message]);
    }

    /// Stage the submodule's gitlink in the parent repo's index.
    pub fn stage_submodule(&self, submodule: &str) {
        git(&[
            "-C",
            &self.root_path.display().to_string(),
            "add",
            submodule,
        ]);
    }

    /// Stage a specific file in a submodule's index.
    pub fn stage_file(&self, submodule: &str, relative_path: &str) {
        let path = self.submodule_path(submodule);
        git(&["-C", &path.display().to_string(), "add", relative_path]);
    }

    /// Unstage a file in a submodule's index (`git restore --staged`).
    pub fn unstage_file(&self, submodule: &str, relative_path: &str) {
        let path = self.submodule_path(submodule);
        git(&[
            "-C",
            &path.display().to_string(),
            "restore",
            "--staged",
            relative_path,
        ]);
    }

    /// Request the current status from the watch server.
    pub fn status(&self) -> Vec<(String, StatusSummary)> {
        let mut conn = send_status_request(&self.root_path).expect("send_status_request failed");
        recv_status_response(&mut conn, false)
            .expect("recv_status_response failed")
            .0
    }

    /// Poll status until it matches the expected predicate, or panic on timeout.
    pub fn assert_status_eventually<F>(&self, description: &str, predicate: F)
    where
        F: Fn(&[(String, StatusSummary)]) -> bool,
    {
        self.assert_status_eventually_with(description, DEFAULT_TIMEOUT, POLL_INTERVAL, predicate);
    }

    /// Like [`assert_status_eventually`], but with configurable timeout and
    /// polling interval.
    pub fn assert_status_eventually_with<F>(
        &self,
        description: &str,
        timeout: Duration,
        poll_interval: Duration,
        predicate: F,
    ) where
        F: Fn(&[(String, StatusSummary)]) -> bool,
    {
        let start = Instant::now();
        loop {
            let status = self.status();
            if predicate(&status) {
                return;
            }
            assert!(
                start.elapsed() < timeout,
                "Timed out after {timeout:?} waiting for: {description}\n\
                 Last status: {status:?}"
            );
            std::thread::sleep(poll_interval);
        }
    }

    /// Assert that a specific submodule has exactly the given flags.
    pub fn assert_submodule_status(&self, submodule: &str, expected: StatusSummary) {
        let description = format!("submodule '{submodule}' to have status {expected:?}");
        self.assert_status_eventually(&description, |statuses| {
            if expected == StatusSummary::CLEAN {
                // CLEAN submodules are omitted from the response
                !statuses.iter().any(|(name, _)| name == submodule)
            } else {
                statuses
                    .iter()
                    .any(|(name, st)| name == submodule && *st == expected)
            }
        });
    }

    /// Assert all submodules are clean.
    pub fn assert_all_clean(&self) {
        self.assert_status_eventually("all submodules clean", |s| s.is_empty());
    }

    /// Assert that `new_submodule_paths` returns exactly the given paths (order-sensitive).
    pub fn assert_new_submodule_paths(&self, expected: &[&str]) {
        let repo = Repository::open(&self.root_path).expect("Failed to open root repo");
        let actual =
            subspy::status::new_submodule_paths(&repo).expect("new_submodule_paths failed");
        let expected: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(actual, expected, "new_submodule_paths mismatch");
    }

    /// Assert that `deleted_submodule_paths` returns exactly the given paths.
    pub fn assert_deleted_submodule_paths(&self, expected: &[&str]) {
        let repo = Repository::open(&self.root_path).expect("Failed to open root repo");
        let actual =
            subspy::status::deleted_submodule_paths(&repo).expect("deleted_submodule_paths failed");
        let expected: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(actual, expected, "deleted_submodule_paths mismatch");
    }

    /// Run a git command in the root repo directory.
    pub fn git_in_root(&self, args: &[&str]) {
        let root = self.root_path.display().to_string();
        let mut full_args = vec!["-C", &root];
        full_args.extend_from_slice(args);
        git(&full_args);
    }

    /// Run a git command in a submodule directory.
    pub fn git_in_submodule(&self, submodule: &str, args: &[&str]) {
        let path = self.submodule_path(submodule).display().to_string();
        let mut full_args = vec!["-C", &path];
        full_args.extend_from_slice(args);
        git(&full_args);
    }

    /// Run a git command in the root repo directory, returning the `Output`
    /// instead of panicking on non-zero exit.
    pub fn git_in_root_may_fail(&self, args: &[&str]) -> std::process::Output {
        let root = self.root_path.display().to_string();
        let mut full_args = vec!["-C", &root];
        full_args.extend_from_slice(args);
        git_may_fail(&full_args)
    }

    /// Run a git command in a submodule directory, returning the `Output`
    /// instead of panicking on non-zero exit.
    pub fn git_in_submodule_may_fail(
        &self,
        submodule: &str,
        args: &[&str],
    ) -> std::process::Output {
        let path = self.submodule_path(submodule).display().to_string();
        let mut full_args = vec!["-C", &path];
        full_args.extend_from_slice(args);
        git_may_fail(&full_args)
    }

    /// Commit a change in the source (upstream) repo for a submodule.
    /// This creates fetchable divergent history for rebase tests.
    pub fn commit_in_source_repo(
        &self,
        submodule: &str,
        file: &str,
        contents: &str,
        message: &str,
    ) {
        let source = self.source_repos_path().join(submodule);
        let file_path = source.join(file);
        if let Some(parent) = file_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&file_path, contents).unwrap();
        let source_str = source.display().to_string();
        git(&["-C", &source_str, "add", "-A"]);
        git(&["-C", &source_str, "commit", "-m", message]);
    }

    /// Stage a new submodule in the root repo without committing.
    ///
    /// Creates the source repo and runs `git submodule add`, which stages
    /// both the gitlink and `.gitmodules`. The caller must commit separately.
    pub fn add_submodule_no_commit(&mut self, name: &str) {
        let source_path = self.source_repos_path().join(name);
        create_source_repo(&source_path);

        let source = source_path.display().to_string();
        let root = self.root_path.display().to_string();
        git(&["-C", &root, "submodule", "add", &source, name]);

        self.submodule_paths
            .insert(name.to_string(), self.root_path.join(name));
    }

    /// Add a new submodule to the root repo at runtime.
    /// Creates the source repo, runs `git submodule add`, and commits.
    pub fn add_submodule(&mut self, name: &str) {
        self.add_submodule_no_commit(name);
        self.git_in_root(&["commit", "-m", &format!("Add submodule {name}")]);
    }

    /// Remove a submodule from the root repo at runtime.
    /// Runs `git rm` and commits, then removes from tracked paths.
    pub fn remove_submodule(&mut self, name: &str) {
        let root = self.root_path.display().to_string();
        git(&["-C", &root, "rm", "-f", name]);
        git(&[
            "-C",
            &root,
            "commit",
            "-m",
            &format!("Remove submodule {name}"),
        ]);
        self.submodule_paths.remove(name);
    }

    /// Path to the `source_repos/` directory in the temp dir.
    pub fn source_repos_path(&self) -> PathBuf {
        // root_path is <temp_dir>/root_repo, so parent is <temp_dir>
        self.root_path
            .parent()
            .expect("root_path must have a parent")
            .join("source_repos")
    }

    /// Start the watch server. Use this after `.no_server().build()` when you
    /// need to set up divergent history before the server runs.
    pub fn start_server(&mut self) {
        assert!(
            self.server_thread.is_none(),
            "Server already running; cannot start again"
        );
        self.server_thread = Some(start_watch_server(&self.root_path));
        self.wait_for_server_ready();
    }

    /// Request a reindex from the watch server.
    pub fn request_reindex(&self, replace_watchers: bool) {
        request_reindex(&self.root_path, replace_watchers, false).expect("Reindex request failed");
    }

    /// Shut down the watch server and wait for the thread to exit.
    pub fn shutdown(&mut self) {
        if self.server_thread.is_some() {
            request_shutdown(&self.root_path).expect("Shutdown request failed");
            if let Some(handle) = self.server_thread.take() {
                handle.join().expect("Watch server thread panicked");
            }
        }
    }

    /// Wait for the server to be ready (IPC listener up and initial indexing complete).
    fn wait_for_server_ready(&self) {
        let start = Instant::now();
        let timeout = Duration::from_secs(60);
        // First, poll with raw ipc_connect to detect when the server is
        // listening. This avoids triggering connect_to_server's auto-start
        // behavior (which would spawn a second daemon process).
        let sock_path = ipc_socket_path(&self.root_path);
        loop {
            if ipc_connect(&sock_path).is_ok() {
                // Server is listening. Do a full status request to
                // wait for initial indexing to complete.
                let mut conn = send_status_request(&self.root_path).unwrap();
                let _ = recv_status_response(&mut conn, false);
                return;
            }
            assert!(
                start.elapsed() < timeout,
                "Watch server did not become ready within {timeout:?}"
            );
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}

impl Drop for TestHarness {
    fn drop(&mut self) {
        // Best-effort shutdown. Ignore errors (test may have already shut
        // it down, or the server may have panicked).
        if self.server_thread.is_some() {
            let _ = request_shutdown(&self.root_path);
            if let Some(handle) = self.server_thread.take() {
                let _ = handle.join();
            }
        }
    }
}

// -- Git setup helpers --
// All repo creation is fully local: no network access, no remotes, no pushes.

/// Creates a non-bare repository at `path` with an initial commit containing
/// a single `README.md` file. Used as the source for submodule additions.
pub fn create_source_repo(path: &Path) {
    let repo = Repository::init(path).expect("Failed to init source repo");

    let readme_path = path.join("README.md");
    std::fs::write(&readme_path, "# Initial\n").unwrap();

    let mut index = repo.index().unwrap();
    index.add_path(Path::new("README.md")).unwrap();
    index.write().unwrap();
    let tree_oid = index.write_tree().unwrap();
    let tree = repo.find_tree(tree_oid).unwrap();

    let sig = Signature::now("Test", "test@test.com").unwrap();
    repo.commit(Some("HEAD"), &sig, &sig, "Initial commit", &tree, &[])
        .unwrap();
}

/// Initializes the root repository at `root_path`, creates source repos for
/// each submodule name, and adds them as submodules. Returns a map of
/// submodule relative paths to their working directory paths.
fn init_repo_with_submodules(
    temp_dir: &Path,
    root_path: &Path,
    submodule_names: &[String],
) -> HashMap<String, PathBuf> {
    let repo = Repository::init(root_path).expect("Failed to init root repo");
    let sig = Signature::now("Test", "test@test.com").unwrap();

    // Create an initial commit so HEAD exists
    {
        let mut index = repo.index().unwrap();
        let tree_oid = index.write_tree().unwrap();
        let tree = repo.find_tree(tree_oid).unwrap();
        repo.commit(Some("HEAD"), &sig, &sig, "Initial commit", &tree, &[])
            .unwrap();
    }

    let mut submod_paths = HashMap::new();
    let sources_dir = temp_dir.join("source_repos");
    std::fs::create_dir_all(&sources_dir).unwrap();

    for name in submodule_names {
        let source_path = sources_dir.join(name);
        create_source_repo(&source_path);

        let url = format!("{}", source_path.display());
        let mut submodule = repo
            .submodule(&url, Path::new(name), true)
            .expect("Failed to add submodule");
        submodule.clone(None).expect("Failed to clone submodule");
        submodule
            .add_finalize()
            .expect("Failed to finalize submodule");

        submod_paths.insert(name.clone(), root_path.join(name));
    }

    // Commit the submodule additions
    {
        let mut index = repo.index().unwrap();
        index.add_path(Path::new(".gitmodules")).unwrap();
        for name in submodule_names {
            index.add_path(Path::new(name)).unwrap();
        }
        index.write().unwrap();
        let tree_oid = index.write_tree().unwrap();
        let tree = repo.find_tree(tree_oid).unwrap();
        let head = repo.head().unwrap().peel_to_commit().unwrap();
        repo.commit(Some("HEAD"), &sig, &sig, "Add submodules", &tree, &[&head])
            .unwrap();
    }

    submod_paths
}

/// Runs a `git` command with the given arguments, panicking on failure.
///
/// Injects `-c user.name` and `-c user.email` so that commits work in
/// environments without a global git config (e.g. CI). Also sets
/// `GIT_EDITOR` and `GIT_SEQUENCE_EDITOR` to prevent interactive editors
/// from opening during operations like `git rebase --continue`.
pub fn git(args: &[&str]) {
    let output = git_may_fail(args);
    assert!(
        output.status.success(),
        "git {} failed: {}",
        args.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Like [`git()`] but returns the `Output` instead of panicking on non-zero
/// exit. Useful for commands that may legitimately fail (e.g. `git rebase`
/// hitting a conflict).
pub fn git_may_fail(args: &[&str]) -> std::process::Output {
    std::process::Command::new("git")
        .args([
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@test.com",
            "-c",
            "protocol.file.allow=always",
        ])
        .env("GIT_EDITOR", "true")
        .env("GIT_SEQUENCE_EDITOR", "true")
        .args(args)
        .output()
        .expect("Failed to run git")
}

/// Starts the watch server on a background thread. Returns the `JoinHandle`.
fn start_watch_server(root_path: &Path) -> JoinHandle<()> {
    let path = root_path.to_path_buf();
    std::thread::Builder::new()
        .name("test_watch_server".to_string())
        .spawn(move || {
            if let Err(e) = watch(&path, false) {
                eprintln!("Watch server exited: {e}");
            }
        })
        .expect("Failed to spawn watch server thread")
}
