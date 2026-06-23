use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::LazyLock,
    thread::JoinHandle,
    time::{Duration, Instant},
};

use subspy::git::configure_git2;

use git2::{Repository, Signature, Time};
use subspy::{
    StatusSummary,
    connection::watch_server::watch,
    connection::{
        client::{recv_status_response, request_reindex, request_shutdown, send_status_request},
        ipc_connect, ipc_socket_path,
    },
};
use tempfile::TempDir;

/// Configures global libgit2 options once across all test threads.
/// See `git::configure_git2` for rationale.
static GIT2_INIT: LazyLock<()> = LazyLock::new(|| {
    // SAFETY: LazyLock guarantees this runs exactly once. All other
    // threads calling HarnessBuilder::build will block on the LazyLock
    // until this completes.
    configure_git2();
});

/// Default timeout for polling assertions.
pub const DEFAULT_TIMEOUT: Duration = Duration::from_secs(10);

/// Polling interval between status checks.
pub const POLL_INTERVAL: Duration = Duration::from_millis(100);

// Identity / time pins used by every fixture commit so SHAs are
// byte-stable across runs - required by the long-format snapshot tests.
pub const FIXTURE_NAME: &str = "Test";
pub const FIXTURE_EMAIL: &str = "test@test.com";
pub const FIXTURE_TIME: i64 = 1_700_000_000;

/// Builder for constructing a [`TestHarness`] with a specific repository layout.
pub struct HarnessBuilder {
    submodule_names: Vec<String>,
    start_server: bool,
    as_worktree: bool,
    worktree_init_submodules: bool,
}

impl HarnessBuilder {
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        Self {
            submodule_names: Vec::new(),
            start_server: true,
            as_worktree: false,
            worktree_init_submodules: true,
        }
    }

    /// Watch a linked worktree of the superproject instead of the superproject
    /// itself. The superproject is built as usual, then a worktree is added and
    /// its submodules checked out (their gitdirs land under
    /// `.git/worktrees/<name>/modules/`); the server and all `Repo` ops target
    /// the worktree.
    pub const fn worktree(mut self) -> Self {
        self.as_worktree = true;
        self
    }

    /// Like [`worktree`](Self::worktree), but leaves the worktree's submodules
    /// unchecked-out, the default state right after `git worktree add` (no
    /// `submodule update --init`). The server must treat the absent submodule
    /// working trees as clean.
    pub const fn worktree_without_submodule_checkout(mut self) -> Self {
        self.as_worktree = true;
        self.worktree_init_submodules = false;
        self
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
        LazyLock::force(&GIT2_INIT);
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let root_path = temp_dir.path().join("root_repo");
        std::fs::create_dir_all(&root_path).unwrap();
        // Canonicalize like the CLI's `get_project_path`
        let root_path = dunce::canonicalize(&root_path).unwrap();

        let submodule_paths =
            init_repo_with_submodules(temp_dir.path(), &root_path, &self.submodule_names);

        // In worktree mode, add a linked worktree of the superproject and watch
        // it instead. Its submodules are re-checked-out under the worktree's own
        // git dir, so the server exercises the worktree path resolution.
        let (active_root, submodule_paths) = if self.as_worktree {
            let wt_path = setup_worktree(
                temp_dir.path(),
                &root_path,
                &self.submodule_names,
                self.worktree_init_submodules,
            );
            let wt_submods = self
                .submodule_names
                .iter()
                .map(|name| (name.clone(), wt_path.join(name)))
                .collect();
            (wt_path, wt_submods)
        } else {
            (root_path, submodule_paths)
        };

        let server_thread = if self.start_server {
            Some(start_watch_server(&active_root))
        } else {
            None
        };

        let submodules = submodule_paths
            .into_iter()
            .map(|(name, path)| (name, Repo::new(&path)))
            .collect();

        let harness = TestHarness {
            root: Repo::new(&active_root),
            server_thread,
            submodules,
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
///
/// File and git operations are exposed compositionally via [`Repo`]: use
/// `harness.root()` for the top-level repo and `harness.submodule(name)`
/// for a submodule's working tree.
pub struct TestHarness {
    /// The root repository.
    root: Repo,
    /// Background thread running `watch()`. `None` after shutdown.
    server_thread: Option<JoinHandle<()>>,
    /// Submodule relative name -> the submodule's working tree as a `Repo`.
    submodules: HashMap<String, Repo>,
    /// Temp directory holding the entire test fixture. Must be the last field
    /// so it outlives the server thread during automatic field drops.
    _temp_dir: TempDir,
}

impl TestHarness {
    /// Returns the root repository as a [`Repo`] for compositional ops.
    pub fn root(&self) -> &Repo {
        &self.root
    }

    /// Returns a submodule's working tree as a [`Repo`] for compositional ops.
    pub fn submodule(&self, name: &str) -> &Repo {
        self.submodules
            .get(name)
            .unwrap_or_else(|| panic!("No submodule named '{name}'"))
    }

    /// Returns the names of all registered submodules.
    pub fn submodule_names(&self) -> impl Iterator<Item = &str> {
        self.submodules.keys().map(String::as_str)
    }

    /// Request the current status from the watch server.
    pub fn status(&self) -> Vec<(String, StatusSummary)> {
        let mut conn =
            send_status_request(self.root.path(), false).expect("send_status_request failed");
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
            if expected == StatusSummary::clean() {
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

    /// Assert that `submodule_changes` returns exactly the given paths as deletions.
    pub fn assert_deleted_submodule_paths(&self, expected: &[&str]) {
        let repo = Repository::open(self.root.path()).expect("Failed to open root repo");
        let changes = subspy::status::submodule_changes(&repo).expect("submodule_changes failed");
        let expected: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(changes.deleted, expected, "deleted submodules mismatch");
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
        let source = Repo::new(&self.source_repos_path().join(submodule));
        source.write(file, contents).add_all().commit(message);
    }

    /// Stage a new submodule in the root repo without committing.
    ///
    /// Creates the source repo and runs `git submodule add`, which stages
    /// both the gitlink and `.gitmodules`. The caller must commit separately.
    pub fn add_submodule_no_commit(&mut self, name: &str) {
        let source_path = self.source_repos_path().join(name);
        create_source_repo(&source_path);

        let source = source_path.display().to_string();
        self.root.run_git(&["submodule", "add", &source, name]);

        self.submodules
            .insert(name.to_string(), Repo::new(&self.root.path().join(name)));
    }

    /// Add a new submodule to the root repo at runtime.
    /// Creates the source repo, runs `git submodule add`, and commits.
    pub fn add_submodule(&mut self, name: &str) {
        self.add_submodule_no_commit(name);
        self.root.commit(&format!("Add submodule {name}"));
    }

    /// Remove a submodule from the root repo at runtime.
    /// Runs `git rm` and commits, then removes from tracked paths.
    pub fn remove_submodule(&mut self, name: &str) {
        self.root.run_git(&["rm", "-f", name]);
        self.root.commit(&format!("Remove submodule {name}"));
        self.submodules.remove(name);
    }

    /// Path to the `source_repos/` directory in the temp dir.
    pub fn source_repos_path(&self) -> PathBuf {
        // root is <temp_dir>/root_repo, so parent is <temp_dir>
        self.root
            .path()
            .parent()
            .expect("root path must have a parent")
            .join("source_repos")
    }

    /// Start the watch server. Use this after `.no_server().build()` when you
    /// need to set up divergent history before the server runs.
    pub fn start_server(&mut self) {
        assert!(
            self.server_thread.is_none(),
            "Server already running; cannot start again"
        );
        self.server_thread = Some(start_watch_server(self.root.path()));
        self.wait_for_server_ready();
    }

    /// Request a reindex from the watch server.
    pub fn request_reindex(&self, replace_watchers: bool) {
        request_reindex(self.root.path(), replace_watchers, false).expect("Reindex request failed");
    }

    /// Shut down the watch server and wait for the thread to exit.
    pub fn shutdown(&mut self) {
        if self.server_thread.is_some() {
            request_shutdown(self.root.path()).expect("Shutdown request failed");
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
        let sock_path = ipc_socket_path(self.root.path());
        loop {
            if ipc_connect(&sock_path).is_ok() {
                // Server is listening. Do a full status request to
                // wait for initial indexing to complete.
                let mut conn = send_status_request(self.root.path(), false).unwrap();
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
            let _ = request_shutdown(self.root.path());
            if let Some(handle) = self.server_thread.take() {
                let _ = handle.join();
            }
        }

        // The server thread is now joined, so every producer has quiesced and
        // the captured trace is complete. Print it to stderr (where `libtest`
        // attributes it to the failing test) if we are unwinding from a test
        // failure; otherwise discard it. Compiled out without `trace_events`.
        #[cfg(trace_events)]
        {
            let root = self.root.path();
            if std::thread::panicking() {
                subspy::connection::watch_server::trace::dump_for(
                    root,
                    &root.display().to_string(),
                );
            } else {
                subspy::connection::watch_server::trace::discard_for(root);
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

    let sig = fixture_signature();
    repo.commit(Some("HEAD"), &sig, &sig, "Initial commit", &tree, &[])
        .unwrap();
}

fn fixture_signature() -> Signature<'static> {
    Signature::new(FIXTURE_NAME, FIXTURE_EMAIL, &Time::new(FIXTURE_TIME, 0)).unwrap()
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
    let sig = fixture_signature();

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

/// Builder for a fixture git repo, used to set up specific repo states
/// declaratively for tests. Wraps `git -C <root> ...` and filesystem
/// mutations so test setups read top-down without scattered boilerplate.
///
/// All methods take `&self` and return `&Self` so calls can chain freely
/// off a single `Repo::init` call.
pub struct Repo {
    root: PathBuf,
}

impl Repo {
    /// `git init` an empty repo at `root` with `master` as the initial branch.
    pub fn init(root: &Path) -> Self {
        let r = Self::new(root);
        r.run_git(&["init", "-q", "--initial-branch=master"]);
        r
    }

    /// Construct a `Repo` handle for an existing repository at `root` without
    /// running any git commands. Useful when the repo was created by other
    /// means (e.g. via libgit2).
    pub fn new(root: &Path) -> Self {
        Self {
            root: root.to_path_buf(),
        }
    }

    /// Returns the repository root path.
    pub fn path(&self) -> &Path {
        &self.root
    }

    /// Unstage a file in this repo's index (`git restore --staged`).
    pub fn restore_staged(&self, path: &str) -> &Self {
        self.run_git(&["restore", "--staged", path]);
        self
    }

    /// Write `content` to `path` (relative to the repo root). Creates any
    /// missing parent directories.
    pub fn write(&self, path: &str, content: &str) -> &Self {
        let full = self.root.join(path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&full, content).unwrap();
        self
    }

    /// `mkdir -p` the directory at `path` (relative to the repo root).
    pub fn mkdir(&self, path: &str) -> &Self {
        std::fs::create_dir_all(self.root.join(path)).unwrap();
        self
    }

    /// Remove a file from the working tree (no `git rm`).
    pub fn rm_file(&self, path: &str) -> &Self {
        std::fs::remove_file(self.root.join(path)).unwrap();
        self
    }

    pub fn add(&self, path: &str) -> &Self {
        self.run_git(&["add", path]);
        self
    }

    pub fn add_all(&self) -> &Self {
        self.run_git(&["add", "-A"]);
        self
    }

    pub fn commit(&self, msg: &str) -> &Self {
        self.run_git(&["commit", "-qm", msg]);
        self
    }

    /// `git checkout -b <name>`: create and switch to a new branch.
    pub fn branch(&self, name: &str) -> &Self {
        self.run_git(&["checkout", "-qb", name]);
        self
    }

    /// `git checkout <refname>`: switch to an existing ref (branch or commit).
    pub fn checkout(&self, refname: &str) -> &Self {
        self.run_git(&["checkout", "-q", refname]);
        self
    }

    pub fn mv(&self, from: &str, to: &str) -> &Self {
        self.run_git(&["mv", from, to]);
        self
    }

    pub fn rm_tracked(&self, path: &str) -> &Self {
        self.run_git(&["rm", "-q", path]);
        self
    }

    /// Run a git command relative to this repo's root via [`git`], asserting success.
    pub fn run_git(&self, args: &[&str]) {
        let r = self.root.display().to_string();
        let mut full: Vec<&str> = vec!["-C", &r];
        full.extend(args);
        git(&full);
    }

    /// Run a git command relative to this repo's root via [`git_may_fail`],
    /// returning the raw `Output` without asserting. Use for commands that
    /// are expected to fail (e.g. a merge that conflicts).
    pub fn try_git(&self, args: &[&str]) -> std::process::Output {
        let r = self.root.display().to_string();
        let mut full: Vec<&str> = vec!["-C", &r];
        full.extend(args);
        git_may_fail(&full)
    }
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
/// hitting a conflict). Pins author/committer identity + date via env
/// so fixture commit SHAs are deterministic.
pub fn git_may_fail(args: &[&str]) -> std::process::Output {
    let pinned_date = format!("{FIXTURE_TIME} +0000");
    std::process::Command::new("git")
        .args([
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@test.com",
            "-c",
            "protocol.file.allow=always",
            "-c",
            "commit.gpgsign=false",
            "-c",
            "tag.gpgsign=false",
        ])
        .env("GIT_EDITOR", "true")
        .env("GIT_SEQUENCE_EDITOR", "true")
        .env("GIT_AUTHOR_NAME", FIXTURE_NAME)
        .env("GIT_AUTHOR_EMAIL", FIXTURE_EMAIL)
        .env("GIT_AUTHOR_DATE", &pinned_date)
        .env("GIT_COMMITTER_NAME", FIXTURE_NAME)
        .env("GIT_COMMITTER_EMAIL", FIXTURE_EMAIL)
        .env("GIT_COMMITTER_DATE", &pinned_date)
        .args(args)
        .output()
        .expect("Failed to run git")
}

/// Starts the watch server on a background thread. Returns the `JoinHandle`.
/// Adds a linked worktree of the superproject at `super_root` (under
/// `temp_dir`) and checks out its submodules, whose gitdirs land under
/// `<super>/.git/worktrees/<name>/modules/`. Returns the canonicalized worktree
/// path (matching how the CLI resolves project paths).
fn setup_worktree(
    temp_dir: &Path,
    super_root: &Path,
    submodule_names: &[String],
    init_submodules: bool,
) -> PathBuf {
    let wt_path = temp_dir.join("worktree");
    Repo::new(super_root).run_git(&[
        "worktree",
        "add",
        "-q",
        wt_path.to_str().expect("worktree path not UTF-8"),
        "HEAD",
    ]);
    if init_submodules && !submodule_names.is_empty() {
        // Local-path submodule URLs need the file-protocol opt-in on modern git.
        Repo::new(&wt_path).run_git(&[
            "-c",
            "protocol.file.allow=always",
            "submodule",
            "update",
            "--init",
            "-q",
        ]);
    }
    dunce::canonicalize(&wt_path).expect("canonicalize worktree path")
}

fn start_watch_server(root_path: &Path) -> JoinHandle<()> {
    let path = root_path.to_path_buf();
    std::thread::Builder::new()
        .name("test_watch_server".to_string())
        .spawn(move || {
            // In a `trace_events` build, capture this server's events into a
            // per-test buffer keyed by repo root; the harness drains it on
            // teardown (printing only if the test failed). No-op otherwise.
            #[cfg(trace_events)]
            subspy::connection::watch_server::trace::capture_for(&path);
            if let Err(e) = watch(&path, false) {
                eprintln!("Watch server exited: {e}");
            }
        })
        .expect("Failed to spawn watch server thread")
}
