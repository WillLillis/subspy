mod common;

use std::time::Duration;

use common::{TestRepo, WatchServerHandle, poll_until};
use subspy::{StatusSummary, connection::client::{request_reindex, request_status}};

/// Helper to find a submodule's status in the result vec.
fn find_status(statuses: &[(String, StatusSummary)], name: &str) -> Option<StatusSummary> {
    statuses
        .iter()
        .find(|(path, _)| path == name)
        .map(|(_, st)| *st)
}

#[test]
fn reindex_reflects_changes() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    // Initially clean
    let statuses = request_status(repo.path()).unwrap();
    assert!(statuses.is_empty(), "Should start clean");

    // Modify a tracked file
    std::fs::write(repo.submodule_path("sub1").join("file.txt"), "changed\n").unwrap();

    // Reindex — this blocks until the server finishes reindexing
    request_reindex(repo.path()).expect("Reindex should succeed");

    // Poll for the updated status since the status map update and the next
    // status request can race
    let path = repo.path().to_path_buf();
    poll_until(
        Duration::from_secs(5),
        Duration::from_millis(100),
        || {
            let Ok(statuses) = request_status(&path) else {
                return false;
            };
            find_status(&statuses, "sub1")
                .is_some_and(|s| s.contains(StatusSummary::MODIFIED_CONTENT))
        },
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn reindex_picks_up_new_submodule() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    // Initially only sub1
    let statuses = request_status(repo.path()).unwrap();
    assert!(statuses.is_empty(), "Should start clean");

    // Add a second submodule
    repo.add_submodule("sub2");

    // Modify sub2 so it shows up as dirty
    std::fs::write(repo.submodule_path("sub2").join("file.txt"), "dirty\n").unwrap();

    // Reindex to pick up the new submodule
    request_reindex(repo.path()).expect("Reindex should succeed");

    // Poll for the updated status
    let path = repo.path().to_path_buf();
    poll_until(
        Duration::from_secs(5),
        Duration::from_millis(100),
        || {
            let Ok(statuses) = request_status(&path) else {
                return false;
            };
            find_status(&statuses, "sub2")
                .is_some_and(|s| s.contains(StatusSummary::MODIFIED_CONTENT))
        },
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn submodule_file_change_detected_by_watcher() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    // Initially clean
    let statuses = request_status(repo.path()).unwrap();
    assert!(statuses.is_empty(), "Should start clean");

    // Modify a tracked file — the watcher should pick it up
    std::fs::write(repo.submodule_path("sub1").join("file.txt"), "watcher test\n").unwrap();

    let path = repo.path().to_path_buf();
    poll_until(
        Duration::from_secs(10),
        Duration::from_millis(200),
        || {
            let Ok(statuses) = request_status(&path) else {
                return false;
            };
            find_status(&statuses, "sub1")
                .is_some_and(|s| s.contains(StatusSummary::MODIFIED_CONTENT))
        },
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn untracked_file_creation_detected() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    // Initially clean
    let statuses = request_status(repo.path()).unwrap();
    assert!(statuses.is_empty(), "Should start clean");

    // Create an untracked file
    std::fs::write(
        repo.submodule_path("sub1").join("untracked_new.txt"),
        "hello\n",
    )
    .unwrap();

    let path = repo.path().to_path_buf();
    poll_until(
        Duration::from_secs(10),
        Duration::from_millis(200),
        || {
            let Ok(statuses) = request_status(&path) else {
                return false;
            };
            find_status(&statuses, "sub1")
                .is_some_and(|s| s.contains(StatusSummary::UNTRACKED_CONTENT))
        },
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn file_deletion_detected() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    // Initially clean
    let statuses = request_status(repo.path()).unwrap();
    assert!(statuses.is_empty(), "Should start clean");

    // Delete the tracked file
    std::fs::remove_file(repo.submodule_path("sub1").join("file.txt")).unwrap();

    let path = repo.path().to_path_buf();
    poll_until(
        Duration::from_secs(10),
        Duration::from_millis(200),
        || {
            let Ok(statuses) = request_status(&path) else {
                return false;
            };
            find_status(&statuses, "sub1")
                .is_some_and(|s| s.contains(StatusSummary::MODIFIED_CONTENT))
        },
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn gitmodules_change_triggers_reindex() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    // Add a second submodule (this modifies .gitmodules, triggering the
    // watcher to reindex)
    repo.add_submodule("sub2");

    // Make sub2 dirty so it appears in results
    std::fs::write(repo.submodule_path("sub2").join("file.txt"), "dirty\n").unwrap();

    let path = repo.path().to_path_buf();
    poll_until(
        Duration::from_secs(10),
        Duration::from_millis(200),
        || {
            let Ok(statuses) = request_status(&path) else {
                return false;
            };
            // sub2 should eventually appear after the watcher-triggered reindex
            find_status(&statuses, "sub2").is_some()
        },
    );

    server.shutdown().expect("Shutdown should succeed");
}
