mod common;

use std::path::Path;

use common::{TestRepo, WatchServerHandle};
use git2::{Repository, Signature};
use subspy::{StatusSummary, connection::client::request_status};

/// Helper to find a submodule's status in the result vec.
fn find_status(statuses: &[(String, StatusSummary)], name: &str) -> Option<StatusSummary> {
    statuses
        .iter()
        .find(|(path, _)| path == name)
        .map(|(_, st)| *st)
}

#[test]
fn all_clean_submodules_returns_empty() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");
    repo.add_submodule("sub2");
    repo.add_submodule("sub3");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    let statuses = request_status(repo.path()).expect("request_status should succeed");
    assert!(
        statuses.is_empty(),
        "All clean submodules should yield empty status, got: {statuses:?}"
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn modified_content_detected() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    // Modify a tracked file in the submodule
    let file = repo.submodule_path("sub1").join("file.txt");
    std::fs::write(&file, "modified content\n").unwrap();

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    let statuses = request_status(repo.path()).expect("request_status should succeed");
    let status = find_status(&statuses, "sub1").expect("sub1 should appear in statuses");
    assert!(
        status.contains(StatusSummary::MODIFIED_CONTENT),
        "Expected MODIFIED_CONTENT flag, got: {status:?}"
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn untracked_content_detected() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    // Add an untracked file to the submodule
    let file = repo.submodule_path("sub1").join("untracked.txt");
    std::fs::write(&file, "untracked\n").unwrap();

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    let statuses = request_status(repo.path()).expect("request_status should succeed");
    let status = find_status(&statuses, "sub1").expect("sub1 should appear in statuses");
    assert!(
        status.contains(StatusSummary::UNTRACKED_CONTENT),
        "Expected UNTRACKED_CONTENT flag, got: {status:?}"
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn new_commits_detected() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    // Make a new commit inside the submodule (advancing HEAD beyond what the parent tracks)
    let sub_repo = Repository::open(repo.submodule_path("sub1")).unwrap();
    let file = repo.submodule_path("sub1").join("file.txt");
    std::fs::write(&file, "new content\n").unwrap();
    let mut index = sub_repo.index().unwrap();
    index.add_path(Path::new("file.txt")).unwrap();
    index.write().unwrap();
    let tree_id = index.write_tree().unwrap();
    let tree = sub_repo.find_tree(tree_id).unwrap();
    let sig = Signature::now("test", "test@test.com").unwrap();
    let head = sub_repo.head().unwrap().peel_to_commit().unwrap();
    sub_repo
        .commit(Some("HEAD"), &sig, &sig, "Advance HEAD", &tree, &[&head])
        .unwrap();

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    let statuses = request_status(repo.path()).expect("request_status should succeed");
    let status = find_status(&statuses, "sub1").expect("sub1 should appear in statuses");
    assert!(
        status.contains(StatusSummary::NEW_COMMITS),
        "Expected NEW_COMMITS flag, got: {status:?}"
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn staged_submodule_detected() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    // Make a commit in the submodule
    let sub_repo = Repository::open(repo.submodule_path("sub1")).unwrap();
    let file = repo.submodule_path("sub1").join("file.txt");
    std::fs::write(&file, "staged content\n").unwrap();
    let mut sub_index = sub_repo.index().unwrap();
    sub_index.add_path(Path::new("file.txt")).unwrap();
    sub_index.write().unwrap();
    let tree_id = sub_index.write_tree().unwrap();
    let tree = sub_repo.find_tree(tree_id).unwrap();
    let sig = Signature::now("test", "test@test.com").unwrap();
    let head = sub_repo.head().unwrap().peel_to_commit().unwrap();
    sub_repo
        .commit(Some("HEAD"), &sig, &sig, "Sub commit", &tree, &[&head])
        .unwrap();

    // Stage the submodule in the parent repo (git add sub1)
    let parent_repo = repo.repo();
    let mut parent_index = parent_repo.index().unwrap();
    parent_index.add_path(Path::new("sub1")).unwrap();
    parent_index.write().unwrap();

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    let statuses = request_status(repo.path()).expect("request_status should succeed");
    let status = find_status(&statuses, "sub1").expect("sub1 should appear in statuses");
    assert!(
        status.contains(StatusSummary::STAGED),
        "Expected STAGED flag, got: {status:?}"
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn multiple_flags_combined() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    // Make a new commit (NEW_COMMITS) and add an untracked file (UNTRACKED_CONTENT)
    let sub_repo = Repository::open(repo.submodule_path("sub1")).unwrap();
    let file = repo.submodule_path("sub1").join("file.txt");
    std::fs::write(&file, "changed\n").unwrap();
    let mut index = sub_repo.index().unwrap();
    index.add_path(Path::new("file.txt")).unwrap();
    index.write().unwrap();
    let tree_id = index.write_tree().unwrap();
    let tree = sub_repo.find_tree(tree_id).unwrap();
    let sig = Signature::now("test", "test@test.com").unwrap();
    let head = sub_repo.head().unwrap().peel_to_commit().unwrap();
    sub_repo
        .commit(Some("HEAD"), &sig, &sig, "New commit", &tree, &[&head])
        .unwrap();

    let untracked = repo.submodule_path("sub1").join("extra.txt");
    std::fs::write(&untracked, "extra\n").unwrap();

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    let statuses = request_status(repo.path()).expect("request_status should succeed");
    let status = find_status(&statuses, "sub1").expect("sub1 should appear in statuses");
    assert!(
        status.contains(StatusSummary::NEW_COMMITS),
        "Expected NEW_COMMITS flag, got: {status:?}"
    );
    assert!(
        status.contains(StatusSummary::UNTRACKED_CONTENT),
        "Expected UNTRACKED_CONTENT flag, got: {status:?}"
    );

    server.shutdown().expect("Shutdown should succeed");
}

#[test]
fn many_submodules_all_indexed() {
    let mut repo = TestRepo::new();

    // Create 10 submodules
    for i in 0..10 {
        repo.add_submodule(&format!("sub{i}"));
    }

    // Make sub0 have MODIFIED_CONTENT
    std::fs::write(
        repo.submodule_path("sub0").join("file.txt"),
        "modified\n",
    )
    .unwrap();

    // Make sub1 have UNTRACKED_CONTENT
    std::fs::write(
        repo.submodule_path("sub1").join("new_file.txt"),
        "untracked\n",
    )
    .unwrap();

    // Make sub2 have NEW_COMMITS
    {
        let sub_repo = Repository::open(repo.submodule_path("sub2")).unwrap();
        let file = repo.submodule_path("sub2").join("file.txt");
        std::fs::write(&file, "commit\n").unwrap();
        let mut index = sub_repo.index().unwrap();
        index.add_path(Path::new("file.txt")).unwrap();
        index.write().unwrap();
        let tree_id = index.write_tree().unwrap();
        let tree = sub_repo.find_tree(tree_id).unwrap();
        let sig = Signature::now("test", "test@test.com").unwrap();
        let head = sub_repo.head().unwrap().peel_to_commit().unwrap();
        sub_repo
            .commit(Some("HEAD"), &sig, &sig, "Advance", &tree, &[&head])
            .unwrap();
    }

    // sub3..sub9 remain clean

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    let statuses = request_status(repo.path()).expect("request_status should succeed");

    // sub0: MODIFIED_CONTENT
    let s0 = find_status(&statuses, "sub0").expect("sub0 should be dirty");
    assert!(
        s0.contains(StatusSummary::MODIFIED_CONTENT),
        "sub0: expected MODIFIED_CONTENT, got {s0:?}"
    );

    // sub1: UNTRACKED_CONTENT
    let s1 = find_status(&statuses, "sub1").expect("sub1 should be dirty");
    assert!(
        s1.contains(StatusSummary::UNTRACKED_CONTENT),
        "sub1: expected UNTRACKED_CONTENT, got {s1:?}"
    );

    // sub2: NEW_COMMITS
    let s2 = find_status(&statuses, "sub2").expect("sub2 should be dirty");
    assert!(
        s2.contains(StatusSummary::NEW_COMMITS),
        "sub2: expected NEW_COMMITS, got {s2:?}"
    );

    // sub3..sub9 should not appear (they're clean)
    for i in 3..10 {
        let name = format!("sub{i}");
        assert!(
            find_status(&statuses, &name).is_none(),
            "{name} should be clean and not in results"
        );
    }

    server.shutdown().expect("Shutdown should succeed");
}
