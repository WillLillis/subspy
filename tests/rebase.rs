mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn root_rebase_without_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create divergent history: commit on `feature`, commit on `master`,
    // then checkout `feature` so we can rebase onto `master`.
    harness.git_in_root(&["checkout", "-b", "feature"]);
    harness.write_root_file("feature.txt", "feature work\n");
    harness.git_in_root(&["add", "feature.txt"]);
    harness.git_in_root(&["commit", "-m", "feature commit"]);

    harness.git_in_root(&["checkout", "master"]);
    harness.write_root_file("master.txt", "master work\n");
    harness.git_in_root(&["add", "master.txt"]);
    harness.git_in_root(&["commit", "-m", "master commit"]);

    harness.git_in_root(&["checkout", "feature"]);

    harness.start_server();
    harness.assert_all_clean();

    // Rebase feature onto master, no conflict, should complete cleanly
    harness.git_in_root(&["rebase", "master"]);

    // Server detects rebase start/end, reindexes, everything stays clean
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn root_rebase_with_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create conflicting history: same file modified on both branches
    harness.git_in_root(&["checkout", "-b", "feature"]);
    harness.write_root_file("conflict.txt", "feature version\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["commit", "-m", "feature commit"]);

    harness.git_in_root(&["checkout", "master"]);
    harness.write_root_file("conflict.txt", "master version\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["commit", "-m", "master commit"]);

    harness.git_in_root(&["checkout", "feature"]);

    harness.start_server();
    harness.assert_all_clean();

    // Rebase-> this will hit a conflict
    let output = harness.git_in_root_may_fail(&["rebase", "master"]);
    assert!(
        !output.status.success(),
        "Expected rebase to fail with conflict"
    );

    // Resolve the conflict by overwriting the file and continuing
    harness.write_root_file("conflict.txt", "resolved\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["rebase", "--continue"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn submodule_rebase_without_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create divergent history:
    // 1. Commit in the source (upstream) repo
    harness.commit_in_source_repo(
        "sub_a",
        "upstream.txt",
        "upstream work\n",
        "upstream commit",
    );

    // 2. Make a local commit in the submodule workdir
    harness.write_file("sub_a", "local.txt", "local work\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "local commit"]);

    // 3. Fetch from the source repo so we have the upstream commit locally
    harness.git_in_submodule("sub_a", &["fetch", "origin"]);

    harness.start_server();
    // Submodule HEAD differs from parent index (local commit)
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Rebase local work onto origin/master, no conflict
    harness.git_in_submodule("sub_a", &["rebase", "origin/master"]);

    // Still NEW_COMMITS: submodule HEAD is ahead of the gitlink in parent index
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn submodule_rebase_with_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create conflicting history on the same file
    harness.commit_in_source_repo(
        "sub_a",
        "conflict.txt",
        "upstream version\n",
        "upstream commit",
    );

    harness.write_file("sub_a", "conflict.txt", "local version\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "local commit"]);

    harness.git_in_submodule("sub_a", &["fetch", "origin"]);

    harness.start_server();
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Rebase-> conflict expected
    let output = harness.git_in_submodule_may_fail("sub_a", &["rebase", "origin/master"]);
    assert!(
        !output.status.success(),
        "Expected rebase to fail with conflict"
    );

    // Resolve and continue
    harness.write_file("sub_a", "conflict.txt", "resolved\n");
    harness.git_in_submodule("sub_a", &["add", "conflict.txt"]);
    harness.git_in_submodule("sub_a", &["rebase", "--continue"]);

    // Still NEW_COMMITS because submodule HEAD diverged from parent index
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

// ---------------------------------------------------------------------------
// skip_set clearing during reindex
//
// When a submodule is rebasing, the server adds it to `skip_set` to suppress
// event processing (avoiding `index.lock` contention). A client-requested
// reindex with `replace_watchers=false` must still clear and rebuild
// `skip_set` from the current filesystem state. Without this, a submodule
// that was rebasing at the time of the reindex would stay in `skip_set`
// permanently, and its status would never update again.
// ---------------------------------------------------------------------------

#[apply(common::repeat)]
fn reindex_during_submodule_rebase_clears_skip_set(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .no_server()
        .build();

    // Create conflicting history in sub_a so the rebase pauses
    harness.commit_in_source_repo(
        "sub_a",
        "conflict.txt",
        "upstream version\n",
        "upstream commit",
    );

    harness.write_file("sub_a", "conflict.txt", "local version\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "local commit"]);
    harness.git_in_submodule("sub_a", &["fetch", "origin"]);

    harness.start_server();
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Start a rebase that will conflict, pausing mid-rebase.
    // The server adds sub_a to skip_set.
    let output = harness.git_in_submodule_may_fail("sub_a", &["rebase", "origin/master"]);
    assert!(
        !output.status.success(),
        "Expected rebase to fail with conflict"
    );

    // Trigger a non-watcher-replacing reindex while sub_a is mid-rebase.
    // This must clear and rebuild skip_set; sub_a should be re-added
    // because the rebase marker still exists on disk.
    harness.request_reindex(false);

    // Resolve the conflict and finish the rebase. The server must detect
    // the rebase-end event and remove sub_a from skip_set.
    harness.write_file("sub_a", "conflict.txt", "resolved\n");
    harness.git_in_submodule("sub_a", &["add", "conflict.txt"]);
    harness.git_in_submodule("sub_a", &["rebase", "--continue"]);

    // sub_a status should update (not stuck in skip_set)
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // sub_b should still be independently trackable
    harness.write_file("sub_b", "new.txt", "hello\n");
    harness.assert_submodule_status("sub_b", StatusSummary::UNTRACKED_CONTENT);
}
