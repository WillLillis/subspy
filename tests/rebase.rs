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
