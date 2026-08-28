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
    harness.root().run_git(&["checkout", "-b", "feature"]);
    harness.root().write("feature.txt", "feature work\n");
    harness.root().run_git(&["add", "feature.txt"]);
    harness.root().run_git(&["commit", "-m", "feature commit"]);

    harness.root().run_git(&["checkout", "master"]);
    harness.root().write("master.txt", "master work\n");
    harness.root().run_git(&["add", "master.txt"]);
    harness.root().run_git(&["commit", "-m", "master commit"]);

    harness.root().run_git(&["checkout", "feature"]);

    harness.start_server();
    harness.assert_all_clean();

    // Rebase feature onto master, no conflict, should complete cleanly
    harness.root().run_git(&["rebase", "master"]);

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
    harness.root().run_git(&["checkout", "-b", "feature"]);
    harness.root().write("conflict.txt", "feature version\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness.root().run_git(&["commit", "-m", "feature commit"]);

    harness.root().run_git(&["checkout", "master"]);
    harness.root().write("conflict.txt", "master version\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness.root().run_git(&["commit", "-m", "master commit"]);

    harness.root().run_git(&["checkout", "feature"]);

    harness.start_server();
    harness.assert_all_clean();

    // Rebase-> this will hit a conflict
    let output = harness.root().try_git(&["rebase", "master"]);
    assert!(
        !output.status.success(),
        "Expected rebase to fail with conflict"
    );

    // Resolve the conflict by overwriting the file and continuing
    harness.root().write("conflict.txt", "resolved\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness.root().run_git(&["rebase", "--continue"]);

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
    harness
        .submodule("sub_a")
        .write("local.txt", "local work\n");
    harness.submodule("sub_a").run_git(&["add", "-A"]);
    harness
        .submodule("sub_a")
        .run_git(&["commit", "-m", "local commit"]);

    // 3. Fetch from the source repo so we have the upstream commit locally
    harness.submodule("sub_a").run_git(&["fetch", "origin"]);

    harness.start_server();
    // Submodule HEAD differs from parent index (local commit)
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Rebase local work onto origin/master, no conflict
    harness
        .submodule("sub_a")
        .run_git(&["rebase", "origin/master"]);

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

    harness
        .submodule("sub_a")
        .write("conflict.txt", "local version\n");
    harness.submodule("sub_a").run_git(&["add", "-A"]);
    harness
        .submodule("sub_a")
        .run_git(&["commit", "-m", "local commit"]);

    harness.submodule("sub_a").run_git(&["fetch", "origin"]);

    harness.start_server();
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Rebase-> conflict expected
    let output = harness
        .submodule("sub_a")
        .try_git(&["rebase", "origin/master"]);
    assert!(
        !output.status.success(),
        "Expected rebase to fail with conflict"
    );

    // Resolve and continue
    harness
        .submodule("sub_a")
        .write("conflict.txt", "resolved\n");
    harness.submodule("sub_a").run_git(&["add", "conflict.txt"]);
    harness
        .submodule("sub_a")
        .run_git(&["rebase", "--continue"]);

    // Still NEW_COMMITS because submodule HEAD diverged from parent index
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

// A root index update during a paused rebase must refresh cached
// submodule status.
#[apply(common::repeat)]
fn root_rebase_paused_status_updates_after_add(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Advance sub_a's source so feature can bump the gitlink to it.
    harness.commit_in_source_repo("sub_a", "README.md", "advanced\n", "advance sub_a");
    harness.submodule("sub_a").run_git(&["fetch", "origin"]);
    let advanced_oid = String::from_utf8(
        harness
            .submodule("sub_a")
            .try_git(&["rev-parse", "origin/master"])
            .stdout,
    )
    .unwrap()
    .trim()
    .to_string();

    // feature: bumps sub_a's gitlink + introduces a file that will conflict
    // with master.
    harness.root().run_git(&["checkout", "-b", "feature"]);
    harness
        .submodule("sub_a")
        .run_git(&["checkout", "-q", &advanced_oid]);
    harness.root().run_git(&["add", "sub_a"]);
    harness.root().write("conflict.txt", "feature version\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness
        .root()
        .run_git(&["commit", "-m", "bump sub + add conflict.txt"]);

    // Restore sub_a to master's gitlink.
    harness.root().run_git(&["checkout", "master"]);
    harness
        .root()
        .run_git(&["submodule", "update", "--init", "sub_a"]);
    harness.root().write("conflict.txt", "master version\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness
        .root()
        .run_git(&["commit", "-m", "master conflict.txt"]);

    harness.root().run_git(&["checkout", "feature"]);
    harness
        .root()
        .run_git(&["submodule", "update", "--init", "sub_a"]);

    harness.start_server();
    harness.assert_all_clean();

    // Rebase pauses on conflict.txt. The submodule gitlink change from
    // feature is already applied to the index.
    let output = harness.root().try_git(&["rebase", "master"]);
    assert!(
        !output.status.success(),
        "Expected rebase to pause on conflict"
    );

    // Staging the resolution updates the root index and must refresh the
    // cached submodule status.
    harness.root().write("conflict.txt", "resolved\n");
    harness.root().run_git(&["add", "conflict.txt"]);

    // The server should see post-add state: sub_a has a staged gitlink
    // change (INDEX != HEAD).
    harness.assert_submodule_status("sub_a", StatusSummary::STAGED);

    harness.root().run_git(&["rebase", "--continue"]);

    harness.assert_all_clean();
}

// Exercise watcher churn across a multi-commit root rebase.
#[apply(common::repeat)]
fn root_rebase_many_commits_completes(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .no_server()
        .build();

    harness.root().run_git(&["checkout", "-b", "feature"]);
    for i in 1..=20 {
        harness.root().write(&format!("file_{i}.txt"), "feature\n");
        harness.root().run_git(&["add", &format!("file_{i}.txt")]);
        harness
            .root()
            .run_git(&["commit", "-m", &format!("feature commit {i}")]);
    }

    harness.root().run_git(&["checkout", "master"]);
    harness.root().write("master_only.txt", "master\n");
    harness.root().run_git(&["add", "master_only.txt"]);
    harness.root().run_git(&["commit", "-m", "master commit"]);

    harness.root().run_git(&["checkout", "feature"]);

    harness.start_server();
    harness.assert_all_clean();

    let output = harness.root().try_git(&["rebase", "master"]);
    assert!(
        output.status.success(),
        "Expected 20-commit rebase to succeed (server should not block git)"
    );

    harness.assert_all_clean();
}
