mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn root_cherry_pick_without_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create a commit on a feature branch that touches a different file
    harness.root().run_git(&["checkout", "-b", "feature"]);
    harness.root().write("feature.txt", "feature work\n");
    harness.root().run_git(&["add", "feature.txt"]);
    harness.root().run_git(&["commit", "-m", "feature commit"]);

    // Switch back to master
    harness.root().run_git(&["checkout", "master"]);

    harness.start_server();
    harness.assert_all_clean();

    // Cherry-pick the feature commit-> no conflict
    harness.root().run_git(&["cherry-pick", "feature"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn root_cherry_pick_with_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create conflicting commits on master and feature for the same file
    harness.root().write("conflict.txt", "master version\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness.root().run_git(&["commit", "-m", "master commit"]);

    harness
        .root()
        .run_git(&["checkout", "-b", "feature", "HEAD~1"]);
    harness.root().write("conflict.txt", "feature version\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness.root().run_git(&["commit", "-m", "feature commit"]);

    // Back to master
    harness.root().run_git(&["checkout", "master"]);

    harness.start_server();
    harness.assert_all_clean();

    // Cherry-pick-> conflict expected
    let output = harness.root().try_git(&["cherry-pick", "feature"]);
    assert!(
        !output.status.success(),
        "Expected cherry-pick to fail with conflict"
    );

    // Resolve and continue
    harness.root().write("conflict.txt", "resolved\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness.root().run_git(&["cherry-pick", "--continue"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn submodule_cherry_pick_without_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create a commit on a feature branch inside the submodule
    harness
        .submodule("sub_a")
        .run_git(&["checkout", "-b", "feature"]);
    harness
        .submodule("sub_a")
        .write("feature.txt", "feature work\n");
    harness.submodule("sub_a").run_git(&["add", "-A"]);
    harness
        .submodule("sub_a")
        .run_git(&["commit", "-m", "feature commit"]);

    // Back to master in the submodule
    harness.submodule("sub_a").run_git(&["checkout", "master"]);

    harness.start_server();
    harness.assert_all_clean();

    // Cherry-pick the feature commit-> no conflict
    harness
        .submodule("sub_a")
        .run_git(&["cherry-pick", "feature"]);

    // Submodule HEAD now differs from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn submodule_cherry_pick_with_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create conflicting commits in the submodule
    harness
        .submodule("sub_a")
        .write("conflict.txt", "master version\n");
    harness.submodule("sub_a").run_git(&["add", "-A"]);
    harness
        .submodule("sub_a")
        .run_git(&["commit", "-m", "master commit"]);

    harness
        .submodule("sub_a")
        .run_git(&["checkout", "-b", "feature", "HEAD~1"]);
    harness
        .submodule("sub_a")
        .write("conflict.txt", "feature version\n");
    harness.submodule("sub_a").run_git(&["add", "-A"]);
    harness
        .submodule("sub_a")
        .run_git(&["commit", "-m", "feature commit"]);

    // Back to master in the submodule
    harness.submodule("sub_a").run_git(&["checkout", "master"]);

    harness.start_server();
    // Submodule already has NEW_COMMITS from the master commit above
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Cherry-pick-> conflict expected
    let output = harness
        .submodule("sub_a")
        .try_git(&["cherry-pick", "feature"]);
    assert!(
        !output.status.success(),
        "Expected cherry-pick to fail with conflict"
    );

    // Resolve and continue
    harness
        .submodule("sub_a")
        .write("conflict.txt", "resolved\n");
    harness.submodule("sub_a").run_git(&["add", "conflict.txt"]);
    harness
        .submodule("sub_a")
        .run_git(&["cherry-pick", "--continue"]);

    // Still NEW_COMMITS-> submodule HEAD diverged from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}
