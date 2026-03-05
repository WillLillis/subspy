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
    harness.git_in_root(&["checkout", "-b", "feature"]);
    harness.write_root_file("feature.txt", "feature work\n");
    harness.git_in_root(&["add", "feature.txt"]);
    harness.git_in_root(&["commit", "-m", "feature commit"]);

    // Switch back to master
    harness.git_in_root(&["checkout", "master"]);

    harness.start_server();
    harness.assert_all_clean();

    // Cherry-pick the feature commit-> no conflict
    harness.git_in_root(&["cherry-pick", "feature"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn root_cherry_pick_with_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create conflicting commits on master and feature for the same file
    harness.write_root_file("conflict.txt", "master version\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["commit", "-m", "master commit"]);

    harness.git_in_root(&["checkout", "-b", "feature", "HEAD~1"]);
    harness.write_root_file("conflict.txt", "feature version\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["commit", "-m", "feature commit"]);

    // Back to master
    harness.git_in_root(&["checkout", "master"]);

    harness.start_server();
    harness.assert_all_clean();

    // Cherry-pick-> conflict expected
    let output = harness.git_in_root_may_fail(&["cherry-pick", "feature"]);
    assert!(
        !output.status.success(),
        "Expected cherry-pick to fail with conflict"
    );

    // Resolve and continue
    harness.write_root_file("conflict.txt", "resolved\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["cherry-pick", "--continue"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn submodule_cherry_pick_without_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create a commit on a feature branch inside the submodule
    harness.git_in_submodule("sub_a", &["checkout", "-b", "feature"]);
    harness.write_file("sub_a", "feature.txt", "feature work\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "feature commit"]);

    // Back to master in the submodule
    harness.git_in_submodule("sub_a", &["checkout", "master"]);

    harness.start_server();
    harness.assert_all_clean();

    // Cherry-pick the feature commit-> no conflict
    harness.git_in_submodule("sub_a", &["cherry-pick", "feature"]);

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
    harness.write_file("sub_a", "conflict.txt", "master version\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "master commit"]);

    harness.git_in_submodule("sub_a", &["checkout", "-b", "feature", "HEAD~1"]);
    harness.write_file("sub_a", "conflict.txt", "feature version\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "feature commit"]);

    // Back to master in the submodule
    harness.git_in_submodule("sub_a", &["checkout", "master"]);

    harness.start_server();
    // Submodule already has NEW_COMMITS from the master commit above
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Cherry-pick-> conflict expected
    let output = harness.git_in_submodule_may_fail("sub_a", &["cherry-pick", "feature"]);
    assert!(
        !output.status.success(),
        "Expected cherry-pick to fail with conflict"
    );

    // Resolve and continue
    harness.write_file("sub_a", "conflict.txt", "resolved\n");
    harness.git_in_submodule("sub_a", &["add", "conflict.txt"]);
    harness.git_in_submodule("sub_a", &["cherry-pick", "--continue"]);

    // Still NEW_COMMITS-> submodule HEAD diverged from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}
