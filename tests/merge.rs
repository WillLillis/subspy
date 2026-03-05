mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn root_merge_without_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create divergent history on different files
    harness.git_in_root(&["checkout", "-b", "feature"]);
    harness.write_root_file("feature.txt", "feature work\n");
    harness.git_in_root(&["add", "feature.txt"]);
    harness.git_in_root(&["commit", "-m", "feature commit"]);

    harness.git_in_root(&["checkout", "master"]);
    harness.write_root_file("master.txt", "master work\n");
    harness.git_in_root(&["add", "master.txt"]);
    harness.git_in_root(&["commit", "-m", "master commit"]);

    harness.start_server();
    harness.assert_all_clean();

    // Merge feature into master, no conflict
    harness.git_in_root(&["merge", "feature", "-m", "merge feature"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn root_merge_with_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create conflicting history on the same file
    harness.git_in_root(&["checkout", "-b", "feature"]);
    harness.write_root_file("conflict.txt", "feature version\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["commit", "-m", "feature commit"]);

    harness.git_in_root(&["checkout", "master"]);
    harness.write_root_file("conflict.txt", "master version\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["commit", "-m", "master commit"]);

    harness.start_server();
    harness.assert_all_clean();

    // Merge, conflict expected
    let output = harness.git_in_root_may_fail(&["merge", "feature"]);
    assert!(
        !output.status.success(),
        "Expected merge to fail with conflict"
    );

    // Resolve and commit
    harness.write_root_file("conflict.txt", "resolved\n");
    harness.git_in_root(&["add", "conflict.txt"]);
    harness.git_in_root(&["commit", "-m", "resolve merge conflict"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn submodule_merge_without_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create divergent history inside the submodule on different files
    harness.git_in_submodule("sub_a", &["checkout", "-b", "feature"]);
    harness.write_file("sub_a", "feature.txt", "feature work\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "feature commit"]);

    harness.git_in_submodule("sub_a", &["checkout", "master"]);
    harness.write_file("sub_a", "master.txt", "master work\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "master commit"]);

    harness.start_server();
    // Submodule HEAD already diverges from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Merge feature into master inside the submodule, no conflict
    harness.git_in_submodule("sub_a", &["merge", "feature", "-m", "merge feature"]);

    // Still NEW_COMMITS-> submodule HEAD diverges from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn submodule_merge_with_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create conflicting history inside the submodule on the same file
    harness.write_file("sub_a", "conflict.txt", "master version\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "master commit"]);

    harness.git_in_submodule("sub_a", &["checkout", "-b", "feature", "HEAD~1"]);
    harness.write_file("sub_a", "conflict.txt", "feature version\n");
    harness.git_in_submodule("sub_a", &["add", "-A"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "feature commit"]);

    harness.git_in_submodule("sub_a", &["checkout", "master"]);

    harness.start_server();
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Merge, conflict expected
    let output = harness.git_in_submodule_may_fail("sub_a", &["merge", "feature"]);
    assert!(
        !output.status.success(),
        "Expected merge to fail with conflict"
    );

    // Resolve and commit
    harness.write_file("sub_a", "conflict.txt", "resolved\n");
    harness.git_in_submodule("sub_a", &["add", "conflict.txt"]);
    harness.git_in_submodule("sub_a", &["commit", "-m", "resolve merge conflict"]);

    // Still NEW_COMMITS-> submodule HEAD diverged from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}
