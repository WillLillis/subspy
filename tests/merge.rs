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
    harness.root().run_git(&["checkout", "-b", "feature"]);
    harness.root().write("feature.txt", "feature work\n");
    harness.root().run_git(&["add", "feature.txt"]);
    harness.root().run_git(&["commit", "-m", "feature commit"]);

    harness.root().run_git(&["checkout", "master"]);
    harness.root().write("master.txt", "master work\n");
    harness.root().run_git(&["add", "master.txt"]);
    harness.root().run_git(&["commit", "-m", "master commit"]);

    harness.start_server();
    harness.assert_all_clean();

    // Merge feature into master, no conflict
    harness
        .root()
        .run_git(&["merge", "feature", "-m", "merge feature"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn root_merge_with_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create conflicting history on the same file
    harness.root().run_git(&["checkout", "-b", "feature"]);
    harness.root().write("conflict.txt", "feature version\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness.root().run_git(&["commit", "-m", "feature commit"]);

    harness.root().run_git(&["checkout", "master"]);
    harness.root().write("conflict.txt", "master version\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness.root().run_git(&["commit", "-m", "master commit"]);

    harness.start_server();
    harness.assert_all_clean();

    // Merge, conflict expected
    let output = harness.root().try_git(&["merge", "feature"]);
    assert!(
        !output.status.success(),
        "Expected merge to fail with conflict"
    );

    // Resolve and commit
    harness.root().write("conflict.txt", "resolved\n");
    harness.root().run_git(&["add", "conflict.txt"]);
    harness
        .root()
        .run_git(&["commit", "-m", "resolve merge conflict"]);

    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn submodule_merge_without_conflict(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create divergent history inside the submodule on different files
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

    harness.submodule("sub_a").run_git(&["checkout", "master"]);
    harness
        .submodule("sub_a")
        .write("master.txt", "master work\n");
    harness.submodule("sub_a").run_git(&["add", "-A"]);
    harness
        .submodule("sub_a")
        .run_git(&["commit", "-m", "master commit"]);

    harness.start_server();
    // Submodule HEAD already diverges from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Merge feature into master inside the submodule, no conflict
    harness
        .submodule("sub_a")
        .run_git(&["merge", "feature", "-m", "merge feature"]);

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

    harness.submodule("sub_a").run_git(&["checkout", "master"]);

    harness.start_server();
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Merge, conflict expected
    let output = harness.submodule("sub_a").try_git(&["merge", "feature"]);
    assert!(
        !output.status.success(),
        "Expected merge to fail with conflict"
    );

    // Resolve and commit
    harness
        .submodule("sub_a")
        .write("conflict.txt", "resolved\n");
    harness.submodule("sub_a").run_git(&["add", "conflict.txt"]);
    harness
        .submodule("sub_a")
        .run_git(&["commit", "-m", "resolve merge conflict"]);

    // Still NEW_COMMITS-> submodule HEAD diverged from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}
