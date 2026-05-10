mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn checkout_branch_with_different_submodule_commits(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // On master, sub_a is at its initial commit. Create a feature branch
    // where sub_a points to a newer commit.
    harness.root().run_git(&["checkout", "-b", "feature"]);

    harness
        .submodule("sub_a")
        .write("feature.txt", "feature work\n");
    harness
        .submodule("sub_a")
        .add_all()
        .commit("feature commit in sub_a");
    harness.root().add("sub_a");
    harness
        .root()
        .run_git(&["commit", "-m", "update sub_a on feature"]);

    // Switch back to master and update the submodule workdir to match
    // master's gitlink (initial commit).
    harness.root().run_git(&["checkout", "master"]);
    harness.root().run_git(&["submodule", "update"]);

    // Start the server on master so everything is clean.
    harness.start_server();
    harness.assert_all_clean();

    // Checkout feature. `git checkout` updates the root index (gitlink now
    // points to the feature commit) and then updates HEAD. The submodule
    // workdir is *not* updated (no `--recurse-submodules`), so sub_a's
    // workdir HEAD still matches master's gitlink, not feature's.
    //
    // Correct status: NEW_COMMITS (workdir HEAD ≠ index gitlink).
    //
    // The race that can occur on large repos: the server detects the index
    // rename before HEAD is updated, reads status against the stale HEAD,
    // and produces STAGED | NEW_COMMITS. If .git/HEAD changes are not
    // detected, the stale status sticks.
    harness.root().run_git(&["checkout", "feature"]);
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn submodule_update_after_checkout(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create a feature branch where sub_a has a new commit
    harness.root().run_git(&["checkout", "-b", "feature"]);
    harness
        .submodule("sub_a")
        .write("feature.txt", "feature work\n");
    harness
        .submodule("sub_a")
        .add_all()
        .commit("feature commit in sub_a");
    harness.root().add("sub_a");
    harness
        .root()
        .run_git(&["commit", "-m", "update sub_a on feature"]);

    // Back to master, sync submodule workdir
    harness.root().run_git(&["checkout", "master"]);
    harness.root().run_git(&["submodule", "update"]);

    harness.start_server();
    harness.assert_all_clean();

    // Checkout feature without --recurse-submodules so workdir lags behind
    harness.root().run_git(&["checkout", "feature"]);
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // `git submodule update` syncs the workdir to match the gitlink
    harness.root().run_git(&["submodule", "update"]);
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn checkout_with_recurse_submodules(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .no_server()
        .build();

    // Create a feature branch where sub_a has a new commit
    harness.root().run_git(&["checkout", "-b", "feature"]);
    harness
        .submodule("sub_a")
        .write("feature.txt", "feature work\n");
    harness
        .submodule("sub_a")
        .add_all()
        .commit("feature commit in sub_a");
    harness.root().add("sub_a");
    harness
        .root()
        .run_git(&["commit", "-m", "update sub_a on feature"]);

    // Back to master, sync submodule workdir
    harness.root().run_git(&["checkout", "master"]);
    harness.root().run_git(&["submodule", "update"]);

    harness.start_server();
    harness.assert_all_clean();

    // Checkout feature with --recurse-submodules so git updates the submodule
    // workdir automatically, so status should stay clean
    harness
        .root()
        .run_git(&["checkout", "--recurse-submodules", "feature"]);
    harness.assert_all_clean();
}

/// Same scenario with many submodules to widen the race window between
/// git's index rename and HEAD update during checkout.
#[apply(common::repeat)]
fn checkout_branch_many_submodules(_run: u32) {
    const N: usize = 50;

    let mut harness = common::HarnessBuilder::new()
        .submodules(N)
        .no_server()
        .build();

    // Create a feature branch where every submodule has a new commit.
    harness.root().run_git(&["checkout", "-b", "feature"]);
    for i in 0..N {
        let name = format!("sub_{i}");
        harness
            .submodule(&name)
            .write("feature.txt", "feature work\n");
        harness.submodule(&name).add_all().commit("feature commit");
        harness.root().add(&name);
    }
    harness
        .root()
        .run_git(&["commit", "-m", "update all submodules on feature"]);

    // Back to master, update all submodule workdirs to match master's gitlinks.
    harness.root().run_git(&["checkout", "master"]);
    harness.root().run_git(&["submodule", "update"]);

    harness.start_server();
    harness.assert_all_clean();

    // Checkout feature-> all submodule workdirs lag behind the new gitlinks.
    harness.root().run_git(&["checkout", "feature"]);

    // Every submodule should show NEW_COMMITS, not STAGED | NEW_COMMITS.
    for i in 0..N {
        harness.assert_submodule_status(&format!("sub_{i}"), StatusSummary::NEW_COMMITS);
    }
}
