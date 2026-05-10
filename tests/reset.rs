mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn submodule_reset_soft(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit a new file in the submodule
    harness.submodule("sub_a").write("new.txt", "content\n");
    harness.submodule("sub_a").add_all().commit("add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Soft reset: HEAD moves back, but changes remain staged
    harness
        .submodule("sub_a")
        .run_git(&["reset", "--soft", "HEAD~1"]);

    // HEAD now matches parent gitlink again, but there are staged changes
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn submodule_reset_mixed(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit a new file in the submodule
    harness.submodule("sub_a").write("new.txt", "content\n");
    harness.submodule("sub_a").add_all().commit("add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Mixed reset (default): HEAD moves back, changes become unstaged/untracked
    harness.submodule("sub_a").run_git(&["reset", "HEAD~1"]);

    // The new file is now untracked
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn submodule_reset_hard(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit a new file in the submodule
    harness.submodule("sub_a").write("new.txt", "content\n");
    harness.submodule("sub_a").add_all().commit("add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Hard reset: HEAD moves back, all changes discarded
    harness
        .submodule("sub_a")
        .run_git(&["reset", "--hard", "HEAD~1"]);

    // Everything is clean again
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn root_reset_staged_gitlink(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit in submodule-> creates NEW_COMMITS
    harness.submodule("sub_a").write("new.txt", "content\n");
    harness.submodule("sub_a").add_all().commit("add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Stage the gitlink in the parent repo
    harness.root().add("sub_a");
    harness.assert_submodule_status("sub_a", StatusSummary::STAGED);

    // Reset the staged gitlink-> back to NEW_COMMITS
    harness.root().run_git(&["reset", "HEAD", "--", "sub_a"]);
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}
