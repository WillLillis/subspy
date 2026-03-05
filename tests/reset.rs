mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn submodule_reset_soft(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit a new file in the submodule
    harness.write_file("sub_a", "new.txt", "content\n");
    harness.commit_in_submodule("sub_a", "add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Soft reset: HEAD moves back, but changes remain staged
    harness.git_in_submodule("sub_a", &["reset", "--soft", "HEAD~1"]);

    // HEAD now matches parent gitlink again, but there are staged changes
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn submodule_reset_mixed(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit a new file in the submodule
    harness.write_file("sub_a", "new.txt", "content\n");
    harness.commit_in_submodule("sub_a", "add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Mixed reset (default): HEAD moves back, changes become unstaged/untracked
    harness.git_in_submodule("sub_a", &["reset", "HEAD~1"]);

    // The new file is now untracked
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn submodule_reset_hard(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit a new file in the submodule
    harness.write_file("sub_a", "new.txt", "content\n");
    harness.commit_in_submodule("sub_a", "add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Hard reset: HEAD moves back, all changes discarded
    harness.git_in_submodule("sub_a", &["reset", "--hard", "HEAD~1"]);

    // Everything is clean again
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn root_reset_staged_gitlink(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit in submodule-> creates NEW_COMMITS
    harness.write_file("sub_a", "new.txt", "content\n");
    harness.commit_in_submodule("sub_a", "add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Stage the gitlink in the parent repo
    harness.stage_submodule("sub_a");
    harness.assert_submodule_status("sub_a", StatusSummary::STAGED);

    // Reset the staged gitlink-> back to NEW_COMMITS
    harness.git_in_root(&["reset", "HEAD", "--", "sub_a"]);
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}
