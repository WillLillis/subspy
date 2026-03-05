mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn submodule_stash_saves_and_restores_modified(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Modify a tracked file inside the submodule
    harness.write_file("sub_a", "README.md", "modified\n");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Stash the modification, submodule should return to clean
    harness.git_in_submodule("sub_a", &["stash"]);
    harness.assert_all_clean();

    // Pop the stash-> modification reappears
    harness.git_in_submodule("sub_a", &["stash", "pop"]);
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn submodule_stash_saves_and_restores_untracked(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Modify a tracked file AND create an untracked file
    harness.write_file("sub_a", "README.md", "modified\n");
    harness.write_file("sub_a", "untracked.txt", "new file\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::MODIFIED_CONTENT | StatusSummary::UNTRACKED_CONTENT,
    );

    // `git stash -u` saves both tracked modifications and untracked files
    harness.git_in_submodule("sub_a", &["stash", "-u"]);
    harness.assert_all_clean();

    // Pop the stash so both the modification and untracked file reappear
    harness.git_in_submodule("sub_a", &["stash", "pop"]);
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::MODIFIED_CONTENT | StatusSummary::UNTRACKED_CONTENT,
    );
}
