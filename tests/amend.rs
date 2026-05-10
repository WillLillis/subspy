mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn submodule_commit_amend(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Make a commit in the submodule-> HEAD diverges from parent gitlink
    harness.submodule("sub_a").write("file.txt", "first\n");
    harness.submodule("sub_a").add_all().commit("first commit");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Write more content, stage it, and amend the commit
    harness.submodule("sub_a").write("file.txt", "amended\n");
    harness.submodule("sub_a").add("file.txt");
    harness
        .submodule("sub_a")
        .run_git(&["commit", "--amend", "-m", "amended commit"]);

    // Still NEW_COMMITS-> submodule HEAD still diverges from parent gitlink
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}
