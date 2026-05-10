mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn submodule_git_clean(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Write an untracked file inside the submodule
    harness.submodule("sub_a").write("junk.txt", "temporary\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // `git clean -fd` removes untracked files and directories
    harness.submodule("sub_a").run_git(&["clean", "-fd"]);
    harness.assert_all_clean();
}
