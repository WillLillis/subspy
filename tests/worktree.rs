mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

// ---------------------------------------------------------------------------
// Linked worktree support
//
// A linked worktree's `.git` is a *file* pointing at
// `<main>/.git/worktrees/<name>/`, where its index, HEAD, and submodule gitdirs
// (`modules/<sub>`) live; refs stay shared in the main repo's `.git/`. These
// tests run the watch server against the worktree (via `.worktree()`) and check
// that submodule status is tracked correctly through the resolved git dir.
// ---------------------------------------------------------------------------

#[apply(common::repeat)]
fn worktree_clean(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub")
        .worktree()
        .build();
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn worktree_untracked_content(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub")
        .worktree()
        .build();
    harness.assert_all_clean();

    harness.submodule("sub").write("new.txt", "untracked\n");
    harness.assert_submodule_status("sub", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn worktree_modified_content(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub")
        .worktree()
        .build();
    harness.assert_all_clean();

    // README.md is the source repo's one tracked file.
    harness.submodule("sub").write("README.md", "# changed\n");
    harness.assert_submodule_status("sub", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn worktree_clean_after_revert(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub")
        .worktree()
        .build();
    harness.assert_all_clean();

    harness.submodule("sub").write("new.txt", "untracked\n");
    harness.assert_submodule_status("sub", StatusSummary::UNTRACKED_CONTENT);

    harness.submodule("sub").rm_file("new.txt");
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn worktree_stage_commit_cycle(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub")
        .worktree()
        .build();
    harness.assert_all_clean();

    harness.submodule("sub").write("feature.txt", "new\n");
    harness.assert_submodule_status("sub", StatusSummary::UNTRACKED_CONTENT);

    harness.submodule("sub").add_all().commit("Add feature");
    harness.assert_submodule_status("sub", StatusSummary::NEW_COMMITS);

    harness.root().add("sub");
    harness.assert_submodule_status("sub", StatusSummary::STAGED);

    harness.root().run_git(&["commit", "-m", "Update sub"]);
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn worktree_uninitialized_submodule_is_clean(_run: u32) {
    // `git worktree add` does not check out submodules, so the worktree's
    // submodule working tree is absent (no gitlink, empty dir). The server must
    // treat it as clean rather than erroring on the missing `.git`.
    let harness = common::HarnessBuilder::new()
        .submodule("sub")
        .worktree_without_submodule_checkout()
        .build();
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn worktree_multiple_submodules(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("libs/core")
        .submodule("vendor/dep")
        .worktree()
        .build();
    harness.assert_all_clean();

    harness.submodule("libs/core").write("x.txt", "u\n");
    harness.assert_submodule_status("libs/core", StatusSummary::UNTRACKED_CONTENT);
    harness.assert_submodule_status("vendor/dep", StatusSummary::clean());
}
