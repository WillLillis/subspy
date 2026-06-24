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

    harness.root().commit("Update sub");
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn worktree_external_ref_update_is_seen(_run: u32) {
    // A direct ref update (a fetch moving the worktree's branch, a tool, or a
    // raw `git update-ref`) changes only a ref in the shared common dir, with no
    // event in the per-worktree git dir -- so unlike an ordinary commit (which
    // rewrites the index and touches the lock files), only the common-dir refs
    // watch can catch it.
    let harness = common::HarnessBuilder::new()
        .submodule("sub")
        .worktree()
        .build();
    harness.assert_all_clean();

    // Advance the submodule and commit the gitlink so the worktree branch is one
    // commit ahead and clean again.
    harness.submodule("sub").write("f.txt", "x\n");
    harness.submodule("sub").add_all().commit("sub change");
    harness.root().add("sub");
    harness.root().commit("bump sub");
    harness.assert_all_clean();

    // Move the branch back one commit via update-ref (ref-only: no index/lock
    // event). The index still holds the newer gitlink, so the submodule now
    // diverges from HEAD and must show as staged. `wt-branch` is the worktree's
    // branch created by the harness.
    harness
        .root()
        .run_git(&["update-ref", "refs/heads/wt-branch", "HEAD~1"]);
    harness.assert_submodule_status("sub", StatusSummary::STAGED);
}

#[apply(common::repeat)]
fn worktree_reindex_preserves_status(_run: u32) {
    // Reindex must re-resolve the worktree's git dir and re-place watchers
    // there, not at `<root>/.git`; status survives both reindex modes.
    let harness = common::HarnessBuilder::new()
        .submodule("sub")
        .worktree()
        .build();
    harness.submodule("sub").write("new.txt", "u\n");
    harness.assert_submodule_status("sub", StatusSummary::UNTRACKED_CONTENT);

    harness.request_reindex(false);
    harness.assert_submodule_status("sub", StatusSummary::UNTRACKED_CONTENT);

    harness.request_reindex(true); // replace watchers
    harness.assert_submodule_status("sub", StatusSummary::UNTRACKED_CONTENT);
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
