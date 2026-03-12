mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn clean_repo_shows_no_dirty_submodules(_run: u32) {
    let harness = common::HarnessBuilder::new().submodules(3).build();
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn modified_file_shows_modified_content(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("lib_a")
        .submodule("lib_b")
        .build();
    harness.assert_all_clean();

    harness.write_file("lib_a", "README.md", "changed\n");
    harness.assert_submodule_status("lib_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn new_file_shows_untracked_content(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness.write_file("sub_a", "new_file.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn commit_in_submodule_shows_new_commits(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness.write_file("sub_a", "feature.txt", "new feature\n");
    // Wait for the watcher to process the file write and release index.lock
    // before doing git operations that also need index.lock
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    harness.commit_in_submodule("sub_a", "Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn status_returns_to_clean_after_reverting(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness.write_file("sub_a", "scratch.txt", "temp\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    harness.remove_file("sub_a", "scratch.txt");
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn multiple_submodules_independent_statuses(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .submodule("sub_c")
        .build();
    harness.assert_all_clean();

    harness.write_file("sub_a", "README.md", "changed\n");
    harness.write_file("sub_b", "new.txt", "hello\n");
    // sub_c untouched

    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
    harness.assert_submodule_status("sub_b", StatusSummary::UNTRACKED_CONTENT);
    harness.assert_submodule_status("sub_c", StatusSummary::CLEAN);
}

#[apply(common::repeat)]
fn combined_modified_and_untracked_content(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Modify an existing tracked file
    harness.write_file("sub_a", "README.md", "changed\n");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Also add an untracked file
    harness.write_file("sub_a", "new_file.txt", "hello\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::MODIFIED_CONTENT | StatusSummary::UNTRACKED_CONTENT,
    );
}

#[apply(common::repeat)]
fn commit_then_stage_gitlink(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Create an untracked file
    harness.write_file("sub_a", "feature.txt", "new feature\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // Commit it in the submodule-> now the submodule HEAD differs from the
    // gitlink recorded in the parent's index
    harness.commit_in_submodule("sub_a", "Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Stage the submodule gitlink in the parent repo-> index now matches
    // the submodule's HEAD but differs from the parent's HEAD
    harness.stage_submodule("sub_a");
    harness.assert_submodule_status("sub_a", StatusSummary::STAGED);
}

#[apply(common::repeat)]
fn parent_commit_clears_staged(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit in submodule so the gitlink diverges from parent's index
    harness.write_file("sub_a", "feature.txt", "new feature\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.commit_in_submodule("sub_a", "Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Stage the gitlink in the parent
    harness.stage_submodule("sub_a");
    harness.assert_submodule_status("sub_a", StatusSummary::STAGED);

    // Commit in the parent -> gitlink now matches HEAD, STAGED should clear
    harness.git_in_root(&["commit", "-m", "Update sub_a"]);
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn parent_commit_clears_staged_with_dirty_worktree(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit in submodule
    harness.write_file("sub_a", "feature.txt", "new feature\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.commit_in_submodule("sub_a", "Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Dirty the worktree *after* the commit
    harness.write_file("sub_a", "README.md", "modified\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS | StatusSummary::MODIFIED_CONTENT,
    );

    // Stage the gitlink in the parent
    harness.stage_submodule("sub_a");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::STAGED | StatusSummary::MODIFIED_CONTENT,
    );

    // Commit in the parent -> STAGED clears, MODIFIED_CONTENT remains
    harness.git_in_root(&["commit", "-m", "Update sub_a"]);
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn parent_commit_clears_staged_with_staged_submodule_files(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit in submodule
    harness.write_file("sub_a", "feature.txt", "new feature\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.commit_in_submodule("sub_a", "Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Dirty the worktree and stage a file *inside* the submodule's own index
    harness.write_file("sub_a", "README.md", "modified\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS | StatusSummary::MODIFIED_CONTENT,
    );
    harness.write_file("sub_a", "extra.txt", "extra\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS
            | StatusSummary::MODIFIED_CONTENT
            | StatusSummary::UNTRACKED_CONTENT,
    );
    harness.stage_file("sub_a", "extra.txt");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS | StatusSummary::MODIFIED_CONTENT,
    );

    // Stage the gitlink in the parent
    harness.stage_submodule("sub_a");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::STAGED | StatusSummary::MODIFIED_CONTENT,
    );

    // Commit in the parent -> STAGED clears, MODIFIED_CONTENT remains
    harness.git_in_root(&["commit", "-m", "Update sub_a"]);
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn stage_and_unstage_file(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Create a new file and wait for the watcher to process before staging
    harness.write_file("sub_a", "new.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // Stage the file
    harness.stage_file("sub_a", "new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Unstage the file (git restore --staged), file still exists on disk as untracked
    harness.unstage_file("sub_a", "new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
}
