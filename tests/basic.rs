mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

// ---------------------------------------------------------------------------
// Multi-component submodule paths
//
// Submodule names can contain path separators (e.g. `libs/foo`). These tests
// ensure the server correctly handles the resulting `.git/modules/libs/foo/`
// directory structure, including event classification and `refs/heads/`
// detection.
// ---------------------------------------------------------------------------

#[apply(common::repeat)]
fn nested_path_clean_repo(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("libs/core")
        .submodule("vendor/thirdparty")
        .build();
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn nested_path_modified_content(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("libs/core")
        .submodule("libs/utils")
        .build();
    harness.assert_all_clean();

    harness.write_file("libs/core", "README.md", "changed\n");
    harness.assert_submodule_status("libs/core", StatusSummary::MODIFIED_CONTENT);
    harness.assert_submodule_status("libs/utils", StatusSummary::CLEAN);
}

#[apply(common::repeat)]
fn nested_path_untracked_content(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("vendor/thirdparty")
        .build();
    harness.assert_all_clean();

    harness.write_file("vendor/thirdparty", "new.txt", "hello\n");
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn nested_path_commit_shows_new_commits(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("libs/core").build();
    harness.assert_all_clean();

    harness.write_file("libs/core", "feature.txt", "new\n");
    harness.assert_submodule_status("libs/core", StatusSummary::UNTRACKED_CONTENT);

    harness.commit_in_submodule("libs/core", "Add feature");
    harness.assert_submodule_status("libs/core", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn nested_path_full_stage_commit_cycle(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("libs/core").build();
    harness.assert_all_clean();

    harness.write_file("libs/core", "feature.txt", "new\n");
    harness.assert_submodule_status("libs/core", StatusSummary::UNTRACKED_CONTENT);

    harness.commit_in_submodule("libs/core", "Add feature");
    harness.assert_submodule_status("libs/core", StatusSummary::NEW_COMMITS);

    harness.stage_submodule("libs/core");
    harness.assert_submodule_status("libs/core", StatusSummary::STAGED);

    harness.git_in_root(&["commit", "-m", "Update libs/core"]);
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn nested_path_independent_statuses(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("libs/core")
        .submodule("libs/utils")
        .submodule("vendor/thirdparty")
        .build();
    harness.assert_all_clean();

    harness.write_file("libs/core", "README.md", "changed\n");
    harness.write_file("vendor/thirdparty", "new.txt", "hello\n");
    // libs/utils untouched

    harness.assert_submodule_status("libs/core", StatusSummary::MODIFIED_CONTENT);
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::UNTRACKED_CONTENT);
    harness.assert_submodule_status("libs/utils", StatusSummary::CLEAN);
}

// ---------------------------------------------------------------------------
// Submodule commit detection via refs/heads/
//
// When `git commit` runs inside a submodule, the branch ref rename at
// `.git/modules/<name>/refs/heads/<branch>` is the most reliable post-commit
// signal. These tests verify the server detects submodule commits correctly,
// including the transition from MODIFIED_CONTENT (staged changes) to
// NEW_COMMITS (committed changes) — the exact scenario that fails when
// refs/heads/ events are dropped.
// ---------------------------------------------------------------------------

#[apply(common::repeat)]
fn submodule_commit_clears_modified_content(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Modify a tracked file -> MODIFIED_CONTENT
    harness.write_file("sub_a", "README.md", "changed\n");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Commit the change -> MODIFIED_CONTENT must clear, NEW_COMMITS appears
    harness.commit_in_submodule("sub_a", "Update README");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn submodule_commit_clears_staged_files(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Create and stage a file inside the submodule
    harness.write_file("sub_a", "new.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.stage_file("sub_a", "new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Commit the staged file -> staged changes clear, NEW_COMMITS appears
    harness.commit_in_submodule("sub_a", "Add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn submodule_commit_with_remaining_dirty_files(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Create two files
    harness.write_file("sub_a", "staged.txt", "will commit\n");
    harness.write_file("sub_a", "unstaged.txt", "will not commit\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // Stage only one, then commit
    harness.stage_file("sub_a", "staged.txt");
    harness.git_in_submodule("sub_a", &["commit", "-m", "Partial commit"]);

    // NEW_COMMITS from the commit + UNTRACKED_CONTENT from unstaged.txt
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS | StatusSummary::UNTRACKED_CONTENT,
    );
}

#[apply(common::repeat)]
fn submodule_commit_then_dirty_worktree(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit a new file
    harness.write_file("sub_a", "feature.txt", "v1\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.commit_in_submodule("sub_a", "Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Immediately dirty the worktree after committing
    harness.write_file("sub_a", "README.md", "modified\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS | StatusSummary::MODIFIED_CONTENT,
    );
}

#[apply(common::repeat)]
fn nested_path_submodule_commit_clears_modified_content(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("libs/core").build();
    harness.assert_all_clean();

    // Modify a tracked file in a nested-path submodule
    harness.write_file("libs/core", "README.md", "changed\n");
    harness.assert_submodule_status("libs/core", StatusSummary::MODIFIED_CONTENT);

    // Commit -> MODIFIED_CONTENT must clear via refs/heads/ detection
    harness.commit_in_submodule("libs/core", "Update README");
    harness.assert_submodule_status("libs/core", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn nested_path_stage_and_unstage_file(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("vendor/thirdparty")
        .build();
    harness.assert_all_clean();

    harness.write_file("vendor/thirdparty", "new.txt", "hello\n");
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::UNTRACKED_CONTENT);

    harness.stage_file("vendor/thirdparty", "new.txt");
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::MODIFIED_CONTENT);

    harness.unstage_file("vendor/thirdparty", "new.txt");
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::UNTRACKED_CONTENT);
}

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
