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

    harness
        .submodule("libs/core")
        .write("README.md", "changed\n");
    harness.assert_submodule_status("libs/core", StatusSummary::MODIFIED_CONTENT);
    harness.assert_submodule_status("libs/utils", StatusSummary::clean());
}

#[apply(common::repeat)]
fn nested_path_untracked_content(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("vendor/thirdparty")
        .build();
    harness.assert_all_clean();

    harness
        .submodule("vendor/thirdparty")
        .write("new.txt", "hello\n");
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn nested_path_commit_shows_new_commits(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("libs/core").build();
    harness.assert_all_clean();

    harness.submodule("libs/core").write("feature.txt", "new\n");
    harness.assert_submodule_status("libs/core", StatusSummary::UNTRACKED_CONTENT);

    harness
        .submodule("libs/core")
        .add_all()
        .commit("Add feature");
    harness.assert_submodule_status("libs/core", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn nested_path_full_stage_commit_cycle(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("libs/core").build();
    harness.assert_all_clean();

    harness.submodule("libs/core").write("feature.txt", "new\n");
    harness.assert_submodule_status("libs/core", StatusSummary::UNTRACKED_CONTENT);

    harness
        .submodule("libs/core")
        .add_all()
        .commit("Add feature");
    harness.assert_submodule_status("libs/core", StatusSummary::NEW_COMMITS);

    harness.root().add("libs/core");
    harness.assert_submodule_status("libs/core", StatusSummary::STAGED);

    harness
        .root()
        .run_git(&["commit", "-m", "Update libs/core"]);
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

    harness
        .submodule("libs/core")
        .write("README.md", "changed\n");
    harness
        .submodule("vendor/thirdparty")
        .write("new.txt", "hello\n");
    // libs/utils untouched

    harness.assert_submodule_status("libs/core", StatusSummary::MODIFIED_CONTENT);
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::UNTRACKED_CONTENT);
    harness.assert_submodule_status("libs/utils", StatusSummary::clean());
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
    harness.submodule("sub_a").write("README.md", "changed\n");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Commit the change -> MODIFIED_CONTENT must clear, NEW_COMMITS appears
    harness.submodule("sub_a").add_all().commit("Update README");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn submodule_commit_clears_staged_files(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Create and stage a file inside the submodule
    harness.submodule("sub_a").write("new.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.submodule("sub_a").add("new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Commit the staged file -> staged changes clear, NEW_COMMITS appears
    harness.submodule("sub_a").add_all().commit("Add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn submodule_commit_with_remaining_dirty_files(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Create two files
    harness
        .submodule("sub_a")
        .write("staged.txt", "will commit\n");
    harness
        .submodule("sub_a")
        .write("unstaged.txt", "will not commit\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // Stage only one, then commit
    harness.submodule("sub_a").add("staged.txt");
    harness
        .submodule("sub_a")
        .run_git(&["commit", "-m", "Partial commit"]);

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
    harness.submodule("sub_a").write("feature.txt", "v1\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.submodule("sub_a").add_all().commit("Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Immediately dirty the worktree after committing
    harness.submodule("sub_a").write("README.md", "modified\n");
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
    harness
        .submodule("libs/core")
        .write("README.md", "changed\n");
    harness.assert_submodule_status("libs/core", StatusSummary::MODIFIED_CONTENT);

    // Commit -> MODIFIED_CONTENT must clear via refs/heads/ detection
    harness
        .submodule("libs/core")
        .add_all()
        .commit("Update README");
    harness.assert_submodule_status("libs/core", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn nested_path_stage_and_unstage_file(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("vendor/thirdparty")
        .build();
    harness.assert_all_clean();

    harness
        .submodule("vendor/thirdparty")
        .write("new.txt", "hello\n");
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::UNTRACKED_CONTENT);

    harness.submodule("vendor/thirdparty").add("new.txt");
    harness.assert_submodule_status("vendor/thirdparty", StatusSummary::MODIFIED_CONTENT);

    harness
        .submodule("vendor/thirdparty")
        .restore_staged("new.txt");
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

    harness.submodule("lib_a").write("README.md", "changed\n");
    harness.assert_submodule_status("lib_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn new_file_shows_untracked_content(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness.submodule("sub_a").write("new_file.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn commit_in_submodule_shows_new_commits(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness
        .submodule("sub_a")
        .write("feature.txt", "new feature\n");
    // Wait for the watcher to process the file write and release index.lock
    // before doing git operations that also need index.lock
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    harness.submodule("sub_a").add_all().commit("Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);
}

#[apply(common::repeat)]
fn status_returns_to_clean_after_reverting(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness.submodule("sub_a").write("scratch.txt", "temp\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    harness.submodule("sub_a").rm_file("scratch.txt");
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

    harness.submodule("sub_a").write("README.md", "changed\n");
    harness.submodule("sub_b").write("new.txt", "hello\n");
    // sub_c untouched

    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
    harness.assert_submodule_status("sub_b", StatusSummary::UNTRACKED_CONTENT);
    harness.assert_submodule_status("sub_c", StatusSummary::clean());
}

#[apply(common::repeat)]
fn combined_modified_and_untracked_content(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Modify an existing tracked file
    harness.submodule("sub_a").write("README.md", "changed\n");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Also add an untracked file
    harness.submodule("sub_a").write("new_file.txt", "hello\n");
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
    harness
        .submodule("sub_a")
        .write("feature.txt", "new feature\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // Commit it in the submodule-> now the submodule HEAD differs from the
    // gitlink recorded in the parent's index
    harness.submodule("sub_a").add_all().commit("Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Stage the submodule gitlink in the parent repo-> index now matches
    // the submodule's HEAD but differs from the parent's HEAD
    harness.root().add("sub_a");
    harness.assert_submodule_status("sub_a", StatusSummary::STAGED);
}

#[apply(common::repeat)]
fn parent_commit_clears_staged(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit in submodule so the gitlink diverges from parent's index
    harness
        .submodule("sub_a")
        .write("feature.txt", "new feature\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.submodule("sub_a").add_all().commit("Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Stage the gitlink in the parent
    harness.root().add("sub_a");
    harness.assert_submodule_status("sub_a", StatusSummary::STAGED);

    // Commit in the parent -> gitlink now matches HEAD, STAGED should clear
    harness.root().run_git(&["commit", "-m", "Update sub_a"]);
    harness.assert_all_clean();
}

#[apply(common::repeat)]
fn parent_commit_clears_staged_with_dirty_worktree(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit in submodule
    harness
        .submodule("sub_a")
        .write("feature.txt", "new feature\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.submodule("sub_a").add_all().commit("Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Dirty the worktree *after* the commit
    harness.submodule("sub_a").write("README.md", "modified\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS | StatusSummary::MODIFIED_CONTENT,
    );

    // Stage the gitlink in the parent
    harness.root().add("sub_a");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::STAGED | StatusSummary::MODIFIED_CONTENT,
    );

    // Commit in the parent -> STAGED clears, MODIFIED_CONTENT remains
    harness.root().run_git(&["commit", "-m", "Update sub_a"]);
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn parent_commit_clears_staged_with_staged_submodule_files(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Commit in submodule
    harness
        .submodule("sub_a")
        .write("feature.txt", "new feature\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.submodule("sub_a").add_all().commit("Add feature");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // Dirty the worktree and stage a file *inside* the submodule's own index
    harness.submodule("sub_a").write("README.md", "modified\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS | StatusSummary::MODIFIED_CONTENT,
    );
    harness.submodule("sub_a").write("extra.txt", "extra\n");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS
            | StatusSummary::MODIFIED_CONTENT
            | StatusSummary::UNTRACKED_CONTENT,
    );
    harness.submodule("sub_a").add("extra.txt");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::NEW_COMMITS | StatusSummary::MODIFIED_CONTENT,
    );

    // Stage the gitlink in the parent
    harness.root().add("sub_a");
    harness.assert_submodule_status(
        "sub_a",
        StatusSummary::STAGED | StatusSummary::MODIFIED_CONTENT,
    );

    // Commit in the parent -> STAGED clears, MODIFIED_CONTENT remains
    harness.root().run_git(&["commit", "-m", "Update sub_a"]);
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(common::repeat)]
fn stage_and_unstage_file(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Create a new file and wait for the watcher to process before staging
    harness.submodule("sub_a").write("new.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // Stage the file
    harness.submodule("sub_a").add("new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);

    // Unstage the file (git restore --staged), file still exists on disk as untracked
    harness.submodule("sub_a").restore_staged("new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
}
