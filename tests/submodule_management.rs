mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn add_submodule_detected_by_server(_run: u32) {
    let mut harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Dirty sub_a so we can verify it's unaffected by the add operation
    harness.write_file("sub_a", "untracked.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // Stage sub_b without committing, gitlink is in index but not in HEAD
    harness.add_submodule_no_commit("sub_b");
    harness.assert_submodule_status("sub_b", StatusSummary::STAGED_NEW);

    // Commit the addition, so it's no longer "new"
    harness.git_in_root(&["commit", "-m", "Add submodule sub_b"]);
    harness.assert_submodule_status("sub_b", StatusSummary::clean());

    // Dirty sub_b and verify the server picked it up
    harness.write_file("sub_b", "new_file.txt", "world\n");
    harness.assert_submodule_status("sub_b", StatusSummary::UNTRACKED_CONTENT);

    // sub_a should still have its untracked content
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn add_submodule_without_commit_detected_by_server(_run: u32) {
    let mut harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Stage sub_b without committing -- no follow-up git command produces a
    // root event. The debounce fallback must fire to trigger the reindex.
    harness.add_submodule_no_commit("sub_b");
    harness.assert_submodule_status("sub_b", StatusSummary::STAGED_NEW);

    // Dirty sub_b and verify the server picked it up via the debounce reindex.
    // STAGED_NEW persists because the submodule hasn't been committed yet.
    harness.write_file("sub_b", "new_file.txt", "hello\n");
    harness.assert_submodule_status(
        "sub_b",
        StatusSummary::UNTRACKED_CONTENT | StatusSummary::STAGED_NEW,
    );

    // sub_a should be unaffected
    harness.assert_submodule_status("sub_a", StatusSummary::clean());
}

#[apply(common::repeat)]
fn remove_submodule_without_commit_detected_by_server(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .build();
    harness.assert_all_clean();

    // Remove sub_b without committing -- no follow-up git command produces a
    // root event. The debounce fallback must fire to trigger the reindex.
    harness.git_in_root(&["rm", "-f", "sub_b"]);

    // sub_b should no longer appear in the status after the debounce reindex
    harness.assert_status_eventually("sub_b removed from status", |statuses| {
        !statuses.iter().any(|(name, _)| name == "sub_b")
    });

    // The staged gitlink deletion should be detected
    harness.assert_deleted_submodule_paths(&["sub_b"]);

    // sub_a should be unaffected
    harness.assert_submodule_status("sub_a", StatusSummary::clean());
}

#[apply(common::repeat)]
fn remove_submodule_without_commit_shows_deleted_path(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .submodule("sub_c")
        .build();
    harness.assert_all_clean();

    // No deletions yet
    harness.assert_deleted_submodule_paths(&[]);

    // Stage removal of two submodules
    harness.git_in_root(&["rm", "-f", "sub_b"]);
    harness.git_in_root(&["rm", "-f", "sub_c"]);

    harness.assert_deleted_submodule_paths(&["sub_b", "sub_c"]);

    // sub_a should not appear as deleted
    harness.assert_submodule_status("sub_a", StatusSummary::clean());
}

#[apply(common::repeat)]
fn remove_submodule_detected_by_server(_run: u32) {
    let mut harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .build();
    harness.assert_all_clean();

    // Dirty both submodules
    harness.write_file("sub_a", "untracked.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    harness.write_file("sub_b", "untracked.txt", "world\n");
    harness.assert_submodule_status("sub_b", StatusSummary::UNTRACKED_CONTENT);

    // Remove sub_b, which  triggers .gitmodules change-> deferred reindex
    harness.remove_submodule("sub_b");

    // sub_a should still have its untracked content
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // sub_b should no longer appear in the status
    harness.assert_status_eventually("sub_b removed from status", |statuses| {
        !statuses.iter().any(|(name, _)| name == "sub_b")
    });
}
