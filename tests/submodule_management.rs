mod common;

use rstest_reuse::apply;
use subspy::StatusSummary;

#[apply(common::repeat)]
fn add_submodule_detected_by_server(_run: u32) {
    let mut harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Dirty sub_a so we can verify it's unaffected by the add operation
    harness.submodule("sub_a").write("untracked.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // Stage sub_b without committing, gitlink is in index but not in HEAD
    harness.add_submodule_no_commit("sub_b");
    harness.assert_submodule_status("sub_b", StatusSummary::STAGED_NEW);

    // Commit the addition, so it's no longer "new"
    harness
        .root()
        .run_git(&["commit", "-m", "Add submodule sub_b"]);
    harness.assert_submodule_status("sub_b", StatusSummary::clean());

    // Dirty sub_b and verify the server picked it up
    harness.submodule("sub_b").write("new_file.txt", "world\n");
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
    harness.submodule("sub_b").write("new_file.txt", "hello\n");
    harness.assert_submodule_status(
        "sub_b",
        StatusSummary::UNTRACKED_CONTENT | StatusSummary::STAGED_NEW,
    );

    // sub_a should be unaffected
    harness.assert_submodule_status("sub_a", StatusSummary::clean());
}

// Reproduces a reported bug: `git submodule add <src> temporary/some_submod`
// then `git restore --staged temporary` (unstage the gitlink). git reports the
// submodule as untracked, not staged. The server must drop the STAGED_NEW flag
// it cached when the gitlink was first staged.
#[apply(common::repeat)]
fn unstage_new_submodule_clears_staged_new(_run: u32) {
    let mut harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness.add_submodule_no_commit("temporary/some_submod");
    harness.assert_submodule_status("temporary/some_submod", StatusSummary::STAGED_NEW);

    // `git restore --staged temporary` removes the gitlink from the index.
    harness.root().restore_staged("temporary");
    harness.assert_submodule_status("temporary/some_submod", StatusSummary::clean());

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
    harness.root().run_git(&["rm", "-f", "sub_b"]);

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
    harness.root().run_git(&["rm", "-f", "sub_b"]);
    harness.root().run_git(&["rm", "-f", "sub_c"]);

    harness.assert_deleted_submodule_paths(&["sub_b", "sub_c"]);

    // sub_a should not appear as deleted
    harness.assert_submodule_status("sub_a", StatusSummary::clean());
}

#[apply(common::repeat)]
fn rm_rf_submodule_workdir_reported_as_deleted(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .build();
    harness.assert_all_clean();

    // Wipe sub_b's workdir without staging anything. The gitlink stays in HEAD
    // and the index, so this mirrors `git status` showing
    // `deleted: sub_b` in the unstaged section.
    std::fs::remove_dir_all(harness.submodule("sub_b").path()).unwrap();

    harness.assert_submodule_status("sub_b", StatusSummary::DELETED_WORKDIR);

    // The deletion is unstaged, so `deleted_submodule_paths` (which captures
    // gitlinks staged for removal) must remain empty.
    harness.assert_deleted_submodule_paths(&[]);

    // sub_a should be unaffected.
    harness.assert_submodule_status("sub_a", StatusSummary::clean());
}

/// A submodule whose workdir is `rm -rf`'d must still be watched after it is
/// restored. The submodule's own recursive watch dies silently when its
/// directory is removed, so the parent "tripwire" watch is what notices both
/// the deletion and the restore (re-arming the watch via a reindex). The final
/// `write` is the deterministic part: without a re-armed watch, the server
/// never sees the new file and the assertion times out.
#[apply(common::repeat)]
fn restored_submodule_workdir_is_rewatched(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .build();
    harness.assert_all_clean();

    // rm -rf sub_b's workdir: the gitlink stays in HEAD/index, so it is a
    // deletion. Caught by the parent tripwire, not sub_b's own (dying) watch.
    std::fs::remove_dir_all(harness.submodule("sub_b").path()).unwrap();
    harness.assert_submodule_status("sub_b", StatusSummary::DELETED_WORKDIR);

    // Restore the workdir from the submodule's gitdir.
    harness
        .root()
        .run_git(&["submodule", "update", "--force", "sub_b"]);
    harness.assert_submodule_status("sub_b", StatusSummary::clean());

    // A change made after the restore must be picked up, proving the watch was
    // re-armed rather than left dead.
    harness
        .submodule("sub_b")
        .write("after_restore.txt", "hi\n");
    harness.assert_submodule_status("sub_b", StatusSummary::UNTRACKED_CONTENT);

    // sub_a is untouched throughout.
    harness.assert_submodule_status("sub_a", StatusSummary::clean());
}

/// A reindex that runs while a submodule's workdir is deleted must keep
/// reporting it as `DELETED_WORKDIR`, not drop it. Linux normally takes the
/// targeted re-read path for a deletion (a lock-free `submodule_status` read),
/// but the reindex path first calls `get_modules_path`, which reads the
/// submodule's now-gone `.git` gitlink and fails with `NotFound`. Dropping the
/// submodule there is the macOS bug, where `FSEvents` reports the `rm -rf` as a
/// rename that routes through a reindex instead of a targeted re-read. Here we
/// force the reindex path on every platform with an explicit reindex request.
///
/// `request_reindex` blocks until indexing finishes, and `populate_status_map`
/// holds the status-map mutex across the whole reindex, so the assertion sees
/// the post-reindex map rather than the value the targeted path left behind.
/// Without the fix the submodule is dropped from the rebuilt map and the
/// assertion times out.
#[apply(common::repeat)]
fn reindex_over_deleted_workdir_still_reports_deleted(_run: u32) {
    let harness = common::HarnessBuilder::new()
        .submodule("sub_a")
        .submodule("sub_b")
        .build();
    harness.assert_all_clean();

    std::fs::remove_dir_all(harness.submodule("sub_b").path()).unwrap();
    harness.assert_submodule_status("sub_b", StatusSummary::DELETED_WORKDIR);

    // Force a full reindex over the deleted workdir.
    harness.request_reindex(false);
    harness.assert_submodule_status("sub_b", StatusSummary::DELETED_WORKDIR);

    // sub_a is unaffected.
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
    harness.submodule("sub_a").write("untracked.txt", "hello\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    harness.submodule("sub_b").write("untracked.txt", "world\n");
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
