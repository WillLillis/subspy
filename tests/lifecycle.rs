mod common;

use rstest_reuse::apply;
use subspy::{StatusSummary, connection::client::request_reindex};

#[apply(common::repeat)]
fn shutdown_completes_cleanly(_run: u32) {
    let mut harness = common::HarnessBuilder::new().submodules(2).build();
    harness.assert_all_clean();
    // shutdown() sends the request, waits for ack, and joins the server thread.
    // If any of that fails, it panics.
    harness.shutdown();
}

#[apply(common::repeat)]
fn reindex_preserves_status(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness.write_file("sub_a", "dirty.txt", "dirty\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    request_reindex(harness.root_path(), false, false).unwrap();

    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
}

#[apply(common::repeat)]
fn reindex_replace_watchers_preserves_status(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    harness.write_file("sub_a", "dirty.txt", "dirty\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    request_reindex(harness.root_path(), true, false).unwrap();

    // Existing status should survive the reindex
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);

    // New watchers should detect subsequent changes
    harness.remove_file("sub_a", "dirty.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::CLEAN);

    harness.write_file("sub_a", "README.md", "modified\n");
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}
