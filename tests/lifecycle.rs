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
