mod common;

use std::io::{BufReader, Read};

use rstest_reuse::apply;
use subspy::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ClientRequest, IPC_VERSION, ServerMessage,
        client::request_reindex, ipc_connect, ipc_socket_path, write_full_message,
    },
};

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

#[apply(common::repeat)]
fn version_mismatch_returns_error_and_server_stays_alive(_run: u32) {
    let harness = common::HarnessBuilder::new().submodule("sub_a").build();
    harness.assert_all_clean();

    // Send a request with a wrong version
    let sock_path = ipc_socket_path(harness.root_path());
    let conn = ipc_connect(&sock_path).unwrap();
    let mut conn = BufReader::new(conn);
    let bad_request = ClientRequest {
        version: IPC_VERSION + 1,
        message: ClientMessage::Status(std::process::id()),
    };
    let mut req_msg = [0; 9];
    let req_msg_len = bincode::encode_into_slice(&bad_request, &mut req_msg, BINCODE_CFG).unwrap();
    write_full_message(&mut conn, &req_msg[..req_msg_len]).unwrap();

    // Read the response - should be VersionMismatch
    let mut len_buf = [0u8; 4];
    conn.read_exact(&mut len_buf).unwrap();
    let msg_len = u32::from_le_bytes(len_buf) as usize;
    let mut buffer = [0u8; 5];
    conn.read_exact(&mut buffer[..msg_len]).unwrap();
    let (resp, _): (ServerMessage, usize) =
        bincode::borrow_decode_from_slice(&buffer[..msg_len], BINCODE_CFG).unwrap();
    assert_eq!(
        resp,
        ServerMessage::VersionMismatch {
            server_version: IPC_VERSION
        }
    );

    // Server should still be alive - normal requests should work
    harness.assert_all_clean();
}
