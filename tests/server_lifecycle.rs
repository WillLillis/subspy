mod common;

use common::{TestRepo, WatchServerHandle};
use subspy::connection::client::{request_shutdown, request_status};

#[test]
fn server_starts_and_accepts_connections() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    let statuses = request_status(repo.path()).expect("request_status should succeed");
    // Clean submodule => empty result
    assert!(
        statuses.is_empty(),
        "Expected no dirty submodules, got: {statuses:?}"
    );

    server.shutdown().expect("Server shutdown should succeed");
}

#[test]
fn server_shutdown_returns_ack() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    // request_shutdown returns Ok(()) when it receives ShutdownAck
    request_shutdown(repo.path()).expect("request_shutdown should return Ok");

    // The server thread should join cleanly
    server.shutdown().expect("Server thread should complete Ok");
}

#[test]
fn double_server_start_fails() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    let server = WatchServerHandle::start(repo.path());
    server.wait_until_ready();

    // Second watch() on the same path should fail with AddrInUse
    let result = subspy::connection::watch_server::watch(repo.path());
    assert!(result.is_err(), "Second watch() should fail");

    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("occupied") || err_msg.contains("AddrInUse") || err_msg.contains("address"),
        "Error should indicate address in use, got: {err_msg}"
    );

    server.shutdown().expect("Server shutdown should succeed");
}

#[test]
fn client_without_server_returns_error() {
    let mut repo = TestRepo::new();
    repo.add_submodule("sub1");

    // No server is running, so both client functions should fail
    let status_result = request_status(repo.path());
    assert!(
        status_result.is_err(),
        "request_status without server should fail"
    );

    let shutdown_result = request_shutdown(repo.path());
    assert!(
        shutdown_result.is_err(),
        "request_shutdown without server should fail"
    );
}
