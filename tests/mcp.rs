//! Smoke tests for the `subspy-mcp` binary. Each test launches the compiled
//! server and drives it over stdin/stdout the way an MCP client would.

mod common;

use std::{
    io::{BufRead as _, BufReader, Write as _},
    path::Path,
    process::{Child, ChildStdin, Command, ExitStatus, Stdio},
    sync::mpsc::{self, Receiver},
    time::{Duration, Instant},
};

use common::HarnessBuilder;
use pretty_assertions::assert_eq;
use serde_json::{Value, json};

/// How long to wait for any one response before failing the test.
const RESPONSE_TIMEOUT: Duration = Duration::from_secs(30);

/// How long the server may take to exit once the client disconnects.
const EXIT_TIMEOUT: Duration = Duration::from_secs(10);

/// A minimal MCP client driving one `subspy-mcp` process.
struct McpClient {
    child: Child,
    stdin: Option<ChildStdin>,
    /// stdout lines, read on a separate thread so a stuck server fails the
    /// test at [`RESPONSE_TIMEOUT`] instead of hanging it.
    lines: Receiver<String>,
    next_id: u64,
}

impl McpClient {
    /// Starts the server in `cwd` and completes the initialization handshake.
    fn start(cwd: &Path) -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_subspy-mcp"))
            .current_dir(cwd)
            .env("NO_COLOR", "1")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn subspy-mcp");
        let stdin = child.stdin.take();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        let (tx, lines) = mpsc::channel();
        std::thread::spawn(move || {
            for line in stdout.lines() {
                let Ok(line) = line else { break };
                if tx.send(line).is_err() {
                    break;
                }
            }
        });

        let mut client = Self {
            child,
            stdin,
            lines,
            next_id: 0,
        };
        let init = client.request(
            "initialize",
            &json!({
                "protocolVersion": "2025-11-25",
                "capabilities": {},
                "clientInfo": { "name": "subspy-tests", "version": "0" },
            }),
        );
        assert_eq!(init["serverInfo"]["name"], "subspy");
        client.send(&json!({ "jsonrpc": "2.0", "method": "notifications/initialized" }));
        client
    }

    fn send(&mut self, message: &Value) {
        let stdin = self.stdin.as_mut().unwrap();
        writeln!(stdin, "{message}").unwrap();
        stdin.flush().unwrap();
    }

    /// Sends a request and returns its `result`, skipping any notifications.
    /// Every line the server writes must parse as JSON-RPC.
    fn request(&mut self, method: &str, params: &Value) -> Value {
        self.next_id += 1;
        let id = self.next_id;
        self.send(&json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": params }));
        loop {
            let line = self
                .lines
                .recv_timeout(RESPONSE_TIMEOUT)
                .unwrap_or_else(|e| panic!("no response to {method}: {e}"));
            let mut message: Value = serde_json::from_str(&line).unwrap();
            if message["id"] != id {
                continue;
            }
            assert!(
                message.get("error").is_none(),
                "{method} failed: {}",
                message["error"]
            );
            return message["result"].take();
        }
    }

    fn call_tool(&mut self, name: &str, arguments: &Value) -> Value {
        self.request(
            "tools/call",
            &json!({ "name": name, "arguments": arguments }),
        )
    }

    /// Ends the session the way a client does, by closing stdin, and returns
    /// the server's exit status.
    fn close(mut self) -> ExitStatus {
        drop(self.stdin.take());
        let deadline = Instant::now() + EXIT_TIMEOUT;
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                return status;
            }
            assert!(
                Instant::now() < deadline,
                "server still running {EXIT_TIMEOUT:?} after the client disconnected"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

impl Drop for McpClient {
    /// Kills a server the test left running, such as after a failed assertion.
    fn drop(&mut self) {
        drop(self.stdin.take());
        if self.child.try_wait().ok().flatten().is_none() {
            let _ = self.child.kill();
        }
        let _ = self.child.wait();
    }
}

#[test]
fn serves_a_session_and_exits_cleanly() {
    let harness = HarnessBuilder::new().submodule("sub").build();
    let mut client = McpClient::start(harness.root().path());

    let result = client.call_tool("status", &json!({}));
    assert_eq!(result["isError"], false, "{result}");

    let status = client.close();
    assert!(status.success(), "server exited with {status}");
}

#[test]
fn a_failed_call_leaves_the_server_running() {
    let harness = HarnessBuilder::new().submodule("sub").build();
    let root = harness.root().path();
    let mut client = McpClient::start(root);

    let failed = client.call_tool("status", &json!({ "path": root.join("missing") }));
    assert_eq!(failed["isError"], true, "{failed}");

    let served = client.call_tool("status", &json!({}));
    assert_eq!(served["isError"], false, "{served}");
}
