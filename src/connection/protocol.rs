//! IPC message types exchanged between the client and the watch server, plus
//! the wire-format stability tests that pin their byte layout.

use bincode::{BorrowDecode, Encode};

use crate::StatusSummary;

use super::IPC_VERSION;

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub struct ClientRequest {
    pub version: u8,
    pub message: ClientMessage,
}

impl ClientRequest {
    #[must_use]
    pub const fn new(message: ClientMessage) -> Self {
        Self {
            version: IPC_VERSION,
            message,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ClientMessage {
    Reindex { pid: u32, replace_watchers: bool },
    Shutdown,
    Status(u32),
    Debug,
}

/// The watch server's internal state snapshot, sent as the
/// `ServerMessage::DebugInfo` payload in response to a debug request.
#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub struct DebugState {
    pub server_pid: u32,
    pub rayon_threads: u32,
    pub progress_subscribers: Option<Vec<u32>>,
    pub watcher_count: u32,
    pub watched_paths: Vec<(String, String, u32)>,
    pub skip_set: Vec<String>,
    pub root_rebasing: bool,
    pub root_path: String,
    pub socket_name: String,
    pub submodule_statuses: Option<Vec<(String, StatusSummary)>>,
    /// In-flight rayon tasks: `(relative_path, state)` where state is
    /// "active", "active (cancelling)", "dirty", or "dirty (cancelling)"
    pub in_flight: Option<Vec<(String, String)>>,
    /// Progress queues keyed by client PID: `(pid, [(curr, total)])`
    #[expect(clippy::type_complexity)]
    pub progress_queues: Option<Vec<(u32, Vec<(u32, u32)>)>>,
    /// The last watcher error that triggered a reindex, if any
    pub last_watcher_error: Option<String>,
    /// Non-recursive tripwire watches on submodule ancestor directories:
    /// `(watch_path, pending_event_count)`.
    pub tripwires: Vec<(String, u32)>,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, BorrowDecode)]
pub enum ServerMessage {
    Status {
        statuses: Vec<(String, StatusSummary)>,
        total: u32,
    },
    Indexing {
        curr: u32,
        total: u32,
    },
    ShutdownAck,
    DebugInfo(Box<DebugState>),
    VersionMismatch {
        server_version: u8,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::connection::BINCODE_CFG;

    #[test]
    fn unit_variant_sizes() {
        let cases: &[(&str, Vec<u8>)] = &[
            (
                "ServerMessage::ShutdownAck",
                bincode::encode_to_vec(ServerMessage::ShutdownAck, BINCODE_CFG).unwrap(),
            ),
            (
                "ClientMessage::Shutdown",
                bincode::encode_to_vec(ClientMessage::Shutdown, BINCODE_CFG).unwrap(),
            ),
            (
                "ClientMessage::Debug",
                bincode::encode_to_vec(ClientMessage::Debug, BINCODE_CFG).unwrap(),
            ),
        ];

        for (name, encoded) in cases {
            assert_eq!(
                encoded.len(),
                4,
                "Expected {name} to encode to 4 bytes, got {} bytes",
                encoded.len(),
            );
        }
    }

    /// Verifies that the worst-case encoded sizes of `ClientRequest` and
    /// `ServerMessage::Indexing` / `VersionMismatch` fit within the stack
    /// buffers used to encode/decode them in `client.rs` and `client_handler.rs`.
    #[test]
    fn max_message_sizes() {
        // ClientRequest wrapping Reindex with max u32 is the largest request
        let reindex_max = bincode::encode_to_vec(
            ClientRequest::new(ClientMessage::Reindex {
                pid: u32::MAX,
                replace_watchers: true,
            }),
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            reindex_max.len() <= 10,
            "ClientRequest(Reindex(u32::MAX, true)) encoded to {} bytes, exceeds buffer size of 10",
            reindex_max.len(),
        );

        // ClientRequest wrapping Status with max u32
        let status_max = bincode::encode_to_vec(
            ClientRequest::new(ClientMessage::Status(u32::MAX)),
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            status_max.len() <= 10,
            "ClientRequest(Status(u32::MAX)) encoded to {} bytes, exceeds buffer size of 10",
            status_max.len(),
        );

        // ServerMessage::Indexing with max values (used in try_send_progress_update)
        let indexing_max = bincode::encode_to_vec(
            ServerMessage::Indexing {
                curr: u32::MAX,
                total: u32::MAX,
            },
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            indexing_max.len() <= 12,
            "ServerMessage::Indexing(u32::MAX, u32::MAX) encoded to {} bytes, exceeds buffer size of 12",
            indexing_max.len(),
        );

        // ServerMessage::VersionMismatch with max u8
        let mismatch_max = bincode::encode_to_vec(
            ServerMessage::VersionMismatch {
                server_version: u8::MAX,
            },
            BINCODE_CFG,
        )
        .unwrap();
        assert!(
            mismatch_max.len() <= 5,
            "ServerMessage::VersionMismatch(u8::MAX) encoded to {} bytes, exceeds buffer size of 5",
            mismatch_max.len(),
        );
    }

    /// Asserts that every fixed-size IPC message fits within
    /// [`MAX_FIXED_MSG_LEN`], ensuring [`write_full_message`] uses the
    /// single-write fast path for all of them.
    #[test]
    fn fixed_messages_fit_inline_write_buffer() {
        use crate::connection::transport::MAX_FIXED_MSG_LEN;

        let fixed_messages: &[(&str, Vec<u8>)] = &[
            (
                "ClientRequest(Reindex)",
                bincode::encode_to_vec(
                    ClientRequest::new(ClientMessage::Reindex {
                        pid: u32::MAX,
                        replace_watchers: true,
                    }),
                    BINCODE_CFG,
                )
                .unwrap(),
            ),
            (
                "ClientRequest(Shutdown)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Shutdown), BINCODE_CFG)
                    .unwrap(),
            ),
            (
                "ClientRequest(Status)",
                bincode::encode_to_vec(
                    ClientRequest::new(ClientMessage::Status(u32::MAX)),
                    BINCODE_CFG,
                )
                .unwrap(),
            ),
            (
                "ClientRequest(Debug)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Debug), BINCODE_CFG)
                    .unwrap(),
            ),
            (
                "ServerMessage::Indexing",
                bincode::encode_to_vec(
                    ServerMessage::Indexing {
                        curr: u32::MAX,
                        total: u32::MAX,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
            ),
            (
                "ServerMessage::ShutdownAck",
                bincode::encode_to_vec(ServerMessage::ShutdownAck, BINCODE_CFG).unwrap(),
            ),
            (
                "ServerMessage::VersionMismatch",
                bincode::encode_to_vec(
                    ServerMessage::VersionMismatch {
                        server_version: u8::MAX,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
            ),
        ];

        for (name, encoded) in fixed_messages {
            assert!(
                encoded.len() <= MAX_FIXED_MSG_LEN,
                "{name} encoded to {} bytes, exceeds MAX_FIXED_MSG_LEN ({MAX_FIXED_MSG_LEN}). \
                 Increase the constant or the message will use two syscalls.",
                encoded.len(),
            );
        }
    }

    #[test]
    fn client_request_round_trip() {
        let request = ClientRequest::new(ClientMessage::Status(42));
        let encoded = bincode::encode_to_vec(&request, BINCODE_CFG).unwrap();
        let (decoded, _): (ClientRequest, usize) =
            bincode::borrow_decode_from_slice(&encoded, BINCODE_CFG).unwrap();
        assert_eq!(request, decoded);
    }

    #[test]
    fn version_mismatch_round_trip() {
        let msg = ServerMessage::VersionMismatch { server_version: 7 };
        let encoded = bincode::encode_to_vec(&msg, BINCODE_CFG).unwrap();
        let (decoded, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&encoded, BINCODE_CFG).unwrap();
        assert_eq!(msg, decoded);
    }

    /// Hardcoded byte sequences for every IPC message variant. If any of these
    /// change, the wire format has broken: bump `IPC_VERSION` and update the
    /// expected byte slices to match the actual bytes shown in the failure output.
    #[test]
    #[allow(clippy::too_many_lines)]
    fn wire_format_stability() {
        use crate::{StatusSummary, connection::DebugState};

        let cases: &[(&str, Vec<u8>, &[u8])] = &[
            // -- ClientRequest variants --
            (
                "ClientRequest(Reindex { pid: 1, replace_watchers: false })",
                bincode::encode_to_vec(
                    ClientRequest::new(ClientMessage::Reindex {
                        pid: 1,
                        replace_watchers: false,
                    }),
                    BINCODE_CFG,
                )
                .unwrap(),
                // version(0) | variant(0,0,0,0) | pid(1,0,0,0) | bool(0)
                &[0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
            ),
            (
                "ClientRequest(Shutdown)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Shutdown), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(1,0,0,0)
                &[0, 1, 0, 0, 0],
            ),
            (
                "ClientRequest(Status(42))",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Status(42)), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(2,0,0,0) | pid(42,0,0,0)
                &[0, 2, 0, 0, 0, 42, 0, 0, 0],
            ),
            (
                "ClientRequest(Debug)",
                bincode::encode_to_vec(ClientRequest::new(ClientMessage::Debug), BINCODE_CFG)
                    .unwrap(),
                // version(0) | variant(3,0,0,0)
                &[0, 3, 0, 0, 0],
            ),
            // -- ServerMessage variants --
            (
                "ServerMessage::Status(empty, total=0)",
                bincode::encode_to_vec(
                    ServerMessage::Status {
                        statuses: vec![],
                        total: 0,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(0,0,0,0) | vec_len(0,0,0,0,0,0,0,0) | total(0,0,0,0)
                &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            ),
            (
                "ServerMessage::Status(one entry, total=3)",
                bincode::encode_to_vec(
                    ServerMessage::Status {
                        statuses: vec![("sub".to_string(), StatusSummary::MODIFIED_CONTENT)],
                        total: 3,
                    },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(0,0,0,0) | vec_len(1,0,0,0,0,0,0,0)
                // | str_len(3,0,0,0,0,0,0,0) | "sub" | flags(1)
                // | total(3,0,0,0)
                &[
                    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, b's', b'u', b'b',
                    1, 3, 0, 0, 0,
                ],
            ),
            (
                "ServerMessage::Indexing { curr: 5, total: 10 }",
                bincode::encode_to_vec(ServerMessage::Indexing { curr: 5, total: 10 }, BINCODE_CFG)
                    .unwrap(),
                // variant(1,0,0,0) | curr(5,0,0,0) | total(10,0,0,0)
                &[1, 0, 0, 0, 5, 0, 0, 0, 10, 0, 0, 0],
            ),
            (
                "ServerMessage::ShutdownAck",
                bincode::encode_to_vec(ServerMessage::ShutdownAck, BINCODE_CFG).unwrap(),
                // variant(2,0,0,0)
                &[2, 0, 0, 0],
            ),
            (
                "ServerMessage::DebugInfo(empty)",
                bincode::encode_to_vec(
                    ServerMessage::DebugInfo(Box::new(DebugState {
                        server_pid: 0,
                        rayon_threads: 0,
                        progress_subscribers: None,
                        watcher_count: 0,
                        watched_paths: vec![],
                        skip_set: vec![],
                        root_rebasing: false,
                        root_path: String::new(),
                        socket_name: String::new(),
                        submodule_statuses: None,
                        in_flight: None,
                        progress_queues: None,
                        last_watcher_error: None,
                        tripwires: vec![],
                    })),
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(3,0,0,0)
                // | server_pid(0,0,0,0) | rayon_threads(0,0,0,0)
                // | progress_subscribers:None(0)
                // | watcher_count(0,0,0,0)
                // | watched_paths:empty(0,0,0,0,0,0,0,0)
                // | skip_set:empty(0,0,0,0,0,0,0,0)
                // | root_rebasing:false(0)
                // | root_path:""(0,0,0,0,0,0,0,0)
                // | socket_name:""(0,0,0,0,0,0,0,0)
                // | submodule_statuses:None(0)
                // | in_flight:None(0) | progress_queues:None(0)
                // | last_watcher_error:None(0)
                // | tripwires:empty(0,0,0,0,0,0,0,0)
                &[
                    3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                ],
            ),
            (
                "ServerMessage::VersionMismatch { server_version: 0 }",
                bincode::encode_to_vec(
                    ServerMessage::VersionMismatch { server_version: 0 },
                    BINCODE_CFG,
                )
                .unwrap(),
                // variant(4,0,0,0) | version(0)
                &[4, 0, 0, 0, 0],
            ),
        ];

        for (name, actual, expected) in cases {
            assert_eq!(
                actual, expected,
                "Wire format changed for {name}! \
                 If this is intentional, bump IPC_VERSION and update the expected bytes."
            );
        }
    }
}
