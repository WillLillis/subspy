//! The `prompt` subcommand: outputs a compact submodule status summary
//! for shell prompt integration. Designed to be fast and silent on errors.

use std::{
    borrow::Cow,
    io::BufReader,
    path::Path,
    time::{Duration, Instant},
};

use thiserror::Error;

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ClientRequest, ServerMessage, client::server_not_started,
        ipc_connect, ipc_socket_path, read_full_message, set_recv_timeout,
        write_full_message_fixed,
    },
    git::parse_gitmodules,
    status::compute_local_statuses,
    template::{Template, TemplateError},
    watch::spawn_daemon,
};

pub type PromptResult<T> = Result<T, PromptError>;

#[derive(Error, Debug)]
pub enum PromptError {
    #[error(transparent)]
    Template(#[from] TemplateError),
}

/// The format string used when the user doesn't provide one.
const DEFAULT_FORMAT: &str = "{dirty} {staged} {new_commits} {clean} {total}";

const PLACEHOLDERS: [&str; 5] = ["dirty", "staged", "new_commits", "clean", "total"];

/// Outputs a formatted summary of submodule statuses for shell prompt
/// integration.
///
/// With `use_server`, waits up to `timeout` for a server response, spawning the
/// server when necessary. Timeout and communication failures produce no output.
///
/// Without `use_server`, computes status locally via libgit2.
///
/// # Errors
///
/// Returns [`TemplateError`] if the format string is invalid. Runtime failures
/// are suppressed because prompt output must remain silent.
pub fn prompt(
    root_path: &Path,
    use_server: bool,
    format: Option<&str>,
    timeout: Duration,
) -> PromptResult<()> {
    let template = Template::parse(format.unwrap_or(DEFAULT_FORMAT), &PLACEHOLDERS)?;
    let (statuses, total) = if use_server {
        let Some((statuses, total)) = try_get_statuses(root_path, timeout) else {
            return Ok(());
        };
        (statuses, total as usize)
    } else {
        let Ok(gitmodule_entries) = parse_gitmodules(root_path) else {
            return Ok(());
        };
        let total = gitmodule_entries.len();
        let Ok(statuses) = compute_local_statuses(root_path) else {
            return Ok(());
        };
        (statuses, total)
    };

    let mut dirty = 0u32;
    let mut staged = 0u32;
    let mut new_commits = 0u32;

    for (_, status) in &statuses {
        if status.contains(StatusSummary::MODIFIED_CONTENT)
            || status.contains(StatusSummary::UNTRACKED_CONTENT)
            || status.contains(StatusSummary::UNREADABLE)
        {
            dirty += 1;
        }
        if status.contains(StatusSummary::STAGED) || status.contains(StatusSummary::STAGED_NEW) {
            staged += 1;
        }
        if status.contains(StatusSummary::NEW_COMMITS) {
            new_commits += 1;
        }
    }

    let no_widths = [0; 5];
    let output = template.expand(
        |name| {
            let value: u32 = match name {
                "dirty" => dirty,
                "staged" => staged,
                "new_commits" => new_commits,
                "clean" => total.saturating_sub(statuses.len()) as u32,
                "total" => total as u32,
                _ => unreachable!("validated by Template::parse"),
            };
            Cow::Owned(value.to_string())
        },
        &no_widths,
    );
    print!("{output}");
    Ok(())
}

/// Connects to the watch server and retrieves submodule statuses. If no
/// server is running, spawns one and retries until connected or `timeout`
/// is exceeded. Returns `None` if the timeout expires or communication fails.
fn try_get_statuses(
    root_path: &Path,
    timeout: Duration,
) -> Option<(Vec<(String, StatusSummary)>, u32)> {
    let deadline = Instant::now() + timeout;
    let sock_path = ipc_socket_path(root_path);

    let mut spawned = false;
    let conn = loop {
        match ipc_connect(&sock_path) {
            Ok(conn) => break conn,
            Err(e) if server_not_started(&e) => {
                if !spawned {
                    let _ = spawn_daemon(root_path, None);
                    spawned = true;
                }
                if Instant::now() >= deadline {
                    return None;
                }
                std::thread::yield_now();
            }
            Err(_) => return None,
        }
    };

    let mut conn = BufReader::new(conn);

    let req = ClientRequest::new(ClientMessage::Status(std::process::id()));
    let mut req_msg = [0; 9];
    let req_msg_len = bincode::encode_into_slice(&req, &mut req_msg, BINCODE_CFG).ok()?;
    write_full_message_fixed(&mut conn, &req_msg[..req_msg_len]).ok()?;

    // Set the socket timeout once to avoid a `setsockopt` syscall per read. The
    // deadline check prevents another read after the budget expires, so only the
    // current read can overrun it.
    let remaining = deadline.saturating_duration_since(Instant::now());
    set_recv_timeout(conn.get_ref(), Some(remaining)).ok()?;

    let mut buffer = Vec::with_capacity(4096);
    let result = loop {
        if Instant::now() >= deadline {
            break None;
        }
        read_full_message(&mut conn, &mut buffer).ok()?;
        let (resp_msg, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG).ok()?;
        match resp_msg {
            ServerMessage::Status { statuses, total } => break Some((statuses, total)),
            ServerMessage::Indexing { .. } => {}
            ServerMessage::VersionMismatch { .. }
            | ServerMessage::ShutdownAck
            | ServerMessage::DebugInfo(_) => {
                break None;
            }
        }
    };

    let _ = set_recv_timeout(conn.get_ref(), None);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_format_is_valid() {
        Template::parse(DEFAULT_FORMAT, &PLACEHOLDERS).unwrap();
    }
}
