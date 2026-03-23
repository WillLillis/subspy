use std::{
    borrow::Cow,
    io::BufReader,
    path::Path,
    time::{Duration, Instant},
};

use git2::Repository;
use interprocess::local_socket::{Stream, traits::Stream as _};
use thiserror::Error;

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ClientRequest, ServerMessage, client::server_not_started,
        ipc_name, read_full_message, write_full_message,
    },
    status::compute_local_statuses,
    template::{TemplateError, expand_template, validate_template},
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

/// Indices into [`PLACEHOLDERS`] for fields that require the total submodule count.
const IDX_CLEAN: usize = 3;
const IDX_TOTAL: usize = 4;

/// Pre-computed `used` array for [`DEFAULT_FORMAT`].
const DEFAULT_USED: [bool; 5] = [true; 5];

/// Outputs a formatted summary of submodule statuses for shell prompt
/// integration.
///
/// When `use_server` is true, attempts a non-blocking connection to the watch
/// server. If no server is running, spawns one in the background and exits
/// with no output so the prompt isn't blocked.
///
/// When `use_server` is false, computes status locally via libgit2.
///
/// # Errors
///
/// Returns `TemplateError` if the format string is invalid. Any non `TemplateError` error
/// is intentionally swallowed in this function. We cannot display runtime errors in the prompt,
/// and garbage "placeholder" data is worst than no data.
#[allow(clippy::missing_panics_doc)]
pub fn prompt(
    root_path: &Path,
    use_server: bool,
    format: Option<&str>,
    timeout: Duration,
) -> PromptResult<()> {
    // Skip validation for the default template. It's verified and `DEFAULT_USED`
    // captures which placeholders are used.
    let (template, used) = match format {
        Some(t) => (t, validate_template(t, &PLACEHOLDERS)?),
        None => (DEFAULT_FORMAT, DEFAULT_USED),
    };
    // The `repo.submodules()` can be incredibly expensive, so avoid it if the template doesn't
    // require it
    let need_total = used[IDX_CLEAN] || used[IDX_TOTAL];

    let (statuses, total) = if use_server {
        let Some((statuses, total)) = try_get_statuses(root_path, timeout) else {
            return Ok(());
        };
        (statuses, Some(total as usize))
    } else {
        let Ok(repo) = Repository::open(root_path) else {
            return Ok(());
        };
        let total = if need_total {
            let Ok(subs) = repo.submodules() else {
                return Ok(());
            };
            Some(subs.len())
        } else {
            None
        };
        let Ok(statuses) = compute_local_statuses(root_path, &repo) else {
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
            || status.contains(StatusSummary::LOCK_FAILURE)
        {
            dirty += 1;
        }
        if status.contains(StatusSummary::STAGED) {
            staged += 1;
        }
        if status.contains(StatusSummary::NEW_COMMITS) {
            new_commits += 1;
        }
    }

    let no_widths = [0; 5];
    let output = expand_template(
        template,
        &PLACEHOLDERS,
        |name| {
            let value: u32 = match name {
                "dirty" => dirty,
                "staged" => staged,
                "new_commits" => new_commits,
                "clean" => {
                    let total = total.expect("need_total guards this path");
                    total.saturating_sub(statuses.len()) as u32
                }
                "total" => {
                    let total = total.expect("need_total guards this path");
                    total as u32
                }
                _ => unreachable!("validated by validate_template"),
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
    let name = ipc_name(root_path).ok()?;

    let mut spawned = false;
    let conn = loop {
        match Stream::connect(name.clone()) {
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

    let remaining = deadline.saturating_duration_since(Instant::now());
    conn.set_recv_timeout(Some(remaining)).ok()?;
    let mut conn = BufReader::new(conn);

    let req = ClientRequest::new(ClientMessage::Status(std::process::id()));
    let mut req_msg = [0; 9];
    let req_msg_len = bincode::encode_into_slice(&req, &mut req_msg, BINCODE_CFG).ok()?;
    write_full_message(&mut conn, &req_msg[..req_msg_len]).ok()?;

    let mut buffer = Vec::with_capacity(4096);
    loop {
        read_full_message(&mut conn, &mut buffer).ok()?;
        let (resp_msg, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG).ok()?;
        match resp_msg {
            ServerMessage::Status { statuses, total } => return Some((statuses, total)),
            ServerMessage::Indexing { .. } => {}
            ServerMessage::VersionMismatch { .. }
            | ServerMessage::ShutdownAck
            | ServerMessage::DebugInfo(_) => {
                return None;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_format_matches_precomputed_used() {
        let used = validate_template(DEFAULT_FORMAT, &PLACEHOLDERS).unwrap();
        assert_eq!(used, DEFAULT_USED);
    }
}
