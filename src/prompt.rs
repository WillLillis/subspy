use std::{borrow::Cow, io::BufReader, path::Path};

use git2::Repository;
use interprocess::local_socket::{Stream, traits::Stream as _};
use log::error;
use thiserror::Error;

use crate::{
    StatusSummary,
    connection::{
        BINCODE_CFG, ClientMessage, ServerMessage, ipc_name, read_full_message, write_full_message,
    },
    list::parse_gitmodules,
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

const DEFAULT_FORMAT: &str = "{dirty} {staged} {new_commits} {clean} {total}";

const PLACEHOLDERS: [&str; 5] = ["dirty", "staged", "new_commits", "clean", "total"];

/// Indices into [`PLACEHOLDERS`] for fields that require the total submodule count.
const IDX_CLEAN: usize = 3;
const IDX_TOTAL: usize = 4;

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
/// Returns `TemplateError` if the format string is invalid.
pub fn prompt(root_path: &Path, use_server: bool, format: Option<&str>) -> PromptResult<()> {
    let template = format.unwrap_or(DEFAULT_FORMAT);
    let used = validate_template(template, &PLACEHOLDERS)?;
    let need_total = used[IDX_CLEAN] || used[IDX_TOTAL];

    let (statuses, total) = if use_server {
        let Some(statuses) = try_get_statuses(root_path) else {
            let _ = spawn_daemon(root_path, None);
            return Ok(());
        };
        let total = if need_total {
            match parse_gitmodules(root_path) {
                Ok(entries) => entries.len(),
                Err(e) => {
                    error!("Failed to parse .gitmodules: {e}");
                    return Ok(());
                }
            }
        } else {
            0
        };
        (statuses, total)
    } else {
        let Ok(repo) = Repository::open(root_path) else {
            return Ok(());
        };
        let total = if need_total {
            repo.submodules().map(|s| s.len()).unwrap_or(0)
        } else {
            0
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

    let clean = total.saturating_sub(statuses.len()) as u32;
    let total = total as u32;

    let no_widths = [0; 5];
    let output = expand_template(
        template,
        &PLACEHOLDERS,
        |name| {
            let value = match name {
                "dirty" => dirty,
                "staged" => staged,
                "new_commits" => new_commits,
                "clean" => clean,
                "total" => total,
                _ => unreachable!("validated by validate_template"),
            };
            Cow::Owned(value.to_string())
        },
        &no_widths,
    );
    print!("{output}");
    Ok(())
}

/// Attempts a non-blocking connection to the watch server and retrieves
/// submodule statuses. Returns `None` if the server isn't running or
/// communication fails.
fn try_get_statuses(root_path: &Path) -> Option<Vec<(String, StatusSummary)>> {
    let name = ipc_name(root_path).ok()?;
    let conn = Stream::connect(name).ok()?;
    let mut conn = BufReader::new(conn);

    let status_req = ClientMessage::Status(std::process::id());
    let mut req_msg = [0; 8];
    let req_msg_len = bincode::encode_into_slice(&status_req, &mut req_msg, BINCODE_CFG).ok()?;
    write_full_message(&mut conn, &req_msg[..req_msg_len]).ok()?;

    let mut buffer = Vec::with_capacity(4096);
    loop {
        read_full_message(&mut conn, &mut buffer).ok()?;
        let (resp_msg, _): (ServerMessage, usize) =
            bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG).ok()?;
        match resp_msg {
            ServerMessage::Status(statuses) => return Some(statuses),
            ServerMessage::Indexing { .. } => {}
            ServerMessage::ShutdownAck | ServerMessage::DebugInfo(_) => {
                error!("Unexpected server message in prompt status request");
                return None;
            }
        }
    }
}
