use std::{fmt, path::Path};

use thiserror::Error;

use crate::connection::{DebugState, client::request_debug};

pub type DebugResult<T> = Result<T, DebugError>;

#[derive(Debug, Error)]
pub enum DebugError {
    #[error(transparent)]
    BincodeEncode(#[from] bincode::error::EncodeError),
    #[error(transparent)]
    BincodeDecode(#[from] bincode::error::DecodeError),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    VersionMismatch(#[from] crate::connection::VersionMismatchError),
}

/// Issues a debug state request to the watch server for `root_path` and prints
/// the result.
///
/// # Errors
///
/// Returns `Err` if communication with the watch server fails.
pub fn debug(root_path: &Path) -> DebugResult<()> {
    let state = request_debug(root_path)?;
    println!("{state}");
    Ok(())
}

impl fmt::Display for DebugState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Server PID: {}", self.server_pid)?;
        writeln!(f, "Worker threads: {}", self.rayon_threads)?;
        writeln!(f, "Root path: {}", self.root_path)?;
        writeln!(f, "Socket: {}", self.socket_name)?;
        writeln!(f, "Root rebasing: {}", self.root_rebasing)?;
        writeln!(f, "Watcher count: {}", self.watcher_count)?;
        write!(f, "Progress subscribers: ")?;
        match &self.progress_subscribers {
            None => writeln!(f, "WARNING: mutex locked, could not read")?,
            Some(subs) if subs.is_empty() => writeln!(f, "(none)")?,
            Some(subs) => {
                let pids: Vec<String> = subs.iter().map(ToString::to_string).collect();
                writeln!(f, "{}", pids.join(", "))?;
            }
        }

        writeln!(f, "\nWatched paths:")?;
        if self.watched_paths.is_empty() {
            writeln!(f, "  (none)")?;
        } else {
            for (relative, watch_path, pending) in &self.watched_paths {
                writeln!(
                    f,
                    "  {} -> {watch_path} ({pending} pending events)",
                    if relative.is_empty() {
                        "(root)"
                    } else {
                        relative
                    }
                )?;
            }
        }

        writeln!(f, "\nSkip set:")?;
        if self.skip_set.is_empty() {
            writeln!(f, "  (none)")?;
        } else {
            for path in &self.skip_set {
                writeln!(f, "  {path}")?;
            }
        }

        writeln!(f, "\nIn-flight tasks:")?;
        match &self.in_flight {
            None => writeln!(f, "  WARNING: mutex locked, could not read")?,
            Some(tasks) if tasks.is_empty() => writeln!(f, "  (none)")?,
            Some(tasks) => {
                for (path, task_state) in tasks {
                    writeln!(f, "  {path}: {task_state}")?;
                }
            }
        }

        writeln!(f, "\nProgress queues:")?;
        match &self.progress_queues {
            None => writeln!(f, "  WARNING: mutex locked, could not read")?,
            Some(queues) if queues.is_empty() => writeln!(f, "  (none)")?,
            Some(queues) => {
                for (pid, updates) in queues {
                    writeln!(f, "  PID {pid}: {} pending update(s)", updates.len())?;
                    for (curr, total) in updates {
                        writeln!(f, "    {curr}/{total}")?;
                    }
                }
            }
        }

        writeln!(f, "\nSubmodule statuses:")?;
        match &self.submodule_statuses {
            None => write!(f, "  WARNING: mutex locked, could not read")?,
            Some(statuses) if statuses.is_empty() => write!(f, "  (none)")?,
            Some(statuses) => {
                let last_idx = statuses.len() - 1;
                for (i, (path, status)) in statuses.iter().enumerate() {
                    if i == last_idx {
                        write!(f, "  {path}: {status}")?;
                    } else {
                        writeln!(f, "  {path}: {status}")?;
                    }
                }
            }
        }

        writeln!(f, "\n\nLast watcher error:")?;
        match self.last_watcher_error {
            Some(ref err) => write!(f, "  {err}")?,
            None => write!(f, "  (none)")?,
        }

        Ok(())
    }
}
