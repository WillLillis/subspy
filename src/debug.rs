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
        writeln!(f, "Root rebasing: {}", self.root_rebasing)?;
        writeln!(f, "Watcher count: {}", self.watcher_count)?;
        write!(f, "Progress subscribers: ")?;
        if self.progress_subscribers.is_empty() {
            writeln!(f, "(none)")?;
        } else {
            let pids: Vec<String> = self
                .progress_subscribers
                .iter()
                .map(ToString::to_string)
                .collect();
            writeln!(f, "{}", pids.join(", "))?;
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
        if self.in_flight.is_empty() {
            writeln!(f, "  (none)")?;
        } else {
            for (path, task_state) in &self.in_flight {
                writeln!(f, "  {path}: {task_state}")?;
            }
        }

        writeln!(f, "\nProgress queues:")?;
        if self.progress_queues.is_empty() {
            writeln!(f, "  (none)")?;
        } else {
            for (pid, updates) in &self.progress_queues {
                writeln!(f, "  PID {pid}: {} pending update(s)", updates.len())?;
                for (curr, total) in updates {
                    writeln!(f, "    {curr}/{total}")?;
                }
            }
        }

        writeln!(f, "\nSubmodule statuses:")?;
        if self.submodule_statuses.is_empty() {
            write!(f, "  (none)")?;
        } else {
            let last_idx = self.submodule_statuses.len() - 1;
            for (i, (path, status)) in self.submodule_statuses.iter().enumerate() {
                if i == last_idx {
                    write!(f, "  {path}: {status}")?;
                } else {
                    writeln!(f, "  {path}: {status}")?;
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
