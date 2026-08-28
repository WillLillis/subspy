//! Daemon lifecycle: spawning the background watch server process.

use std::path::{Path, PathBuf};

use thiserror::Error;

use crate::connection::IpcError;

pub type WatchResult<T> = Result<T, WatchError>;

#[derive(Error, Debug)]
pub enum WatchError {
    #[error(transparent)]
    BincodeEncode(#[from] bincode::error::EncodeError),
    #[error(transparent)]
    BincodeDecode(#[from] bincode::error::DecodeError),
    #[error(transparent)]
    Ipc(#[from] IpcError),
    #[error(transparent)]
    FileWatch(#[from] notify::Error),
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    Receive(#[from] crossbeam_channel::RecvError),
    #[error("{} is not a submodule gitlink (its gitdir is not under .git/modules/)", .0.display())]
    NotSubmoduleGitlink(PathBuf),
    #[error("submodule name in {} is not valid UTF-8: {error}", path.display())]
    NonUtf8SubmoduleName {
        path: PathBuf,
        error: std::str::Utf8Error,
    },
}

/// Spawns the watch server as a fully detached background process for `path`.
///
/// The server is started by re-invoking the current executable with
/// `--subspy-internal start <path> --foreground`. The sentinel makes the
/// receiving process run subspy's CLI even when `current_exe()` resolves
/// to the `subspy-git` shim.
///
/// # Errors
///
/// Returns `std::io::Error` if the current executable path cannot be determined
/// or the child process cannot be spawned.
pub fn spawn_daemon(path: &Path, log_level: Option<&str>) -> std::io::Result<()> {
    let exe = std::env::current_exe()?;
    let mut cmd = build_daemon_command(&exe, path, log_level);
    crate::proc::configure_detached_daemon(&mut cmd);
    cmd.spawn()?;
    Ok(())
}

/// Builds the argv-pinned `Command` for the daemon child. Prepends
/// [`INTERNAL_FLAG`] so the receiving process runs subspy's CLI even
/// if `current_exe()` resolved to the `subspy-git` shim.
///
/// [`INTERNAL_FLAG`]: crate::entry::INTERNAL_FLAG
fn build_daemon_command(
    exe: &Path,
    repo_path: &Path,
    log_level: Option<&str>,
) -> std::process::Command {
    let mut cmd = std::process::Command::new(exe);
    cmd.arg(crate::entry::INTERNAL_FLAG)
        .arg("start")
        .arg(repo_path)
        .arg("--foreground")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if let Some(level) = log_level {
        cmd.args(["--log-level", level]);
    }
    cmd
}

#[cfg(test)]
mod daemon_command_tests {
    use super::build_daemon_command;
    use crate::entry::INTERNAL_FLAG;
    use std::ffi::OsStr;
    use std::path::Path;

    use pretty_assertions::assert_eq;

    #[test]
    fn argv_starts_with_internal_flag_then_start_path_foreground() {
        let cmd = build_daemon_command(Path::new("/path/to/subspy"), Path::new("/repo/root"), None);
        let args: Vec<Option<&str>> = cmd.get_args().map(OsStr::to_str).collect();
        assert_eq!(args[0], Some(INTERNAL_FLAG));
        assert_eq!(args[1], Some("start"));
        assert_eq!(args[2], Some("/repo/root"));
        assert_eq!(args[3], Some("--foreground"));
        assert_eq!(args.len(), 4, "no extra args when log_level is None");
    }

    #[test]
    fn log_level_appended_when_provided() {
        let cmd = build_daemon_command(Path::new("/exe"), Path::new("/repo"), Some("debug"));
        let args: Vec<Option<&str>> = cmd.get_args().map(OsStr::to_str).collect();
        assert_eq!(args.last().copied().flatten(), Some("debug"));
        assert_eq!(args[args.len() - 2], Some("--log-level"));
    }
}
