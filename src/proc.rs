//! Cross-platform helpers for `std::process::Command` flag setup.
//!
//! Centralizes the Windows target  configuration and process creation flags used
//! used bythe daemon and shim-spawned git processes.

use std::process::Command;

/// A process ID as the platform represents it.
#[cfg(unix)]
pub type Pid = libc::pid_t;

/// A process ID as the platform represents it.
#[cfg(target_os = "windows")]
pub type Pid = u32;

#[cfg(target_os = "windows")]
mod windows_flags {
    // https://learn.microsoft.com/en-us/windows/win32/procthread/process-creation-flags
    /// Detaches the new process from its parent's console.
    pub(super) const DETACHED_PROCESS: u32 = 0x0000_0008;
    /// Starts a new process group with Ctrl+C disabled for its members.
    pub(super) const CREATE_NEW_PROCESS_GROUP: u32 = 0x0000_0200;
    /// Suppresses console window creation while preserving inherited stdio handles.
    pub(super) const CREATE_NO_WINDOW: u32 = 0x0800_0000;
}

/// Configures `cmd` to run as a fully detached background daemon.
#[cfg(unix)]
pub fn configure_detached_daemon(cmd: &mut Command) {
    use std::os::unix::process::CommandExt as _;
    // SAFETY: `setsid` is async-signal-safe.
    unsafe {
        cmd.pre_exec(|| {
            libc::setsid();
            Ok(())
        });
    }
}

/// Configures `cmd` to run as a fully detached background daemon.
///
/// Sets `DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP` so the child has
/// no console and survives the parent / Ctrl+C in the parent shell.
#[cfg(target_os = "windows")]
pub fn configure_detached_daemon(cmd: &mut Command) {
    use std::os::windows::process::CommandExt as _;
    use windows_flags::{CREATE_NEW_PROCESS_GROUP, DETACHED_PROCESS};
    cmd.creation_flags(DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP);
}

/// Configures `cmd` to run synchronously without popping a console window
/// when the parent is a GUI process (e.g. `GitExtensions` launching the shim).
///
/// On other platforms this is a `const` no-op. The Windows implementation sets
/// `CREATE_NO_WINDOW`.
#[cfg(not(target_os = "windows"))]
pub const fn configure_hidden_console(_cmd: &mut Command) {}

/// Configures `cmd` to run synchronously without popping a console window
/// when the parent is a GUI process (e.g. `GitExtensions` launching the shim).
///
/// Sets `CREATE_NO_WINDOW` so a console-subsystem child does not allocate
/// a fresh console while still inheriting any pipes the parent set up.
#[cfg(target_os = "windows")]
pub fn configure_hidden_console(cmd: &mut Command) {
    use std::os::windows::process::CommandExt as _;
    use windows_flags::CREATE_NO_WINDOW;
    cmd.creation_flags(CREATE_NO_WINDOW);
}

/// Sends `SIGTERM` to the process with ID `pid`.
///
/// # Errors
///
/// Returns [`std::io::Error`] if the signal cannot be sent.
///
/// # Panics
///
/// Panics if `pid` is not positive.
#[cfg(unix)]
pub fn terminate_process(pid: Pid) -> std::io::Result<()> {
    assert!(pid > 0, "invalid process ID {pid}");
    // SAFETY: `kill` has no memory-safety preconditions.
    if unsafe { libc::kill(pid, libc::SIGTERM) } == -1 {
        let error = std::io::Error::last_os_error();
        // If the process didn't already exit
        if error.raw_os_error() != Some(libc::ESRCH) {
            return Err(error);
        }
    }
    Ok(())
}

/// Terminates the process with ID `pid`.
///
/// # Errors
///
/// Returns [`std::io::Error`] if the process cannot be opened or terminated.
///
/// # Panics
///
/// Panics if closing the process handle fails.
#[cfg(target_os = "windows")]
pub fn terminate_process(pid: Pid) -> std::io::Result<()> {
    use windows_sys::Win32::{
        Foundation::{CloseHandle, ERROR_INVALID_PARAMETER},
        System::Threading::{OpenProcess, PROCESS_TERMINATE, TerminateProcess},
    };

    /// How `OpenProcess` reports the ID of a process that no longer exists.
    const NO_SUCH_PROCESS: i32 = ERROR_INVALID_PARAMETER.cast_signed();

    // SAFETY: `OpenProcess` has no memory-safety preconditions.
    let process = unsafe { OpenProcess(PROCESS_TERMINATE, 0, pid) };
    if process.is_null() {
        let error = std::io::Error::last_os_error();
        if error.raw_os_error() == Some(NO_SUCH_PROCESS) {
            return Ok(());
        }
        return Err(error);
    }
    // SAFETY: `OpenProcess` returned a non-null handle, so it is open with the
    // `PROCESS_TERMINATE` access requested above.
    let result = if unsafe { TerminateProcess(process, 1) } == 0 {
        Err(std::io::Error::last_os_error())
    } else {
        Ok(())
    };
    // SAFETY: `process` is the open handle `OpenProcess` returned, and this is the
    // only place that closes it.
    let closed = unsafe { CloseHandle(process) };
    assert!(
        closed != 0,
        "closing the process handle failed: {}",
        std::io::Error::last_os_error()
    );
    result
}
