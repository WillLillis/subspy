//! Cross-platform helpers for `std::process::Command` flag setup.
//!
//! Keeps the `#[cfg(target_os = "windows")]` and magic Windows process
//! creation flag values in one place so callers don't repeat them.

use std::process::Command;

#[cfg(target_os = "windows")]
mod windows_flags {
    // https://learn.microsoft.com/en-us/windows/win32/procthread/process-creation-flags
    /// The new process does not inherit its parent's console.
    pub(super) const DETACHED_PROCESS: u32 = 0x0000_0008;
    /// The new process is the root of a new process group. CTRL+C signals
    /// will be disabled for all processes within the new group.
    pub(super) const CREATE_NEW_PROCESS_GROUP: u32 = 0x0000_0200;
    /// The new process runs without a console window, even from a GUI parent.
    /// Inherited stdio handles still work.
    pub(super) const CREATE_NO_WINDOW: u32 = 0x0800_0000;
}

/// Configures `cmd` to run as a fully detached background daemon.
///
/// On other platforms this is a no-op (and `const`); the Windows
/// implementation sets `DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP`.
#[cfg(not(target_os = "windows"))]
pub const fn configure_detached_daemon(_cmd: &mut Command) {}

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
/// On other platforms this is a no-op (and `const`); the Windows
/// implementation sets `CREATE_NO_WINDOW`.
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
