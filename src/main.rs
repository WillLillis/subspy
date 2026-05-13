//! Thin entry point for the `subspy` binary. All logic lives in
//! [`subspy::entry`] so the `subspy-git` shim can share it.

use std::process::ExitCode;

fn main() -> ExitCode {
    subspy::entry::subspy_entry(std::env::args_os())
}
