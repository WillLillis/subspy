//! Records the version string `--version` prints, including the commit it was
//! built from when that is knowable.

use std::{env, path::Path, process::Command};

fn main() {
    let package = env::var("CARGO_PKG_VERSION").expect("cargo sets CARGO_PKG_VERSION");
    let version = match git(&["rev-parse", "--short", "HEAD"]) {
        Some(commit) => format!("{package} ({commit})"),
        None => package,
    };
    println!("cargo::rustc-env=SUBSPY_VERSION={version}");

    // Keep the recorded commit fresh.
    for name in ["HEAD", "refs/heads"] {
        let Some(path) = git(&["rev-parse", "--git-path", name]) else {
            continue;
        };
        if Path::new(&path).exists() {
            println!("cargo::rerun-if-changed={path}");
        }
    }
}

fn git(args: &[&str]) -> Option<String> {
    let out = Command::new("git").args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8(out.stdout).ok()?.trim().to_string();
    (!text.is_empty()).then_some(text)
}
