//! End-to-end tests for the `subspy-git` shim binary. Each test invokes
//! the compiled shim (via `CARGO_BIN_EXE_subspy-git`) and compares its
//! output / exit code against real `git`, exercising the "intercept
//! when possible, forward to git otherwise" contract.

use std::process::{Command, Output};
use tempfile::TempDir;

const fn shim_path() -> &'static str {
    env!("CARGO_BIN_EXE_subspy-git")
}

fn run(program: &str, cwd: &std::path::Path, args: &[&str]) -> Output {
    Command::new(program)
        .args(args)
        .current_dir(cwd)
        .env("NO_COLOR", "1")
        .output()
        .expect("spawn failed")
}

fn assert_outputs_match(cwd: &std::path::Path, args: &[&str]) {
    let real = run("git", cwd, args);
    let shim = run(shim_path(), cwd, args);
    assert_eq!(
        real.status.code(),
        shim.status.code(),
        "exit code mismatch\nreal stderr: {}\nshim stderr: {}",
        String::from_utf8_lossy(&real.stderr),
        String::from_utf8_lossy(&shim.stderr),
    );
    assert_eq!(
        String::from_utf8_lossy(&real.stdout),
        String::from_utf8_lossy(&shim.stdout),
        "stdout mismatch for `subspy-git {}`",
        args.join(" "),
    );
    assert_eq!(
        String::from_utf8_lossy(&real.stderr),
        String::from_utf8_lossy(&shim.stderr),
        "stderr mismatch for `subspy-git {}`",
        args.join(" "),
    );
}

/// Outside any repo, the shim must produce git's `fatal: not a git
/// repository` (exit code, stderr text, empty stdout). Reaches this
/// behavior by falling back to real git after `Repository::open`
/// fails inside the intercepted code path.
#[test]
fn status_outside_repo_matches_git() {
    let tmp = TempDir::new().unwrap();
    assert_outputs_match(tmp.path(), &["status"]);
}

/// A corrupt `.git` makes the intercepted code path fail at repo
/// open. The shim must fall back to real git rather than emit its
/// own error string.
#[test]
fn status_on_corrupt_repo_falls_back() {
    let tmp = TempDir::new().unwrap();
    // A `.git` that exists but isn't a valid repository.
    std::fs::create_dir(tmp.path().join(".git")).unwrap();
    std::fs::write(tmp.path().join(".git/HEAD"), "garbage\n").unwrap();

    let real = run("git", tmp.path(), &["status"]);
    let shim = run(shim_path(), tmp.path(), &["status"]);
    assert_eq!(real.status.code(), shim.status.code());
    // We don't pin the stderr verbatim because git's wording can vary
    // by version; the point is that we deferred to git rather than
    // emitting our own error string.
    assert!(
        !String::from_utf8_lossy(&shim.stderr).contains("subspy-git:"),
        "shim leaked its own error string: {}",
        String::from_utf8_lossy(&shim.stderr),
    );
}

/// Happy path: in a normal repo, the shim's intercepted status output
/// must match real git's, so the fallback machinery hasn't broken the
/// success case.
#[test]
fn status_in_clean_repo_matches_git() {
    let tmp = TempDir::new().unwrap();
    run("git", tmp.path(), &["init", "-q", "-b", "master"]);
    std::fs::write(tmp.path().join("file.txt"), "hello\n").unwrap();
    run("git", tmp.path(), &["add", "-A"]);
    run(
        "git",
        tmp.path(),
        &[
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@test.com",
            "commit",
            "-qm",
            "initial",
        ],
    );

    assert_outputs_match(tmp.path(), &["status"]);
}

/// Ref names with non-UTF-8 bytes are legal per git. Subspy must not
/// panic on them. Our output substitutes U+FFFD for invalid sequences
/// (`from_utf8_lossy`) where git emits the raw bytes, so byte-for-byte
/// parity isn't expected here -- we just assert no crash and that the
/// surrounding text is present.
///
/// Unix-only: the test writes a filename containing 0xFF 0xFE into
/// `.git/refs/heads/`, which isn't representable on Windows (NTFS
/// filenames are UTF-16).
#[cfg(unix)]
#[test]
fn status_on_non_utf8_branch_name_does_not_panic() {
    use std::os::unix::ffi::OsStrExt as _;

    let tmp = TempDir::new().unwrap();
    run("git", tmp.path(), &["init", "-q", "-b", "master"]);
    std::fs::write(tmp.path().join("file.txt"), "hello\n").unwrap();
    run("git", tmp.path(), &["add", "-A"]);
    run(
        "git",
        tmp.path(),
        &[
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@test.com",
            "commit",
            "-qm",
            "initial",
        ],
    );

    // Build a branch ref with invalid UTF-8 bytes (0xFF 0xFE) by writing
    // directly to .git/refs/heads/, then point HEAD at it. `git branch`
    // and `update-ref` won't accept invalid bytes via the CLI.
    let oid = std::process::Command::new("git")
        .args(["rev-parse", "master"])
        .current_dir(tmp.path())
        .output()
        .expect("rev-parse failed");
    let oid_str = String::from_utf8(oid.stdout).expect("oid is ascii");

    let refs_heads = tmp.path().join(".git/refs/heads");
    let bad_ref_name = std::ffi::OsStr::from_bytes(b"bad\xff\xfename");
    let bad_ref_path = refs_heads.join(bad_ref_name);
    std::fs::write(&bad_ref_path, &oid_str).expect("write ref");
    std::fs::write(
        tmp.path().join(".git/HEAD"),
        b"ref: refs/heads/bad\xff\xfename\n",
    )
    .expect("write HEAD");

    let shim = run(shim_path(), tmp.path(), &["status"]);
    assert!(
        shim.status.success(),
        "shim exited {:?}\nstderr: {}",
        shim.status.code(),
        String::from_utf8_lossy(&shim.stderr),
    );
    // Either matches git verbatim or substitutes U+FFFD -- accept both.
    let stdout = String::from_utf8_lossy(&shim.stdout);
    assert!(
        stdout.contains("On branch bad") && stdout.contains("name"),
        "unexpected stdout: {stdout:?}",
    );
}

/// A non-`status` subcommand has to forward to real git verbatim
/// regardless of any shim logic.
#[test]
fn unknown_subcommand_forwards_to_git() {
    let tmp = TempDir::new().unwrap();
    run("git", tmp.path(), &["init", "-q", "-b", "master"]);

    assert_outputs_match(tmp.path(), &["--version"]);
}
