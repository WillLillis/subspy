//! End-to-end tests for the `subspy-git` shim binary. Each test invokes
//! the compiled shim (via `CARGO_BIN_EXE_subspy-git`) and compares its
//! output / exit code against real `git`, exercising the "intercept
//! when possible, forward to git otherwise" contract.

use std::process::{Command, Output};
use tempfile::TempDir;
use testutil::HarnessBuilder;

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

fn run_without_git(cwd: &std::path::Path, args: &[&str]) -> Output {
    Command::new(shim_path())
        .args(args)
        .current_dir(cwd)
        .env("NO_COLOR", "1")
        .env("PATH", "")
        .output()
        .expect("spawn shim")
}

fn init_repo(path: &std::path::Path) {
    run("git", path, &["init", "-q", "-b", "master"]);
    std::fs::write(path.join("seed.txt"), "seed\n").unwrap();
    run("git", path, &["add", "-A"]);
    run(
        "git",
        path,
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

fn assert_rendered_locally_matches(cwd: &std::path::Path, args: &[&str]) -> Output {
    let real = run("git", cwd, args);
    let shim = run_without_git(cwd, args);
    assert_eq!(real.status.code(), shim.status.code());
    assert_eq!(real.stdout, shim.stdout, "stdout mismatch for {args:?}");
    assert_eq!(real.stderr, shim.stderr, "stderr mismatch for {args:?}");
    shim
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

#[test]
fn cwd_pathspec_is_rendered_locally_and_filters_siblings() {
    let tmp = TempDir::new().unwrap();
    init_repo(tmp.path());
    let selected = tmp.path().join("selected");
    let sibling = tmp.path().join("selected-sibling");
    std::fs::create_dir_all(&selected).unwrap();
    std::fs::create_dir_all(&sibling).unwrap();
    std::fs::write(selected.join("inside.txt"), "inside\n").unwrap();
    std::fs::write(sibling.join("outside.txt"), "outside\n").unwrap();

    // With Git unavailable to the shim, matching proves this was served by
    // Subspy rather than matching only because the shim forwarded it.
    let shim = assert_rendered_locally_matches(&selected, &["status", "--porcelain", "--", "."]);
    assert_eq!(shim.stdout, b"?? selected/\n");
}

#[test]
fn cwd_pathspec_filters_tracked_rows_in_all_formats() {
    let tmp = TempDir::new().unwrap();
    init_repo(tmp.path());
    let selected = tmp.path().join("selected");
    let sibling = tmp.path().join("selected-sibling");
    std::fs::create_dir_all(&selected).unwrap();
    std::fs::create_dir_all(&sibling).unwrap();
    std::fs::write(selected.join("inside.txt"), "initial\n").unwrap();
    std::fs::write(sibling.join("outside.txt"), "initial\n").unwrap();
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
            "tracked dirs",
        ],
    );
    std::fs::write(selected.join("inside.txt"), "changed\n").unwrap();
    std::fs::write(sibling.join("outside.txt"), "changed\n").unwrap();

    for args in [
        &["status", "--", "."][..],
        &["status", "-s", "--", "."][..],
        &["status", "--porcelain", "--", "."][..],
        &["status", "--porcelain=2", "--", "."][..],
        &["status", "--porcelain", "-z", "--", "."][..],
        &["status", "--porcelain=2", "-z", "--", "."][..],
    ] {
        assert_rendered_locally_matches(&selected, args);
    }
}

#[test]
fn cwd_pathspec_splits_cross_boundary_renames() {
    for (from, to) in [
        ("selected/file.txt", "outside/file.txt"),
        ("outside/file.txt", "selected/file.txt"),
    ] {
        let tmp = TempDir::new().unwrap();
        init_repo(tmp.path());
        let selected = tmp.path().join("selected");
        std::fs::create_dir_all(&selected).unwrap();
        let source = tmp.path().join(from);
        std::fs::create_dir_all(source.parent().unwrap()).unwrap();
        std::fs::write(&source, "rename me\n").unwrap();
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
                "rename source",
            ],
        );
        std::fs::create_dir_all(tmp.path().join(to).parent().unwrap()).unwrap();
        run("git", tmp.path(), &["mv", from, to]);

        assert_rendered_locally_matches(&selected, &["status", "--porcelain=2", "--", "."]);
    }
}

#[test]
fn cwd_pathspec_long_format_is_clean_when_only_sibling_changed() {
    let tmp = TempDir::new().unwrap();
    init_repo(tmp.path());
    let selected = tmp.path().join("selected");
    std::fs::create_dir_all(&selected).unwrap();
    std::fs::write(selected.join("inside.txt"), "inside\n").unwrap();
    std::fs::write(tmp.path().join("outside.txt"), "outside\n").unwrap();
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
            "tracked files",
        ],
    );
    std::fs::write(tmp.path().join("outside.txt"), "changed\n").unwrap();

    let shim = assert_rendered_locally_matches(&selected, &["status", "--", "."]);
    assert!(String::from_utf8_lossy(&shim.stdout).contains("working tree clean"));
}

#[test]
fn recursive_untracked_mode_avoids_collapsed_ancestor_decline() {
    let tmp = TempDir::new().unwrap();
    init_repo(tmp.path());
    let selected = tmp.path().join("untracked/sub");
    std::fs::create_dir_all(&selected).unwrap();
    std::fs::write(selected.join("file.txt"), "untracked\n").unwrap();

    let shim = assert_rendered_locally_matches(
        &selected,
        &["status", "--porcelain", "--untracked-files=all", "--", "."],
    );
    assert_eq!(shim.stdout, b"?? untracked/sub/file.txt\n");
}

#[test]
fn cwd_pathspec_filters_submodule_statuses() {
    let harness = HarnessBuilder::new()
        .submodule("selected/inside")
        .submodule("outside")
        .build();
    harness
        .submodule("selected/inside")
        .write("README.md", "selected change\n");
    harness
        .submodule("outside")
        .write("README.md", "outside change\n");
    harness.assert_status_eventually("both submodules dirty", |statuses| statuses.len() == 2);

    let selected = harness.root().path().join("selected");
    for args in [
        &["status", "--", "."][..],
        &["status", "--porcelain", "--", "."][..],
        &["status", "--porcelain=2", "--", "."][..],
    ] {
        assert_rendered_locally_matches(&selected, args);
    }
}

#[test]
fn cwd_pathspec_splits_cross_boundary_submodule_renames() {
    for (from, to) in [
        ("selected/sub", "outside/sub"),
        ("outside/sub", "selected/sub"),
    ] {
        let harness = HarnessBuilder::new().submodule(from).build();
        harness.root().mkdir(to.rsplit_once('/').unwrap().0);
        harness.root().mv(from, to);

        let selected = harness.root().path().join("selected");
        for args in [
            &["status", "--porcelain", "--", "."][..],
            &["status", "--porcelain=2", "--", "."][..],
        ] {
            assert_rendered_locally_matches(&selected, args);
        }
    }
}

#[test]
fn collapsed_untracked_ancestor_declines_and_forwards() {
    let tmp = TempDir::new().unwrap();
    init_repo(tmp.path());
    let selected = tmp.path().join("untracked/sub");
    std::fs::create_dir_all(&selected).unwrap();
    std::fs::write(selected.join("file.txt"), "untracked\n").unwrap();

    assert_outputs_match(&selected, &["status", "--porcelain", "--", "."]);

    let shim = run_without_git(&selected, &["status", "--porcelain", "--", "."]);
    assert!(!shim.status.success(), "request should have been forwarded");
    assert!(
        String::from_utf8_lossy(&shim.stderr).contains("failed to exec `git`")
            || String::from_utf8_lossy(&shim.stderr).contains("failed to spawn `git`")
    );
    assert!(shim.stdout.is_empty(), "decline leaked partial output");
}

#[test]
fn collapsed_ignored_ancestor_is_rendered_locally() {
    let tmp = TempDir::new().unwrap();
    init_repo(tmp.path());
    std::fs::write(tmp.path().join(".gitignore"), "/ignored/\n").unwrap();
    let selected = tmp.path().join("ignored/sub");
    std::fs::create_dir_all(&selected).unwrap();
    std::fs::write(selected.join("file.txt"), "ignored\n").unwrap();

    let shim = assert_rendered_locally_matches(
        &selected,
        &["status", "--porcelain", "--ignored", "--", "."],
    );
    assert_eq!(shim.stdout, b"!! ignored/\n");
}

/// Ref names with non-UTF-8 bytes are legal per git. Subspy must not
/// panic on them. Our output substitutes U+FFFD for invalid sequences
/// (`from_utf8_lossy`) where git emits the raw bytes, so byte-for-byte
/// parity isn't expected here -- we just assert no crash and that the
/// surrounding text is present.
///
/// Linux-only: the test writes a filename containing 0xFF 0xFE into
/// `.git/refs/heads/`, which needs a filesystem that permits non-UTF-8
/// names. Windows (NTFS is UTF-16) and macOS (rejects invalid UTF-8 with
/// EILSEQ) both refuse it.
#[cfg(target_os = "linux")]
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
