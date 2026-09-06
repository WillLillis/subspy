//! Git config keys that change `git status` output, checked against real git
//! through both binaries.
//!
//! These live at the binary level because config resolution happens where argv
//! is parsed, above `assemble_status`. The in-crate porcelain oracle builds
//! `OutputOpts` by hand and so never exercises it.

use std::path::Path;
use std::process::{Command, Output};

use pretty_assertions::assert_eq;
use tempfile::TempDir;

const fn subspy_path() -> &'static str {
    env!("CARGO_BIN_EXE_subspy")
}

const fn shim_path() -> &'static str {
    env!("CARGO_BIN_EXE_subspy-git")
}

fn run(program: &str, cwd: &Path, args: &[&str]) -> Output {
    Command::new(program)
        .args(args)
        .current_dir(cwd)
        .env("NO_COLOR", "1")
        .output()
        .expect("spawn failed")
}

fn git(cwd: &Path, args: &[&str]) -> Output {
    run("git", cwd, args)
}

/// Asserts real git, the shim, and the standalone CLI all agree on `args`.
///
/// The shim takes git's argv verbatim. The CLI takes the same flags plus
/// `--no-server`, so a stale cache can never mask a config read.
fn assert_all_agree(cwd: &Path, args: &[&str]) {
    let expected = git(cwd, args);
    assert!(
        expected.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&expected.stderr)
    );

    let shim = run(shim_path(), cwd, args);
    assert_eq!(
        String::from_utf8_lossy(&expected.stdout),
        String::from_utf8_lossy(&shim.stdout),
        "subspy-git disagrees with git for {args:?}"
    );

    let mut cli_args = args.to_vec();
    cli_args.push("--no-server");
    let cli = run(subspy_path(), cwd, &cli_args);
    assert_eq!(
        String::from_utf8_lossy(&expected.stdout),
        String::from_utf8_lossy(&cli.stdout),
        "subspy disagrees with git for {cli_args:?}\nstderr: {}",
        String::from_utf8_lossy(&cli.stderr)
    );
}

fn init_repo(path: &Path) {
    git(path, &["init", "-q", "-b", "master"]);
    git(path, &["config", "user.name", "Test"]);
    git(path, &["config", "user.email", "test@test.com"]);
}

fn commit_all(path: &Path, msg: &str) {
    git(path, &["add", "-A"]);
    git(path, &["commit", "-q", "-m", msg]);
}

/// A repo with one tracked file, an untracked file, and an untracked directory
/// so `normal` and `all` differ.
fn repo_with_untracked() -> TempDir {
    let tmp = TempDir::new().unwrap();
    init_repo(tmp.path());
    std::fs::write(tmp.path().join("tracked.txt"), "tracked\n").unwrap();
    commit_all(tmp.path(), "init");
    std::fs::create_dir(tmp.path().join("dir")).unwrap();
    std::fs::write(tmp.path().join("dir/nested.txt"), "u\n").unwrap();
    std::fs::write(tmp.path().join("untracked.txt"), "u\n").unwrap();
    tmp
}

#[test]
fn status_show_untracked_files() {
    for mode in ["no", "normal", "all"] {
        let tmp = repo_with_untracked();
        git(tmp.path(), &["config", "status.showUntrackedFiles", mode]);
        for args in [
            &["status", "--porcelain"][..],
            &["status", "--porcelain=2"][..],
            &["status", "--short"][..],
        ] {
            assert_all_agree(tmp.path(), args);
        }
    }
}

#[test]
fn untracked_flag_overrides_config() {
    // Config supplies the default; an explicit flag replaces it, in both
    // directions.
    for (mode, flag) in [("no", "-uall"), ("all", "-uno")] {
        let tmp = repo_with_untracked();
        git(tmp.path(), &["config", "status.showUntrackedFiles", mode]);
        assert_all_agree(tmp.path(), &["status", "--porcelain", flag]);
    }
}

#[test]
fn core_quotepath() {
    for value in ["true", "false"] {
        let tmp = TempDir::new().unwrap();
        init_repo(tmp.path());
        std::fs::write(tmp.path().join("café.txt"), "x\n").unwrap();
        commit_all(tmp.path(), "init");
        std::fs::write(tmp.path().join("café.txt"), "modified\n").unwrap();
        git(tmp.path(), &["config", "core.quotepath", value]);
        for args in [
            &["status", "--porcelain"][..],
            &["status", "--porcelain=2"][..],
            &["status", "--short"][..],
        ] {
            assert_all_agree(tmp.path(), args);
        }
    }
}

#[test]
fn status_show_stash() {
    for value in ["true", "false"] {
        let tmp = TempDir::new().unwrap();
        init_repo(tmp.path());
        std::fs::write(tmp.path().join("f.txt"), "a\n").unwrap();
        commit_all(tmp.path(), "init");
        for content in ["b\n", "c\n"] {
            std::fs::write(tmp.path().join("f.txt"), content).unwrap();
            git(tmp.path(), &["stash", "-q"]);
        }
        std::fs::write(tmp.path().join("f.txt"), "d\n").unwrap();
        git(tmp.path(), &["config", "status.showStash", value]);
        // Only porcelain v2 with `--branch` carries the `# stash N` header.
        assert_all_agree(tmp.path(), &["status", "--porcelain=2", "--branch"]);
    }
}

#[test]
fn show_stash_flag_overrides_config() {
    for (value, flag) in [("true", "--no-show-stash"), ("false", "--show-stash")] {
        let tmp = TempDir::new().unwrap();
        init_repo(tmp.path());
        std::fs::write(tmp.path().join("f.txt"), "a\n").unwrap();
        commit_all(tmp.path(), "init");
        std::fs::write(tmp.path().join("f.txt"), "b\n").unwrap();
        git(tmp.path(), &["stash", "-q"]);
        git(tmp.path(), &["config", "status.showStash", value]);
        assert_all_agree(tmp.path(), &["status", "--porcelain=2", "--branch", flag]);
    }
}

/// Detaches HEAD so the long-format header abbreviates an OID.
fn repo_with_detached_head() -> TempDir {
    let tmp = TempDir::new().unwrap();
    init_repo(tmp.path());
    std::fs::write(tmp.path().join("f.txt"), "a\n").unwrap();
    commit_all(tmp.path(), "one");
    std::fs::write(tmp.path().join("f.txt"), "b\n").unwrap();
    commit_all(tmp.path(), "two");
    git(tmp.path(), &["checkout", "-q", "HEAD~1"]);
    tmp
}

#[test]
fn core_abbrev() {
    // 4 is git's minimum and `no` disables abbreviation. `auto` is the path
    // taken when the key is unset, where the length comes from the object count.
    for value in ["4", "7", "12", "40", "no", "auto"] {
        let tmp = repo_with_detached_head();
        git(tmp.path(), &["config", "core.abbrev", value]);
        assert_all_agree(tmp.path(), &["status"]);
    }
}

#[test]
fn core_abbrev_unset() {
    let tmp = repo_with_detached_head();
    assert_all_agree(tmp.path(), &["status"]);
}

/// A worktree detached at creation has no `checkout:` reflog entry, so git has
/// no target to name.
#[test]
fn detached_worktree_without_reflog() {
    let tmp = repo_with_detached_head();
    let linked = tmp.path().join("linked");
    git(
        tmp.path(),
        &[
            "worktree",
            "add",
            "-q",
            "--detach",
            linked.to_str().unwrap(),
            "HEAD",
        ],
    );
    assert_all_agree(&linked, &["status"]);
}

#[test]
fn status_relative_paths() {
    // Only observable from a subdirectory, and never in porcelain v1 (always
    // repo-root relative) or under `-z`.
    for value in ["true", "false"] {
        let tmp = TempDir::new().unwrap();
        init_repo(tmp.path());
        std::fs::create_dir(tmp.path().join("sub")).unwrap();
        std::fs::write(tmp.path().join("sub/inner.txt"), "a\n").unwrap();
        std::fs::write(tmp.path().join("top.txt"), "b\n").unwrap();
        commit_all(tmp.path(), "init");
        std::fs::write(tmp.path().join("sub/inner.txt"), "modified\n").unwrap();
        std::fs::write(tmp.path().join("top.txt"), "modified\n").unwrap();
        git(tmp.path(), &["config", "status.relativePaths", value]);

        let sub = tmp.path().join("sub");
        for args in [&["status", "--porcelain=2"][..], &["status", "--short"][..]] {
            assert_all_agree(&sub, args);
        }
    }
}
