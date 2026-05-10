//! End-to-end tests for porcelain v1 and v2 output.
//!
//! Strategy: for each scenario we build a fixture repo, run real `git status`
//! to capture the expected output, then run subspy's display function on the
//! same repo with matching options and assert byte-equality. This uses real
//! git as the oracle so we never drift from git's actual output format.
//!
//! Adding a new case: write a `setup_*` function that mutates a fresh repo
//! into the desired state, then add a `Case` entry to `CASES`. Every case
//! runs against the cartesian product of porcelain version, `-z`, and
//! `--branch` matrix.

use git2::Repository;
use std::path::Path;
use std::process::Command;
use tempfile::TempDir;

use super::{
    IgnoreSubmodules, OutputOpts, PorcelainVersion, UntrackedFiles, deleted_submodule_paths,
    porcelain_v1::display_porcelain_v1, porcelain_v2::display_porcelain_v2,
};

/// Runs `git` with consistent author config; panics on non-zero exit.
fn git(args: &[&str]) {
    let output = Command::new("git")
        .args(["-c", "user.name=Test", "-c", "user.email=test@test.com"])
        .args(args)
        .output()
        .expect("failed to run git");
    assert!(
        output.status.success(),
        "git {} failed: {}",
        args.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Initializes a repo with one committed file. Most setups build on this.
fn setup_clean(root: &Path) {
    let r = root.display().to_string();
    git(&["-C", &r, "init", "-q", "--initial-branch=master"]);
    std::fs::write(root.join("file.txt"), "initial\n").unwrap();
    git(&["-C", &r, "add", "-A"]);
    git(&["-C", &r, "commit", "-qm", "initial"]);
}

fn setup_modified_workdir(root: &Path) {
    setup_clean(root);
    std::fs::write(root.join("file.txt"), "modified\n").unwrap();
}

fn setup_untracked(root: &Path) {
    setup_clean(root);
    std::fs::write(root.join("untracked.txt"), "x\n").unwrap();
}

fn setup_staged_modified(root: &Path) {
    setup_clean(root);
    std::fs::write(root.join("file.txt"), "staged change\n").unwrap();
    git(&["-C", &root.display().to_string(), "add", "file.txt"]);
}

fn setup_staged_new(root: &Path) {
    setup_clean(root);
    std::fs::write(root.join("new.txt"), "x\n").unwrap();
    git(&["-C", &root.display().to_string(), "add", "new.txt"]);
}

fn setup_staged_plus_workdir(root: &Path) {
    // Same file modified, staged, then modified again -> XY = "MM"
    setup_clean(root);
    let r = root.display().to_string();
    std::fs::write(root.join("file.txt"), "staged\n").unwrap();
    git(&["-C", &r, "add", "file.txt"]);
    std::fs::write(root.join("file.txt"), "modified again\n").unwrap();
}

fn setup_deleted_staged(root: &Path) {
    setup_clean(root);
    git(&["-C", &root.display().to_string(), "rm", "-q", "file.txt"]);
}

fn setup_deleted_workdir(root: &Path) {
    setup_clean(root);
    std::fs::remove_file(root.join("file.txt")).unwrap();
}

fn setup_renamed_staged(root: &Path) {
    // Regression test for the rename-detection + path-extraction bugs.
    setup_clean(root);
    // The file needs nontrivial content for libgit2's rename detector to
    // confidently match (matches git's diff.renames default behavior).
    std::fs::write(
        root.join("file.txt"),
        "line one\nline two\nline three\nline four\n",
    )
    .unwrap();
    let r = root.display().to_string();
    git(&["-C", &r, "add", "-A"]);
    git(&["-C", &r, "commit", "-qm", "longer content"]);
    git(&["-C", &r, "mv", "file.txt", "renamed.txt"]);
}

fn setup_untracked_in_dir(root: &Path) {
    // Differentiates `--untracked-files=normal` (collapses to `subdir/`)
    // from `--untracked-files=all` (expands to individual files).
    setup_clean(root);
    std::fs::create_dir(root.join("subdir")).unwrap();
    std::fs::write(root.join("subdir/a.txt"), "a\n").unwrap();
    std::fs::write(root.join("subdir/b.txt"), "b\n").unwrap();
}

fn setup_ignored_files(root: &Path) {
    // Only visible with --ignored; clean otherwise.
    setup_clean(root);
    let r = root.display().to_string();
    std::fs::write(root.join(".gitignore"), "*.log\n").unwrap();
    git(&["-C", &r, "add", ".gitignore"]);
    git(&["-C", &r, "commit", "-qm", "ignore"]);
    std::fs::write(root.join("debug.log"), "x\n").unwrap();
}

fn setup_path_with_space(root: &Path) {
    setup_clean(root);
    std::fs::write(root.join("has space.txt"), "x\n").unwrap();
}

fn setup_mixed(root: &Path) {
    // Exercises the tracked -> untracked -> ignored ordering pass.
    setup_clean(root);
    let r = root.display().to_string();
    std::fs::write(root.join(".gitignore"), "*.log\n").unwrap();
    git(&["-C", &r, "add", ".gitignore"]);
    git(&["-C", &r, "commit", "-qm", "ignore rules"]);

    std::fs::write(root.join("staged_new.txt"), "x\n").unwrap();
    git(&["-C", &r, "add", "staged_new.txt"]);
    std::fs::write(root.join("file.txt"), "modified\n").unwrap();
    std::fs::write(root.join("untracked.txt"), "u\n").unwrap();
    std::fs::write(root.join("hidden.log"), "ignored\n").unwrap();
}

fn setup_detached_head(root: &Path) {
    setup_clean(root);
    let r = root.display().to_string();
    // Add a second commit so HEAD~1 exists.
    std::fs::write(root.join("file.txt"), "v2\n").unwrap();
    git(&["-C", &r, "add", "-A"]);
    git(&["-C", &r, "commit", "-qm", "v2"]);
    git(&["-C", &r, "checkout", "-q", "HEAD~1"]);
}

/// A test scenario: a setup function that builds the repo state, plus the
/// options we want both git and subspy to see.
struct Case {
    name: &'static str,
    setup: fn(&Path),
}

/// Cases are parameterized at test time over the (version, `null_terminate`,
/// branch, untracked-mode, ignored) matrix, so each entry here exercises
/// many test runs.
const CASES: &[Case] = &[
    Case {
        name: "clean",
        setup: setup_clean,
    },
    Case {
        name: "modified workdir",
        setup: setup_modified_workdir,
    },
    Case {
        name: "staged modified",
        setup: setup_staged_modified,
    },
    Case {
        name: "staged new file",
        setup: setup_staged_new,
    },
    Case {
        name: "MM (staged + workdir)",
        setup: setup_staged_plus_workdir,
    },
    Case {
        name: "deleted (staged)",
        setup: setup_deleted_staged,
    },
    Case {
        name: "deleted (workdir)",
        setup: setup_deleted_workdir,
    },
    Case {
        name: "renamed (staged)",
        setup: setup_renamed_staged,
    },
    Case {
        name: "untracked",
        setup: setup_untracked,
    },
    Case {
        name: "untracked in dir",
        setup: setup_untracked_in_dir,
    },
    Case {
        name: "path with space",
        setup: setup_path_with_space,
    },
    Case {
        name: "mixed (tracked + untracked + ignored)",
        setup: setup_mixed,
    },
    Case {
        name: "detached HEAD",
        setup: setup_detached_head,
    },
    Case {
        name: "ignored files",
        setup: setup_ignored_files,
    },
];

/// Translates `OutputOpts` to the equivalent `git status` argv. Mirrors
/// subspy's defaults so the two sides agree without explicit redundant flags.
fn git_status_args(opts: OutputOpts) -> Vec<String> {
    let mut a: Vec<String> = vec!["status".into()];
    match opts.porcelain {
        Some(PorcelainVersion::V1) => a.push("--porcelain".into()),
        Some(PorcelainVersion::V2) => a.push("--porcelain=2".into()),
        None => {}
    }
    if opts.null_terminate {
        a.push("-z".into());
    }
    if opts.branch {
        a.push("--branch".into());
    }
    match opts.untracked_files {
        UntrackedFiles::Normal => {} // git's default
        UntrackedFiles::All => a.push("--untracked-files=all".into()),
        UntrackedFiles::No => a.push("--untracked-files=no".into()),
    }
    if opts.show_ignored {
        a.push("--ignored".into());
    }
    match opts.ignore_submodules {
        IgnoreSubmodules::None => {} // matches subspy's default; git's default for status is "all"
        IgnoreSubmodules::Untracked => a.push("--ignore-submodules=untracked".into()),
        IgnoreSubmodules::Dirty => a.push("--ignore-submodules=dirty".into()),
        IgnoreSubmodules::All => a.push("--ignore-submodules=all".into()),
    }
    a
}

/// Mirrors `status::status`'s `StatusOptions` setup. Kept in sync by
/// constructing from the same `OutputOpts` shape.
fn build_status_options(opts: OutputOpts) -> git2::StatusOptions {
    let mut so = git2::StatusOptions::new();
    match opts.untracked_files {
        UntrackedFiles::Normal => {
            so.include_untracked(true).recurse_untracked_dirs(false);
        }
        UntrackedFiles::All => {
            so.include_untracked(true).recurse_untracked_dirs(true);
        }
        UntrackedFiles::No => {
            so.include_untracked(false);
        }
    }
    so.include_ignored(opts.show_ignored).no_refresh(true);
    so.renames_head_to_index(true)
        .renames_index_to_workdir(true)
        .renames_from_rewrites(true);
    so
}

/// Runs `case` with `opts` against both real git and subspy, asserts equal.
fn run_case(case: &Case, opts: OutputOpts) {
    let tmp = TempDir::new().unwrap();
    (case.setup)(tmp.path());

    // Capture real git's output.
    let cwd = tmp.path().display().to_string();
    let args = git_status_args(opts);
    let mut all = vec!["-C".to_string(), cwd];
    all.extend(args.iter().cloned());
    let go = Command::new("git").args(&all).output().expect("git failed");
    assert!(
        go.status.success(),
        "git {} failed for case '{}': {}",
        args.join(" "),
        case.name,
        String::from_utf8_lossy(&go.stderr)
    );
    let expected = go.stdout;

    // Capture subspy's output into a Vec<u8>.
    let repo = Repository::open(tmp.path()).unwrap();
    let mut so = build_status_options(opts);
    let non_submod = repo.statuses(Some(&mut so)).unwrap();
    let deleted = deleted_submodule_paths(&repo).unwrap();
    let submodules = Vec::new();

    let mut got: Vec<u8> = Vec::new();
    match opts.porcelain {
        Some(PorcelainVersion::V1) => display_porcelain_v1(
            &mut got,
            &repo,
            &non_submod,
            &submodules,
            &deleted,
            opts.null_terminate,
            opts.branch,
        )
        .unwrap(),
        Some(PorcelainVersion::V2) => display_porcelain_v2(
            &mut got,
            &repo,
            &non_submod,
            &submodules,
            &deleted,
            opts.null_terminate,
            opts.branch,
        )
        .unwrap(),
        None => panic!("porcelain test runner doesn't support non-porcelain output"),
    }

    assert_eq!(
        got,
        expected,
        "case '{}' (porcelain={:?}, z={}, branch={})\n--- git ---\n{}\n--- subspy ---\n{}",
        case.name,
        opts.porcelain,
        opts.null_terminate,
        opts.branch,
        String::from_utf8_lossy(&expected),
        String::from_utf8_lossy(&got),
    );
}

const fn opts_with(
    version: PorcelainVersion,
    null_terminate: bool,
    branch: bool,
    untracked_files: UntrackedFiles,
    show_ignored: bool,
) -> OutputOpts {
    OutputOpts {
        porcelain: Some(version),
        null_terminate,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files,
        show_ignored,
        branch,
    }
}

#[test]
fn v1_default() {
    let opts = opts_with(
        PorcelainVersion::V1,
        false,
        false,
        UntrackedFiles::Normal,
        false,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v1_z() {
    let opts = opts_with(
        PorcelainVersion::V1,
        true,
        false,
        UntrackedFiles::Normal,
        false,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v1_branch() {
    let opts = opts_with(
        PorcelainVersion::V1,
        false,
        true,
        UntrackedFiles::Normal,
        false,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v2_default() {
    let opts = opts_with(
        PorcelainVersion::V2,
        false,
        false,
        UntrackedFiles::Normal,
        false,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v2_z() {
    let opts = opts_with(
        PorcelainVersion::V2,
        true,
        false,
        UntrackedFiles::Normal,
        false,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v2_branch() {
    let opts = opts_with(
        PorcelainVersion::V2,
        false,
        true,
        UntrackedFiles::Normal,
        false,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v1_untracked_all() {
    let opts = opts_with(
        PorcelainVersion::V1,
        false,
        false,
        UntrackedFiles::All,
        false,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v2_untracked_all() {
    let opts = opts_with(
        PorcelainVersion::V2,
        false,
        false,
        UntrackedFiles::All,
        false,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v1_ignored() {
    let opts = opts_with(
        PorcelainVersion::V1,
        false,
        false,
        UntrackedFiles::Normal,
        true,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v2_ignored() {
    let opts = opts_with(
        PorcelainVersion::V2,
        false,
        false,
        UntrackedFiles::Normal,
        true,
    );
    for c in CASES {
        run_case(c, opts);
    }
}
