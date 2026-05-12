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
use testutil::{HarnessBuilder, Repo, TestHarness};

use crate::RepoKind;

use super::{
    IgnoreSubmodules, OutputOpts, PorcelainVersion, UntrackedFiles, compute_local_statuses,
    deleted_submodule_paths, porcelain_v1::display_porcelain_v1,
    porcelain_v2::display_porcelain_v2, submodule::apply_ignore_submodules,
};

fn setup_empty_repo(root: &Path) {
    Repo::init(root);
}

fn setup_empty_repo_with_untracked(root: &Path) {
    Repo::init(root).write("untracked.txt", "x\n");
}

/// Initializes a repo with one committed file. Most setups build on this.
fn setup_clean(root: &Path) {
    Repo::init(root)
        .write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
}

fn setup_modified_workdir(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("file.txt", "modified\n");
}

fn setup_untracked(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("untracked.txt", "x\n");
}

fn setup_staged_modified(root: &Path) {
    setup_clean(root);
    Repo::new(root)
        .write("file.txt", "staged change\n")
        .add("file.txt");
}

fn setup_staged_new(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("new.txt", "x\n").add("new.txt");
}

fn setup_staged_plus_workdir(root: &Path) {
    // Same file modified, staged, then modified again -> XY = "MM"
    setup_clean(root);
    Repo::new(root)
        .write("file.txt", "staged\n")
        .add("file.txt")
        .write("file.txt", "modified again\n");
}

fn setup_deleted_staged(root: &Path) {
    setup_clean(root);
    Repo::new(root).rm_tracked("file.txt");
}

fn setup_deleted_workdir(root: &Path) {
    setup_clean(root);
    Repo::new(root).rm_file("file.txt");
}

fn setup_renamed_staged(root: &Path) {
    // Regression test for the rename-detection + path-extraction bugs.
    // The file needs nontrivial content for libgit2's rename detector to
    // confidently match (matches git's diff.renames default behavior).
    setup_clean(root);
    Repo::new(root)
        .write("file.txt", "line one\nline two\nline three\nline four\n")
        .add_all()
        .commit("longer content")
        .mv("file.txt", "renamed.txt");
}

fn setup_untracked_in_dir(root: &Path) {
    // Differentiates `--untracked-files=normal` (collapses to `subdir/`)
    // from `--untracked-files=all` (expands to individual files).
    setup_clean(root);
    Repo::new(root)
        .mkdir("subdir")
        .write("subdir/a.txt", "a\n")
        .write("subdir/b.txt", "b\n");
}

fn setup_ignored_files(root: &Path) {
    // Only visible with --ignored; clean otherwise.
    setup_clean(root);
    Repo::new(root)
        .write(".gitignore", "*.log\n")
        .add(".gitignore")
        .commit("ignore")
        .write("debug.log", "x\n");
}

fn setup_path_with_space(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("has space.txt", "x\n");
}

fn setup_mixed(root: &Path) {
    // Exercises the tracked -> untracked -> ignored ordering pass.
    setup_clean(root);
    Repo::new(root)
        .write(".gitignore", "*.log\n")
        .add(".gitignore")
        .commit("ignore rules")
        .write("staged_new.txt", "x\n")
        .add("staged_new.txt")
        .write("file.txt", "modified\n")
        .write("untracked.txt", "u\n")
        .write("hidden.log", "ignored\n");
}

fn setup_detached_head(root: &Path) {
    setup_clean(root);
    Repo::new(root)
        .write("file.txt", "v2\n")
        .add_all()
        .commit("v2")
        .checkout("HEAD~1");
}

fn setup_path_with_non_ascii(root: &Path) {
    // Triggers high-byte octal escaping (`\303\251` etc.) in non-z mode.
    setup_clean(root);
    Repo::new(root).write("café.txt", "x\n");
}

fn setup_path_with_backslash(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("with\\back.txt", "x\n");
}

fn setup_multiple_renames(root: &Path) {
    // Two independent renames in the same commit; rename detector must
    // pair them up correctly.
    let r = Repo::init(root);
    r.write("alpha.txt", "alpha line 1\nalpha line 2\nalpha line 3\n")
        .write("beta.txt", "beta line 1\nbeta line 2\nbeta line 3\n")
        .add_all()
        .commit("init")
        .mv("alpha.txt", "alpha_renamed.txt")
        .mv("beta.txt", "beta_renamed.txt");
}

fn setup_dotfile(root: &Path) {
    // Untracked dotfile - git doesn't treat them specially in porcelain.
    setup_clean(root);
    Repo::new(root).write(".hidden", "x\n");
}

/// Merge with several conflict shapes: UU (both modified), AA (both added),
/// UD (deleted by them), DU (deleted by us). Exercises the conflict XY codes
/// in v1 and the `u`-line in v2.
fn setup_merge_conflict(root: &Path) {
    let r = Repo::init(root);
    r.write("shared.txt", "base\n")
        .write("us_delete.txt", "base\n")
        .write("them_delete.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("shared.txt", "feature\n")
        .rm_file("us_delete.txt")
        .write("them_delete.txt", "modified in feature\n")
        .write("both_add.txt", "feature version\n")
        .add_all()
        .commit("feature")
        .checkout("master")
        .write("shared.txt", "master\n")
        .write("us_delete.txt", "modified in master\n")
        .rm_file("them_delete.txt")
        .write("both_add.txt", "master version\n")
        .add_all()
        .commit("master");
    // Attempt the merge - expected to fail with conflicts. Assert on the
    // exit code so a future tweak that accidentally makes the merge succeed
    // fails loudly rather than silently testing a clean state.
    let output = r.try_git(&["merge", "feature", "--no-edit"]);
    assert!(
        !output.status.success(),
        "expected `git merge feature` to conflict, but it succeeded"
    );
}

/// A test scenario.
struct Case {
    name: &'static str,
    setup: CaseSetup,
}

/// How a case prepares its fixture repo. Plain cases take a fresh empty
/// directory; submodule cases get a `TestHarness` with the requested
/// submodules already added (via libgit2, no watch server).
enum CaseSetup {
    Plain(fn(&Path)),
    WithSubmodules {
        names: &'static [&'static str],
        setup: fn(&TestHarness),
    },
}

/// Cases are parameterized at test time over the (version, `null_terminate`,
/// branch, untracked-mode, ignored) matrix, so each entry here exercises
/// many test runs.
const CASES: &[Case] = &[
    plain("empty repo", setup_empty_repo),
    plain("empty repo with untracked", setup_empty_repo_with_untracked),
    plain("clean", setup_clean),
    plain("modified workdir", setup_modified_workdir),
    plain("staged modified", setup_staged_modified),
    plain("staged new file", setup_staged_new),
    plain("MM (staged + workdir)", setup_staged_plus_workdir),
    plain("deleted (staged)", setup_deleted_staged),
    plain("deleted (workdir)", setup_deleted_workdir),
    plain("renamed (staged)", setup_renamed_staged),
    plain("untracked", setup_untracked),
    plain("untracked in dir", setup_untracked_in_dir),
    plain("path with space", setup_path_with_space),
    plain("mixed (tracked + untracked + ignored)", setup_mixed),
    plain("detached HEAD", setup_detached_head),
    plain("ignored files", setup_ignored_files),
    plain("merge conflict (UU/AA/UD/DU)", setup_merge_conflict),
    plain("path with non-ASCII", setup_path_with_non_ascii),
    plain("path with backslash", setup_path_with_backslash),
    plain("multiple renames", setup_multiple_renames),
    plain("dotfile (untracked)", setup_dotfile),
    submodule_case("submodule clean", &["sub_a"], setup_submod_clean),
    submodule_case(
        "submodule dirty workdir",
        &["sub_a"],
        setup_submod_dirty_workdir,
    ),
    submodule_case(
        "submodule new commits",
        &["sub_a"],
        setup_submod_new_commits,
    ),
    submodule_case("submodule deleted", &["sub_a"], setup_submod_deleted),
    submodule_case(
        "submodule workdir rm -rf",
        &["sub_a"],
        setup_submod_rm_rf_workdir,
    ),
];

const fn plain(name: &'static str, setup: fn(&Path)) -> Case {
    Case {
        name,
        setup: CaseSetup::Plain(setup),
    }
}

const fn submodule_case(
    name: &'static str,
    names: &'static [&'static str],
    setup: fn(&TestHarness),
) -> Case {
    Case {
        name,
        setup: CaseSetup::WithSubmodules { names, setup },
    }
}

fn setup_submod_clean(_h: &TestHarness) {
    // Harness already builds a clean repo with one submodule; nothing to do.
}

fn setup_submod_dirty_workdir(h: &TestHarness) {
    // Untracked file inside the submodule -> parent shows ` M sub_a`.
    h.submodule("sub_a").write("dirty.txt", "x\n");
}

fn setup_submod_new_commits(h: &TestHarness) {
    // Add a new commit inside the submodule that isn't reflected in the
    // parent's gitlink -> parent shows ` M sub_a`.
    h.submodule("sub_a")
        .write("README.md", "updated\n")
        .add_all()
        .commit("submodule update");
}

fn setup_submod_deleted(h: &TestHarness) {
    // `git rm` the submodule from the parent index -> parent shows the
    // gitlink as deleted (handled via deleted_submodule_paths).
    h.root().run_git(&["rm", "-q", "sub_a"]);
}

fn setup_submod_rm_rf_workdir(h: &TestHarness) {
    // Wipe the submodule's workdir but leave the gitlink in HEAD and the
    // index -> parent shows ` D sub_a` in v1 / `.D` with m_work=0 in v2.
    std::fs::remove_dir_all(h.submodule("sub_a").path()).unwrap();
}

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
fn build_status_options(opts: OutputOpts, repo_kind: RepoKind) -> git2::StatusOptions {
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
    if repo_kind == RepoKind::WithSubmodules {
        so.exclude_submodules(true);
    }
    so
}

/// Runs `case` with `opts` against both real git and subspy, asserts equal.
fn run_case(case: &Case, opts: OutputOpts) {
    match &case.setup {
        CaseSetup::Plain(setup) => {
            let tmp = TempDir::new().unwrap();
            setup(tmp.path());
            assert_outputs_match(tmp.path(), case.name, opts, RepoKind::Normal);
        }
        CaseSetup::WithSubmodules { names, setup } => {
            let mut builder = HarnessBuilder::new().no_server();
            for n in *names {
                builder = builder.submodule(n);
            }
            let harness = builder.build();
            setup(&harness);
            assert_outputs_match(
                harness.root().path(),
                case.name,
                opts,
                RepoKind::WithSubmodules,
            );
        }
    }
}

/// Runs real git and subspy against the prepared `repo_root` with `opts`,
/// asserting byte-equal output. `repo_kind` controls whether the subspy
/// path also computes per-submodule statuses (mirrors `status::status`).
fn assert_outputs_match(repo_root: &Path, case_name: &str, opts: OutputOpts, repo_kind: RepoKind) {
    // Capture real git's output.
    let cwd = repo_root.display().to_string();
    let args = git_status_args(opts);
    let mut all = vec!["-C".to_string(), cwd];
    all.extend(args.iter().cloned());
    let go = Command::new("git").args(&all).output().expect("git failed");
    assert!(
        go.status.success(),
        "git {} failed for case '{}': {}",
        args.join(" "),
        case_name,
        String::from_utf8_lossy(&go.stderr)
    );
    let expected = go.stdout;

    // Capture subspy's output into a Vec<u8>.
    let repo = Repository::open(repo_root).unwrap();
    let mut so = build_status_options(opts, repo_kind);
    let non_submod = repo.statuses(Some(&mut so)).unwrap();
    let deleted = if opts.ignore_submodules == IgnoreSubmodules::All {
        Vec::new()
    } else {
        deleted_submodule_paths(&repo).unwrap()
    };
    let submodules = if repo_kind == RepoKind::WithSubmodules {
        compute_local_statuses(repo_root, &repo).unwrap()
    } else {
        Vec::new()
    };
    let submodules = apply_ignore_submodules(submodules, opts.ignore_submodules);

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
        case_name,
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
