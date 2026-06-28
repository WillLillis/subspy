//! End-to-end tests for porcelain v1 and v2 output.
//!
//! Each case runs real `git status --porcelain[=v2] [-z] [--branch]` and
//! asserts byte-equality with subspy's output. Live oracle (rather than
//! committed snapshots like long / short) because porcelain is git's
//! stability-promised format - if real git ever drifts, we want to know
//! immediately rather than rubber-stamping a stale snapshot.

use std::path::{Path, PathBuf};
use std::process::Command;
use tempfile::TempDir;
use testutil::{HarnessBuilder, Repo, TestHarness};

use crate::{
    RepoKind,
    cli::ProjectPath,
    status::{
        IgnoreSubmodules, IgnoredFiles, OutputFormat, OutputOpts, PorcelainOpts, PorcelainVersion,
        UntrackedFiles, assemble_status, compute_local_statuses,
        porcelain_v1::display_porcelain_v1, porcelain_v2::display_porcelain_v2,
    },
};

use super::fixtures::{
    setup_below_git_rename_threshold_staged, setup_clean, setup_deleted_staged,
    setup_deleted_workdir, setup_modified_workdir, setup_moved_modified_staged,
    setup_moved_modified_unstaged, setup_renamed_staged, setup_staged_modified, setup_staged_new,
    setup_submodule_gitlink_conflict, setup_submodule_gitlink_conflict_dirty, setup_untracked,
    setup_untracked_in_dir, setup_upstream_ahead, setup_upstream_behind, setup_upstream_diverged,
    setup_upstream_gone, setup_upstream_up_to_date,
};

fn setup_empty_repo(root: &Path) {
    Repo::init(root);
}

fn setup_empty_repo_with_untracked(root: &Path) {
    Repo::init(root).write("untracked.txt", "x\n");
}

fn setup_staged_plus_workdir(root: &Path) {
    // Same file modified, staged, then modified again -> XY = "MM"
    setup_clean(root);
    Repo::new(root)
        .write("file.txt", "staged\n")
        .add("file.txt")
        .write("file.txt", "modified again\n");
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

fn setup_git_rename_long_record_staged(root: &Path) {
    Repo::init(root)
        .write("old.txt", &"a".repeat(65))
        .add_all()
        .commit("initial")
        .write("new.txt", &format!("{}b", "a".repeat(65)))
        .rm_file("old.txt")
        .add_all();
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
    // Plain `mv` + edit, unstaged: must be `D old` + `?? new` like git, never a
    // spurious worktree rename. Guards the `renames_index_to_workdir` fix.
    plain("moved+modified (unstaged)", setup_moved_modified_unstaged),
    plain("moved+modified (staged)", setup_moved_modified_staged),
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
    // Interleaving: a submodule must slot between files by path, not after them.
    submodule_case(
        "submodule interleaved (workdir)",
        &["mmm"],
        setup_submod_interleaved_workdir,
    ),
    submodule_case(
        "submodule interleaved (staged)",
        &["mmm"],
        setup_submod_interleaved_staged,
    ),
    submodule_case(
        "submodule interleaved (deleted)",
        &["mmm"],
        setup_submod_interleaved_deleted,
    ),
    submodule_case(
        "submodule interleaved (renamed)",
        &["mmm"],
        setup_submod_interleaved_renamed,
    ),
    // An unmerged submodule: reported once as a `u` line, never as a separate
    // dirty row. The clean case exercises `S...`; the dirty case folds the
    // submodule's own commit/modified/untracked state into `SCMU`.
    submodule_case(
        "submodule gitlink conflict",
        &["sub"],
        setup_submodule_gitlink_conflict,
    ),
    submodule_case(
        "submodule gitlink conflict dirty",
        &["sub"],
        setup_submodule_gitlink_conflict_dirty,
    ),
    // Upstream tracking. Only `--branch` output diverges per upstream
    // state, so these exist primarily to exercise the `v1_branch` /
    // `v2_branch` matrix arms; without `--branch` they produce the
    // same output as `clean`.
    plain("upstream up-to-date", setup_upstream_up_to_date),
    plain("upstream ahead", setup_upstream_ahead),
    plain("upstream behind", setup_upstream_behind),
    plain("upstream diverged", setup_upstream_diverged),
    plain("upstream gone", setup_upstream_gone),
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

// -- Interleaving: the submodule `mmm` sorts between `aaa.txt` and `zzz.txt`,
// so the single path-sorted change stream must place it between them. The
// live oracle byte-compares each against real git.

/// Commits `aaa.txt` and `zzz.txt` in the root, returning its `Repo`.
fn seed_bracketing_files(h: &TestHarness) {
    h.root()
        .write("aaa.txt", "a\n")
        .write("zzz.txt", "z\n")
        .add_all()
        .commit("bracketing files");
}

fn setup_submod_interleaved_workdir(h: &TestHarness) {
    seed_bracketing_files(h);
    h.root().write("aaa.txt", "a2\n").write("zzz.txt", "z2\n");
    // Untracked content inside the submodule -> ` M mmm`.
    h.submodule("mmm").write("dirty.txt", "x\n");
}

fn setup_submod_interleaved_staged(h: &TestHarness) {
    seed_bracketing_files(h);
    h.root()
        .write("aaa.txt", "a2\n")
        .write("zzz.txt", "z2\n")
        .add_all();
    // Advance the submodule and stage the gitlink -> staged ` M mmm`.
    h.submodule("mmm")
        .write("README.md", "moved\n")
        .add_all()
        .commit("advance");
    h.root().add("mmm");
}

fn setup_submod_interleaved_deleted(h: &TestHarness) {
    seed_bracketing_files(h);
    h.root()
        .write("aaa.txt", "a2\n")
        .write("zzz.txt", "z2\n")
        .add_all();
    // Staged deletion of the submodule's gitlink (also touches .gitmodules).
    h.root().run_git(&["rm", "-q", "mmm"]);
}

fn setup_submod_interleaved_renamed(h: &TestHarness) {
    seed_bracketing_files(h);
    // `git mv` the submodule to another bracketed path -> staged rename keyed
    // on the new path (`nnn`, still between aaa.txt and zzz.txt).
    h.root().run_git(&["mv", "mmm", "nnn"]);
}

/// Translates `OutputOpts` to the equivalent `git status` argv. Mirrors
/// subspy's defaults so the two sides agree without explicit redundant flags.
fn git_status_args(opts: OutputOpts) -> Vec<String> {
    let mut a: Vec<String> = Vec::new();
    // `-c` globals must precede the subcommand.
    if !opts.quote_path {
        a.push("-c".into());
        a.push("core.quotepath=false".into());
    }
    a.push("status".into());
    match opts.format {
        OutputFormat::Porcelain(PorcelainVersion::V1) => a.push("--porcelain".into()),
        OutputFormat::Porcelain(PorcelainVersion::V2) => a.push("--porcelain=2".into()),
        OutputFormat::Short => a.push("-s".into()),
        OutputFormat::Long => {}
    }
    if opts.null_terminate {
        a.push("-z".into());
    }
    if opts.branch {
        a.push("--branch".into());
    }
    if !opts.ahead_behind {
        a.push("--no-ahead-behind".into());
    }
    match opts.untracked_files {
        UntrackedFiles::Normal => {} // git's default
        UntrackedFiles::All => a.push("--untracked-files=all".into()),
        UntrackedFiles::No => a.push("--untracked-files=no".into()),
    }
    match opts.ignored_files {
        IgnoredFiles::No => {} // git's default
        IgnoredFiles::Traditional => a.push("--ignored=traditional".into()),
    }
    match opts.ignore_submodules {
        IgnoreSubmodules::None => {} // default: show submodule changes (same in subspy and git)
        IgnoreSubmodules::Untracked => a.push("--ignore-submodules=untracked".into()),
        IgnoreSubmodules::Dirty => a.push("--ignore-submodules=dirty".into()),
        IgnoreSubmodules::All => a.push("--ignore-submodules=all".into()),
    }
    a
}

/// Runs `case` with `opts` against both real git and subspy, asserts equal.
fn run_case(case: &Case, opts: OutputOpts) {
    match &case.setup {
        CaseSetup::Plain(setup) => {
            let tmp = TempDir::new().unwrap();
            setup(tmp.path());
            let project = ProjectPath {
                repo_root: tmp.path().to_path_buf(),
                effective_cwd: tmp.path().to_path_buf(),
                kind: RepoKind::Normal,
            };
            assert_outputs_match(&project, case.name, opts);
        }
        CaseSetup::WithSubmodules { names, setup } => {
            let mut builder = HarnessBuilder::new().no_server();
            for n in *names {
                builder = builder.submodule(n);
            }
            let harness = builder.build();
            setup(&harness);
            let project = ProjectPath {
                repo_root: harness.root().path().to_path_buf(),
                effective_cwd: harness.root().path().to_path_buf(),
                kind: RepoKind::WithSubmodules,
            };
            assert_outputs_match(&project, case.name, opts);
        }
    }
}

/// Runs real git and subspy against the prepared repo with `opts`,
/// asserting byte-equal output. Mirrors the data passed to
/// `status::status`: `project.effective_cwd` is both the dir we pass to
/// git via `-C` and the input to subspy's `Relativizer`; `project.kind`
/// drives whether per-submodule statuses are computed.
fn assert_outputs_match(project: &ProjectPath, case_name: &str, opts: OutputOpts) {
    // Capture real git's output.
    let cwd = project.effective_cwd.display().to_string();
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
    let porcelain_opts = PorcelainOpts {
        null_terminate: opts.null_terminate,
        branch: opts.branch,
        ahead_behind: opts.ahead_behind,
        quote_path: opts.quote_path,
        show_stash: opts.show_stash,
    };
    let format = opts.format;
    let with_submodules = project.kind == RepoKind::WithSubmodules;
    let got: Vec<u8> = assemble_status(
        project,
        opts,
        || {
            Ok(if with_submodules {
                compute_local_statuses(&project.repo_root)?
            } else {
                Vec::new()
            })
        },
        |repo, entries, rel| {
            let mut got: Vec<u8> = Vec::new();
            match format {
                OutputFormat::Porcelain(PorcelainVersion::V1) => {
                    display_porcelain_v1(&mut got, repo, entries, porcelain_opts)?;
                }
                OutputFormat::Porcelain(PorcelainVersion::V2) => {
                    display_porcelain_v2(&mut got, repo, entries, rel, porcelain_opts)?;
                }
                OutputFormat::Long | OutputFormat::Short => {
                    panic!("porcelain test runner doesn't support non-porcelain output")
                }
            }
            Ok(got)
        },
    )
    .unwrap();

    assert_eq!(
        got,
        expected,
        "case '{}' (format={:?}, z={}, branch={})\n--- git ---\n{}\n--- subspy ---\n{}",
        case_name,
        opts.format,
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
    ignored_files: IgnoredFiles,
) -> OutputOpts {
    OutputOpts {
        format: OutputFormat::Porcelain(version),
        null_terminate,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files,
        ignored_files,
        branch,
        ahead_behind: true,
        quote_path: true,
        show_stash: false,
    }
}

#[test]
fn v1_default() {
    let opts = opts_with(
        PorcelainVersion::V1,
        false,
        false,
        UntrackedFiles::Normal,
        IgnoredFiles::No,
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
        IgnoredFiles::No,
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
        IgnoredFiles::No,
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
        IgnoredFiles::No,
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
        IgnoredFiles::No,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v2_rename_classification_matches_git_score_threshold() {
    let opts = opts_with(
        PorcelainVersion::V2,
        false,
        false,
        UntrackedFiles::No,
        IgnoredFiles::No,
    );
    for case in [
        plain(
            "below git rename threshold (staged)",
            setup_below_git_rename_threshold_staged,
        ),
        plain(
            "git rename long record (staged)",
            setup_git_rename_long_record_staged,
        ),
    ] {
        run_case(&case, opts);
    }
}

#[test]
fn v2_z_rename_classification_matches_git_score_threshold() {
    let opts = opts_with(
        PorcelainVersion::V2,
        true,
        false,
        UntrackedFiles::No,
        IgnoredFiles::No,
    );
    for case in [
        plain(
            "below git rename threshold (staged)",
            setup_below_git_rename_threshold_staged,
        ),
        plain(
            "git rename long record (staged)",
            setup_git_rename_long_record_staged,
        ),
    ] {
        run_case(&case, opts);
    }
}

#[test]
fn v2_branch() {
    let opts = opts_with(
        PorcelainVersion::V2,
        false,
        true,
        UntrackedFiles::Normal,
        IgnoredFiles::No,
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
        IgnoredFiles::No,
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
        IgnoredFiles::No,
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
        IgnoredFiles::Traditional,
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
        IgnoredFiles::Traditional,
    );
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v1_quotepath_false() {
    // `path_with_non_ASCII` is the case where the setting actually
    // changes output: bytes >= 0x80 should be emitted verbatim.
    let opts = OutputOpts {
        format: OutputFormat::Porcelain(PorcelainVersion::V1),
        null_terminate: false,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files: UntrackedFiles::Normal,
        ignored_files: IgnoredFiles::No,
        branch: false,
        ahead_behind: true,
        quote_path: false,
        show_stash: false,
    };
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v2_quotepath_false() {
    let opts = OutputOpts {
        format: OutputFormat::Porcelain(PorcelainVersion::V2),
        null_terminate: false,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files: UntrackedFiles::Normal,
        ignored_files: IgnoredFiles::No,
        branch: false,
        ahead_behind: true,
        quote_path: false,
        show_stash: false,
    };
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v1_branch_no_ahead_behind() {
    // `[different]` instead of `[ahead/behind N]` for diverged upstreams.
    let opts = OutputOpts {
        format: OutputFormat::Porcelain(PorcelainVersion::V1),
        null_terminate: false,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files: UntrackedFiles::Normal,
        ignored_files: IgnoredFiles::No,
        branch: true,
        ahead_behind: false,
        quote_path: true,
        show_stash: false,
    };
    for c in CASES {
        run_case(c, opts);
    }
}

#[test]
fn v2_branch_no_ahead_behind() {
    // `+? -?` instead of `+N -M` for diverged upstreams.
    let opts = OutputOpts {
        format: OutputFormat::Porcelain(PorcelainVersion::V2),
        null_terminate: false,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files: UntrackedFiles::Normal,
        ignored_files: IgnoredFiles::No,
        branch: true,
        ahead_behind: false,
        quote_path: true,
        show_stash: false,
    };
    for c in CASES {
        run_case(c, opts);
    }
}

// -- subdirectory invocation --
//
// Validates that subspy emits cwd-relative paths matching `git -C <dir>
// status --porcelain[=2]`. Files are seeded in three positions relative
// to the invocation cwd: above (`root.txt`), at (`src/main.rs`), and
// sibling (`tests/foo.rs`), plus a path with a space to exercise
// quoting interaction with the `../` prefix.

fn setup_subdir_fixture(root: &Path) -> PathBuf {
    let root_str = root.display().to_string();
    git(&["-C", &root_str, "init", "-q"]);
    git(&["-C", &root_str, "config", "user.email", "t@t"]);
    git(&["-C", &root_str, "config", "user.name", "T"]);
    std::fs::write(root.join("root.txt"), "orig\n").unwrap();
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(root.join("src/main.rs"), "orig\n").unwrap();
    std::fs::create_dir_all(root.join("tests")).unwrap();
    std::fs::write(root.join("tests/foo.rs"), "orig\n").unwrap();
    std::fs::write(root.join("with space.txt"), "orig\n").unwrap();
    git(&["-C", &root_str, "add", "-A"]);
    git(&["-C", &root_str, "commit", "-q", "-m", "init"]);
    // Modify each so they show up in status.
    std::fs::write(root.join("root.txt"), "changed\n").unwrap();
    std::fs::write(root.join("src/main.rs"), "changed\n").unwrap();
    std::fs::write(root.join("tests/foo.rs"), "changed\n").unwrap();
    std::fs::write(root.join("with space.txt"), "changed\n").unwrap();
    root.join("src")
}

fn git(args: &[&str]) {
    let out = Command::new("git").args(args).output().expect("git failed");
    assert!(
        out.status.success(),
        "git {:?} failed: {}",
        args,
        String::from_utf8_lossy(&out.stderr)
    );
}

fn subdir_project(repo_root: PathBuf, effective_cwd: PathBuf) -> ProjectPath {
    ProjectPath {
        repo_root,
        effective_cwd,
        kind: RepoKind::Normal,
    }
}

#[test]
fn v1_from_subdir() {
    let tmp = TempDir::new().unwrap();
    let subdir = setup_subdir_fixture(tmp.path());
    let project = subdir_project(tmp.path().to_path_buf(), subdir);
    let opts = opts_with(
        PorcelainVersion::V1,
        false,
        false,
        UntrackedFiles::Normal,
        IgnoredFiles::No,
    );
    assert_outputs_match(&project, "v1 from subdir", opts);
}

#[test]
fn v1_z_from_subdir() {
    let tmp = TempDir::new().unwrap();
    let subdir = setup_subdir_fixture(tmp.path());
    let project = subdir_project(tmp.path().to_path_buf(), subdir);
    let opts = opts_with(
        PorcelainVersion::V1,
        true,
        false,
        UntrackedFiles::Normal,
        IgnoredFiles::No,
    );
    assert_outputs_match(&project, "v1 -z from subdir", opts);
}

#[test]
fn v2_from_subdir() {
    let tmp = TempDir::new().unwrap();
    let subdir = setup_subdir_fixture(tmp.path());
    let project = subdir_project(tmp.path().to_path_buf(), subdir);
    let opts = opts_with(
        PorcelainVersion::V2,
        false,
        false,
        UntrackedFiles::Normal,
        IgnoredFiles::No,
    );
    assert_outputs_match(&project, "v2 from subdir", opts);
}

#[test]
fn v2_z_from_subdir() {
    let tmp = TempDir::new().unwrap();
    let subdir = setup_subdir_fixture(tmp.path());
    let project = subdir_project(tmp.path().to_path_buf(), subdir);
    let opts = opts_with(
        PorcelainVersion::V2,
        true,
        false,
        UntrackedFiles::Normal,
        IgnoredFiles::No,
    );
    assert_outputs_match(&project, "v2 -z from subdir", opts);
}
