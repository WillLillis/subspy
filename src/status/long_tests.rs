//! Snapshot tests for the long-format `display_status` output. Each
//! case builds a fixture repo, runs `display_status` in-process, and
//! compares the bytes to `src/status/snapshots/long/<case>.snapshot`.
//! Regenerate with `UPDATE_LONG_SNAPSHOTS=1`. See CONTRIBUTING.md for
//! workflow details.

use git2::Repository;
use pretty_assertions::assert_eq;
use std::path::{Path, PathBuf};
use tempfile::TempDir;
use testutil::{HarnessBuilder, Repo, TestHarness};

use crate::{RepoKind, cli::ProjectPath};

use super::{
    IgnoreSubmodules, OutputOpts, UntrackedFiles, compute_local_statuses, deleted_submodule_paths,
    display::display_status, submodule::apply_ignore_submodules,
};

struct Case {
    name: &'static str,
    setup: Setup,
}

enum Setup {
    /// `effective_cwd` equals the repo root.
    Plain(fn(&Path)),
    /// `effective_cwd` is `repo_root/<subdir>`.
    Subdir {
        setup: fn(&Path),
        subdir: &'static str,
    },
    /// Repo built via `HarnessBuilder` with submodules.
    WithSubmodules {
        names: &'static [&'static str],
        setup: fn(&TestHarness),
    },
}

const CASES: &[Case] = &[
    Case {
        name: "clean_repo",
        setup: Setup::Plain(setup_clean),
    },
    Case {
        name: "modified_workdir",
        setup: Setup::Plain(setup_modified_workdir),
    },
    Case {
        name: "staged_modified",
        setup: Setup::Plain(setup_staged_modified),
    },
    Case {
        name: "staged_new",
        setup: Setup::Plain(setup_staged_new),
    },
    Case {
        name: "deleted_workdir",
        setup: Setup::Plain(setup_deleted_workdir),
    },
    Case {
        name: "deleted_staged",
        setup: Setup::Plain(setup_deleted_staged),
    },
    Case {
        name: "renamed_staged",
        setup: Setup::Plain(setup_renamed_staged),
    },
    Case {
        name: "renamed_staged_in_subdir",
        setup: Setup::Subdir {
            setup: setup_renamed_staged_in_subdir,
            subdir: "sub",
        },
    },
    Case {
        name: "untracked_files",
        setup: Setup::Plain(setup_untracked),
    },
    Case {
        name: "untracked_in_dir",
        setup: Setup::Plain(setup_untracked_in_dir),
    },
    Case {
        name: "untracked_high_byte_filename",
        setup: Setup::Plain(setup_untracked_high_byte_filename),
    },
    Case {
        name: "merge_with_conflict",
        setup: Setup::Plain(setup_merge_with_conflict),
    },
    Case {
        name: "merge_with_conflict_in_subdir",
        setup: Setup::Subdir {
            setup: setup_merge_with_conflict_in_subdir,
            subdir: "sub",
        },
    },
    Case {
        name: "cherry_pick_with_conflict",
        setup: Setup::Plain(setup_cherry_pick_with_conflict),
    },
    Case {
        name: "submodule_modified",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_modified,
        },
    },
    Case {
        name: "submodule_deleted_workdir",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_deleted_workdir,
        },
    },
    Case {
        name: "submodule_new_commits",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_new_commits,
        },
    },
    Case {
        name: "upstream_up_to_date",
        setup: Setup::Plain(setup_upstream_up_to_date),
    },
    Case {
        name: "upstream_ahead",
        setup: Setup::Plain(setup_upstream_ahead),
    },
    Case {
        name: "upstream_behind",
        setup: Setup::Plain(setup_upstream_behind),
    },
    Case {
        name: "upstream_diverged",
        setup: Setup::Plain(setup_upstream_diverged),
    },
];

// -- Plain setups --

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

fn setup_deleted_workdir(root: &Path) {
    setup_clean(root);
    Repo::new(root).rm_file("file.txt");
}

fn setup_deleted_staged(root: &Path) {
    setup_clean(root);
    Repo::new(root).rm_tracked("file.txt");
}

fn setup_renamed_staged(root: &Path) {
    // Same content trick as porcelain tests: longer body so libgit2's
    // rename detector recognizes the move.
    Repo::init(root)
        .write("file.txt", "line one\nline two\nline three\nline four\n")
        .add_all()
        .commit("initial")
        .mv("file.txt", "renamed.txt");
}

fn setup_renamed_staged_in_subdir(root: &Path) {
    // Rename inside `sub/`, so both paths render relative to the `sub/`
    // cwd. The longer body ensures libgit2's rename detector matches.
    Repo::init(root)
        .write(
            "sub/file.txt",
            "line one\nline two\nline three\nline four\n",
        )
        .add_all()
        .commit("initial")
        .mv("sub/file.txt", "sub/renamed.txt");
}

fn setup_untracked(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("untracked.txt", "x\n");
}

fn setup_untracked_in_dir(root: &Path) {
    setup_clean(root);
    Repo::new(root)
        .mkdir("subdir")
        .write("subdir/a.txt", "x\n")
        .write("subdir/b.txt", "y\n");
}

fn setup_untracked_high_byte_filename(root: &Path) {
    setup_clean(root);
    // U+00E9 (e-acute) -> bytes 0xC3 0xA9; quoted form is "caf\303\251.txt".
    Repo::new(root).write("caf\u{00e9}.txt", "x\n");
}

fn setup_merge_with_conflict(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("file.txt", "feature change\n")
        .add_all()
        .commit("feature")
        .checkout("master")
        .write("file.txt", "master change\n")
        .add_all()
        .commit("master");
    // Conflicting merge; exits nonzero, which is the state we want.
    repo.try_git(&["merge", "feature"]);
}

fn setup_merge_with_conflict_in_subdir(root: &Path) {
    let repo = Repo::init(root);
    repo.write("sub/file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("sub/file.txt", "feature change\n")
        .add_all()
        .commit("feature")
        .checkout("master")
        .write("sub/file.txt", "master change\n")
        .add_all()
        .commit("master");
    repo.try_git(&["merge", "feature"]);
}

fn setup_cherry_pick_with_conflict(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("file.txt", "from feature\n")
        .add_all()
        .commit("feature commit")
        .checkout("master")
        .write("file.txt", "from master\n")
        .add_all()
        .commit("master commit");
    repo.try_git(&["cherry-pick", "feature"]);
}

// -- Submodule setups --

fn setup_submodule_modified(h: &TestHarness) {
    // Untracked-content variant: change README.md (a tracked file in
    // the submodule's source repo) without staging/committing.
    h.submodule("sub").write("README.md", "modified\n");
}

fn setup_submodule_deleted_workdir(h: &TestHarness) {
    let path = h.submodule("sub").path().to_path_buf();
    std::fs::remove_dir_all(&path).unwrap();
}

fn setup_submodule_new_commits(h: &TestHarness) {
    // Make a new commit inside the submodule so its HEAD diverges from
    // the gitlink the root repo recorded.
    h.submodule("sub")
        .write("README.md", "moved forward\n")
        .add_all()
        .commit("submodule advances");
}

// -- Upstream-tracking setups --
//
// We fake an upstream without a real remote: `update-ref` positions
// `refs/remotes/origin/master`, and the configs below wire `master` to
// track it. The url + fetch refspec are both required for git to treat
// `origin/master` as a remote-tracking ref (otherwise `@{u}` won't
// resolve); the url itself is a dummy and never fetched.

fn configure_master_tracks_origin(repo: &Repo) {
    repo.run_git(&["config", "branch.master.remote", "origin"]);
    repo.run_git(&["config", "branch.master.merge", "refs/heads/master"]);
    repo.run_git(&["config", "remote.origin.url", "/dev/null"]);
    repo.run_git(&[
        "config",
        "remote.origin.fetch",
        "+refs/heads/*:refs/remotes/origin/*",
    ]);
}

fn setup_upstream_up_to_date(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    configure_master_tracks_origin(&repo);
}

fn setup_upstream_ahead(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    // origin/master pinned at the initial commit; HEAD advances past it.
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    configure_master_tracks_origin(&repo);
    repo.write("file.txt", "ahead\n")
        .add_all()
        .commit("local commit");
}

fn setup_upstream_behind(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    // Make a second commit, mark it as origin/master, then reset HEAD back.
    repo.write("file.txt", "remote\n")
        .add_all()
        .commit("remote commit");
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    repo.run_git(&["reset", "-q", "--hard", "HEAD~1"]);
    configure_master_tracks_origin(&repo);
}

fn setup_upstream_diverged(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    // Build the "remote" side first, capture as origin/master, reset HEAD.
    repo.write("file.txt", "remote\n")
        .add_all()
        .commit("remote commit");
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    repo.run_git(&["reset", "-q", "--hard", "HEAD~1"]);
    configure_master_tracks_origin(&repo);
    // Then advance HEAD on a different content path so the two diverge.
    repo.write("file.txt", "local\n")
        .add_all()
        .commit("local commit");
}

// -- Harness wiring --

const fn default_opts() -> OutputOpts {
    OutputOpts {
        porcelain: None,
        null_terminate: false,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files: UntrackedFiles::Normal,
        show_ignored: false,
        branch: false,
    }
}

fn snapshot_path(case_name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src/status/snapshots/long")
        .join(format!("{case_name}.snapshot"))
}

/// Mirrors the `StatusOptions` set up by production `status::status`.
/// Kept in sync by hand.
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

fn run_subspy_long(project: &ProjectPath, opts: OutputOpts) -> Vec<u8> {
    let repo = Repository::open(&project.repo_root).unwrap();
    let mut so = build_status_options(opts, project.kind);
    let non_submod = repo.statuses(Some(&mut so)).unwrap();
    let deleted = if opts.ignore_submodules == IgnoreSubmodules::All {
        Vec::new()
    } else {
        deleted_submodule_paths(&repo).unwrap()
    };
    let submodules = if project.kind == RepoKind::WithSubmodules {
        compute_local_statuses(&project.repo_root, &repo).unwrap()
    } else {
        Vec::new()
    };
    let submodules = apply_ignore_submodules(submodules, opts.ignore_submodules);

    let cwd_rel = super::cwd_relative_to_repo(&project.repo_root, &project.effective_cwd);
    let rel = super::relativize::Relativizer::new(&cwd_rel);

    let entries = super::StatusEntries {
        non_submod: &non_submod,
        submodules: &submodules,
        deleted_submodules: &deleted,
    };

    let mut got: Vec<u8> = Vec::new();
    display_status(&mut got, &repo, &entries, &rel).unwrap();
    got
}

fn assert_snapshot(case_name: &str, got: &[u8]) {
    let path = snapshot_path(case_name);
    let updating = std::env::var_os("UPDATE_LONG_SNAPSHOTS").is_some();

    if updating {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&path, got)
            .unwrap_or_else(|e| panic!("failed to write snapshot {}: {e}", path.display()));
        return;
    }

    let expected = std::fs::read(&path).unwrap_or_else(|e| {
        panic!(
            "missing snapshot for '{case_name}' at {} ({e}); \
             re-run with UPDATE_LONG_SNAPSHOTS=1 to seed it",
            path.display()
        )
    });

    let got_str = std::str::from_utf8(got).expect("subspy output not utf-8");
    let expected_str = std::str::from_utf8(&expected).expect("snapshot not utf-8");
    assert_eq!(
        expected_str,
        got_str,
        "snapshot mismatch for '{case_name}' (path: {})",
        path.display()
    );
}

fn run_case(case: &Case) {
    match &case.setup {
        Setup::Plain(setup) => {
            let tmp = TempDir::new().unwrap();
            setup(tmp.path());
            let project = ProjectPath {
                repo_root: tmp.path().to_path_buf(),
                effective_cwd: tmp.path().to_path_buf(),
                kind: RepoKind::Normal,
            };
            let got = run_subspy_long(&project, default_opts());
            assert_snapshot(case.name, &got);
        }
        Setup::Subdir { setup, subdir } => {
            let tmp = TempDir::new().unwrap();
            setup(tmp.path());
            let project = ProjectPath {
                repo_root: tmp.path().to_path_buf(),
                effective_cwd: tmp.path().join(subdir),
                kind: RepoKind::Normal,
            };
            let got = run_subspy_long(&project, default_opts());
            assert_snapshot(case.name, &got);
        }
        Setup::WithSubmodules { names, setup } => {
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
            let got = run_subspy_long(&project, default_opts());
            assert_snapshot(case.name, &got);
        }
    }
}

#[test]
fn human_snapshots() {
    for case in CASES {
        run_case(case);
    }
}
