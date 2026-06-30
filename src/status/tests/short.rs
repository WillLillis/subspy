//! Snapshot tests for the short-format (`git status -s`) output. Each
//! case builds a fixture repo, runs `short::display_short` in-process,
//! and compares the bytes to `src/status/snapshots/short/<case>.snapshot`.
//! Regenerate with `UPDATE_SHORT_SNAPSHOTS=1`. See CONTRIBUTING.md for
//! workflow details.

use pretty_assertions::assert_eq;
use std::path::{Path, PathBuf};
use tempfile::TempDir;
use testutil::HarnessBuilder;

use crate::{
    RepoKind,
    cli::ProjectPath,
    status::{
        IgnoreSubmodules, IgnoredFiles, OutputFormat, OutputOpts, PorcelainOpts, UntrackedFiles,
        assemble_status, compute_local_statuses, short::display_short,
    },
};

use super::fixtures::*;

struct Case {
    name: &'static str,
    setup: Setup,
    /// `--branch` / `-b`: emit the `## branch...` header.
    branch: bool,
}

const CASES: &[Case] = &[
    // Entry cases (no branch header).
    Case {
        name: "clean_repo",
        setup: Setup::Plain(setup_clean),
        branch: false,
    },
    Case {
        name: "modified_workdir",
        setup: Setup::Plain(setup_modified_workdir),
        branch: false,
    },
    Case {
        name: "staged_modified",
        setup: Setup::Plain(setup_staged_modified),
        branch: false,
    },
    Case {
        name: "staged_new",
        setup: Setup::Plain(setup_staged_new),
        branch: false,
    },
    Case {
        name: "deleted_workdir",
        setup: Setup::Plain(setup_deleted_workdir),
        branch: false,
    },
    Case {
        name: "deleted_staged",
        setup: Setup::Plain(setup_deleted_staged),
        branch: false,
    },
    Case {
        name: "renamed_staged",
        setup: Setup::Plain(setup_renamed_staged),
        branch: false,
    },
    // Staged rename, new file then deleted from the worktree: `RD old -> new`.
    Case {
        name: "renamed_then_worktree_deleted",
        setup: Setup::Plain(setup_renamed_then_worktree_deleted),
        branch: false,
    },
    Case {
        name: "renamed_staged_in_subdir",
        setup: Setup::Subdir {
            setup: setup_renamed_staged_in_subdir,
            subdir: "sub",
        },
        branch: false,
    },
    // Sub-threshold staged move: git (and subspy) report it as add + delete,
    // not a rename. Guards the v1/short synthetic-row rendering.
    Case {
        name: "rename_below_threshold_staged",
        setup: Setup::Plain(setup_below_git_rename_threshold_staged),
        branch: false,
    },
    // Same sub-threshold move, new file modified again in the worktree: the
    // split add side must keep the worktree status (`AM new.txt`, not `A `).
    Case {
        name: "rename_below_threshold_staged_wt_modified",
        setup: Setup::Plain(setup_below_git_rename_threshold_staged_wt_modified),
        branch: false,
    },
    // Plain `mv` + edit, unstaged: ` D file.txt` + `?? renamed.txt`, never a
    // worktree rename (guards the `renames_index_to_workdir` fix).
    Case {
        name: "moved_modified_unstaged",
        setup: Setup::Plain(setup_moved_modified_unstaged),
        branch: false,
    },
    // Same move staged: `R  file.txt -> renamed.txt`. git2 sets RENAMED+MODIFIED;
    // the X char must be `R`, not `M` (guards the XY ordering fix).
    Case {
        name: "moved_modified_staged",
        setup: Setup::Plain(setup_moved_modified_staged),
        branch: false,
    },
    Case {
        name: "untracked_files",
        setup: Setup::Plain(setup_untracked),
        branch: false,
    },
    Case {
        name: "untracked_in_dir",
        setup: Setup::Plain(setup_untracked_in_dir),
        branch: false,
    },
    Case {
        name: "untracked_high_byte_filename",
        setup: Setup::Plain(setup_untracked_high_byte_filename),
        branch: false,
    },
    Case {
        name: "merge_with_conflict",
        setup: Setup::Plain(setup_merge_with_conflict),
        branch: false,
    },
    Case {
        name: "merge_with_conflict_in_subdir",
        setup: Setup::Subdir {
            setup: setup_merge_with_conflict_in_subdir,
            subdir: "sub",
        },
        branch: false,
    },
    Case {
        name: "cherry_pick_with_conflict",
        setup: Setup::Plain(setup_cherry_pick_with_conflict),
        branch: false,
    },
    Case {
        name: "submodule_modified",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_modified,
        },
        branch: false,
    },
    Case {
        name: "submodule_deleted_workdir",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_deleted_workdir,
        },
        branch: false,
    },
    Case {
        name: "submodule_new_commits",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_new_commits,
        },
        branch: false,
    },
    Case {
        name: "submodules_interleaved_unstaged",
        setup: Setup::WithSubmodules {
            names: &["ddd", "ppp"],
            setup: setup_submodules_interleaved_unstaged,
        },
        branch: false,
    },
    Case {
        name: "submodules_interleaved_staged",
        setup: Setup::WithSubmodules {
            names: &["ddd", "ppp"],
            setup: setup_submodules_interleaved_staged,
        },
        branch: false,
    },
    Case {
        name: "submodule_gitlink_conflict",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_gitlink_conflict,
        },
        branch: false,
    },
    Case {
        name: "submodule_gitlink_conflict_dirty",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_gitlink_conflict_dirty,
        },
        branch: false,
    },
    // Branch-header cases (`-b` / `--branch`).
    Case {
        name: "branch_clean",
        setup: Setup::Plain(setup_clean),
        branch: true,
    },
    Case {
        name: "branch_upstream_up_to_date",
        setup: Setup::Plain(setup_upstream_up_to_date),
        branch: true,
    },
    Case {
        name: "branch_upstream_ahead",
        setup: Setup::Plain(setup_upstream_ahead),
        branch: true,
    },
    Case {
        name: "branch_upstream_behind",
        setup: Setup::Plain(setup_upstream_behind),
        branch: true,
    },
    Case {
        name: "branch_upstream_diverged",
        setup: Setup::Plain(setup_upstream_diverged),
        branch: true,
    },
    Case {
        name: "branch_upstream_gone",
        setup: Setup::Plain(setup_upstream_gone),
        branch: true,
    },
];

// -- Harness wiring --

fn opts_for(branch: bool) -> OutputOpts {
    OutputOpts {
        format: OutputFormat::Short,
        null_terminate: false,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files: UntrackedFiles::Normal,
        ignored_files: IgnoredFiles::No,
        branch,
        ahead_behind: true,
        quote_path: true,
        show_stash: false,
    }
}

fn snapshot_path(case_name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src/status/snapshots/short")
        .join(format!("{case_name}.snapshot"))
}

fn run_subspy_short(project: &ProjectPath, opts: OutputOpts) -> Vec<u8> {
    crate::paint::force_disable();
    let porcelain_opts = PorcelainOpts {
        null_terminate: opts.null_terminate,
        branch: opts.branch,
        ahead_behind: opts.ahead_behind,
        quote_path: opts.quote_path,
        show_stash: opts.show_stash,
    };
    let with_submodules = project.kind == RepoKind::WithSubmodules;
    assemble_status(
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
            display_short(&mut got, repo, entries, rel, porcelain_opts)?;
            Ok(got)
        },
    )
    .unwrap()
}

fn assert_snapshot(case_name: &str, got: &[u8]) {
    let path = snapshot_path(case_name);
    let updating = std::env::var_os("UPDATE_SHORT_SNAPSHOTS").is_some();

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
             re-run with UPDATE_SHORT_SNAPSHOTS=1 to seed it",
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
    run_case_with(case, opts_for(case.branch));
}

fn run_case_with(case: &Case, opts: OutputOpts) {
    match &case.setup {
        Setup::Plain(setup) => {
            let tmp = TempDir::new().unwrap();
            setup(tmp.path());
            let project = ProjectPath {
                repo_root: tmp.path().to_path_buf(),
                effective_cwd: tmp.path().to_path_buf(),
                kind: RepoKind::Normal,
            };
            let got = run_subspy_short(&project, opts);
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
            let got = run_subspy_short(&project, opts);
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
            let got = run_subspy_short(&project, opts);
            assert_snapshot(case.name, &got);
        }
    }
}

#[test]
fn short_snapshots() {
    for case in CASES {
        run_case(case);
    }
}

#[test]
fn short_no_ahead_behind_snapshots() {
    // `--no-ahead-behind` only changes output when the upstream is
    // diverged from local; matched-OID cases short-circuit identically
    // in both modes. The bracket suffix becomes `[different]`.
    const CASES: &[Case] = &[
        Case {
            name: "branch_no_ahead_behind_upstream_ahead",
            setup: Setup::Plain(setup_upstream_ahead),
            branch: true,
        },
        Case {
            name: "branch_no_ahead_behind_upstream_diverged",
            setup: Setup::Plain(setup_upstream_diverged),
            branch: true,
        },
    ];
    let opts = OutputOpts {
        ahead_behind: false,
        ..opts_for(true)
    };
    for case in CASES {
        run_case_with(case, opts);
    }
}
