//! Snapshot tests for the long-format `display_status` output. Each
//! case builds a fixture repo, runs `display_status` in-process, and
//! compares the bytes to `src/status/snapshots/long/<case>.snapshot`.
//! Regenerate with `UPDATE_LONG_SNAPSHOTS=1`. See CONTRIBUTING.md for
//! workflow details.

use pretty_assertions::assert_eq;
use std::path::{Path, PathBuf};
use tempfile::TempDir;
use testutil::HarnessBuilder;

use crate::{
    RepoKind,
    cli::ProjectPath,
    status::{
        IgnoreSubmodules, IgnoredFiles, OutputFormat, OutputOpts, UntrackedFiles,
        assemble_status, compute_local_statuses, display::display_status,
    },
};

use super::fixtures::*;

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
        name: "assume_unchanged_suppresses",
        setup: Setup::Plain(setup_assume_unchanged_suppresses),
    },
    Case {
        name: "skip_worktree_suppresses",
        setup: Setup::Plain(setup_skip_worktree_suppresses),
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
        name: "unborn_empty",
        setup: Setup::Plain(setup_unborn_empty),
    },
    Case {
        name: "unborn_untracked",
        setup: Setup::Plain(setup_unborn_untracked),
    },
    Case {
        name: "unborn_staged",
        setup: Setup::Plain(setup_unborn_staged),
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
        name: "rebase_interactive_with_conflict",
        setup: Setup::Plain(setup_rebase_interactive_with_conflict),
    },
    Case {
        name: "rebase_apply_with_conflict",
        setup: Setup::Plain(setup_rebase_apply_with_conflict),
    },
    Case {
        name: "bisect",
        setup: Setup::Plain(setup_bisect),
    },
    Case {
        name: "detached_at_tag",
        setup: Setup::Plain(setup_detached_at_tag),
    },
    Case {
        name: "detached_from_tag",
        setup: Setup::Plain(setup_detached_from_tag),
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
        name: "submodule_renamed",
        setup: Setup::WithSubmodules {
            names: &["sub"],
            setup: setup_submodule_renamed,
        },
    },
    Case {
        name: "upstream_up_to_date",
        setup: Setup::Plain(setup_upstream_up_to_date),
    },
    Case {
        name: "upstream_gone",
        setup: Setup::Plain(setup_upstream_gone),
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

// -- Harness wiring --

const fn default_opts() -> OutputOpts {
    OutputOpts {
        format: OutputFormat::Long,
        null_terminate: false,
        ignore_submodules: IgnoreSubmodules::None,
        untracked_files: UntrackedFiles::Normal,
        ignored_files: IgnoredFiles::No,
        branch: false,
        ahead_behind: true,
        quote_path: true,
        show_stash: false,
    }
}

fn snapshot_path(case_name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src/status/snapshots/long")
        .join(format!("{case_name}.snapshot"))
}

fn run_subspy_long(project: &ProjectPath, opts: OutputOpts) -> Vec<u8> {
    crate::paint::force_disable();
    let ahead_behind = opts.ahead_behind;
    let show_stash = opts.show_stash;
    let with_submodules = project.kind == RepoKind::WithSubmodules;
    assemble_status(
        project,
        opts,
        |repo| {
            Ok(if with_submodules {
                compute_local_statuses(&project.repo_root, repo)?
            } else {
                Vec::new()
            })
        },
        |repo, entries, rel| {
            let mut got: Vec<u8> = Vec::new();
            display_status(&mut got, repo, entries, rel, ahead_behind, show_stash)?;
            Ok(got)
        },
    )
    .unwrap()
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

fn run_case(case: &Case, opts: OutputOpts) {
    match &case.setup {
        Setup::Plain(setup) => {
            let tmp = TempDir::new().unwrap();
            setup(tmp.path());
            let project = ProjectPath {
                repo_root: tmp.path().to_path_buf(),
                effective_cwd: tmp.path().to_path_buf(),
                kind: RepoKind::Normal,
            };
            let got = run_subspy_long(&project, opts);
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
            let got = run_subspy_long(&project, opts);
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
            let got = run_subspy_long(&project, opts);
            assert_snapshot(case.name, &got);
        }
    }
}

#[test]
fn long_snapshots() {
    for case in CASES {
        run_case(case, default_opts());
    }
}

#[test]
fn long_show_stash_snapshot() {
    let case = Case {
        name: "show_stash_trailer",
        setup: Setup::Plain(setup_with_stashes),
    };
    let opts = OutputOpts {
        show_stash: true,
        ..default_opts()
    };
    run_case(&case, opts);
}

#[test]
fn long_quote_path_false_snapshot() {
    // `core.quotePath=false` writes high bytes verbatim instead of
    // C-escaped (`café.txt` rather than `"caf\303\251.txt"`).
    let case = Case {
        name: "quote_path_false_high_byte",
        setup: Setup::Plain(setup_modified_high_byte_filename),
    };
    let opts = OutputOpts {
        quote_path: false,
        ..default_opts()
    };
    run_case(&case, opts);
}

#[test]
fn long_untracked_all_snapshot() {
    // `--untracked-files=all` recurses into untracked directories
    // (in contrast to `normal` which collapses them to one entry).
    let case = Case {
        name: "untracked_all_in_dir",
        setup: Setup::Plain(setup_untracked_in_dir),
    };
    let opts = OutputOpts {
        untracked_files: UntrackedFiles::All,
        ..default_opts()
    };
    run_case(&case, opts);
}

#[test]
fn long_no_ahead_behind_snapshots() {
    // `--no-ahead-behind` only changes output when the upstream is
    // diverged from local; matched-OID cases short-circuit identically
    // in both modes. Cover the ahead and diverged shapes.
    const CASES: &[Case] = &[
        Case {
            name: "no_ahead_behind_upstream_ahead",
            setup: Setup::Plain(setup_upstream_ahead),
        },
        Case {
            name: "no_ahead_behind_upstream_diverged",
            setup: Setup::Plain(setup_upstream_diverged),
        },
    ];
    let opts = OutputOpts {
        ahead_behind: false,
        ..default_opts()
    };
    for case in CASES {
        run_case(case, opts);
    }
}
