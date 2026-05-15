//! Snapshot tests for the long-format `display_status` output. Each
//! case builds a fixture repo, runs `display_status` in-process, and
//! compares the bytes to `src/status/snapshots/long/<case>.snapshot`.
//! Regenerate with `UPDATE_LONG_SNAPSHOTS=1`. See CONTRIBUTING.md for
//! workflow details.

use git2::Repository;
use pretty_assertions::assert_eq;
use std::path::{Path, PathBuf};
use tempfile::TempDir;
use testutil::HarnessBuilder;

use crate::{
    RepoKind,
    cli::ProjectPath,
    status::{
        IgnoreSubmodules, OutputFormat, OutputOpts, StatusEntries, UntrackedFiles,
        compute_local_statuses, cwd_relative_to_repo, deleted_submodule_paths,
        display::display_status, relativize::Relativizer, submodule::apply_ignore_submodules,
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

// -- Harness wiring --

const fn default_opts() -> OutputOpts {
    OutputOpts {
        format: OutputFormat::Long,
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

    let cwd_rel = cwd_relative_to_repo(&project.repo_root, &project.effective_cwd);
    let rel = Relativizer::new(&cwd_rel);

    let entries = StatusEntries {
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
