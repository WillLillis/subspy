//! Config resolution, for the keys whose accepted values or precedence are not
//! evident from the key alone.
//!
//! Rendering lives in the format submodules; these call the resolvers directly.

use tempfile::TempDir;
use testutil::Repo;

use crate::status::{
    ConfigDefaults, UntrackedFiles,
    tracked::{RenameDetection, RenameKey, rename_detection},
};

/// A committed repo with `pairs` applied as local config.
fn repo_with_config(pairs: &[(&str, &str)]) -> TempDir {
    let tmp = TempDir::new().unwrap();
    let repo = Repo::init(tmp.path());
    repo.write("file.txt", "a\n").add_all().commit("initial");
    for (key, value) in pairs {
        repo.run_git(&["config", key, value]);
    }
    tmp
}

fn detection(pairs: &[(&str, &str)]) -> RenameDetection {
    let tmp = repo_with_config(pairs);
    let repo = git2::Repository::open(tmp.path()).unwrap();
    rename_detection(&repo)
}

/// Beyond the three mode names, git falls back to a boolean where true is
/// `normal` and false is `no`. That fallback is why `No` and `0` are accepted
/// while `Normal` is a fatal error.
#[test]
fn show_untracked_files_falls_back_to_a_boolean() {
    for (value, expected) in [
        ("No", UntrackedFiles::No),
        ("false", UntrackedFiles::No),
        ("0", UntrackedFiles::No),
        ("true", UntrackedFiles::Normal),
        ("1", UntrackedFiles::Normal),
    ] {
        let tmp = repo_with_config(&[("status.showUntrackedFiles", value)]);
        assert_eq!(
            ConfigDefaults::read(tmp.path()).untracked_files,
            expected,
            "status.showUntrackedFiles={value}"
        );
    }
}

#[test]
fn status_renames_outranks_diff_renames() {
    // Unset, `diff.renames` applies.
    assert_eq!(
        detection(&[("diff.renames", "false")]),
        RenameDetection::Off
    );
    // Set, it wins outright.
    assert_eq!(
        detection(&[("diff.renames", "false"), ("status.renames", "true")]),
        RenameDetection::On
    );
}

/// Copy detection changes which pairs git picks, so it is reported rather than
/// approximated as plain renames. Both spellings count, case-insensitively.
#[test]
fn copies_is_reported_with_its_key() {
    for value in ["copies", "copy", "Copies"] {
        assert_eq!(
            detection(&[("status.renames", value)]),
            RenameDetection::Copies(RenameKey::Status),
            "status.renames={value}"
        );
    }
    assert_eq!(
        detection(&[("diff.renames", "copies")]),
        RenameDetection::Copies(RenameKey::Diff)
    );
}
