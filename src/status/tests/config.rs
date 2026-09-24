//! Config resolution, for the keys whose accepted values or precedence are not
//! evident from the key alone.
//!
//! Rendering lives in the format submodules. These call the resolvers directly.

use rstest_reuse::apply;
use tempfile::TempDir;
use testutil::{RefFormat, Repo};

use crate::{
    status::{
        ConfigDefaults, UntrackedFiles,
        tracked::{RenameDetection, RenameKey, rename_detection},
    },
    test_support::formats,
};

/// A committed repo with `pairs` applied as local config.
fn repo_with_config(pairs: &[(&str, &str)], ref_format: RefFormat) -> TempDir {
    let tmp = TempDir::new().unwrap();
    let repo = Repo::init(tmp.path());
    repo.write("file.txt", "a\n").add_all().commit("initial");
    for (key, value) in pairs {
        repo.run_git(&["config", key, value]);
    }
    repo.migrate_refs(ref_format);
    tmp
}

fn detection(pairs: &[(&str, &str)], ref_format: RefFormat) -> RenameDetection {
    let tmp = repo_with_config(pairs, ref_format);
    let repo = git2::Repository::open(tmp.path()).unwrap();
    rename_detection(&repo)
}

/// Beyond the three mode names, git falls back to a boolean where true is
/// `normal` and false is `no`. That fallback is why `No` and `0` are accepted
/// while `Normal` is a fatal error.
#[apply(formats)]
fn show_untracked_files_falls_back_to_a_boolean(ref_format: RefFormat) {
    for (value, expected) in [
        ("No", UntrackedFiles::No),
        ("false", UntrackedFiles::No),
        ("0", UntrackedFiles::No),
        ("true", UntrackedFiles::Normal),
        ("1", UntrackedFiles::Normal),
    ] {
        let tmp = repo_with_config(&[("status.showUntrackedFiles", value)], ref_format);
        assert_eq!(
            ConfigDefaults::read(tmp.path()).untracked_files,
            expected,
            "status.showUntrackedFiles={value}"
        );
    }
}

#[apply(formats)]
fn status_renames_outranks_diff_renames(ref_format: RefFormat) {
    // Unset, `diff.renames` applies.
    assert_eq!(
        detection(&[("diff.renames", "false")], ref_format),
        RenameDetection::Off
    );
    // Set, it wins outright.
    assert_eq!(
        detection(
            &[("diff.renames", "false"), ("status.renames", "true")],
            ref_format
        ),
        RenameDetection::On
    );
}

/// Copy detection changes which pairs git picks, so it is reported rather than
/// approximated as plain renames. Both spellings count, case-insensitively.
#[apply(formats)]
fn copies_is_reported_with_its_key(ref_format: RefFormat) {
    for value in ["copies", "copy", "Copies"] {
        assert_eq!(
            detection(&[("status.renames", value)], ref_format),
            RenameDetection::Copies(RenameKey::Status),
            "status.renames={value}"
        );
    }
    assert_eq!(
        detection(&[("diff.renames", "copies")], ref_format),
        RenameDetection::Copies(RenameKey::Diff)
    );
}
