//! Config resolution, for the keys whose accepted values or precedence are not
//! evident from the key alone.
//!
//! Rendering lives in the format submodules. These call the resolvers directly.

use rstest_reuse::apply;
use tempfile::TempDir;
use testutil::{RefFormat, Repo};

use crate::{
    status::{
        ConfigDefaults, OutputFormat, PorcelainVersion, StatusFlags, UntrackedFiles,
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

// -- StatusFlags::resolve --

#[test]
fn explicit_flags_outrank_config() {
    let config = ConfigDefaults {
        short: true,
        untracked_files: UntrackedFiles::No,
        quote_path: false,
        show_stash: true,
        ..ConfigDefaults::GIT
    };
    let opts = StatusFlags {
        format: Some(OutputFormat::Long),
        untracked_files: Some(UntrackedFiles::All),
        quote_path: Some(true),
        show_stash: Some(false),
        ..StatusFlags::default()
    }
    .resolve(config);
    assert_eq!(opts.format, OutputFormat::Long);
    assert_eq!(opts.untracked_files, UntrackedFiles::All);
    assert!(opts.quote_path);
    assert!(!opts.show_stash);

    let opts = StatusFlags::default().resolve(config);
    assert_eq!(opts.format, OutputFormat::Short);
    assert_eq!(opts.untracked_files, UntrackedFiles::No);
    assert!(!opts.quote_path);
    assert!(opts.show_stash);
}

/// Bare `-z` is porcelain v1, even over `status.short`.
#[test]
fn bare_null_terminate_is_porcelain_v1() {
    let config = ConfigDefaults {
        short: true,
        ..ConfigDefaults::GIT
    };
    let flags = StatusFlags {
        null_terminate: true,
        ..StatusFlags::default()
    };
    assert_eq!(
        flags.resolve(config).format,
        OutputFormat::Porcelain(PorcelainVersion::V1)
    );
    let short = StatusFlags {
        format: Some(OutputFormat::Short),
        ..flags
    };
    assert_eq!(short.resolve(config).format, OutputFormat::Short);
}

/// `status.branch` reaches the short format only. Porcelain headers need an
/// explicit `--branch`.
#[test]
fn status_branch_reaches_short_only() {
    let config = ConfigDefaults {
        branch: true,
        ..ConfigDefaults::GIT
    };
    let with_format = |format| StatusFlags {
        format: Some(format),
        ..StatusFlags::default()
    };
    assert!(with_format(OutputFormat::Short).resolve(config).branch);
    let porcelain = with_format(OutputFormat::Porcelain(PorcelainVersion::V2));
    assert!(!porcelain.resolve(config).branch);
    let explicit = StatusFlags {
        branch: true,
        ..porcelain
    };
    assert!(explicit.resolve(config).branch);
}

/// `status.aheadBehind` reaches the long format only. Porcelain keeps real
/// counts unless `--no-ahead-behind` says otherwise.
#[test]
fn status_ahead_behind_reaches_long_only() {
    let config = ConfigDefaults {
        ahead_behind: false,
        ..ConfigDefaults::GIT
    };
    let with_format = |format| StatusFlags {
        format: Some(format),
        ..StatusFlags::default()
    };
    assert!(!with_format(OutputFormat::Long).resolve(config).ahead_behind);
    let porcelain = with_format(OutputFormat::Porcelain(PorcelainVersion::V2));
    assert!(porcelain.resolve(config).ahead_behind);
    let explicit = StatusFlags {
        ahead_behind: Some(false),
        ..porcelain
    };
    assert!(!explicit.resolve(config).ahead_behind);
}
