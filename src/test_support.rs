//! Shared unit test support.

use rstest_reuse::{self, template};

// NOTE: The template currently ignores the reftable case until git2 can read
// reftable repositories (git2-rs#1259).

/// Template that runs a test once per `testutil::RefFormat`.
#[template]
#[rstest::rstest]
#[case::files(RefFormat::Files)]
#[ignore = "reftable: needs libgit2 support (git2-rs#1259)"]
#[case::reftable(RefFormat::Reftable)]
pub fn formats(#[case] ref_format: RefFormat) {}
