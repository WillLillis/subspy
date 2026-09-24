//! Shared integration test support.

#![allow(
    unused_macros,
    reason = "each test binary applies only the templates it needs"
)]

pub use testutil::*;

use rstest_reuse::{self, template};

// NOTE: Both templates currently ignore the reftable case until git2 can read
// reftable repositories (git2-rs#1259).

/// Template that runs a test once per [`RefFormat`].
#[template]
#[rstest::rstest]
#[case::files(RefFormat::Files)]
#[ignore = "reftable: needs libgit2 support (git2-rs#1259)"]
#[case::reftable(RefFormat::Reftable)]
pub fn formats(#[case] ref_format: RefFormat) {}

/// Template that runs a test once per [`RefFormat`], 10 times each to surface
/// race conditions.
#[template]
#[rstest::rstest]
#[case::files(RefFormat::Files)]
#[ignore = "reftable: needs libgit2 support (git2-rs#1259)"]
#[case::reftable(RefFormat::Reftable)]
#[allow(clippy::used_underscore_binding)]
pub fn repeat(#[case] ref_format: RefFormat, #[values(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)] _run: u32) {}
