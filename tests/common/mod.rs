pub use testutil::*;

use rstest_reuse::{self, template};

/// Template that repeats a test 10 times to surface race conditions.
#[template]
#[rstest::rstest]
#[allow(clippy::used_underscore_binding)]
pub fn repeat(#[values(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)] _run: u32) {}
