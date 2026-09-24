//! Trees whose root and submodules store refs in different formats.

mod common;

use common::{HarnessBuilder, RefFormat};
use rstest_reuse::{self, apply, template};
use subspy::StatusSummary;

/// Template that runs a test on a files root with reftable submodules and on
/// the reverse, 10 times each to surface race conditions.
#[template]
#[rstest::rstest]
#[case::reftable_submodules(RefFormat::Files, RefFormat::Reftable)]
#[case::files_submodules(RefFormat::Reftable, RefFormat::Files)]
#[ignore = "reftable: needs libgit2 support (git2-rs#1259)"]
#[allow(clippy::used_underscore_binding)]
fn mixed_trees(
    #[case] root_format: RefFormat,
    #[case] submodule_format: RefFormat,
    #[values(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)] _run: u32,
) {
}

#[apply(mixed_trees)]
fn content_changes_in_submodules(root_format: RefFormat, submodule_format: RefFormat, _run: u32) {
    let harness = HarnessBuilder::new()
        .ref_format(root_format)
        .submodule_ref_format(submodule_format)
        .submodule("sub_a")
        .submodule("sub_b")
        .build();
    harness.assert_all_clean();

    harness.submodule("sub_a").write("untracked.txt", "x\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    harness.submodule("sub_b").write("README.md", "changed\n");
    harness.assert_submodule_status("sub_b", StatusSummary::MODIFIED_CONTENT);
}

#[apply(mixed_trees)]
fn ref_updates_in_submodules(root_format: RefFormat, submodule_format: RefFormat, _run: u32) {
    let harness = HarnessBuilder::new()
        .ref_format(root_format)
        .submodule_ref_format(submodule_format)
        .submodule("sub_a")
        .build();
    harness.assert_all_clean();

    let sub_a = harness.submodule("sub_a");
    sub_a.write("new.txt", "content\n");
    harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
    sub_a.add_all();
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
    sub_a.commit("add new.txt");
    harness.assert_submodule_status("sub_a", StatusSummary::NEW_COMMITS);

    // In a reftable submodule, a soft reset rewrites nothing but the ref table.
    sub_a.run_git(&["reset", "--soft", "HEAD~1"]);
    harness.assert_submodule_status("sub_a", StatusSummary::MODIFIED_CONTENT);
}

#[apply(mixed_trees)]
fn submodule_added_at_runtime(root_format: RefFormat, submodule_format: RefFormat, _run: u32) {
    let mut harness = HarnessBuilder::new()
        .ref_format(root_format)
        .submodule_ref_format(submodule_format)
        .submodule("sub_a")
        .build();
    harness.assert_all_clean();

    harness.add_submodule_no_commit("sub_b");
    harness.assert_submodule_status("sub_b", StatusSummary::STAGED_NEW);
    harness.root().commit("Add submodule sub_b");
    harness.assert_submodule_status("sub_b", StatusSummary::clean());

    let sub_b = harness.submodule("sub_b");
    sub_b.write("new.txt", "content\n");
    harness.assert_submodule_status("sub_b", StatusSummary::UNTRACKED_CONTENT);
    sub_b.add_all();
    harness.assert_submodule_status("sub_b", StatusSummary::MODIFIED_CONTENT);
    sub_b.commit("add new.txt");
    harness.assert_submodule_status("sub_b", StatusSummary::NEW_COMMITS);
}
