//! Fixture-setup helpers shared by the long-format and short-format
//! snapshot test modules. `Case` and `Setup` describe one
//! fixture-and-cwd pair; the `setup_*` functions mutate a fresh repo
//! into the state under test.

use std::path::Path;
use testutil::{Repo, TestHarness};

pub struct Case {
    pub name: &'static str,
    pub setup: Setup,
}

pub enum Setup {
    /// `effective_cwd` equals the repo root.
    Plain(fn(&Path)),
    /// `effective_cwd` is `repo_root/<subdir>`.
    Subdir {
        setup: fn(&Path),
        subdir: &'static str,
    },
    /// Repo built via `HarnessBuilder` with submodules.
    WithSubmodules {
        names: &'static [&'static str],
        setup: fn(&TestHarness),
    },
}

// -- Plain setups --

pub fn setup_clean(root: &Path) {
    Repo::init(root)
        .write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
}

pub fn setup_modified_workdir(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("file.txt", "modified\n");
}

pub fn setup_staged_modified(root: &Path) {
    setup_clean(root);
    Repo::new(root)
        .write("file.txt", "staged change\n")
        .add("file.txt");
}

pub fn setup_staged_new(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("new.txt", "x\n").add("new.txt");
}

pub fn setup_deleted_workdir(root: &Path) {
    setup_clean(root);
    Repo::new(root).rm_file("file.txt");
}

pub fn setup_deleted_staged(root: &Path) {
    setup_clean(root);
    Repo::new(root).rm_tracked("file.txt");
}

pub fn setup_renamed_staged(root: &Path) {
    // Longer body so libgit2's rename detector recognizes the move.
    Repo::init(root)
        .write("file.txt", "line one\nline two\nline three\nline four\n")
        .add_all()
        .commit("initial")
        .mv("file.txt", "renamed.txt");
}

pub fn setup_renamed_staged_in_subdir(root: &Path) {
    Repo::init(root)
        .write(
            "sub/file.txt",
            "line one\nline two\nline three\nline four\n",
        )
        .add_all()
        .commit("initial")
        .mv("sub/file.txt", "sub/renamed.txt");
}

/// A plain filesystem move (`mv`, not `git mv`) of a tracked file plus an edit,
/// left UNSTAGED. git reports the old path deleted and the new path untracked --
/// it never pairs a tracked deletion with an untracked file as a worktree
/// rename, even though the bodies are similar. Guards against re-enabling
/// `renames_index_to_workdir`, which made libgit2 emit a spurious worktree
/// rename here (` R old -> new`), diverging from git and producing porcelain a
/// consumer can't parse (the old path landed in a record with no `XY ` prefix).
pub fn setup_moved_modified_unstaged(root: &Path) {
    Repo::init(root)
        .write(
            "file.txt",
            "line one\nline two\nline three\nline four\nline five\nline six\n",
        )
        .add_all()
        .commit("initial")
        // Plain move + edit; the new file stays similar enough that rename
        // detection *would* pair it if it ran on the worktree diff.
        .write(
            "renamed.txt",
            "line one\nline two CHANGED\nline three\nline four\nline five\nline six\n",
        )
        .rm_file("file.txt");
}

/// The same plain move + edit, then `git add`. It is now a staged rename whose
/// content also changed, so git2 sets both `INDEX_RENAMED` and `INDEX_MODIFIED`.
/// git renders this as `renamed:` / `R`, never `modified:` / `M`; guards the
/// XY-character and long-label ordering (RENAMED must outrank MODIFIED).
pub fn setup_moved_modified_staged(root: &Path) {
    setup_moved_modified_unstaged(root);
    Repo::new(root).add_all();
}

pub fn setup_unborn_empty(root: &Path) {
    Repo::init(root);
}

pub fn setup_unborn_untracked(root: &Path) {
    Repo::init(root).write("untracked.txt", "x\n");
}

pub fn setup_unborn_staged(root: &Path) {
    Repo::init(root)
        .write("staged.txt", "x\n")
        .add("staged.txt");
}

pub fn setup_untracked(root: &Path) {
    setup_clean(root);
    Repo::new(root).write("untracked.txt", "x\n");
}

pub fn setup_untracked_in_dir(root: &Path) {
    setup_clean(root);
    Repo::new(root)
        .mkdir("subdir")
        .write("subdir/a.txt", "x\n")
        .write("subdir/b.txt", "y\n");
}

pub fn setup_untracked_high_byte_filename(root: &Path) {
    setup_clean(root);
    // U+00E9 (e-acute) -> bytes 0xC3 0xA9; quoted form is "caf\303\251.txt".
    Repo::new(root).write("caf\u{00e9}.txt", "x\n");
}

pub fn setup_modified_high_byte_filename(root: &Path) {
    // Commit a file whose name contains a high-byte (U+00E9 -> 0xC3 0xA9),
    // then modify it. Used to verify `core.quotePath` handling on a path
    // that's tracked (rather than untracked).
    let repo = Repo::init(root);
    repo.write("caf\u{00e9}.txt", "initial\n")
        .add_all()
        .commit("initial");
    repo.write("caf\u{00e9}.txt", "modified\n");
}

pub fn setup_ignored(root: &Path) {
    let repo = Repo::init(root);
    repo.write(".gitignore", "ignored_dir/\nignored.log\n")
        .add(".gitignore")
        .commit("initial");
    repo.mkdir("ignored_dir")
        .write("ignored_dir/a.txt", "x\n")
        .write("ignored.log", "log\n");
}

pub fn setup_ignored_with_untracked(root: &Path) {
    setup_ignored(root);
    Repo::new(root).write("untracked.txt", "x\n");
}

pub fn setup_with_stashes(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    // Create two stashes by modifying then stashing twice.
    repo.write("file.txt", "first\n");
    repo.run_git(&["stash"]);
    repo.write("file.txt", "second\n");
    repo.run_git(&["stash"]);
}

pub fn setup_assume_unchanged_suppresses(root: &Path) {
    let repo = Repo::init(root);
    repo.write("a.txt", "a\n")
        .write("b.txt", "b\n")
        .add_all()
        .commit("initial");
    repo.run_git(&["update-index", "--assume-unchanged", "a.txt"]);
    // Modify both files; only b.txt should show up.
    repo.write("a.txt", "modified\n")
        .write("b.txt", "modified\n");
}

pub fn setup_skip_worktree_suppresses(root: &Path) {
    let repo = Repo::init(root);
    repo.write("a.txt", "a\n")
        .write("b.txt", "b\n")
        .add_all()
        .commit("initial");
    repo.run_git(&["update-index", "--skip-worktree", "a.txt"]);
    repo.write("a.txt", "modified\n")
        .write("b.txt", "modified\n");
}

pub fn setup_bisect(root: &Path) {
    let repo = Repo::init(root);
    repo.write("a.txt", "one\n").add_all().commit("one");
    repo.write("b.txt", "two\n").add_all().commit("two");
    repo.write("c.txt", "three\n").add_all().commit("three");
    repo.run_git(&["bisect", "start"]);
    repo.run_git(&["bisect", "bad", "HEAD"]);
    repo.run_git(&["bisect", "good", "HEAD~2"]);
}

pub fn setup_detached_at_tag(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "one\n").add_all().commit("one");
    // Use `update-ref` to create the tag: `git tag` honors local
    // `tag.gpgSign` / `tag.forceSignAnnotated` config that some
    // developer environments set, which would fail here.
    repo.run_git(&["update-ref", "refs/tags/v1.0", "HEAD"]);
    repo.write("file.txt", "two\n").add_all().commit("two");
    repo.checkout("v1.0");
}

pub fn setup_detached_from_tag(root: &Path) {
    setup_detached_at_tag(root);
    // Make a new commit while detached: HEAD moves past where the
    // `checkout v1.0` reflog entry landed, so git switches `at` to `from`.
    Repo::new(root)
        .write("extra.txt", "extra\n")
        .add_all()
        .commit("extra commit while detached");
}

pub fn setup_merge_with_conflict(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("file.txt", "feature change\n")
        .add_all()
        .commit("feature")
        .checkout("master")
        .write("file.txt", "master change\n")
        .add_all()
        .commit("master");
    repo.try_git(&["merge", "feature"]);
}

pub fn setup_merge_with_conflict_in_subdir(root: &Path) {
    let repo = Repo::init(root);
    repo.write("sub/file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("sub/file.txt", "feature change\n")
        .add_all()
        .commit("feature")
        .checkout("master")
        .write("sub/file.txt", "master change\n")
        .add_all()
        .commit("master");
    repo.try_git(&["merge", "feature"]);
}

pub fn setup_rebase_apply_with_conflict(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("file.txt", "from feature\n")
        .add_all()
        .commit("feature commit")
        .checkout("master")
        .write("file.txt", "from master\n")
        .add_all()
        .commit("master commit");
    // `--apply` selects the legacy apply backend (rebase-apply/ directory),
    // exercising the `HeaderBody::RebaseWithApplyBackend` code path.
    repo.try_git(&["rebase", "--apply", "feature"]);
}

pub fn setup_rebase_interactive_with_conflict(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("file.txt", "from feature\n")
        .add_all()
        .commit("feature commit")
        .checkout("master")
        .write("file.txt", "from master\n")
        .add_all()
        .commit("master commit");
    // `-i` forces the rebase-merge backend (interactive). `GIT_SEQUENCE_EDITOR=true`
    // (set by `git_may_fail`) accepts the default todo: one `pick` that conflicts
    // on file.txt and stops the rebase mid-flight.
    repo.try_git(&["rebase", "-i", "feature"]);
}

/// A six-commit interactive rebase that stops on a mid-stack conflict,
/// leaving more than the two commands git lists in each direction. Exercises
/// the plural "Last/Next commands" header lines and the "(see more in file
/// ...)" pointer that only the done list gets.
pub fn setup_rebase_interactive_multi_command(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("a.txt", "a\n")
        .add_all()
        .commit("F1 add a")
        .write("b.txt", "b\n")
        .add_all()
        .commit("F2 add b")
        .write("file.txt", "from feature\n")
        .add_all()
        .commit("F3 edit file")
        .write("c.txt", "c\n")
        .add_all()
        .commit("F4 add c")
        .write("d.txt", "d\n")
        .add_all()
        .commit("F5 add d")
        .write("e.txt", "e\n")
        .add_all()
        .commit("F6 add e")
        .checkout("master")
        .write("file.txt", "from master\n")
        .add_all()
        .commit("master commit")
        .checkout("feature");
    // Replay feature's six commits onto master. F1 and F2 add new files and
    // apply cleanly; F3 edits file.txt and conflicts with master's edit,
    // stopping with three commands done (F1, F2, F3) and three remaining
    // (F4, F5, F6). `GIT_SEQUENCE_EDITOR=true` (set by `git_may_fail`) accepts
    // the generated todo as-is.
    repo.try_git(&["rebase", "-i", "master"]);
}

pub fn setup_cherry_pick_with_conflict(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "base\n")
        .add_all()
        .commit("base")
        .branch("feature")
        .write("file.txt", "from feature\n")
        .add_all()
        .commit("feature commit")
        .checkout("master")
        .write("file.txt", "from master\n")
        .add_all()
        .commit("master commit");
    repo.try_git(&["cherry-pick", "feature"]);
}

// -- Submodule setups --

pub fn setup_submodule_modified(h: &TestHarness) {
    h.submodule("sub").write("README.md", "modified\n");
}

pub fn setup_submodule_deleted_workdir(h: &TestHarness) {
    let path = h.submodule("sub").path().to_path_buf();
    std::fs::remove_dir_all(&path).unwrap();
}

pub fn setup_submodule_new_commits(h: &TestHarness) {
    h.submodule("sub")
        .write("README.md", "moved forward\n")
        .add_all()
        .commit("submodule advances");
}

pub fn setup_submodule_renamed(h: &TestHarness) {
    // `git mv old new` on a submodule updates .gitmodules in place and
    // moves the gitlink in the index. HEAD still has the gitlink at the
    // old path, so subspy's submodule_changes should classify this as a
    // rename (same OID, different path) rather than a deletion.
    h.root().run_git(&["mv", "sub", "renamed_sub"]);
}

/// A submodule with both a new commit (HEAD advanced past the parent's
/// gitlink) and modified working-tree content -- the `(modified content, new
/// commits)` shape a submodule that is itself a superproject must still report.
pub fn setup_submodule_modified_and_new_commits(h: &TestHarness) {
    h.submodule("sub")
        .write("README.md", "moved forward\n")
        .add_all()
        .commit("submodule advances")
        .write("README.md", "and now dirty\n");
}

/// Files and submodules whose paths interleave, all with unstaged changes.
/// The submodule rows must sort among the file rows by path
/// (`aaa.txt` < `ddd` < `mmm.txt` < `ppp` < `zzz.txt`) rather than trailing
/// them, in every renderer.
pub fn setup_submodules_interleaved_unstaged(h: &TestHarness) {
    let root = h.root();
    root.write("aaa.txt", "a\n")
        .write("mmm.txt", "m\n")
        .write("zzz.txt", "z\n")
        .add_all()
        .commit("bracketing files");
    root.write("aaa.txt", "a2\n")
        .write("mmm.txt", "m2\n")
        .write("zzz.txt", "z2\n");
    h.submodule("ddd").write("README.md", "dirty\n");
    h.submodule("ppp").write("README.md", "dirty\n");
}

/// Like [`setup_submodules_interleaved_unstaged`] but everything is staged:
/// staged file modifications plus two submodules advanced with their gitlinks
/// staged, exercising the staged-section merge.
pub fn setup_submodules_interleaved_staged(h: &TestHarness) {
    let root = h.root();
    root.write("aaa.txt", "a\n")
        .write("mmm.txt", "m\n")
        .write("zzz.txt", "z\n")
        .add_all()
        .commit("bracketing files");
    root.write("aaa.txt", "a2\n")
        .write("mmm.txt", "m2\n")
        .write("zzz.txt", "z2\n")
        .add_all();
    h.submodule("ddd")
        .write("README.md", "moved\n")
        .add_all()
        .commit("advance ddd");
    h.submodule("ppp")
        .write("README.md", "moved\n")
        .add_all()
        .commit("advance ppp");
    root.add("ddd");
    root.add("ppp");
}

/// `git rev-parse <refname>` in `repo`, trimmed. Used to branch from a captured
/// commit rather than a branch name (so the default-branch name is irrelevant).
fn rev_parse(repo: &Repo, refname: &str) -> String {
    let out = repo.try_git(&["rev-parse", refname]);
    assert!(out.status.success(), "git rev-parse {refname} failed");
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

/// A submodule whose gitlink diverged on two branches and was then merged into
/// an unmerged (conflicted) gitlink: `sub` ends up at index stages 1-3 with no
/// stage 0. git shows it only under "Unmerged paths"; subspy must not also
/// report it as a staged deletion (a conflicted gitlink reads as "missing from
/// the index" when only stage 0 is consulted) nor as an untracked directory.
pub fn setup_submodule_gitlink_conflict(h: &TestHarness) {
    let sub = h.submodule("sub");
    let sub_base = rev_parse(sub, "HEAD");
    // Two divergent submodule commits, each on its own branch so both stay
    // reachable in this clone.
    sub.run_git(&["checkout", "-qb", "side_a"]);
    sub.write("README.md", "side A\n")
        .add_all()
        .commit("sub side A");
    sub.run_git(&["checkout", "-qb", "side_b", &sub_base]);
    sub.write("README.md", "side B\n")
        .add_all()
        .commit("sub side B");

    let root = h.root();
    let root_base = rev_parse(root, "HEAD");
    // branchA records the gitlink at side_a.
    root.run_git(&["checkout", "-qb", "branchA", &root_base]);
    sub.checkout("side_a");
    root.add("sub");
    root.commit("root: sub on side A");
    // branchB (from the same base) records the gitlink at side_b.
    root.run_git(&["checkout", "-qb", "branchB", &root_base]);
    sub.checkout("side_b");
    root.add("sub");
    root.commit("root: sub on side B");
    // Merging branchA leaves `sub` unmerged: the gitlink diverged on both sides
    // (neither is an ancestor), so git cannot auto-resolve it.
    root.try_git(&["merge", "branchA", "-m", "merge sub conflict"]);
}

/// Like [`setup_submodule_gitlink_conflict`], but the conflicted submodule's own
/// working tree is also dirty: advanced past the "ours" gitlink (commit-changed)
/// with modified and untracked content. git folds all of this into the single
/// unmerged entry -- `SCMU` in porcelain v2 -- and never reports a separate
/// dirty submodule row, which is what exercises the conflicted-submodule fold.
pub fn setup_submodule_gitlink_conflict_dirty(h: &TestHarness) {
    setup_submodule_gitlink_conflict(h);
    let sub = h.submodule("sub");
    // A new commit (commit-changed `C`)...
    sub.write("README.md", "advance\n")
        .add_all()
        .commit("sub advance");
    // ...plus modified (`M`) and untracked (`U`) working-tree content.
    sub.write("README.md", "modified\n")
        .write("untracked.txt", "x\n");
}

// -- Upstream-tracking setups --
//
// We fake an upstream without a real remote: `update-ref` positions
// `refs/remotes/origin/master`, and the configs below wire `master` to
// track it. The url + fetch refspec are both required for git to treat
// `origin/master` as a remote-tracking ref (otherwise `@{u}` won't
// resolve); the url itself is a dummy and never fetched.

fn configure_master_tracks_origin(repo: &Repo) {
    repo.run_git(&["config", "branch.master.remote", "origin"]);
    repo.run_git(&["config", "branch.master.merge", "refs/heads/master"]);
    repo.run_git(&["config", "remote.origin.url", "/dev/null"]);
    repo.run_git(&[
        "config",
        "remote.origin.fetch",
        "+refs/heads/*:refs/remotes/origin/*",
    ]);
}

pub fn setup_upstream_up_to_date(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    configure_master_tracks_origin(&repo);
}

pub fn setup_upstream_gone(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    configure_master_tracks_origin(&repo);
    // Delete the tracking ref after wiring up config: simulates `git fetch
    // --prune` removing a remote branch while local config still references it.
    repo.run_git(&["update-ref", "-d", "refs/remotes/origin/master"]);
}

pub fn setup_upstream_ahead(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    configure_master_tracks_origin(&repo);
    repo.write("file.txt", "ahead\n")
        .add_all()
        .commit("local commit");
}

pub fn setup_upstream_behind(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    repo.write("file.txt", "remote\n")
        .add_all()
        .commit("remote commit");
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    repo.run_git(&["reset", "-q", "--hard", "HEAD~1"]);
    configure_master_tracks_origin(&repo);
}

pub fn setup_upstream_diverged(root: &Path) {
    let repo = Repo::init(root);
    repo.write("file.txt", "initial\n")
        .add_all()
        .commit("initial");
    repo.write("file.txt", "remote\n")
        .add_all()
        .commit("remote commit");
    repo.run_git(&["update-ref", "refs/remotes/origin/master", "HEAD"]);
    repo.run_git(&["reset", "-q", "--hard", "HEAD~1"]);
    configure_master_tracks_origin(&repo);
    repo.write("file.txt", "local\n")
        .add_all()
        .commit("local commit");
}
