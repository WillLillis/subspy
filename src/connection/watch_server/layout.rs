//! Resolution of a repository's on-disk git directory layout.
//!
//! For a normal repository the working tree's `.git` is a directory, and both
//! the per-worktree state (index, HEAD, the submodule gitdirs under `modules/`,
//! the `index.lock`/`HEAD.lock` files, rebase markers) and the shared state
//! (refs) live inside it. For a linked worktree the two diverge: `.git` is a
//! *file* pointing at `<main>/.git/worktrees/<name>/`, which holds the
//! per-worktree state, while refs stay in the main repository's `.git/` (the
//! "common dir"). A `--separate-git-dir` repository likewise keeps its git dir
//! outside the working tree.
//!
//! [`GitLayout`] resolves both directories via libgit2 so the watch server
//! places its watches and reads its lock/index/HEAD/refs state from the right
//! locations regardless of which shape the repository takes.

use std::path::{Path, PathBuf};

use git2::Repository;

use crate::watch::WatchResult;

/// The resolved git-directory layout for a watched working tree.
///
/// `git_dir` is the per-worktree directory ([`Repository::path`]); `common_dir`
/// is the shared one ([`Repository::commondir`]). For a non-worktree repository
/// the two are equal.
pub(super) struct GitLayout {
    git_dir: PathBuf,
    common_dir: PathBuf,
}

impl GitLayout {
    /// Resolves the layout for the working tree at `root`.
    ///
    /// libgit2 handles a plain `.git` directory, a linked worktree, and a
    /// `--separate-git-dir` repository uniformly.
    ///
    /// # Errors
    ///
    /// Propagates `git2::Error` if `root` is not a repository libgit2 can open.
    pub(super) fn resolve(root: &Path) -> WatchResult<Self> {
        let repo = Repository::open(root)?;
        Ok(Self {
            git_dir: repo.path().to_path_buf(),
            common_dir: repo.commondir().to_path_buf(),
        })
    }

    /// The per-worktree git directory ([`Repository::path`]). The recursive
    /// watch target, and the anchor for index/HEAD/modules/locks/rebase markers.
    pub(super) fn git_dir(&self) -> &Path {
        &self.git_dir
    }

    /// `<git_dir>/index` -- the working tree's index (per-worktree).
    pub(super) fn index(&self) -> PathBuf {
        self.git_dir.join("index")
    }

    /// `<git_dir>/HEAD` -- the working tree's HEAD (per-worktree).
    pub(super) fn head(&self) -> PathBuf {
        self.git_dir.join("HEAD")
    }

    /// `<git_dir>/modules` -- where this working tree's submodule gitdirs live
    /// (per-worktree: a worktree's submodules sit under
    /// `.git/worktrees/<name>/modules/`, not the main repo's `.git/modules/`).
    pub(super) fn modules(&self) -> PathBuf {
        self.git_dir.join("modules")
    }

    /// `<git_dir>/index.lock`.
    pub(super) fn index_lock(&self) -> PathBuf {
        self.git_dir.join("index.lock")
    }

    /// `<git_dir>/HEAD.lock`.
    pub(super) fn head_lock(&self) -> PathBuf {
        self.git_dir.join("HEAD.lock")
    }

    /// `<common_dir>/refs/heads` -- branch refs are shared across worktrees, so
    /// this is anchored on the common dir, not the per-worktree git dir.
    pub(super) fn refs_heads(&self) -> PathBuf {
        self.common_dir.join("refs").join("heads")
    }
}

#[cfg(test)]
impl GitLayout {
    /// Builds a layout directly from a git dir and common dir, bypassing
    /// libgit2. For tests that exercise path derivation without a real repo.
    pub const fn from_dirs(git_dir: PathBuf, common_dir: PathBuf) -> Self {
        Self {
            git_dir,
            common_dir,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;
    use tempfile::TempDir;

    fn git(dir: &Path, args: &[&str]) {
        let ok = Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .output()
            .expect("git invocation failed")
            .status
            .success();
        assert!(ok, "git {args:?} failed in {}", dir.display());
    }

    fn init_repo(dir: &Path) {
        git(dir, &["init", "-q"]);
        git(dir, &["config", "user.email", "t@t"]);
        git(dir, &["config", "user.name", "t"]);
        std::fs::write(dir.join("f.txt"), "x\n").unwrap();
        git(dir, &["add", "."]);
        git(dir, &["commit", "-qm", "init"]);
    }

    #[test]
    fn normal_repo_git_dir_equals_common_dir() {
        let tmp = TempDir::new().unwrap();
        let root = tmp.path();
        init_repo(root);

        let layout = GitLayout::resolve(root).unwrap();
        // For a plain repo the two coincide, and every per-worktree path sits
        // directly under `<root>/.git`.
        assert_eq!(
            layout.git_dir(),
            layout.refs_heads().parent().unwrap().parent().unwrap()
        );
        assert!(layout.index().ends_with(".git/index"));
        assert!(layout.head().ends_with(".git/HEAD"));
        assert!(layout.modules().ends_with(".git/modules"));
        assert!(layout.index_lock().ends_with(".git/index.lock"));
        assert!(layout.refs_heads().ends_with(".git/refs/heads"));
        // git_dir resolves under the working tree.
        assert!(layout.git_dir().starts_with(root));
    }

    #[test]
    fn linked_worktree_splits_git_dir_from_common_dir() {
        let tmp = TempDir::new().unwrap();
        let main = tmp.path().join("main");
        std::fs::create_dir(&main).unwrap();
        init_repo(&main);
        // A linked worktree: its git dir is `<main>/.git/worktrees/wt`, but refs
        // stay in `<main>/.git`.
        git(&main, &["worktree", "add", "-q", "../wt", "HEAD"]);
        let wt = tmp.path().join("wt");

        let layout = GitLayout::resolve(&wt).unwrap();

        // Per-worktree state lives under `.git/worktrees/wt/`.
        assert!(
            layout.git_dir().ends_with("worktrees/wt"),
            "git_dir = {}",
            layout.git_dir().display()
        );
        assert!(layout.index().ends_with("worktrees/wt/index"));
        assert!(layout.head().ends_with("worktrees/wt/HEAD"));
        assert!(layout.modules().ends_with("worktrees/wt/modules"));
        assert!(layout.index_lock().ends_with("worktrees/wt/index.lock"));

        // Refs are shared: anchored on the main repo's `.git`, NOT the worktree.
        assert!(
            layout.refs_heads().ends_with("main/.git/refs/heads"),
            "refs_heads = {}",
            layout.refs_heads().display()
        );
        assert!(!layout.refs_heads().starts_with(layout.git_dir()));
    }

    #[test]
    fn separate_git_dir_resolves_external_git_dir() {
        let tmp = TempDir::new().unwrap();
        let work = tmp.path().join("work");
        let gitdir = tmp.path().join("external.git");
        std::fs::create_dir_all(&work).unwrap();
        // `git init --separate-git-dir` puts the git dir outside the work tree;
        // `.git` becomes a gitlink file.
        git(
            &work,
            &["init", "-q", "--separate-git-dir", gitdir.to_str().unwrap()],
        );

        let layout = GitLayout::resolve(&work).unwrap();
        // git_dir is the external dir; common_dir equals it (no worktree split).
        assert!(
            layout.index().starts_with(&gitdir),
            "index = {}",
            layout.index().display()
        );
        assert!(layout.refs_heads().starts_with(&gitdir));
    }
}
