use std::path::{Path, PathBuf};

use log::error;
use notify::Watcher as _;
use rustc_hash::FxHashSet;

use super::trace::wtrace;

use crate::connection::watch_server::{ServerWatcher, SharedWatch, WatchServer};

impl WatchServer {
    /// Builds an unarmed shared watcher instance and its event receiver.
    ///
    /// Instances must not be created concurrently: `notify::RecommendedWatcher`
    /// instances created on rayon threads at the same time silently miss
    /// subsequent filesystem events. Every caller runs on the server thread.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if the watcher backend cannot be created.
    fn build_watcher() -> notify::Result<SharedWatch> {
        let (tx, rx) = crossbeam_channel::unbounded();
        let watcher = ServerWatcher::new(
            move |res: Result<notify::Event, notify::Error>| {
                _ = tx.send(res);
            },
            notify::Config::default(),
        )?;

        Ok(SharedWatch {
            receiver: rx,
            watcher,
        })
    }

    /// Places the idle watcher for the parked state: a single recursive watch
    /// over the whole repository.
    ///
    /// # Errors
    ///
    /// Returns [`notify::Error`] if watcher creation or path registration fails.
    pub(super) fn place_idle_watch(&self) -> notify::Result<SharedWatch> {
        let mut watch = Self::build_watcher()?;
        watch
            .watcher
            .watch(&self.root_path, notify::RecursiveMode::Recursive)?;

        Ok(watch)
    }

    /// Places the git watcher: a recursive watch on the git directory, plus the
    /// shared refs directory when a linked worktree keeps it outside. Replaces
    /// any previous git watcher.
    ///
    /// # Errors
    ///
    /// Returns [`notify::Error`] if watcher creation or path registration fails.
    pub(super) fn place_git_watch(&mut self) -> notify::Result<()> {
        let mut watch = Self::build_watcher()?;
        if let Err(e) = watch
            .watcher
            .watch(&self.root_git_path, notify::RecursiveMode::Recursive)
        {
            error!(
                "Failed to place git watch at `{}`: {e}",
                self.root_git_path.display()
            );
            return Err(e);
        }

        // Linked worktrees keep shared refs outside the per-worktree git directory.
        // Add the shared `refs` directory as a second watch root and let
        // `classify_git_event` select branch ref changes. Limiting this watch to
        // `refs` excludes object and submodule traffic from the main repository.
        // The containment check detects layouts already covered by the recursive
        // watch.
        let common_refs = self
            .root_refs_heads_path
            .parent()
            .unwrap_or(self.root_refs_heads_path.as_path());
        if !common_refs.starts_with(&self.root_git_path)
            && let Err(e) = watch
                .watcher
                .watch(common_refs, notify::RecursiveMode::Recursive)
        {
            error!(
                "Failed to watch common-dir refs at `{}`: {e}",
                common_refs.display()
            );
            return Err(e);
        }

        self.git_watch = Some(watch);
        Ok(())
    }

    /// Places a fresh tree watcher carrying its always-on non-recursive watch
    /// on the repository root. That root watch delivers `.gitmodules` changes
    /// (a directory watch survives git's rename-over rewrite, unlike a watch on
    /// the file's own inode, which dies with the replaced inode) and doubles as
    /// the root-level tripwire. Submodule workdir roots and ancestor tripwires
    /// are added afterwards by `populate_status_map`.
    ///
    /// Replaces any previous tree watcher, dropping whatever its queue held.
    /// Callers pair this with a reindex that re-reads every submodule.
    ///
    /// # Errors
    ///
    /// Returns [`notify::Error`] if watcher creation or path registration fails.
    pub(super) fn place_tree_watch(&mut self) -> notify::Result<()> {
        let mut watch = Self::build_watcher()?;
        if let Err(e) = watch
            .watcher
            .watch(&self.root_path, notify::RecursiveMode::NonRecursive)
        {
            error!(
                "Failed to place tree watch at `{}`: {e}",
                self.root_path.display()
            );
            return Err(e);
        }

        self.tree_watch = Some(watch);
        Ok(())
    }

    /// Adds a recursive watch root on the tree watcher for a submodule working
    /// directory.
    ///
    /// If `watch_path` does not exist (i.e. the submodule was removed and we are
    /// reindexing in response to that deletion) the submodule is left without
    /// workdir coverage. Its reappearance is detected by a surviving ancestor
    /// tripwire, whose `Create` event triggers a reindex that places a new
    /// watch root.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if registration fails for any reason other than
    /// the path being absent.
    pub(super) fn watch_submodule(&mut self, watch_path: &Path) -> notify::Result<()> {
        let tree = self.tree_watch.as_mut().expect("tree watch not placed");
        match tree
            .watcher
            .watch(watch_path, notify::RecursiveMode::Recursive)
        {
            Err(e) if matches!(e.kind, notify::ErrorKind::PathNotFound) => {
                wtrace!(|s| WatchUnregistered {
                    path: s.intern_path(watch_path)
                });
                Ok(())
            }
            other => other,
        }
    }

    /// Registers non-recursive tripwire watches on the tree watcher for the
    /// ancestor directories of every submodule. The repository root is excluded
    /// because the tree watcher always watches it. Expects a freshly placed
    /// tree watcher: roots are registered from scratch, not reconciled.
    pub(super) fn place_tripwires(&mut self) {
        // Deduplicate root-relative ancestor paths across submodules sharing
        // parents, then sort for deterministic placement and debug output.
        let mut desired = FxHashSet::default();
        for workdir in self.workdir_to_index.keys() {
            desired.extend(
                workdir
                    .ancestors()
                    .skip(1)
                    .filter(|parent| !parent.as_os_str().is_empty()),
            );
        }
        let mut desired: Vec<PathBuf> = desired.into_iter().map(Path::to_path_buf).collect();
        desired.sort_unstable();

        self.tripwires.clear();
        let tree = self.tree_watch.as_mut().expect("tree watch not placed");
        for relative in desired {
            let watch_path = self.root_path.join(&relative);
            match tree
                .watcher
                .watch(&watch_path, notify::RecursiveMode::NonRecursive)
            {
                Ok(()) => {
                    wtrace!(|s| TripwirePlaced {
                        path: s.intern_path(&watch_path)
                    });
                    self.tripwires.push(relative);
                }
                Err(e) => error!("Failed to place tripwire on {}: {e}", watch_path.display()),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use tempfile::TempDir;

    use super::*;
    use crate::connection::watch_server::layout::GitLayout;

    #[test]
    fn tripwires_cover_submodule_ancestors_excluding_root() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();
        std::fs::create_dir_all(root.join("libs/numeric")).unwrap();
        std::fs::create_dir(root.join("vendor")).unwrap();

        let (_tx, rx) = crossbeam_channel::unbounded();
        let layout = GitLayout::from_dirs(root.join(".git"), root.join(".git"));
        let mut server = WatchServer::new(root, &layout, rx);
        server.place_tree_watch().unwrap();

        server.workdir_to_index.insert(PathBuf::from("libs/a"), 0);
        server
            .workdir_to_index
            .insert(PathBuf::from("libs/numeric/b"), 1);
        server.workdir_to_index.insert(PathBuf::from("vendor/c"), 2);
        server.place_tripwires();
        assert_eq!(
            server.tripwires,
            vec![
                PathBuf::from("libs"),
                PathBuf::from("libs/numeric"),
                PathBuf::from("vendor")
            ]
        );

        // A replacing reindex rebuilds the tree watcher and re-places tripwires
        // from the new submodule set.
        server.place_tree_watch().unwrap();
        server.workdir_to_index.clear();
        server.workdir_to_index.insert(PathBuf::from("vendor/c"), 0);
        server.place_tripwires();
        assert_eq!(server.tripwires, vec![PathBuf::from("vendor")]);

        // A missing ancestor directory is skipped rather than aborting placement.
        server.place_tree_watch().unwrap();
        server.workdir_to_index.insert(PathBuf::from("ghost/x"), 1);
        server.place_tripwires();
        assert_eq!(server.tripwires, vec![PathBuf::from("vendor")]);

        // No submodules leaves only the always-on root watch.
        server.place_tree_watch().unwrap();
        server.workdir_to_index.clear();
        server.place_tripwires();
        assert!(server.tripwires.is_empty());
    }
}
