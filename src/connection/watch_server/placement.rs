use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

use log::error;
use notify::Watcher as _;

use super::trace::wtrace;

use crate::{
    DOT_GIT, DOT_GITMODULES,
    connection::watch_server::{
        ROOT_WATCHER_COUNT, ServerWatcher, WatchEntry, WatchReceiver, WatchServer,
    },
};

impl WatchServer {
    /// Builds an _unarmed_ filesystem watcher and its event receiver.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if the watcher backend cannot be created.
    fn build_watcher() -> notify::Result<(WatchReceiver, ServerWatcher)> {
        let (tx, rx) = crossbeam_channel::unbounded();
        let watcher = ServerWatcher::new(
            move |res: Result<notify::Event, notify::Error>| {
                _ = tx.send(res);
            },
            notify::Config::default(),
        )?;

        Ok((rx, watcher))
    }

    /// Places a watcher of type `mode` on `watch_path`. Returns the receiver and watcher.
    ///
    /// # Errors
    ///
    /// Returns [`notify::Error`] if watcher creation or path registration fails.
    fn place_watch(
        watch_path: impl AsRef<Path>,
        mode: notify::RecursiveMode,
    ) -> notify::Result<(WatchReceiver, ServerWatcher)> {
        let (rx, mut watcher) = Self::build_watcher()?;
        watcher.watch(watch_path.as_ref(), mode)?;

        Ok((rx, watcher))
    }

    /// Places a recursive watch on a submodule working directory. A missing directory
    /// yields a watcher with no registered paths.
    ///
    /// If `watch_path` does not exist (i.e. the submodule was removed and we are
    /// reindexing in response to that deletion) the watcher is returned inactive.
    /// Its connected channel preserves watcher slot and `Select` receiver alignment.
    /// The deleted submodule's reapperance is detected by the surviving parent
    /// tripwire, whose `Create` event triggers a reindex that places a new watch.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if the watcher cannot be created, or if arming it
    /// fails for any reason other than the path being absent.
    pub(super) fn place_submodule_watch(
        watch_path: impl AsRef<Path>,
    ) -> notify::Result<(WatchReceiver, ServerWatcher)> {
        let (rx, mut watcher) = Self::build_watcher()?;
        match watcher.watch(watch_path.as_ref(), notify::RecursiveMode::Recursive) {
            Ok(()) => {}
            Err(e) if matches!(e.kind, notify::ErrorKind::PathNotFound) => {
                wtrace!(|s| WatchDisarmed {
                    path: s.intern_path(watch_path.as_ref())
                });
            }
            Err(e) => return Err(e),
        }

        Ok((rx, watcher))
    }

    /// Places root watchers on `.gitmodules`, per-worktree git state, and shared
    /// refs outside the per-worktree git directory.
    ///
    /// # Errors
    ///
    /// Returns [`notify::Error`] if watcher creation or path registration fails.
    pub(super) fn place_root_watchers(&mut self) -> notify::Result<()> {
        let (rx, watcher) = match Self::place_watch(
            self.root_gitmodules_path.as_path(),
            notify::RecursiveMode::NonRecursive,
        ) {
            Ok((rx, watcher)) => (rx, watcher),
            Err(e) => {
                error!(
                    "Failed to place root watch at `{}`: {e}",
                    self.root_gitmodules_path.display()
                );
                Err(e)?
            }
        };
        self.watchers.push(WatchEntry::new(
            DOT_GITMODULES.to_owned(),
            self.root_gitmodules_path.clone(),
            rx,
            watcher,
        ));

        let (rx, mut watcher) = match Self::place_watch(
            self.root_git_path.as_path(),
            notify::RecursiveMode::Recursive,
        ) {
            Ok((rx, watcher)) => (rx, watcher),
            Err(e) => {
                error!(
                    "Failed to place root watch at `{}`: {e}",
                    self.root_git_path.display()
                );
                Err(e)?
            }
        };

        // Linked worktrees keep shared refs outside the per-worktree git directory.
        // Add the shared `refs` directory to the existing watcher and let
        // `classify_event` select branch ref changes. Limiting this watch to `refs`
        // excludes object and submodule traffic from the main repository. The
        // containment check detects layouts already covered by the recursive watch.
        let common_refs = self
            .root_refs_heads_path
            .parent()
            .unwrap_or(self.root_refs_heads_path.as_path());
        if !common_refs.starts_with(&self.root_git_path)
            && let Err(e) = watcher.watch(common_refs, notify::RecursiveMode::Recursive)
        {
            error!(
                "Failed to watch common-dir refs at `{}`: {e}",
                common_refs.display()
            );
            Err(e)?;
        }

        self.watchers.push(WatchEntry::new(
            DOT_GIT.to_owned(),
            self.root_git_path.clone(),
            rx,
            watcher,
        ));

        debug_assert_eq!(self.watchers.len(), ROOT_WATCHER_COUNT);
        Ok(())
    }

    /// Returns the distinct absolute ancestor directories of every submodule. These
    /// include each submodule's parent, every directory between it and the repository
    /// root, and the root itself when at least one submodule exists.
    ///
    /// For example, a submodule at `libs/foo` contributes `<root>/libs` and `<root>`.
    fn tripwire_dirs(&self) -> BTreeSet<PathBuf> {
        let mut dirs = BTreeSet::new();
        if self.workdir_to_index.is_empty() {
            return dirs;
        }
        dirs.insert(self.root_path.clone());
        for rel in self.workdir_to_index.keys() {
            let mut cur = rel.as_path();
            while let Some(parent) = cur.parent() {
                if parent.as_os_str().is_empty() {
                    break;
                }
                dirs.insert(self.root_path.join(parent));
                cur = parent;
            }
        }
        dirs
    }

    /// (Re)places the tripwire watches from the current submodule set. Failures
    /// are logged and not propagated.
    pub(super) fn place_tripwires(&mut self) {
        self.tripwires.clear();
        for dir in self.tripwire_dirs() {
            match Self::place_watch(&dir, notify::RecursiveMode::NonRecursive) {
                Ok((rx, watcher)) => {
                    wtrace!(|s| TripwirePlaced {
                        path: s.intern_path(&dir)
                    });
                    let rel = dir
                        .strip_prefix(&self.root_path)
                        .unwrap_or(&dir)
                        .to_string_lossy()
                        .into_owned();
                    self.tripwires.push(WatchEntry::new(rel, dir, rx, watcher));
                }
                Err(e) => error!("Failed to place tripwire on {}: {e}", dir.display()),
            }
        }
    }
}
