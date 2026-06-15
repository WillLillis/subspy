use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

use log::error;
use notify::Watcher as _;

use crate::{
    DOT_GIT, DOT_GITMODULES,
    connection::watch_server::{
        ROOT_WATCHER_COUNT, ServerWatcher, WatchListItem, WatchReceiver, WatchServer,
    },
};

impl WatchServer {
    /// Builds a watcher wired to a fresh unbounded channel, **without** arming
    /// it -- callers arm the returned watcher with `watcher.watch(path, mode)`.
    /// Separating creation from arming lets [`Self::place_submodule_watch`]
    /// tolerate a missing workdir while still returning a live watcher and an
    /// open receiver.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if the watcher backend cannot be created.
    fn build_watcher(log_path: PathBuf) -> notify::Result<(WatchReceiver, ServerWatcher)> {
        let (tx, rx) = crossbeam_channel::unbounded();
        let watcher = ServerWatcher::new(
            move |res: Result<notify::Event, notify::Error>| {
                if let Err(e) = tx.send(res) {
                    error!("Watcher for {} failed to send -- {e}", log_path.display());
                }
            },
            notify::Config::default(),
        )?;

        Ok((rx, watcher))
    }

    /// Places a watcher of type `mode` on `watch_path`. Returns the receiver and watcher.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if the watcher cannot be created or the path cannot be watched
    fn place_watch(
        watch_path: impl AsRef<Path>,
        mode: notify::RecursiveMode,
    ) -> notify::Result<(WatchReceiver, ServerWatcher)> {
        let (rx, mut watcher) = Self::build_watcher(watch_path.as_ref().to_path_buf())?;
        watcher.watch(watch_path.as_ref(), mode)?;

        Ok((rx, watcher))
    }

    /// Places a **recursive** watch on a submodule working directory, tolerating
    /// a missing directory.
    ///
    /// If `watch_path` does not exist (i.e. the submodule was `rm -rf`'d and we
    /// are reindexing in response to that deletion) the watcher is returned
    /// **disarmed**: created and connected to its channel, so its watcher slot
    /// and `Select` receiver stay valid and index-aligned, but watching nothing.
    /// The deleted submodule's reappearance is detected by the surviving parent
    /// tripwire, whose `Create` event triggers a reindex that re-arms this watch.
    ///
    /// Without this, a reindex landing while the workdir is gone fails fatally
    /// (`PathNotFound`) and takes down the whole server.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if the watcher cannot be created, or if arming it
    /// fails for any reason other than the path being absent.
    pub(super) fn place_submodule_watch(
        watch_path: impl AsRef<Path>,
    ) -> notify::Result<(WatchReceiver, ServerWatcher)> {
        let (rx, mut watcher) = Self::build_watcher(watch_path.as_ref().to_path_buf())?;
        match watcher.watch(watch_path.as_ref(), notify::RecursiveMode::Recursive) {
            Ok(()) => {}
            Err(e) if matches!(e.kind, notify::ErrorKind::PathNotFound) => {
                wtrace!(
                    "submod workdir {} absent; watch left disarmed",
                    watch_path.as_ref().display()
                );
            }
            Err(e) => return Err(e),
        }

        Ok((rx, watcher))
    }

    /// Places watchers on the root path independent of the given repository's submodules
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if any watchers cannot be created
    pub(super) fn place_root_watchers(&mut self) -> notify::Result<()> {
        let (rx, watcher) = match Self::place_watch(
            self.root_gitmodules_path.as_path(),
            notify::RecursiveMode::NonRecursive, // ignored
        ) {
            Ok((rx, watcher)) => (rx, watcher),
            Err(e) => {
                error!(
                    "Failed to place root watch at `{}` - {e}",
                    self.root_gitmodules_path.display()
                );
                Err(e)?
            }
        };
        self.watchers.push(WatchListItem::new(
            DOT_GITMODULES.to_owned(),
            self.root_gitmodules_path.clone(),
            rx,
            watcher,
        ));

        let (rx, watcher) = match Self::place_watch(
            self.root_git_path.as_path(),
            notify::RecursiveMode::Recursive,
        ) {
            Ok((rx, watcher)) => (rx, watcher),
            Err(e) => {
                error!(
                    "Failed to place root watch at `{}` - {e}",
                    self.root_git_path.display()
                );
                Err(e)?
            }
        };
        self.watchers.push(WatchListItem::new(
            DOT_GIT.to_owned(),
            self.root_git_path.clone(),
            rx,
            watcher,
        ));

        debug_assert_eq!(self.watchers.len(), ROOT_WATCHER_COUNT);
        Ok(())
    }

    /// The distinct ancestor directories of every submodule (as absolute paths):
    /// each submodule's parent, and every directory between it and the repo
    /// root, with the root always included. Computed from the root-relative
    /// `workdir_to_index` keys, so a submodule at `libs/foo` contributes
    /// `<root>/libs` and `<root>`.
    fn tripwire_dirs(&self) -> BTreeSet<PathBuf> {
        let mut dirs = BTreeSet::new();
        for rel in self.workdir_to_index.keys() {
            let mut cur = rel.as_path();
            while let Some(parent) = cur.parent() {
                if parent.as_os_str().is_empty() {
                    // Reached the top level; the parent is the repo root itself.
                    dirs.insert(self.root_path.clone());
                    break;
                }
                dirs.insert(self.root_path.join(parent));
                cur = parent;
            }
        }
        dirs
    }

    /// (Re)places the tripwire watches from the current submodule set.
    /// Best-effort: a directory that can't be watched is logged and skipped
    /// rather than failing the whole reindex.
    pub(super) fn place_tripwires(&mut self) {
        self.tripwires.clear();
        for dir in self.tripwire_dirs() {
            match Self::place_watch(&dir, notify::RecursiveMode::NonRecursive) {
                Ok((rx, watcher)) => {
                    wtrace!("tripwire {}", dir.display());
                    let rel = dir
                        .strip_prefix(&self.root_path)
                        .unwrap_or(&dir)
                        .to_string_lossy()
                        .into_owned();
                    self.tripwires
                        .push(WatchListItem::new(rel, dir, rx, watcher));
                }
                Err(e) => error!("Failed to place tripwire on {} -- {e}", dir.display()),
            }
        }
    }
}
