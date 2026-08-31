use std::path::Path;

use log::error;
use notify::Watcher as _;
use rustc_hash::FxHashSet;

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
    /// The deleted submodule's reappearance is detected by the surviving parent
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
                wtrace!(|s| WatchUnregistered {
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

    /// Reconciles tripwire watches with the current submodule set. Existing coverage
    /// is retained, missing coverage is established before obsolete watchers are dropped.
    pub(super) fn place_tripwires(&mut self) {
        // Deduplicate root-relative ancestor paths for every candidate and shared
        // parent
        let mut desired = FxHashSet::default();
        if !self.workdir_to_index.is_empty() {
            desired.insert(Path::new(""));
            for workdir in self.workdir_to_index.keys() {
                desired.extend(
                    workdir
                        .ancestors()
                        .skip(1)
                        .filter(|parent| !parent.as_os_str().is_empty()),
                );
            }
        }
        let root_path = &self.root_path;
        let tripwires = &mut self.tripwires;
        let old_len = tripwires.len();
        debug_assert!(
            tripwires
                .windows(2)
                .all(|pair| pair[0].watch_path < pair[1].watch_path)
        );

        // Search only the original, sorted prefix while appending additions.
        // This establishes new coverage before obsolete entries are removed.
        for &relative in &desired {
            let exists = tripwires[..old_len]
                .binary_search_by(|entry| {
                    entry
                        .watch_path
                        .strip_prefix(root_path)
                        .unwrap_or(&entry.watch_path)
                        .cmp(relative)
                })
                .is_ok();
            if exists {
                continue;
            }

            let watch_path = root_path.join(relative);
            match Self::place_watch(&watch_path, notify::RecursiveMode::NonRecursive) {
                Ok((rx, watcher)) => {
                    wtrace!(|s| TripwirePlaced {
                        path: s.intern_path(&watch_path)
                    });
                    tripwires.push(WatchEntry::new(
                        relative.to_string_lossy().into_owned(),
                        watch_path,
                        rx,
                        watcher,
                    ));
                }
                Err(e) => error!("Failed to place tripwire on {}: {e}", watch_path.display()),
            }
        }

        let added = tripwires.len() > old_len;
        tripwires.retain(|entry| {
            let relative = entry
                .watch_path
                .strip_prefix(root_path)
                .unwrap_or(&entry.watch_path);
            desired.contains(relative)
        });
        if added {
            tripwires.sort_unstable_by(|a, b| a.watch_path.cmp(&b.watch_path));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use tempfile::TempDir;

    use super::*;
    use crate::connection::watch_server::layout::GitLayout;

    fn receiver_for(server: &WatchServer, path: &Path) -> WatchReceiver {
        server
            .tripwires
            .iter()
            .find(|entry| entry.watch_path == path)
            .unwrap_or_else(|| panic!("no tripwire for {}", path.display()))
            .receiver
            .clone()
    }

    #[test]
    fn tripwire_reconciliation_preserves_unchanged_coverage() {
        let temp = TempDir::new().unwrap();
        let root = temp.path();
        std::fs::create_dir(root.join("libs")).unwrap();
        std::fs::create_dir(root.join("vendor")).unwrap();

        let (_tx, rx) = crossbeam_channel::unbounded();
        let layout = GitLayout::from_dirs(root.join(".git"), root.join(".git"));
        let mut server = WatchServer::new(root, &layout, rx);

        server
            .workdir_to_index
            .insert(PathBuf::from("libs/a"), ROOT_WATCHER_COUNT);
        server.place_tripwires();

        let root_receiver = receiver_for(&server, root);
        let libs_receiver = receiver_for(&server, &root.join("libs"));

        // Reconciliation with unchanged topology must preserve both watchers
        // and any events already queued on their receivers.
        server.place_tripwires();

        assert!(root_receiver.same_channel(&receiver_for(&server, root)));
        assert!(libs_receiver.same_channel(&receiver_for(&server, &root.join("libs"))));

        // Replace one parent directory with another. The repository-root
        // tripwire remains useful and must survive the topology change.
        server.workdir_to_index.clear();
        server
            .workdir_to_index
            .insert(PathBuf::from("vendor/b"), ROOT_WATCHER_COUNT);
        server.place_tripwires();

        assert!(root_receiver.same_channel(&receiver_for(&server, root)));

        let paths: Vec<_> = server
            .tripwires
            .iter()
            .map(|entry| entry.watch_path.clone())
            .collect();
        assert_eq!(paths, vec![root.to_path_buf(), root.join("vendor")]);

        // The add-one/remove-one reconciliation above leaves the vector the
        // same length. A second pass verifies that it was nevertheless sorted
        // and that the newly added watcher is now retained.
        let vendor_receiver = receiver_for(&server, &root.join("vendor"));
        server.place_tripwires();

        assert!(vendor_receiver.same_channel(&receiver_for(&server, &root.join("vendor"))));

        // Removing the final submodule removes all tripwire coverage.
        server.workdir_to_index.clear();
        server.place_tripwires();
        assert!(server.tripwires.is_empty());
    }
}
