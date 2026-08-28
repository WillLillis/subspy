use std::{collections::BTreeMap, path::PathBuf, sync::MutexGuard};

use git2::Repository;
use log::{error, info};

use super::trace::wtrace;

use crate::{
    DOT_GIT, StatusSummary,
    connection::{
        progress::{ProgressUpdate, broadcast_progress},
        watch_server::{ROOT_WATCHER_COUNT, WatchListItem, WatchServer},
    },
    create_progress_bar,
    git::{parse_gitmodules, submodule_modules_subpath},
    watch::{WatchError, WatchResult},
};

impl WatchServer {
    /// Gathers the status for all submodules within the given repository. When
    /// `place_submod_watches` is true, also places watchers on their directories.
    ///
    /// # Errors
    ///
    /// Returns:
    ///     - [`git2::Error`] if `.gitmodules` cannot be opened or parsed.
    ///     - [`notify::Error`] if a submodule watcher cannot be created, or
    ///       if it cannot be armed for a path that still exists.
    ///
    /// Per-submodule metadata and status failures are published as
    /// [`StatusSummary::UNREADABLE`] instead.
    #[allow(clippy::too_many_lines)]
    pub(super) fn populate_status_map(
        &mut self,
        display_progress: bool,
        place_submod_watches: bool,
        mut status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        use std::sync::atomic::{AtomicU32, Ordering};

        use rayon::prelude::*;

        // git replaces `.gitmodules` via an atomic rename, so a reader always
        // sees a complete old-or-new file, and the `.gitmodules` watcher re-fires
        // for eventual consistency.
        let gitmodule_entries = parse_gitmodules(&self.root_path)?;

        if gitmodule_entries.is_empty() {
            log::warn!(
                "No submodules found in {}",
                self.root_path.join(".gitmodules").display()
            );
        }

        self.root_rebasing = self.root_git_path.join("rebase-merge").exists();

        info!("Indexing project at {}", self.root_path.display());
        let n_submodules = gitmodule_entries.len() as u32;
        wtrace!(Reindexing {
            n: n_submodules,
            place_watches: place_submod_watches,
        });
        let progress_bar = display_progress
            .then(|| create_progress_bar(u64::from(n_submodules), "Indexing submodules"));

        broadcast_progress(
            &self.progress_subscribers,
            &self.progress_queue,
            ProgressUpdate::new(0, n_submodules),
        );

        let completed = AtomicU32::new(0);
        let root_path = &self.root_path;
        let progress_subscribers = &self.progress_subscribers;
        let progress_queue = &self.progress_queue;
        let tl_repo = thread_local::ThreadLocal::new();

        let results: Vec<_> = gitmodule_entries
            .into_par_iter()
            .map(|(_, relative_path, _)| {
                let full_path = root_path.join(&relative_path);

                // `get_modules_path` reads the submodule's `.git` gitlink to find
                // its real `.git/modules/<name>` dir. It is resolved here, off the
                // gitlink and independent of the repo/status read, and carried
                // separately from the (fallible) status so that a transient
                // status-read failure still leaves us the `modules_path_to_index`
                // routing entry the `.git/modules` watcher needs. A deleted workdir
                // has no gitlink, so `NotFound` leaves `modules_path` unresolved while
                // the status read below reports `DELETED_WORKDIR`.
                let (modules_path, status): (Option<PathBuf>, WatchResult<StatusSummary>) =
                    match self.get_modules_path(&relative_path) {
                        // A hard resolution error (not a missing gitlink) leaves no
                        // path to route with, so fail the slot and skip the read.
                        Err(e)
                            if !matches!(
                                &e,
                                WatchError::IO(io) if io.kind() == std::io::ErrorKind::NotFound
                            ) =>
                        {
                            error!(
                                "Failed to get modules path for submodule {relative_path}: {e}\nSkipping...",
                            );
                            (None, Err(e))
                        }
                        resolved => {
                            let modules_path = resolved.ok();
                            let status = (|| {
                                let repo = tl_repo.get_or_try(|| Repository::open(root_path))
                                    .map_err(|e| {
                                        error!("Failed to open repository while indexing {relative_path}: {e}");
                                        e
                                    })?;

                                // Status reads run concurrently with git's atomic index
                                // replacement pattern. Failures become `StatusSummary::UNREADABLE`
                                // below and queue a retry.
                                //
                                // libgit2 reports a missing submodule workdir as `WD_DELETED`,
                                // which maps to `DELETED_WORKDIR` by relative path and remains
                                // correct even under a rename.
                                let status = repo.submodule_status(&relative_path, git2::SubmoduleIgnore::None)
                                    .map_err(|e| {
                                        error!("Failed to read status for {relative_path} while populating status map: {e}");
                                        e
                                    })?.into();

                                Ok(status)
                            })();
                            (modules_path, status)
                        }
                    };

                let count = completed.fetch_add(1, Ordering::Relaxed) + 1;
                broadcast_progress(
                    progress_subscribers,
                    progress_queue,
                    ProgressUpdate::new(count, n_submodules),
                );
                if let Some(pb) = &progress_bar {
                    pb.inc(1);
                }

                (relative_path, full_path, modules_path, status)
            })
            .collect();

        status_guard.clear();
        // Bitset accessors require in-bounds indices. `self.watchers` and this
        // pass's submodule slots can differ during a reindex without watcher
        // replacement, so size both sets for the larger index range.
        let watcher_slot_count = self.watchers.len().max(ROOT_WATCHER_COUNT + results.len());
        self.skip_set.clear_and_resize(watcher_slot_count);
        self.pending_rescan.clear_and_resize(watcher_slot_count);
        if place_submod_watches {
            self.modules_path_to_index.clear();
            self.workdir_to_index.clear();
        }
        // NOTE: Watcher placement must not be parallelized. Creating
        // `notify::RecommendedWatcher` instances concurrently on rayon threads
        // causes watchers to silently miss subsequent filesystem events, likely
        // due to interference between rayon's work-stealing and notify's
        // internal event threads.
        //
        // Every submodule occupies a slot in this loop regardless of whether
        // its status read succeeded. This keeps `index` (= ROOT_WATCHER_COUNT + i)
        // aligned with watcher positions across calls. `rayon` preserves order for
        // indexed iterators, and `parse_gitmodules()` returns a consistent order.
        for (i, (relative_path, full_path, modules_path, status)) in results.into_iter().enumerate()
        {
            let index = ROOT_WATCHER_COUNT + i;
            if let Ok(status) = status {
                status_guard.insert(relative_path.clone(), status);
            } else {
                status_guard.insert(relative_path.clone(), StatusSummary::UNREADABLE);
                self.pending_rescan.insert(index);
            }
            if place_submod_watches {
                self.pending_rescan.insert(index);
                // Preserve `.git/modules/<name>` event routing when the status
                // read fails. Deleted workdirs regain this entry after a restoring
                // reindex resolves the gitlink.
                if let Some(modules_path) = modules_path {
                    self.modules_path_to_index.insert(modules_path, index);
                }
                let (rx, watcher) = Self::place_submodule_watch(&full_path)?;
                wtrace!(|s| WatchSubmod {
                    index,
                    path: s.intern_path(&full_path),
                });
                // Record the (root-relative) workdir->index mapping for every
                // submodule, even ones whose status read failed. Tripwire
                // routing must still be able to find a submodule by path.
                self.workdir_to_index
                    .insert(PathBuf::from(&relative_path), index);
                self.watchers
                    .push(WatchListItem::new(relative_path, full_path, rx, watcher));
            }
        }
        drop(status_guard);

        // Tripwires depend only on the submodule set, so (re)place them whenever
        // the submodule watches are (re)placed.
        if place_submod_watches {
            self.place_tripwires();
        }

        if let Some(pb) = &progress_bar {
            pb.finish();
        }

        Ok(())
    }

    /// Returns the path to the submodule's `.git/modules/` entry (e.g.
    /// `.git/modules/libs/foo` for a submodule at `libs/foo`).
    fn get_modules_path(&self, submod_rel_path: &str) -> WatchResult<PathBuf> {
        // Read the submodule's `.git` file to find its actual modules path.
        // We can't just assume `.git/modules/<submod_rel_path>` because git
        // doesn't update the modules directory when a submodule is renamed.
        let dot_git_path = self.root_path.join(submod_rel_path).join(DOT_GIT);
        let dot_git_bytes = std::fs::read(&dot_git_path)?;

        // `submodule_modules_subpath` returns the submodule's path within
        // `.git/modules/` (the bit after the marker).
        let Some(modules_subpath) = submodule_modules_subpath(&dot_git_bytes) else {
            return Err(WatchError::NotSubmoduleGitlink(dot_git_path));
        };

        // `modules_subpath` is raw gitfile data, while `Path::join` needs an
        // `OsStr`. Unix can construct it from those bytes verbatim. Other targets
        // have no lossless conversion from arbitrary bytes, so require UTF-8.
        #[cfg(unix)]
        let suffix = {
            use std::os::unix::ffi::OsStrExt as _;
            std::ffi::OsStr::from_bytes(modules_subpath)
        };
        #[cfg(not(unix))]
        let suffix = std::str::from_utf8(modules_subpath).map_err(|error| {
            WatchError::NonUtf8SubmoduleName {
                path: dot_git_path,
                error,
            }
        })?;

        Ok(self.root_modules_path.join(suffix))
    }
}
