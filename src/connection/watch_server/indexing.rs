use std::{collections::BTreeMap, path::PathBuf, sync::MutexGuard};

use git2::Repository;
use log::{error, info};

use super::trace::wtrace;

use crate::{
    DOT_GIT, StatusSummary,
    connection::{
        progress::{ProgressUpdate, broadcast_progress},
        watch_server::{SubmoduleSlot, WatchServer},
    },
    create_progress_bar,
    git::{GitmodulesEntry, submodule_modules_subpath},
    watch::{WatchError, WatchResult},
};

impl WatchServer {
    /// Gathers the status for every submodule in `gitmodule_entries`. When
    /// `place_submod_watches` is true, also places watch roots on their
    /// directories.
    ///
    /// The caller parses `.gitmodules` and owns the placement decision: a
    /// non-replacing pass is only sound while the entries line up one to one
    /// with the live slots (see [`Self::slots_match`]).
    ///
    /// # Errors
    ///
    /// Returns [`notify::Error`] if a submodule watch root cannot be
    /// registered for a path that still exists.
    ///
    /// Per-submodule metadata and status failures are published as
    /// [`StatusSummary::UNREADABLE`] instead.
    #[allow(clippy::too_many_lines)]
    pub(super) fn populate_status_map(
        &mut self,
        gitmodule_entries: Vec<GitmodulesEntry>,
        display_progress: bool,
        place_submod_watches: bool,
        mut status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        use std::sync::atomic::{AtomicU32, Ordering};

        use rayon::prelude::*;

        if gitmodule_entries.is_empty() {
            log::warn!(
                "No submodules found in {}",
                self.root_path.join(".gitmodules").display()
            );
        }

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
            ProgressUpdate::new(0, n_submodules),
        );

        let completed = AtomicU32::new(0);
        let root_path = &self.root_path;
        let progress_subscribers = &self.progress_subscribers;
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
                    ProgressUpdate::new(count, n_submodules),
                );
                if let Some(pb) = &progress_bar {
                    pb.inc(1);
                }

                (relative_path, full_path, modules_path, status)
            })
            .collect();

        status_guard.clear();
        // Bitset accessors require in-bounds indices. `self.submodules` and this
        // pass's slots can differ during a reindex without watcher replacement,
        // so size `pending_rescan` for the larger index range.
        let slot_count = self.submodules.len().max(results.len());
        self.pending_rescan.clear_and_resize(slot_count);
        if place_submod_watches {
            self.modules_path_to_index.clear();
            self.workdir_to_index.clear();
            self.submodules.clear();
        }
        // Every submodule occupies a slot in this loop regardless of whether
        // its status read succeeded. This keeps slot `i` aligned with `results`
        // order across calls. `rayon` preserves order for indexed iterators,
        // and `parse_gitmodules()` returns a consistent order.
        for (i, (relative_path, full_path, modules_path, status)) in results.into_iter().enumerate()
        {
            if let Ok(status) = status {
                status_guard.insert(relative_path.clone(), status);
            } else {
                status_guard.insert(relative_path.clone(), StatusSummary::UNREADABLE);
                self.pending_rescan.insert(i);
            }
            if place_submod_watches {
                self.pending_rescan.insert(i);
                // Preserve `.git/modules/<name>` event routing when the status
                // read fails. Deleted workdirs regain this entry after a restoring
                // reindex resolves the gitlink.
                if let Some(modules_path) = modules_path {
                    self.modules_path_to_index.insert(modules_path, i);
                }
                self.watch_submodule(&full_path)?;
                wtrace!(|s| WatchSubmod {
                    index: i,
                    path: s.intern_path(&full_path),
                });
                // Record the (root-relative) workdir->slot mapping for every
                // submodule, even ones whose status read failed. Path routing
                // must still be able to find a submodule by prefix.
                self.workdir_to_index.insert(PathBuf::from(&relative_path), i);
                self.submodules.push(SubmoduleSlot {
                    relative_path,
                    workdir_path: full_path,
                });
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

    /// Whether `entries` still lines up one to one with the live submodule
    /// slots. Retry marks and event routing key on slot indices, and slot `i`
    /// holds the `i`-th parsed entry, so a non-replacing reindex is only sound
    /// while the entries match the slots in both membership and order.
    pub(super) fn slots_match(&self, entries: &[GitmodulesEntry]) -> bool {
        entries.len() == self.submodules.len()
            && entries
                .iter()
                .zip(&self.submodules)
                .all(|((_, relative_path, _), slot)| *relative_path == slot.relative_path)
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

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::connection::watch_server::layout::GitLayout;

    fn entry(path: &str) -> GitmodulesEntry {
        (path.to_owned(), path.to_owned(), None)
    }

    // Slot `i` must hold the `i`-th parsed entry for retry marks and event
    // routing to reach the right submodule, so a same-set reordering of
    // `.gitmodules` invalidates the slots just like a membership change.
    #[test]
    fn slots_match_requires_membership_and_order() {
        let (_tx, rx) = crossbeam_channel::unbounded();
        let layout = GitLayout::from_dirs(
            Path::new("/repo/.git").to_path_buf(),
            Path::new("/repo/.git").to_path_buf(),
        );
        let mut server = WatchServer::new(Path::new("/repo"), &layout, rx);
        for name in ["libs/a", "libs/b"] {
            server.submodules.push(SubmoduleSlot {
                relative_path: name.to_owned(),
                workdir_path: Path::new("/repo").join(name),
            });
        }

        assert!(server.slots_match(&[entry("libs/a"), entry("libs/b")]));
        assert!(!server.slots_match(&[entry("libs/b"), entry("libs/a")]));
        assert!(!server.slots_match(&[entry("libs/a")]));
        assert!(!server.slots_match(&[entry("libs/a"), entry("libs/b"), entry("libs/c")]));
        assert!(!server.slots_match(&[entry("libs/a"), entry("libs/c")]));

        // An emptied `.gitmodules` mismatches live slots, and matches once the
        // slots are gone too.
        assert!(!server.slots_match(&[]));
        server.submodules.clear();
        assert!(server.slots_match(&[]));
    }
}
