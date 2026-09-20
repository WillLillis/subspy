use std::{collections::BTreeMap, path::PathBuf, sync::MutexGuard};

use git2::Repository;
use log::{error, info};

use super::trace::wtrace;

use crate::{
    DOT_GIT, StatusSummary,
    connection::{
        progress::{ProgressUpdate, broadcast_progress},
        watch_server::WatchServer,
    },
    create_progress_bar,
    git::{submodule_modules_subpath, substatus},
    watch::{WatchError, WatchResult},
};

impl WatchServer {
    /// Gathers the status for every path in `submodule_paths`.
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
        submodule_paths: Vec<String>,
        display_progress: bool,
        mut status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        use std::sync::atomic::{AtomicU32, Ordering};

        use rayon::prelude::*;

        if submodule_paths.is_empty() {
            log::warn!(
                "No submodule gitlinks found in the index of {}",
                self.root_path.display()
            );
        }

        info!("Indexing project at {}", self.root_path.display());
        let n_submodules = submodule_paths.len() as u32;
        wtrace!(Reindexing { n: n_submodules });
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

        let results: Vec<_> = submodule_paths
            .into_par_iter()
            .map(|relative_path| {
                let full_path = root_path.join(&relative_path);

                // `get_modules_path` reads the submodule's `.git` gitlink to find
                // its real `.git/modules/<name>` dir. It is resolved here, off the
                // gitlink and independent of the repo/status read, and carried
                // separately from the (fallible) status so that a transient
                // status-read failure still leaves us the `modules_path_to_index`
                // routing entry the `.git/modules` watcher needs. `Ok(None)` is a
                // shape with no entry by design, and its status read proceeds.
                let (modules_path, status): (Option<PathBuf>, WatchResult<StatusSummary>) =
                    match self.get_modules_path(&relative_path) {
                        // A hard resolution error leaves no path to route with,
                        // so fail the slot and skip the read.
                        Err(e) => {
                            error!(
                                "Failed to get modules path for submodule {relative_path}: {e}\nSkipping...",
                            );
                            (None, Err(e))
                        }
                        Ok(modules_path) => {
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
                                // A missing submodule workdir reads as DELETED_WORKDIR, keyed by
                                // relative path, which remains correct even under a rename.
                                let status = substatus::submodule_status(repo, &relative_path)
                                    .map_err(|e| {
                                        error!("Failed to read status for {relative_path} while populating status map: {e}");
                                        e
                                    })?;

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
        self.pending_rescan.clear_and_resize(results.len());
        self.modules_path_to_index.clear();
        self.workdir_to_index.clear();
        self.submodules.clear();
        // Every submodule occupies a slot in this loop regardless of whether
        // its status read succeeded. This keeps slot `i` aligned with `results`
        // order across calls. `rayon` preserves order for indexed iterators,
        // and the paths arrive in index order.
        for (i, (relative_path, full_path, modules_path, status)) in results.into_iter().enumerate()
        {
            if let Ok(status) = status {
                status_guard.insert(relative_path.clone(), status);
            } else {
                status_guard.insert(relative_path.clone(), StatusSummary::UNREADABLE);
            }
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
            self.workdir_to_index
                .insert(PathBuf::from(&relative_path), i);
            self.submodules.push(relative_path);
        }
        drop(status_guard);

        // Tripwires depend only on the submodule set, so (re)place them alongside
        // the submodule watches
        self.place_tripwires();

        if let Some(pb) = &progress_bar {
            pb.finish();
        }

        Ok(())
    }

    /// Returns the path to the submodule's `.git/modules/` entry (e.g.
    /// `.git/modules/libs/foo` for a submodule at `libs/foo`), or `None` for the
    /// shapes that have no such entry (e.g. deleted workdir or an embedded gitdir)
    fn get_modules_path(&self, submod_rel_path: &str) -> WatchResult<Option<PathBuf>> {
        // Read the submodule's `.git` file to find its actual modules path.
        let dot_git_path = self.root_path.join(submod_rel_path).join(DOT_GIT);
        let dot_git_bytes = match std::fs::read(&dot_git_path) {
            Ok(bytes) => bytes,
            // An absent gitlink (deleted workdir) and an embedded gitdir
            // have no `.git/modules` entry by design.
            Err(e)
                if matches!(
                    e.kind(),
                    std::io::ErrorKind::NotFound | std::io::ErrorKind::IsADirectory
                ) =>
            {
                return Ok(None);
            }
            #[cfg(windows)]
            Err(e) if e.kind() == std::io::ErrorKind::PermissionDenied && dot_git_path.is_dir() => {
                return Ok(None);
            }
            Err(e) => return Err(e.into()),
        };

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

        Ok(Some(self.root_modules_path.join(suffix)))
    }
}
