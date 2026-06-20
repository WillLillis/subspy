use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    sync::MutexGuard,
};

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
    git::{GitlinkKind, parse_gitlink, parse_gitmodules},
    watch::{LockFileGuard, WatchError, WatchResult},
};

/// Returns the converted `StatusSummary` status for the submodule at `relative_path` guarded by
/// `lock_path`. If the lock file at `lock_path` cannot be acquired, returns
/// `Ok(StatusSummary::LOCK_FAILURE)`.
fn get_submod_status(
    repo: &Repository,
    relative_path: &str,
    lock_path: &Path,
) -> WatchResult<StatusSummary> {
    // Unlike the incremental path (`try_spawn_submod_update`, which reads
    // lock-free), the reindex acquires the submodule's `index.lock` on purpose:
    // a failure surfaces as `StatusSummary::LOCK_FAILURE` so a wedged submodule
    // is visible to the user (commit 27f2ecb), and this one-shot pass has no
    // per-submodule retry loop to make a lock-free read converge the way the
    // incremental path's dirty / `SubmoduleLockRelease` retries do. Contention
    // with a concurrent git op is handled upstream by debouncing the reindex
    // (`ReindexDebounce`), not by dropping this lock; and a recorded
    // `LOCK_FAILURE` is re-read once the lock is released (see
    // `lock_release_needs_reread`).
    let lock = LockFileGuard::acquire(lock_path);
    let status: StatusSummary = if lock.is_ok() {
        repo.submodule_status(relative_path, git2::SubmoduleIgnore::None)?
            .into()
    } else {
        // Pass failures to acquire the relevant `index.lock` file as pseudo
        // statuses so they can be displayed to the user to resolve.
        error!(
            "Failed to acquire lock file `{}` before retrieving status",
            lock_path.display()
        );
        StatusSummary::LOCK_FAILURE
    };
    // Explicitly drop `lock` as soon as possible, rather than at some point after the return
    drop(lock);
    Ok(status)
}

impl WatchServer {
    /// Gathers the status for all submodules within the given repository. When
    /// `place_submod_watches` is true, also places watchers on their directories.
    ///
    /// # Errors
    ///
    /// Returns `notify::Error` if any watchers cannot be created, or `git2::Error` if any
    /// git operation fails.
    #[allow(clippy::too_many_lines)]
    pub(super) fn populate_status_map(
        &mut self,
        display_progress: bool,
        place_submod_watches: bool,
        mut status_guard: MutexGuard<'_, BTreeMap<String, StatusSummary>>,
    ) -> WatchResult<()> {
        use std::sync::atomic::{AtomicU32, Ordering};

        use rayon::prelude::*;

        // Read `.gitmodules` WITHOUT holding `.git/index.lock`. git replaces
        // `.gitmodules` via an atomic rename, so a reader always sees a complete
        // old-or-new file, and the `.gitmodules` watcher re-fires for eventual
        // consistency. Holding the index lock here is unnecessary for that read
        // and actively harmful. It makes concurrent `git` commands fail fast on
        // the pre-existing lock. (`parse_gitmodules` reads `.gitmodules` via
        // `git2::Config`)
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
                // routing entry the `.git/modules` watcher needs (without it those
                // events would resolve to no submodule, and nothing would drive the
                // retry). A `rm -rf`'d workdir has no gitlink -> NotFound -> `None`,
                // read lock-free below.
                let (modules_path, status): (Option<PathBuf>, WatchResult<(StatusSummary, bool)>) =
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
                                "Failed to get modules path for submodule {relative_path} - {e}, skipping...",
                            );
                            (None, Err(e))
                        }
                        // Ok(path) -> Some; a missing gitlink -> None (lock-free read).
                        // TODO: the inner read would be cleaner as a `try` block once
                        // stabilized (https://github.com/rust-lang/rust/issues/31436).
                        resolved => {
                            let modules_path = resolved.ok();
                            let status = (|| {
                                let repo = tl_repo.get_or_try(|| Repository::open(root_path))
                                    .map_err(|e| {
                                        error!("Failed to open repository while indexing {relative_path}: {e}");
                                        e
                                    })?;

                                // This is definitely a race condition, and is not meant to catch "active"
                                // rebases while the status map is being populated. Instead, the intention is
                                // for "stalled" rebases (i.e. that has hit a conflict that must be manually
                                // resolved) so that we can properly skip updating this submodule until its
                                // rebase has been completed.
                                let is_in_rebase = modules_path
                                    .as_deref()
                                    .is_some_and(|p| p.join("rebase-merge").exists());

                                let status = if is_in_rebase {
                                    StatusSummary::NEW_COMMITS
                                } else if let Some(modules_path) = &modules_path {
                                    get_submod_status(repo, &relative_path, &modules_path.join("index.lock"))
                                        .map_err(|e| {
                                            error!("Failed to get {relative_path} status while populating status map: {e}");
                                            e
                                        })?
                                } else {
                                    // Deleted workdir: no `index.lock` to contend with, so read
                                    // lock-free, mirroring `try_spawn_submod_update`. libgit2
                                    // reports a gone workdir as WD_DELETED -> DELETED_WORKDIR,
                                    // by relative path, so this is correct even under a rename.
                                    repo.submodule_status(&relative_path, git2::SubmoduleIgnore::None)
                                        .map_err(|e| {
                                            error!("Failed to get deleted {relative_path} status while populating status map: {e}");
                                            e
                                        })?
                                        .into()
                                };

                                Ok((status, is_in_rebase))
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
        // `skip_set` is indexed by watcher position and read with an unchecked
        // index in the event loop, so it must cover every live watcher. A
        // no-replace reindex leaves `self.watchers` at its current length while
        // this pass still assigns slots up to `ROOT_WATCHER_COUNT +
        // results.len()`, so size to whichever is larger. Using only the new
        // submodule count would let a no-replace reindex that shrinks the set
        // leave `skip_set` shorter than `watchers` (an out-of-bounds read);
        // using only `watchers.len()` would under-size it when the set grows
        // (an out-of-bounds insert below). On the replace path `watchers` holds
        // just the root watchers here, so the new count dominates.
        let skip_set_len = self.watchers.len().max(ROOT_WATCHER_COUNT + results.len());
        self.skip_set.clear_and_resize(skip_set_len);
        if place_submod_watches {
            self.modules_path_to_index.clear();
            self.workdir_to_index.clear();
        }
        // NOTE: Watcher placement must NOT be parallelized. Creating
        // `notify::RecommendedWatcher` instances concurrently on rayon threads
        // causes watchers to silently miss subsequent filesystem events, likely
        // due to interference between rayon's work-stealing and notify's
        // internal event threads. This was measured and reverted.
        //
        // Every submodule occupies a slot in this loop regardless of whether
        // its status read succeeded. This keeps `index` (= ROOT_WATCHER_COUNT + i)
        // aligned with watcher positions across calls: rayon preserves order for
        // indexed iterators, and `parse_gitmodules()` returns a consistent order.
        // Skipping failed submodules would shift subsequent indices and misalign
        // skip_set / modules_path_to_index with the watcher array.
        for (i, (relative_path, full_path, modules_path, status)) in results.into_iter().enumerate()
        {
            let index = ROOT_WATCHER_COUNT + i;
            // Status and skip_set come only from a successful read. A failed read
            // leaves no status entry but still reserves a watcher slot (below);
            // the watcher will generate events that trigger re-reads via
            // try_spawn_submod_update, so the status will eventually converge.
            if let Ok((status, is_in_rebase)) = status {
                status_guard.insert(relative_path.clone(), status);
                if is_in_rebase {
                    self.skip_set.insert(index);
                }
            }
            if place_submod_watches {
                // Route `.git/modules/<name>` events to this slot whenever the
                // path resolved, independent of the status read: a transient
                // read failure must not strand the submodule without routing,
                // since the routed event is what drives the retry. A deleted
                // workdir has no resolvable path (`None`) and gets no entry until
                // a restore reindex repopulates it.
                if let Some(modules_path) = modules_path {
                    self.modules_path_to_index.insert(modules_path, index);
                }
                let (rx, watcher) = Self::place_submodule_watch(&full_path)?;
                wtrace!(|s| WatchSubmod {
                    index,
                    path: s.intern_path(&full_path),
                });
                // Record the (root-relative) workdir->index mapping for every
                // submodule, even ones whose status read failed: tripwire
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

        // `parse_gitlink` returns the submodule's path within `.git/modules/`
        // (the bit after the marker) as raw bytes -- the name may contain
        // non-UTF-8 bytes -- which we UTF-8 validate only for the `PathBuf` join.
        let GitlinkKind::Submodule { modules_subpath } = parse_gitlink(&dot_git_bytes) else {
            return Err(WatchError::NotSubmoduleGitlink(dot_git_path));
        };

        let suffix = std::str::from_utf8(modules_subpath).map_err(|error| {
            WatchError::NonUtf8SubmoduleName {
                path: dot_git_path,
                error,
            }
        })?;

        Ok(self.root_modules_path.join(suffix))
    }
}
