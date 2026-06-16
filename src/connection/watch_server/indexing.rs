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
    git::parse_gitmodules,
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

                // TODO: This would be better as a `try` block if that's ever stabilized
                // (https://github.com/rust-lang/rust/issues/31436)
                // (`.git/modules/` path, status, is in rebase)
                let inner: WatchResult<(Option<PathBuf>, StatusSummary, bool)> = (|| {
                    let repo = tl_repo.get_or_try(|| Repository::open(root_path))
                        .map_err(|e| {
                            error!("Failed to open repository while indexing {relative_path}: {e}");
                            e
                        })?;

                    // `get_modules_path` reads the submodule's `.git` gitlink to
                    // find its real `.git/modules/<name>` dir. A `rm -rf`'d workdir
                    // has no gitlink -> NotFound: fall through with `None` and read
                    // status lock-free below (still resolves to WD_DELETED).
                    // Without the gitlink we can't recover the modules dir, so the
                    // submodule gets no `modules_path_to_index` entry until a
                    // restoring `git submodule update` reindexes and repopulates it.
                    let modules_path = match self.get_modules_path(&relative_path) {
                        Ok(p) => Some(p),
                        Err(WatchError::IO(e)) if e.kind() == std::io::ErrorKind::NotFound => None,
                        Err(e) => {
                            error!(
                                "Failed to get modules path for submodule {relative_path} - {e}, skipping...",
                            );
                            Err(e)?
                        }
                    };
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
                        match get_submod_status(
                            repo,
                            &relative_path,
                            &modules_path.join("index.lock"),
                        ) {
                            Ok(st) => st,
                            Err(e) => {
                                error!("Failed to get {relative_path} status while populating status map: {e}");
                                Err(e)?
                            }
                        }
                    } else {
                        // Deleted workdir: no `index.lock` to contend with, so read
                        // lock-free, mirroring `try_spawn_submod_update`. libgit2
                        // reports a gone workdir as WD_DELETED -> DELETED_WORKDIR,
                        // by relative path, so this is correct even under a rename.
                        match repo.submodule_status(&relative_path, git2::SubmoduleIgnore::None) {
                            Ok(st) => st.into(),
                            Err(e) => {
                                error!("Failed to get deleted {relative_path} status while populating status map: {e}");
                                Err(e)?
                            }
                        }
                    };

                    Ok((modules_path, status, is_in_rebase))
                })();

                let count = completed.fetch_add(1, Ordering::Relaxed) + 1;
                broadcast_progress(
                    progress_subscribers,
                    progress_queue,
                    ProgressUpdate::new(count, n_submodules),
                );
                if let Some(pb) = &progress_bar {
                    pb.inc(1);
                }

                (relative_path, full_path, inner)
            })
            .collect();

        status_guard.clear();
        self.skip_set
            .clear_and_resize(ROOT_WATCHER_COUNT + results.len());
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
        for (i, (relative_path, full_path, inner)) in results.into_iter().enumerate() {
            let index = ROOT_WATCHER_COUNT + i;
            // Only populate status/skip_set/modules_path_to_index on success.
            // Failed submodules get no status entry but still reserve a watcher
            // slot -- the watcher will generate events that trigger re-reads via
            // try_spawn_submod_update, so the status will eventually converge.
            if let Ok((modules_path, status, is_in_rebase)) = inner {
                status_guard.insert(relative_path.clone(), status);
                if is_in_rebase {
                    self.skip_set.insert(index);
                }
                // A deleted submodule has no resolvable modules path (`None`);
                // it gets no routing entry until a restore reindex repopulates it.
                if place_submod_watches && let Some(modules_path) = modules_path {
                    self.modules_path_to_index.insert(modules_path, index);
                }
            }
            if place_submod_watches {
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

        // The file content is "gitdir: ../../.git/modules/name\n". We only
        // need the part after ".git/modules/", so find that marker directly
        // on the raw bytes (the marker is ASCII) and UTF-8 validate only
        // the suffix (the submodule name, which may contain non-ASCII).
        // The marker never appears before byte 10 ("gitdir: ../"), so skip
        // that prefix when searching.
        #[expect(
            clippy::items_after_statements,
            reason = "constants are function-local"
        )]
        const MODULES_MARKER: &[u8] = b".git/modules/";
        #[expect(
            clippy::items_after_statements,
            reason = "constants are function-local"
        )]
        const MIN_PREFIX_LEN: usize = "gitdir: ../".len();
        let suffix_start = dot_git_bytes
            .get(MIN_PREFIX_LEN..)
            .and_then(|tail| {
                tail.windows(MODULES_MARKER.len())
                    .position(|w| w == MODULES_MARKER)
            })
            .ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!(
                        "Expected {} to contain \".git/modules/\"",
                        dot_git_path.display()
                    ),
                )
            })?
            + MIN_PREFIX_LEN
            + MODULES_MARKER.len();

        let suffix =
            std::str::from_utf8(dot_git_bytes[suffix_start..].trim_ascii()).map_err(|e| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!("{}: {e}", dot_git_path.display()),
                )
            })?;

        Ok(self.root_modules_path.join(suffix))
    }
}
