use std::path::{Path, PathBuf};

use notify::{
    EventKind,
    event::{AccessKind, AccessMode, ModifyKind},
};

use crate::connection::watch_server::{
    DOT_GIT_WATCHER_IDX, DOT_GITMODULES_WATCHER_IDX, ROOT_WATCHER_COUNT, WatchServer,
};

use super::trace::wtrace;

/// Summarizes an event received from a watcher. Create with [`WatchServer::classify_event`]
#[derive(Debug, Copy, Clone)]
pub(super) enum EventType {
    /// Something changed in `.git/` or `.gitmodules` that may affect submodule statuses
    RootGitOperation,
    /// A change occurred in one of the watched submodule's source
    SubmoduleChange,
    /// A change occurred in one of the watched submodule's `.git/` subdirectory
    SubmoduleGitOperation,
    /// A submodule's `index.lock` was removed, indicating a git operation completed
    /// or was aborted. Used to re-fire deferred status reads.
    SubmoduleLockRelease,
    /// A rebase started within a submodule
    SubmoduleRebaseStart,
    /// A rebase ended within a submodule
    SubmoduleRebaseEnd,
    /// A rebase started within the root repository
    RootRebaseStart,
    /// A rebase ended within the root repository
    RootRebaseEnd,
}

/// Determines whether `event` is relevant by its `kind`. Relevant events include writes
/// and deletions.
const fn event_is_relevant(event: &notify::Event) -> bool {
    matches!(
        event.kind,
        EventKind::Remove(_)
            | EventKind::Access(AccessKind::Close(AccessMode::Write))
            | EventKind::Create(_)
            // Windows and macOS don't produce `Close(Write)`; file modifications
            // are reported as `Modify(...)` instead.
            | EventKind::Modify(ModifyKind::Any | ModifyKind::Data(_))
    )
}

impl WatchServer {
    /// Converts a watcher event to a relevant `EventType`, if possible
    fn classify_event(&self, event: &notify::Event, watcher_idx: usize) -> Option<EventType> {
        if !event_is_relevant(event) {
            // File renames within submodule source trees are legitimate changes, but we
            // can't allow Modify(Name) events through globally because git's
            // `index.lock` -> `index` rename would trigger spurious reindexes.
            //
            // However, renames under `.git/modules/` _are_ meaningful, e.g. a
            // `git add` inside a submodule produces only a `MOVED_TO index` event
            // on Linux (inotify), and without this carve-out it would be silently
            // dropped. Root index renames (`index.lock`->`index`) also need
            // detection so that operations like `git add <submodule>` in the
            // parent repo are visible.
            let is_git_dir_rename = watcher_idx == DOT_GIT_WATCHER_IDX
                && matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
                && event.paths.iter().any(|p| {
                    (p.starts_with(&self.root_modules_path)
                        && (p.file_name().is_some_and(|n| {
                            n == "index" || n == "index.lock" || n == "HEAD" || n == "HEAD.lock"
                        }) || self.is_submod_refs_heads(p)))
                        || p.eq(&self.root_index_path)
                        || p.eq(&self.root_lock_path)
                        || p.eq(&self.root_head_path)
                        || p.eq(&self.root_head_lock_path)
                        || p.starts_with(&self.root_refs_heads_path)
                });
            // macOS/FSEvents reports git's atomic `.gitmodules` replace (write
            // `.gitmodules.lock`, rename it over `.gitmodules`) as a rename
            // rather than the Remove inotify delivers. The `.gitmodules` watcher
            // only ever sees its own file, so any rename here is a real change
            // that must trigger a reindex to pick up an added/removed submodule.
            let is_gitmodules_rename = watcher_idx == DOT_GITMODULES_WATCHER_IDX
                && matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)));
            if !is_git_dir_rename && !is_gitmodules_rename {
                // Root watches are kept at indices 0 and 1
                let is_root_watcher = watcher_idx < ROOT_WATCHER_COUNT;
                if is_root_watcher || !matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
                {
                    return None;
                }
            }
        }

        if watcher_idx == DOT_GIT_WATCHER_IDX {
            if event
                .paths
                .iter()
                .any(|p| p.starts_with(&self.root_modules_path))
            {
                if event.paths.iter().any(|p| {
                    Self::is_index_or_head_path(p)
                        || self.is_submod_refs_heads(p)
                        // On Linux, inotify may only report the MOVED_FROM
                        // half of a `.lock` → target rename. The filename is
                        // "index.lock"/"HEAD.lock" rather than "index"/"HEAD",
                        // so `is_index_or_head_path` misses it. Treat a
                        // rename of these lock files as a completed git
                        // operation so the server re-reads submodule status.
                        || (matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
                            && p.file_name()
                                .is_some_and(|n| n == "index.lock" || n == "HEAD.lock"))
                }) {
                    // NOTE: We don't take the same `Remove` defensive measures for submodule
                    // `index`/`HEAD` operations as we do with the root repository. This is because
                    // the event loop continues to run (as opposed to breaking out for a reindex),
                    // so the rebase start event is caught in time.
                    Some(EventType::SubmoduleGitOperation)
                } else if self.is_submod_rebase_start_event(event) {
                    Some(EventType::SubmoduleRebaseStart)
                } else if self.is_submod_rebase_end_event(event) {
                    Some(EventType::SubmoduleRebaseEnd)
                } else if matches!(event.kind, EventKind::Remove(_))
                    && event
                        .paths
                        .iter()
                        .any(|p| p.file_name().is_some_and(|n| n == "index.lock"))
                {
                    Some(EventType::SubmoduleLockRelease)
                } else {
                    None
                }
            } else if event.paths.iter().any(|p| {
                p.eq(&self.root_index_path)
                    || p.eq(&self.root_head_path)
                    || p.starts_with(&self.root_refs_heads_path)
                    // The filesystem watcher may deliver git's
                    // `index.lock`/`HEAD.lock` -> target rename as only the
                    // "source" half (path = the `.lock` file, not the target),
                    // dropping the target-half event that the clauses above key
                    // on. Without this, a one-shot op like `git restore
                    // --staged` whose only delivered event is the `.lock` source
                    // half is classified `None`, so no re-read fires and a
                    // cached status (e.g. STAGED_NEW for a just-unstaged
                    // submodule) persists until the next git op. Mirrors the
                    // submodule branch above.
                    || (matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
                        && (p.eq(&self.root_lock_path) || p.eq(&self.root_head_lock_path)))
            }) {
                // Git's atomic update pattern for `index`, `HEAD`, and branch
                // refs: write to the `.lock` file, delete the original, rename
                // `.lock`-> target. The `Remove` event for the transient
                // deletion is ignored, acting on it would race with the
                // immediately following rename. All other events (writes,
                // renames) are classified as `RootGitOperation` and handled in
                // the event loop by spawning lock-free rayon tasks to re-check
                // submodule statuses.
                //
                // Detecting HEAD changes is critical for `git checkout`:
                // the index is updated before HEAD, so rayon tasks spawned
                // from the index rename may read status against the stale
                // HEAD (producing STAGED | NEW_COMMITS). When the HEAD
                // rename fires shortly after, it triggers a second round of
                // rayon tasks that correct the status.
                //
                // Detecting branch ref changes (under `refs/heads/`) is
                // critical for `git commit`: the index rename fires first,
                // but HEAD still points at the old commit, so rayon tasks
                // see a stale INDEX_MODIFIED (STAGED). The branch ref
                // rename fires shortly after and triggers a corrective
                // round.
                if matches!(event.kind, EventKind::Remove(_)) {
                    None
                } else {
                    Some(EventType::RootGitOperation)
                }
            } else if self.is_root_rebase_start_event(event) {
                Some(EventType::RootRebaseStart)
            } else if self.is_root_rebase_end_event(event) {
                Some(EventType::RootRebaseEnd)
            } else {
                None
            }
        } else if watcher_idx == DOT_GITMODULES_WATCHER_IDX {
            Some(EventType::RootGitOperation)
        } else {
            Some(EventType::SubmoduleChange)
        }
    }

    /// Classifies an event via [`Self::classify_event`] and, under
    /// `--cfg trace_events`, prints the raw event (kind + paths) with its
    /// resulting classification.
    #[inline]
    pub(super) fn classify_and_trace_event(
        &self,
        event: &notify::Event,
        index: usize,
    ) -> Option<EventType> {
        let event_type = self.classify_event(event, index);
        wtrace!(|s| Classified {
            index,
            rel: s.intern_str(&self.watchers[index].relative_path),
            kind: event.kind,
            paths: event.paths.iter().map(|p| s.intern_path(p)).collect(),
            result: event_type,
        });
        event_type
    }

    /// Helper to determine whether `paths` contains the `rebase-merge` path as
    /// a child of `prefix`
    #[inline]
    fn has_rebase_marker_path(paths: &[PathBuf], prefix: &Path) -> bool {
        paths
            .iter()
            .any(|p| p.starts_with(prefix) && p.file_name().is_some_and(|n| n.eq("rebase-merge")))
    }

    #[inline]
    fn is_submod_rebase_start_event(&self, event: &notify::Event) -> bool {
        // NOTE: We could add an additional check here that the `rebase-merge` path is a directory,
        // but git shouldn't create a file with that name so it's fine
        matches!(event.kind, EventKind::Create(_))
            && Self::has_rebase_marker_path(&event.paths, &self.root_modules_path)
    }

    #[inline]
    fn is_submod_rebase_end_event(&self, event: &notify::Event) -> bool {
        matches!(event.kind, EventKind::Remove(_))
            && Self::has_rebase_marker_path(&event.paths, &self.root_modules_path)
    }

    #[inline]
    fn is_root_rebase_start_event(&self, event: &notify::Event) -> bool {
        matches!(event.kind, EventKind::Create(_))
            && Self::has_rebase_marker_path(&event.paths, &self.root_git_path)
    }

    #[inline]
    fn is_root_rebase_end_event(&self, event: &notify::Event) -> bool {
        matches!(event.kind, EventKind::Remove(_))
            && Self::has_rebase_marker_path(&event.paths, &self.root_git_path)
    }

    // NOTE: There's an interesting edge case here. In _theory_, all we need to do is respond
    // to changes to `.git/index`. However, when a new commit/branch is checked out, the files
    // within the repo are modified _before_ `.git/HEAD` is, and `.git/index` is modified
    // sometime before `HEAD` as well. This leads to a race condition where the watch server
    // re-indexes a submodule after `.git/index` (or one of the actual source files) was
    // modified, only sees the modified files (and _not_ the changed `HEAD`, since it hasn't
    // been updated yet), and "correctly" gets the status from `git2` as "modified content" when
    // in reality it should be "new commits". By also triggering on modifications to
    // `.git/HEAD`, we mitigate this race condition and get the correct status eventually.
    #[inline]
    fn is_index_or_head_path(p: &Path) -> bool {
        // NOTE: We don't check if `p.is_file()` here, as git sometimes deletes `index` before
        // renaming `index.lock`->`index`. If it doesn't exist at the time of the check, we'll get
        // an "incorrect" false. We _could_ check via the metadata and handle errors that way, but
        // in reality this should be just fine.
        p.file_name()
            .is_some_and(|name| name.eq("index") || name.eq("HEAD"))
    }

    /// Returns `true` if `p` is a branch ref path under a known submodule's
    /// `.git/modules/<name>/refs/heads/`. Uses `modules_path_to_index` to
    /// correctly handle multi-component submodule names (e.g. `libs/foo`).
    ///
    /// Detecting branch ref renames in submodules is critical for `git commit`:
    /// the ref update is the most reliable post-commit signal. Without it, the
    /// server can get stuck reporting pre-commit status (e.g. stale
    /// `MODIFIED_CONTENT` from staged changes that were just committed).
    fn is_submod_refs_heads(&self, p: &Path) -> bool {
        // Cheap pre-filter: if the path doesn't contain a "refs" component it
        // can't be a refs/heads update.  This avoids the expensive ancestor
        // walk + HashMap lookups for the vast majority of .git/modules events
        // (object files, pack files, logs, etc.).
        if !p.components().any(|c| c.as_os_str() == "refs") {
            return false;
        }
        p.ancestors().any(|ancestor| {
            self.modules_path_to_index.contains_key(ancestor)
                && p.strip_prefix(ancestor).is_ok_and(|rel| {
                    let mut c = rel.components();
                    c.next().is_some_and(|a| a.as_os_str() == "refs")
                        && c.next().is_some_and(|b| b.as_os_str() == "heads")
                })
        })
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn root_lock_rename_source_half_triggers_recheck() {
        // The filesystem watcher can deliver git's `index.lock`/`HEAD.lock` ->
        // target rename as only the "source" half (path = the `.lock` file).
        // The root branch of `classify_event` must still treat that as a
        // RootGitOperation so submodule statuses get re-read; otherwise a cached
        // STAGED_NEW (or any stale status) persists until the next git op. The
        // submodule branch already handles this; the root branch did not.
        // Observed on Windows; inotify can split a rename the same way.
        use notify::event::RenameMode;

        let (_tx, rx) = crossbeam_channel::unbounded();
        // A plain repo: git dir and common dir both `/repo/.git`.
        let layout = super::super::layout::GitLayout::from_dirs(
            Path::new("/repo/.git").to_path_buf(),
            Path::new("/repo/.git").to_path_buf(),
        );
        let server = WatchServer::new(Path::new("/repo"), &layout, rx);
        for lock in ["index.lock", "HEAD.lock"] {
            let event = notify::Event::new(EventKind::Modify(ModifyKind::Name(RenameMode::From)))
                .add_path(PathBuf::from("/repo/.git").join(lock));
            assert!(
                matches!(
                    server.classify_event(&event, DOT_GIT_WATCHER_IDX),
                    Some(EventType::RootGitOperation)
                ),
                "source-half rename of {lock} should classify as RootGitOperation"
            );
        }

        // A lock *rollback* (the `.lock` deleted, index unchanged) must still be
        // ignored: acting on it would spawn pointless re-reads on every op that
        // touches the index without changing it.
        let rollback = notify::Event::new(EventKind::Remove(notify::event::RemoveKind::File))
            .add_path(PathBuf::from("/repo/.git/index.lock"));
        assert!(
            server
                .classify_event(&rollback, DOT_GIT_WATCHER_IDX)
                .is_none(),
            "index.lock removal (rollback) should not trigger a re-read"
        );
    }

    #[test]
    fn is_index_or_head_matches_index() {
        assert!(WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/index"
        )));
    }

    #[test]
    fn is_index_or_head_matches_head() {
        assert!(WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/HEAD"
        )));
    }

    #[test]
    fn is_index_or_head_rejects_index_lock() {
        assert!(!WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/index.lock"
        )));
    }

    #[test]
    fn is_index_or_head_rejects_head_lock() {
        assert!(!WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/HEAD.lock"
        )));
    }

    #[test]
    fn is_index_or_head_rejects_other() {
        assert!(!WatchServer::is_index_or_head_path(Path::new(
            ".git/modules/sub/config"
        )));
    }

    // -- has_rebase_marker_path --

    #[test]
    fn has_rebase_marker_under_prefix() {
        let paths = vec![PathBuf::from(".git/modules/sub/rebase-merge")];
        assert!(WatchServer::has_rebase_marker_path(
            &paths,
            Path::new(".git/modules")
        ));
    }

    #[test]
    fn has_rebase_marker_wrong_prefix() {
        let paths = vec![PathBuf::from("/other/path/rebase-merge")];
        assert!(!WatchServer::has_rebase_marker_path(
            &paths,
            Path::new(".git/modules")
        ));
    }

    #[test]
    fn has_rebase_marker_wrong_filename() {
        let paths = vec![PathBuf::from(".git/modules/sub/rebase-apply")];
        assert!(!WatchServer::has_rebase_marker_path(
            &paths,
            Path::new(".git/modules")
        ));
    }

    #[test]
    fn has_rebase_marker_empty_paths() {
        let paths: Vec<PathBuf> = vec![];
        assert!(!WatchServer::has_rebase_marker_path(
            &paths,
            Path::new(".git/modules")
        ));
    }
}
