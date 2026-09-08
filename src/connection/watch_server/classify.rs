use std::{
    ops::Bound,
    path::{Path, PathBuf},
};

use notify::{
    EventKind,
    event::{AccessKind, AccessMode, ModifyKind},
};

use crate::connection::watch_server::WatchServer;

use super::trace::wtrace;

/// Summarizes an event received from the git watcher. Create with
/// [`WatchServer::classify_git_event`]
#[derive(Debug, Copy, Clone)]
pub(super) enum EventType {
    /// Something changed in the root git directory that may affect submodule statuses
    RootGitOperation,
    /// A change occurred in a submodule's gitdir under `.git/modules/`
    SubmoduleGitOperation,
    /// A submodule's `index.lock` was removed, indicating a git operation completed
    /// or was aborted. Used to re-fire deferred status reads.
    SubmoduleLockRelease,
}

/// Where one path of a tree-watcher event routes. Create with
/// [`WatchServer::classify_tree_path`]
#[derive(Debug, Copy, Clone)]
pub(super) enum TreeAction {
    /// `.gitmodules` changed (including a lock rename delivered as only its
    /// source half)
    Gitmodules,
    /// A change inside the workdir of the submodule at this slot index
    Submodule(usize),
    /// A path outside every submodule workdir, subject to tripwire logic
    Structural,
    /// Irrelevant for this path's class
    Ignored,
}

/// Determines whether `event` is relevant by its [`kind`](`notify::Event::kind`).
pub(super) const fn event_is_relevant(event: &notify::Event) -> bool {
    matches!(
        event.kind,
        EventKind::Remove(_)
            | EventKind::Access(AccessKind::Close(AccessMode::Write))
            | EventKind::Create(_)
            // Windows and macOS don't produce `Close(Write)`. File modifications
            // are reported as `Modify(...)` instead.
            | EventKind::Modify(ModifyKind::Any | ModifyKind::Data(_))
    )
}

/// Determines whether an event should wake a parked server.
///
/// Recursive watch registration reports the watcher's own directory opens as
/// `Access(Open)`, and should be ignored.
pub(super) const fn event_is_idle_activity(event: &notify::Event) -> bool {
    !matches!(event.kind, EventKind::Access(AccessKind::Open(_)))
}

/// Whether `event` is a rename by its [`kind`](`notify::Event::kind`).
const fn event_is_rename(event: &notify::Event) -> bool {
    matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
}

impl WatchServer {
    /// Converts a git-watcher event to a relevant [`EventType`], if possible.
    fn classify_git_event(&self, event: &notify::Event) -> Option<EventType> {
        if !event_is_relevant(event) {
            // Renames are excluded from `event_is_relevant` because they are
            // routine inside submodule source trees. Under the git directory
            // they _are_ meaningful, e.g. a `git add` inside a submodule
            // produces only a `MOVED_TO index` event on Linux (inotify). Root
            // index renames (`index.lock`->`index`) also need detection so that
            // operations like `git add <submodule>` in the parent repo are
            // visible.
            let is_git_dir_rename = event_is_rename(event)
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
            if !is_git_dir_rename {
                return None;
            }
        }

        if event
            .paths
            .iter()
            .any(|p| p.starts_with(&self.root_modules_path))
        {
            if event.paths.iter().any(|p| {
                Self::is_index_or_head_path(p)
                    || self.is_submod_refs_heads(p)
                    // On Linux, inotify may only report the MOVED_FROM
                    // half of a `target.lock`-> `target` rename. The filename
                    // is "index.lock"/"HEAD.lock" rather than "index"/"HEAD",
                    // so `is_index_or_head_path` misses it. Treat a
                    // rename of these lock files as a completed git
                    // operation so the server re-reads submodule status.
                    || (event_is_rename(event)
                        && p.file_name()
                            .is_some_and(|n| n == "index.lock" || n == "HEAD.lock"))
            }) || Self::is_rebase_marker_event(event, &self.root_modules_path)
            {
                Some(EventType::SubmoduleGitOperation)
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
                || (event_is_rename(event)
                    && (p.eq(&self.root_lock_path) || p.eq(&self.root_head_lock_path)))
        }) {
            // Git's atomic update pattern for `index`, `HEAD`, and branch
            // refs: write to the `.lock` file, delete the original, rename
            // `.lock`-> target. The `Remove` event for the transient
            // deletion is ignored, acting on it would race with the
            // immediately following rename. All other events (writes,
            // renames) are classified as `RootGitOperation` and handled in
            // the event loop by spawning rayon tasks to re-check submodule
            // statuses.
            //
            // Detecting HEAD changes is needed for `git checkout`:
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
        } else if Self::is_rebase_marker_event(event, &self.root_git_path) {
            Some(EventType::RootGitOperation)
        } else {
            None
        }
    }

    /// Classifies a git-watcher event via [`Self::classify_git_event`] and,
    /// under `cfg(trace_events)`, prints the raw event with its classification.
    #[inline]
    pub(super) fn classify_and_trace_git_event(&self, event: &notify::Event) -> Option<EventType> {
        let event_type = self.classify_git_event(event);
        wtrace!(|s| GitClassified {
            kind: event.kind,
            paths: event.paths.iter().map(|p| s.intern_path(p)).collect(),
            result: event_type,
        });
        event_type
    }

    /// Routes one path of a tree-watcher event to its [`TreeAction`].
    pub(super) fn classify_tree_path(&self, path: &Path, event: &notify::Event) -> TreeAction {
        // `.gitmodules` changes arrive through the non-recursive root watch.
        // Renames pass alongside the relevant kinds: git rewrites the file by
        // renaming `.gitmodules.lock` over it, and macOS reports that replace
        // as a rename rather than the `Remove` inotify delivers. The lock path
        // matters on its own because the watcher may deliver the rename as
        // only its source half.
        if path == self.root_gitmodules_path.as_path() {
            return if event_is_relevant(event) || event_is_rename(event) {
                TreeAction::Gitmodules
            } else {
                TreeAction::Ignored
            };
        }
        if path == self.root_gitmodules_lock_path.as_path() {
            return if event_is_rename(event) {
                TreeAction::Gitmodules
            } else {
                TreeAction::Ignored
            };
        }

        let Ok(rel) = path.strip_prefix(&self.root_path) else {
            return TreeAction::Ignored;
        };
        if let Some((workdir, slot)) = self.submod_for_workdir_path(rel) {
            // A `Create` or rename of the workdir root itself means the workdir
            // appeared or moved. Its recursive watch root is dead (a watch
            // cannot witness its own directory being created), so this must
            // take the structural path that re-arms coverage, not count as an
            // in-workdir change. A `Remove` of the root stays an in-workdir
            // change: the status re-read it spawns reports `DELETED_WORKDIR`.
            if rel == workdir
                && (matches!(event.kind, EventKind::Create(_)) || event_is_rename(event))
            {
                return TreeAction::Structural;
            }
            // File renames within submodule source trees are legitimate
            // changes. They are admitted here rather than in
            // `event_is_relevant` so that git's `index.lock` -> `index`
            // rename stays excluded on the watch roots where it is routine.
            return if event_is_relevant(event) || event_is_rename(event) {
                TreeAction::Submodule(slot)
            } else {
                TreeAction::Ignored
            };
        }
        TreeAction::Structural
    }

    /// Finds the workdir key and slot of the submodule whose workdir contains
    /// `rel`, a root-relative path. Submodule workdirs are disjoint (git
    /// refuses a submodule path inside another submodule), so the greatest key
    /// at or before `rel` is the only candidate prefix.
    fn submod_for_workdir_path(&self, rel: &Path) -> Option<(&Path, usize)> {
        self.workdir_to_index
            .range::<Path, _>((Bound::Unbounded, Bound::Included(rel)))
            .next_back()
            .and_then(|(key, &idx)| rel.starts_with(key).then_some((key.as_path(), idx)))
    }

    /// Finds the slot of the submodule whose `.git/modules/` path matches the event.
    #[inline]
    pub(super) fn submod_for_event(&self, event: &notify::Event) -> Option<usize> {
        event.paths.iter().find_map(|p| {
            p.ancestors()
                .find_map(|ancestor| self.modules_path_to_index.get(ancestor))
                .copied()
        })
    }

    /// Whether `paths` contains the `rebase-merge` path as a child of `prefix`
    #[inline]
    fn has_rebase_marker_path(paths: &[PathBuf], prefix: &Path) -> bool {
        paths
            .iter()
            .any(|p| p.starts_with(prefix) && p.file_name().is_some_and(|n| n.eq("rebase-merge")))
    }

    #[inline]
    fn is_rebase_marker_event(event: &notify::Event, prefix: &Path) -> bool {
        matches!(event.kind, EventKind::Create(_) | EventKind::Remove(_))
            && Self::has_rebase_marker_path(&event.paths, prefix)
    }

    // There's an interesting edge case here. In _theory_, all we need to do is respond
    // to changes to `.git/index`. However, when a new commit/branch is checked out, the files
    // within the repo are modified _before_ `.git/HEAD` is, and `.git/index` is modified
    // sometime before `HEAD` as well. This leads to a race condition where the watch server
    // re-indexes a submodule after `.git/index` (or one of the actual source files) was
    // modified, only sees the modified files (and _not_ the changed `HEAD`, since it hasn't
    // been updated yet), and "correctly" gets the status from `git2` as "modified content" when
    // in reality it should be "new commits". By also triggering on modifications to
    // `.git/HEAD`, we converge to the correct status eventually.
    #[inline]
    fn is_index_or_head_path(p: &Path) -> bool {
        p.file_name()
            .is_some_and(|name| name.eq("index") || name.eq("HEAD"))
    }

    /// Returns `true` if `p` is a branch ref path under a known submodule's
    /// `.git/modules/<name>/refs/heads/`. Uses `modules_path_to_index` to
    /// correctly handle multi-component submodule names (e.g. `libs/foo`).
    ///
    /// Detecting branch ref renames in submodules is needed for `git commit`, as
    /// the ref update is the most reliable post-commit signal.
    fn is_submod_refs_heads(&self, p: &Path) -> bool {
        // Cheap pre-filter: if the path doesn't contain a "refs" component it
        // can't be a `refs/heads` update. This avoids the expensive ancestor
        // walk + HashMap lookups for the vast majority of `.git/modules` events
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

    use notify::event::{RemoveKind, RenameMode};

    use super::*;
    use crate::connection::watch_server::layout::GitLayout;

    fn test_server() -> WatchServer {
        let (_tx, rx) = crossbeam_channel::unbounded();
        // A plain repo: git dir and common dir both `/repo/.git`.
        let layout = GitLayout::from_dirs(
            Path::new("/repo/.git").to_path_buf(),
            Path::new("/repo/.git").to_path_buf(),
        );
        WatchServer::new(Path::new("/repo"), &layout, rx)
    }

    // The filesystem watcher can deliver git's `index.lock`/`HEAD.lock` ->
    // target rename as only the "source" half (path = the `.lock` file).
    // The root branch of `classify_git_event` must still treat that as a
    // RootGitOperation so submodule statuses get re-read. Otherwise, a cached
    // STAGED_NEW (or any stale status) persists until the next git op.
    #[test]
    fn root_lock_rename_source_half_triggers_recheck() {
        let server = test_server();
        for lock in ["index.lock", "HEAD.lock"] {
            let event = notify::Event::new(EventKind::Modify(ModifyKind::Name(RenameMode::From)))
                .add_path(PathBuf::from("/repo/.git").join(lock));
            assert!(
                matches!(
                    server.classify_git_event(&event),
                    Some(EventType::RootGitOperation)
                ),
                "source-half rename of {lock} should classify as RootGitOperation"
            );
        }

        // A lock *rollback* (the `.lock` deleted, index unchanged) should still be
        // ignored: acting on it would spawn pointless re-reads on every op that
        // touches the index without changing it.
        let rollback = notify::Event::new(EventKind::Remove(RemoveKind::File))
            .add_path(PathBuf::from("/repo/.git/index.lock"));
        assert!(
            server.classify_git_event(&rollback).is_none(),
            "index.lock removal (rollback) should not trigger a re-read"
        );
    }

    // Git rewrites `.gitmodules` by renaming `.gitmodules.lock` over it. Both
    // rename halves must route to `Gitmodules` so a reindex fires even when the
    // watcher delivers only the source half, while a lock rollback (delete
    // without rename) stays ignored.
    #[test]
    fn gitmodules_rewrite_routes_from_either_rename_half() {
        let server = test_server();

        let source_half = notify::Event::new(EventKind::Modify(ModifyKind::Name(RenameMode::From)))
            .add_path(PathBuf::from("/repo/.gitmodules.lock"));
        assert!(matches!(
            server.classify_tree_path(Path::new("/repo/.gitmodules.lock"), &source_half),
            TreeAction::Gitmodules
        ));

        let target_half = notify::Event::new(EventKind::Modify(ModifyKind::Name(RenameMode::To)))
            .add_path(PathBuf::from("/repo/.gitmodules"));
        assert!(matches!(
            server.classify_tree_path(Path::new("/repo/.gitmodules"), &target_half),
            TreeAction::Gitmodules
        ));

        let direct_write =
            notify::Event::new(EventKind::Access(AccessKind::Close(AccessMode::Write)))
                .add_path(PathBuf::from("/repo/.gitmodules"));
        assert!(matches!(
            server.classify_tree_path(Path::new("/repo/.gitmodules"), &direct_write),
            TreeAction::Gitmodules
        ));

        let lock_rollback = notify::Event::new(EventKind::Remove(RemoveKind::File))
            .add_path(PathBuf::from("/repo/.gitmodules.lock"));
        assert!(matches!(
            server.classify_tree_path(Path::new("/repo/.gitmodules.lock"), &lock_rollback),
            TreeAction::Ignored
        ));
    }

    // Workdir routing must contain a path to the submodule whose workdir holds
    // it, and must not leak onto a sibling whose name merely shares a string
    // prefix (`libs/a` vs `libs/ab`).
    #[test]
    fn tree_paths_route_by_workdir_containment() {
        let mut server = test_server();
        server.workdir_to_index.insert(PathBuf::from("libs/a"), 0);
        server
            .workdir_to_index
            .insert(PathBuf::from("libs/numeric/b"), 1);

        let write = |p: &str| {
            notify::Event::new(EventKind::Access(AccessKind::Close(AccessMode::Write)))
                .add_path(PathBuf::from(p))
        };

        let deep = write("/repo/libs/a/src/lib.rs");
        assert!(matches!(
            server.classify_tree_path(&deep.paths[0], &deep),
            TreeAction::Submodule(0)
        ));

        let nested = write("/repo/libs/numeric/b/f.txt");
        assert!(matches!(
            server.classify_tree_path(&nested.paths[0], &nested),
            TreeAction::Submodule(1)
        ));

        // The workdir root itself is part of the submodule (e.g. its removal).
        let root_removal = notify::Event::new(EventKind::Remove(RemoveKind::Folder))
            .add_path(PathBuf::from("/repo/libs/a"));
        assert!(matches!(
            server.classify_tree_path(&root_removal.paths[0], &root_removal),
            TreeAction::Submodule(0)
        ));

        // The workdir root appearing or moving is structural: the submodule's
        // recursive watch root is dead and only a reindex re-arms it. Routing
        // these to `Submodule` would heal the status but leave the restored
        // workdir unwatched.
        for kind in [
            EventKind::Create(notify::event::CreateKind::Folder),
            EventKind::Modify(ModifyKind::Name(RenameMode::To)),
        ] {
            let root_restore = notify::Event::new(kind).add_path(PathBuf::from("/repo/libs/a"));
            assert!(
                matches!(
                    server.classify_tree_path(&root_restore.paths[0], &root_restore),
                    TreeAction::Structural
                ),
                "{kind:?} at the workdir root should be structural"
            );
        }

        // A sibling sharing a string prefix is not contained in the workdir.
        let sibling = write("/repo/libs/ab/f.txt");
        assert!(matches!(
            server.classify_tree_path(&sibling.paths[0], &sibling),
            TreeAction::Structural
        ));

        // An ancestor directory of a workdir is structural, not a submodule hit.
        let ancestor = notify::Event::new(EventKind::Create(notify::event::CreateKind::Folder))
            .add_path(PathBuf::from("/repo/libs"));
        assert!(matches!(
            server.classify_tree_path(&ancestor.paths[0], &ancestor),
            TreeAction::Structural
        ));
    }
}
