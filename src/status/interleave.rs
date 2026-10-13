//! Interleaving submodule status rows with the libgit2 file entries by
//! pathname, matching git's single path-sorted change stream per section.
//!
//! subspy keeps submodule statuses in a list separate from the `git2::Statuses`
//! file entries (the watch server supplies submodules), but git emits both in
//! one stream sorted by path within each section. [`for_each_merged`] merges
//! the (already path-ordered) file entries with the submodule rows so renderers
//! reproduce that ordering. The file side remains lazy and uncollected. With
//! no submodule rows it is simply the file iterator. Only the (small) submodule
//! list is sorted.

use git2::StatusEntry;

use crate::{StatusSummary, git::path::GitPath};

use super::SubmoduleRename;

/// A submodule-origin change row. Structurally cannot be a file entry, so a
/// `Vec<SubRow>` is exactly the set of rows to interleave.
pub(super) enum SubRow<'a> {
    /// A submodule with working-tree/index changes (path, summary).
    Modified(&'a GitPath, StatusSummary),
    /// A submodule whose gitlink was removed from the index.
    Deleted(&'a GitPath),
    /// A staged submodule rename.
    Renamed(&'a SubmoduleRename),
}

impl SubRow<'_> {
    /// The pathname git orders this row by. Renames sort by the new
    /// (destination) path, matching git and the file entries.
    const fn key(&self) -> &[u8] {
        match self {
            Self::Modified(path, _) | Self::Deleted(path) => path.as_bytes(),
            Self::Renamed(rename) => rename.new.as_bytes(),
        }
    }
}

/// One row of the merged stream handed to the render callback, by value.
pub(super) enum Row<'a> {
    File(StatusEntry<'a>),
    Sub(SubRow<'a>),
}

/// Calls `on_row` for each row in git's path order, merging the already
/// path ordered `files` with `submods`. `files` stays lazy, while `submods`
/// is bounded by the submodule count and is sorted in place.
///
/// `files` must already be filtered to the entries that render in this section
/// and follow libgit2's path order. A filtered [`git2::Statuses::iter`]
/// satisfies both requirements.
pub(super) fn for_each_merged<'a, E>(
    files: impl Iterator<Item = StatusEntry<'a>>,
    mut submods: Vec<SubRow<'a>>,
    mut on_row: impl FnMut(Row<'a>) -> Result<(), E>,
) -> Result<(), E> {
    submods.sort_by(|x, y| x.key().cmp(y.key()));
    let mut files = files;
    let mut submods = submods.into_iter();

    let mut pending_file = files.next();
    let mut pending_sub = submods.next();
    loop {
        match (pending_file.take(), pending_sub.take()) {
            (Some(file), Some(sub)) => {
                // File and submodule paths are disjoint, eliminating exact ties.
                // Emit the submodule when it sorts first.
                if sub.key() < file.path_bytes() {
                    on_row(Row::Sub(sub))?;
                    pending_file = Some(file);
                    pending_sub = submods.next();
                } else {
                    on_row(Row::File(file))?;
                    pending_sub = Some(sub);
                    pending_file = files.next();
                }
            }
            (Some(file), None) => {
                on_row(Row::File(file))?;
                pending_file = files.next();
            }
            (None, Some(sub)) => {
                on_row(Row::Sub(sub))?;
                pending_sub = submods.next();
            }
            (None, None) => break,
        }
    }
    Ok(())
}
