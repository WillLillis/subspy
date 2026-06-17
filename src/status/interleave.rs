//! Interleaving submodule status rows with the libgit2 file entries by
//! pathname, matching git's single path-sorted change stream per section.
//!
//! subspy keeps submodule statuses in a list separate from the `git2::Statuses`
//! file entries (the watch server supplies submodules), but git emits both in
//! one stream sorted by path within each section. [`for_each_merged`] merges
//! the (already path-ordered) file entries with the submodule rows so renderers
//! reproduce that ordering. The file side stays lazy -- no entries are
//! collected -- so when there are no submodule rows it is just the file
//! iterator; only the (small) submodule list is sorted.

use git2::StatusEntry;

use crate::StatusSummary;

use super::SubmoduleRename;

/// A submodule-origin change row. Structurally cannot be a file entry, so a
/// `Vec<SubRow>` is exactly the set of rows to interleave.
pub(super) enum SubRow<'a> {
    /// A submodule with working-tree/index changes (path, summary).
    Modified(&'a str, StatusSummary),
    /// A submodule whose gitlink was removed from the index.
    Deleted(&'a str),
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

/// The pathname git/libgit2 order a tracked-change file entry by. libgit2 sorts
/// by the destination path, but `StatusEntry::path_bytes` returns the *old*
/// path for a rename, so read the delta's new-file path directly to stay
/// consistent with the file stream's order (and git's).
fn entry_sort_key<'e>(entry: &'e StatusEntry<'_>) -> &'e [u8] {
    entry
        .head_to_index()
        .or_else(|| entry.index_to_workdir())
        .and_then(|delta| delta.new_file().path_bytes())
        .unwrap_or_else(|| entry.path_bytes())
}

/// Calls `on_row` for each row in git's path order, merging the
/// already-path-ordered `files` with `submods`. `files` stays lazy; `submods`
/// (bounded by the submodule count) is sorted in place. Paths are compared as
/// bytes, matching git's `strcmp` ordering and handling non-UTF-8 paths.
///
/// `files` must already be filtered to the entries that render in this section
/// and be in libgit2's native (destination-path) order -- both hold for a
/// filtered `git2::Statuses::iter()`.
pub(super) fn for_each_merged<'a, E>(
    files: impl Iterator<Item = StatusEntry<'a>>,
    mut submods: Vec<SubRow<'a>>,
    mut on_row: impl FnMut(Row<'a>) -> Result<(), E>,
) -> Result<(), E> {
    submods.sort_by(|x, y| x.key().cmp(y.key()));
    let mut files = files;
    let mut submods = submods.into_iter();
    // One element of look-ahead per side, held as owned bindings so each branch
    // emits a value it already has -- no peek-then-unwrap.
    let mut pending_file = files.next();
    let mut pending_sub = submods.next();
    loop {
        match (pending_file.take(), pending_sub.take()) {
            (Some(file), Some(sub)) => {
                // A path is either a file or a submodule, never both, so there
                // are no exact ties; emit the submodule when it sorts before.
                if sub.key() < entry_sort_key(&file) {
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
