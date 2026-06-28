//! The `status` subcommand: displays submodule and working-tree status
//! in a format that mirrors `git status`.
//!
//! Output formats live in dedicated submodules:
//! - [`display`] for the long-format (default, human-readable) layout
//! - [`short`] for `git status -s` / `--short`
//! - [`porcelain_v1`] and [`porcelain_v2`] for the machine-readable formats
//!
//! Helper modules:
//! - [`xy_line`]: shared `XY PATH` writer for short + porcelain v1
//! - [`header`]: branch/upstream/operation-state header rendering (long format)
//! - [`conflict`]: shared conflict-index parsing
//! - [`submodule`]: submodule status computation and filtering
//! - [`relativize`]: cwd-relative path rewriting at write time
//! - [`quote`]: C-style path quoting (the `core.quotePath` semantics)

mod case_collision;
mod conflict;
mod display;
mod header;
mod interleave;
mod porcelain_v1;
mod porcelain_v2;
mod quote;
mod relativize;
mod rename_score;
mod short;
mod submodule;
mod tracked;
mod xy_line;

#[cfg(test)]
mod tests;

use clap::ValueEnum;
use git2::Repository;
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use std::{borrow::Cow, io, path::Path};

use crate::{
    RepoKind, StatusSummary,
    cli::ProjectPath,
    connection::{
        IpcError,
        client::{recv_status_response, send_status_request},
    },
    watch::LockFileError,
};

pub use relativize::Relativizer;
pub use submodule::{SubmoduleChanges, SubmoduleRename, compute_local_statuses, submodule_changes};

pub type StatusResult<T> = Result<T, StatusError>;

#[derive(Error, Debug)]
pub enum StatusError {
    #[error(transparent)]
    Ipc(#[from] IpcError),
    #[error(transparent)]
    Git(#[from] git2::Error),
    #[error(transparent)]
    LockFile(#[from] LockFileError),
    #[error(transparent)]
    IO(#[from] io::Error),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum PorcelainVersion {
    #[value(name = "1", alias = "v1")]
    V1,
    #[value(name = "2", alias = "v2")]
    V2,
}

/// Which renderer to use for status output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputFormat {
    /// Default `git status` output (the long, human-readable layout).
    #[default]
    Long,
    /// `git status -s` / `--short` (terse `XY PATH` with colors).
    Short,
    /// `git status --porcelain[=v1|v2]` (stable machine-readable).
    Porcelain(PorcelainVersion),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum IgnoreSubmodules {
    #[default]
    #[value(name = "none")]
    None,
    #[value(name = "untracked")]
    Untracked,
    #[value(name = "dirty")]
    Dirty,
    #[value(name = "all")]
    All,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum UntrackedFiles {
    #[default]
    #[value(name = "normal")]
    Normal,
    #[value(name = "no")]
    No,
    #[value(name = "all")]
    All,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum IgnoredFiles {
    /// Don't show ignored entries (git's default when `--ignored` is absent).
    #[default]
    #[value(name = "no")]
    No,
    /// Show ignored files and directory names (git's default for bare
    /// `--ignored` or `--ignored=traditional`).
    #[value(name = "traditional")]
    Traditional,
    // git's `--ignored=matching` mode is intentionally absent: it shows
    // paths that directly match an ignore pattern, while libgit2's
    // `recurse_ignored_dirs(true)` enumerates contents of ignored
    // directories regardless of pattern. The two diverge on common
    // cases (e.g. a `dir/` gitignore line), so the shim forwards
    // `--ignored=matching` to real git, and the subspy CLI rejects it
    // rather than producing approximate output.
}

/// Output format and filtering options passed through from git-status-compatible flags.
#[derive(Debug, Clone, Copy)]
#[expect(clippy::struct_excessive_bools, reason = "matches git")]
pub struct OutputOpts {
    pub format: OutputFormat,
    pub null_terminate: bool,
    pub ignore_submodules: IgnoreSubmodules,
    pub untracked_files: UntrackedFiles,
    pub ignored_files: IgnoredFiles,
    pub branch: bool,
    /// Compute and display detailed upstream ahead/behind counts. When
    /// false, long format reports only divergence (no specific counts)
    /// and porcelain v2 emits `# branch.ab +? -?`.
    pub ahead_behind: bool,
    /// `core.quotepath` (default `true`). When `false`, bytes `>= 0x80`
    /// in paths are emitted verbatim instead of as octal escapes.
    pub quote_path: bool,
    /// `--show-stash`. Long format appends `Your stash currently has
    /// N entr...`; porcelain v2 with `--branch` emits `# stash N`.
    /// Short / porcelain v1 are unaffected.
    pub show_stash: bool,
}

/// Porcelain-specific format flags (`-z`, `--branch`, `--ahead-behind`,
/// `core.quotepath`).
#[derive(Debug, Clone, Copy)]
#[expect(clippy::struct_excessive_bools, reason = "matches git")]
pub struct PorcelainOpts {
    pub null_terminate: bool,
    pub branch: bool,
    pub ahead_behind: bool,
    pub quote_path: bool,
    pub show_stash: bool,
}

/// The set of status entries to render.
pub struct StatusEntries<'a> {
    pub non_submod: &'a git2::Statuses<'a>,
    pub submodules: &'a [(String, StatusSummary)],
    pub deleted_submodules: &'a [String],
    pub renamed_submodules: &'a [SubmoduleRename],
    /// Byte paths of unmerged (conflicted) entries. Renderers drop the phantom
    /// untracked rows libgit2 emits for a conflicted submodule's working tree;
    /// git reports such a path only under "Unmerged paths". Empty when the index
    /// has no conflicts.
    pub conflicted_paths: &'a FxHashSet<Vec<u8>>,
    /// Unmerged submodules and their folded status (modified/untracked/new
    /// commits), keyed by path. Already excluded from `submodules` so they don't
    /// render as a separate dirty row; porcelain v2 uses this for the `u`-line
    /// `S<c><m><u>` field. Empty when the index has no gitlink conflicts.
    pub conflicted_submodules: &'a FxHashMap<String, StatusSummary>,
    /// Byte paths of libgit2's case-collision phantom deletes: a spurious
    /// `WT_DELETED` for a path whose case-variant occupies the one working file
    /// on a `core.ignorecase` filesystem. Renderers skip these; git collapses
    /// the collision to a single line. Empty on case-sensitive filesystems and
    /// whenever nothing is worktree-deleted. See [`case_collision`].
    pub phantom_deletes: &'a FxHashSet<Vec<u8>>,
}

/// Builds the `git2::StatusOptions` used by production and tests. Kept
/// in one place so the two stay in sync.
#[must_use]
pub fn build_status_options(opts: OutputOpts, repo_kind: RepoKind) -> git2::StatusOptions {
    let mut st_opts = git2::StatusOptions::new();
    match opts.untracked_files {
        UntrackedFiles::Normal => {
            st_opts
                .include_untracked(true)
                .recurse_untracked_dirs(false);
        }
        UntrackedFiles::All => {
            st_opts.include_untracked(true).recurse_untracked_dirs(true);
        }
        UntrackedFiles::No => {
            st_opts.include_untracked(false);
        }
    }
    match opts.ignored_files {
        IgnoredFiles::No => {
            st_opts.include_ignored(false);
        }
        IgnoredFiles::Traditional => {
            st_opts.include_ignored(true).recurse_ignored_dirs(false);
        }
    }
    // The repo was just opened, so the index is already fresh from disk.
    // Skip the redundant stat-cache refresh pass.
    st_opts.no_refresh(true);

    // Match git's default `diff.renames=true` so a staged move renders as
    // `R old -> new` rather than separate `D old`/`A new` entries. This is
    // intentionally only the HEAD->index (staged) diff. git does NOT detect
    // renames in the index->workdir (unstaged) diff: an untracked file is never
    // a rename target there, so a plain `mv` of a tracked file shows as `D old`
    // + `?? new`. libgit2's `renames_index_to_workdir` would instead pair the
    // deletion with the untracked file and emit a spurious worktree rename,
    // diverging from git and producing porcelain a consumer can't parse (the
    // old path lands in a record with no valid `XY ` prefix), so it stays off.
    st_opts
        .renames_head_to_index(true)
        .renames_from_rewrites(true);

    // Exclude submodules from the plain status walk whenever subspy supplies
    // their statuses itself -- the watch server at the top level, or local
    // computation for a (possibly nested) superproject. Otherwise they would
    // render as bare entries, missing the `(modified content, ...)` detail.
    if repo_kind.has_submodules() {
        st_opts.exclude_submodules(true);
    }
    st_opts
}

/// Opens the repository, runs the shared status-assembly pipeline, and
/// hands the result to `render`.
///
/// Pipeline: `git2::statuses`, `submodule_changes`, ignore-submodules
/// masking, rename-new filter, relativizer, `StatusEntries`. The
/// `submodule_statuses` closure is the caller's hook for supplying
/// submodule-level statuses -- production receives them over IPC,
/// tests fall back to `compute_local_statuses`.
///
/// # Errors
///
/// Propagates `StatusError` from the closures and from intermediate
/// libgit2 calls.
pub fn assemble_status<R>(
    project: &ProjectPath,
    opts: OutputOpts,
    submodule_statuses: impl FnOnce() -> StatusResult<Vec<(String, StatusSummary)>>,
    render: impl FnOnce(&Repository, &StatusEntries<'_>, &Relativizer<'_>) -> StatusResult<R>,
) -> StatusResult<R> {
    let repo = Repository::open(&project.repo_root)?;
    let mut so = build_status_options(opts, project.kind);
    let non_submod = repo.statuses(Some(&mut so))?;

    // Conflicted submodules need special handling (see below). Both pieces are
    // gated on this cheap check over the already-computed status set, so a
    // conflict-free repo never re-reads the index or touches submodule HEADs.
    let has_conflicts = non_submod
        .iter()
        .any(|e| e.status().contains(git2::Status::CONFLICTED));

    // libgit2 reports a conflicted submodule's working tree as an untracked
    // directory (with no stage-0 gitlink, it no longer recognizes the path as a
    // submodule), so the renderers need the conflicted paths to suppress those
    // phantom rows.
    let conflicted_paths = if has_conflicts {
        conflict::conflicted_paths(&repo.index()?)?
    } else {
        FxHashSet::default()
    };

    // libgit2 emits a phantom `WT_DELETED` for a case-collision (two index
    // entries differing only in case, collapsed to one working file) that git
    // reports as a single line. Only possible with `core.ignorecase`, and only
    // when something is worktree-deleted, so the common case short-circuits on
    // the cheap scan before ever reading config.
    let phantom_deletes = if non_submod
        .iter()
        .any(|e| e.status().contains(git2::Status::WT_DELETED))
        && repo
            .config()
            .and_then(|c| c.get_bool("core.ignorecase"))
            .unwrap_or(false)
    {
        case_collision::phantom_deletes(&non_submod)
    } else {
        FxHashSet::default()
    };

    let submod_changes = if opts.ignore_submodules == IgnoreSubmodules::All {
        SubmoduleChanges::default()
    } else {
        submodule_changes(&repo)?
    };

    let raw_submods = submodule_statuses()?;
    // Per-submodule `submodule.<name>.ignore` only matters when the global
    // flag is unset (or `--ignore-submodules=none`). Any other global value
    // overrides everything, so skip the config scan.
    let per_submodule_ignore = if opts.ignore_submodules == IgnoreSubmodules::None {
        crate::git::parse_per_submodule_ignore(&repo, &project.repo_root)
    } else {
        rustc_hash::FxHashMap::default()
    };
    let mut submods = submodule::apply_ignore_submodules(
        raw_submods,
        opts.ignore_submodules,
        &per_submodule_ignore,
    );
    submodule::filter_rename_new_paths(&mut submods, &submod_changes.renamed);

    // An unmerged submodule is reported once, through the conflict machinery,
    // never also as a separate dirty row. Fold each into its conflict entry:
    // drop it from the normal submodule rows (every format), and carry its
    // state (modified/untracked from libgit2, plus a HEAD-vs-ours commit check
    // libgit2 can't do during a conflict) for the porcelain v2 `u` line.
    let conflicted_submodules = if has_conflicts {
        let folded = submodule::conflicted_submodule_statuses(&repo, &project.repo_root, &submods)?;
        submods.retain(|(path, _)| !folded.contains_key(path));
        folded
    } else {
        FxHashMap::default()
    };

    // Path-formatting policy by output mode:
    // - Porcelain v1: repo-root-relative regardless of cwd.
    // - Porcelain v2: cwd-relative without `-z`, repo-root-relative
    //   with `-z` (where paths are stable identifiers).
    // - Short and long: cwd-relative.
    let cwd_rel = cwd_relative_to_repo(&project.repo_root, &project.effective_cwd);
    let rel = relativize::Relativizer::new(&cwd_rel, opts.quote_path);

    let entries = StatusEntries {
        non_submod: &non_submod,
        submodules: &submods,
        deleted_submodules: &submod_changes.deleted,
        renamed_submodules: &submod_changes.renamed,
        conflicted_paths: &conflicted_paths,
        conflicted_submodules: &conflicted_submodules,
        phantom_deletes: &phantom_deletes,
    };

    render(&repo, &entries, &rel)
}

/// Retrieves and displays the statuses for the repository described by
/// `project`. Paths in the output are reported relative to
/// [`ProjectPath::effective_cwd`], matching `git -C <path> status`.
///
/// # Errors
///
/// Returns `Err` if statuses cannot be retrieved from the repository or watch server
pub fn status(
    project: &ProjectPath,
    display_progress: bool,
    use_server: bool,
    opts: OutputOpts,
    out: &mut impl io::Write,
) -> StatusResult<()> {
    // Send IPC request early so the server starts processing while we
    // do local work.
    let mut conn = if use_server {
        Some(send_status_request(&project.repo_root, display_progress)?)
    } else {
        None
    };

    let porcelain_opts = PorcelainOpts {
        null_terminate: opts.null_terminate,
        branch: opts.branch,
        ahead_behind: opts.ahead_behind,
        quote_path: opts.quote_path,
        show_stash: opts.show_stash,
    };
    let format = opts.format;
    let ahead_behind = opts.ahead_behind;
    let show_stash = opts.show_stash;
    let ignore_submodules = opts.ignore_submodules;
    let kind = project.kind;

    assemble_status(
        project,
        opts,
        || match conn {
            Some(ref mut c) => Ok(recv_status_response(c, display_progress)?.0),
            None if kind.has_submodules() && ignore_submodules != IgnoreSubmodules::All => {
                compute_local_statuses(&project.repo_root)
            }
            None => Ok(Vec::new()),
        },
        |repo, entries, rel| {
            match format {
                OutputFormat::Long => {
                    display::display_status(out, repo, entries, rel, ahead_behind, show_stash)?;
                }
                OutputFormat::Short => {
                    short::display_short(out, repo, entries, rel, porcelain_opts)?;
                }
                OutputFormat::Porcelain(PorcelainVersion::V1) => {
                    porcelain_v1::display_porcelain_v1(out, repo, entries, porcelain_opts)?;
                }
                OutputFormat::Porcelain(PorcelainVersion::V2) => {
                    porcelain_v2::display_porcelain_v2(out, repo, entries, rel, porcelain_opts)?;
                }
            }
            Ok(())
        },
    )
}

/// Returns `effective_cwd` expressed relative to `repo_root`, as forward-slash
/// separated bytes suitable for [`relativize::Relativizer::new`].
///
/// Returns `Cow::Borrowed(b"")` when `effective_cwd == repo_root` or when the
/// prefix relationship can't be computed - both cases produce a no-op
/// `Relativizer`.
fn cwd_relative_to_repo<'a>(repo_root: &Path, effective_cwd: &'a Path) -> Cow<'a, [u8]> {
    effective_cwd
        .strip_prefix(repo_root)
        .map_or(Cow::Borrowed(b"".as_slice()), os_path_to_slash_bytes)
}

/// The bytes of `path` with platform separators normalized to `/`, for
/// prefix-matching against git's path bytes.
///
/// On Unix this borrows the raw `OsStr` bytes, so a non-UTF-8 cwd component
/// round-trips. On Windows paths are always valid Unicode (UTF-8 is lossless),
/// and `\` separators are normalized to `/`.
fn os_path_to_slash_bytes(path: &Path) -> Cow<'_, [u8]> {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt as _;
        Cow::Borrowed(path.as_os_str().as_bytes())
    }
    #[cfg(not(unix))]
    {
        Cow::Owned(path.to_string_lossy().replace('\\', "/").into_bytes())
    }
}

/// Line terminator for porcelain output: NUL with `-z`, LF without.
const fn line_terminator(null_terminate: bool) -> &'static str {
    if null_terminate { "\0" } else { "\n" }
}

/// Returns the branch name HEAD points at, intended for the unborn-branch
/// case (empty repo, no commits) where `repo.head()` returned `Err` but
/// `HEAD` still points at some `refs/heads/<branch>`.
fn unborn_branch_name<'a>(head: &'a git2::Reference<'_>) -> Option<&'a str> {
    head.symbolic_target()
        .ok()
        .flatten()
        .map(|t| t.strip_prefix("refs/heads/").unwrap_or(t))
}

/// Resolves the configured upstream short name (e.g. `origin/master`) for
/// the branch whose full ref name is `local_ref_name`, without requiring
/// the remote-tracking ref to exist. Used to distinguish "no upstream
/// configured" from "configured but gone" once `Branch::upstream()` has
/// already failed.
fn configured_upstream_short_name(repo: &Repository, local_ref_name: &str) -> Option<String> {
    let buf = repo.branch_upstream_name(local_ref_name).ok()?;
    let full = buf.as_str().ok()?;
    Some(
        full.strip_prefix("refs/remotes/")
            .unwrap_or(full)
            .to_string(),
    )
}

/// How the current branch relates to its configured upstream. Resolved once by
/// [`upstream_status`] and formatted per-renderer (long / short+v1 / porcelain-v2).
enum UpstreamStatus {
    /// No upstream configured (or `HEAD` isn't a resolvable local branch).
    None,
    /// An upstream is configured but its remote-tracking ref is gone (e.g. after
    /// `git fetch --prune`); `name` is the configured short name.
    Gone { name: String },
    /// Upstream `name` exists; the branch diverges from it by `divergence`.
    Tracking {
        name: String,
        divergence: Divergence,
    },
}

/// The ahead/behind relationship of a branch to its upstream.
enum Divergence {
    /// Ahead/behind commit counts; `(0, 0)` means the tips are equal (up to date).
    Counts(usize, usize),
    /// The tips differ but the counts were skipped (`--no-ahead-behind`).
    Skipped,
}

/// Resolves the [`UpstreamStatus`] of `head` (the current `HEAD` reference).
///
/// Callers handle the unborn- and detached-HEAD cases themselves; a non-branch
/// `head` resolves to [`UpstreamStatus::None`].
///
/// # Errors
///
/// Propagates a `git2::Error` if a branch tip can't be peeled to a commit or the
/// ahead/behind graph walk fails -- both indicate repository corruption (a
/// missing/unreadable commit object), not merely a missing upstream.
fn upstream_status(
    repo: &Repository,
    head: &git2::Reference<'_>,
    ahead_behind: bool,
) -> StatusResult<UpstreamStatus> {
    let Ok(local_name) = head.shorthand() else {
        return Ok(UpstreamStatus::None);
    };
    let Ok(local) = repo.find_branch(local_name, git2::BranchType::Local) else {
        return Ok(UpstreamStatus::None);
    };
    let Ok(upstream) = local.upstream() else {
        // No upstream resolved: distinguish "none configured" from "configured
        // but gone" so renderers can show a `[gone]` marker.
        let gone = head
            .name()
            .ok()
            .and_then(|ref_name| configured_upstream_short_name(repo, ref_name));
        return Ok(gone.map_or(UpstreamStatus::None, |name| UpstreamStatus::Gone { name }));
    };
    let name = String::from_utf8_lossy(upstream.get().shorthand_bytes()).into_owned();
    let local_oid = local.get().peel_to_commit()?.id();
    let upstream_oid = upstream.get().peel_to_commit()?.id();
    let divergence = if local_oid == upstream_oid {
        Divergence::Counts(0, 0)
    } else if ahead_behind {
        let (ahead, behind) = repo.graph_ahead_behind(local_oid, upstream_oid)?;
        Divergence::Counts(ahead, behind)
    } else {
        Divergence::Skipped
    };
    Ok(UpstreamStatus::Tracking { name, divergence })
}
