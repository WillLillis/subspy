//! Config-supplied defaults for `git status` output.
//!
//! git treats these keys as defaults that an explicit flag replaces, so they
//! are resolved where argv is parsed rather than inside the status pipeline.
//! Both binaries share [`ConfigDefaults::read`] so the two agree.

use std::path::Path;

use git2::Repository;

use super::UntrackedFiles;

/// The [`super::OutputOpts`] values git takes from config when no flag sets them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[expect(clippy::struct_excessive_bools, reason = "matches git")]
pub struct ConfigDefaults {
    /// `status.showUntrackedFiles`
    pub untracked_files: UntrackedFiles,
    /// `core.quotepath`
    pub quote_path: bool,
    /// `status.showStash`
    pub show_stash: bool,
    /// `status.relativePaths`
    pub relative_paths: bool,
    /// `advice.statusHints`
    pub status_hints: bool,
}

impl ConfigDefaults {
    /// git's built-ins, used when the repository or its config is unreadable.
    pub const GIT: Self = Self {
        untracked_files: UntrackedFiles::Normal,
        quote_path: true,
        show_stash: false,
        relative_paths: true,
        status_hints: true,
    };

    /// Reads the defaults from the effective config for `repo_root`, which
    /// includes the global and system files git would consult.
    #[must_use]
    pub fn read(repo_root: &Path) -> Self {
        let Ok(config) = Repository::open(repo_root).and_then(|repo| repo.config()) else {
            return Self::GIT;
        };
        Self {
            untracked_files: untracked_files(&config).unwrap_or(Self::GIT.untracked_files),
            quote_path: config
                .get_bool("core.quotepath")
                .unwrap_or(Self::GIT.quote_path),
            show_stash: config
                .get_bool("status.showStash")
                .unwrap_or(Self::GIT.show_stash),
            relative_paths: config
                .get_bool("status.relativePaths")
                .unwrap_or(Self::GIT.relative_paths),
            status_hints: config
                .get_bool("advice.statusHints")
                .unwrap_or(Self::GIT.status_hints),
        }
    }
}

/// `status.showUntrackedFiles` takes the three mode names, lowercase only, and
/// otherwise falls back to a boolean where true is `normal` and false is `no`.
/// That fallback is what makes `No` and `0` valid while `Normal` is not.
fn untracked_files(config: &git2::Config) -> Option<UntrackedFiles> {
    const KEY: &str = "status.showUntrackedFiles";
    match config.get_string(KEY).ok()?.as_str() {
        "no" => Some(UntrackedFiles::No),
        "normal" => Some(UntrackedFiles::Normal),
        "all" => Some(UntrackedFiles::All),
        _ => match config.get_bool(KEY) {
            Ok(true) => Some(UntrackedFiles::Normal),
            Ok(false) => Some(UntrackedFiles::No),
            Err(_) => None,
        },
    }
}
