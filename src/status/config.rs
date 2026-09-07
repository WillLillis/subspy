//! Config-supplied defaults for `git status` output.
//!
//! git treats these keys as defaults that an explicit flag replaces, so they
//! are resolved where argv is parsed rather than inside the status pipeline.
//! Both binaries share [`ConfigDefaults::read`] so the two agree.

use std::path::Path;

use git2::Repository;

use super::{
    IgnoreSubmodules, UntrackedFiles,
    header::abbrev_is_valid,
    tracked::{RenameKey, configured_rename_detection},
};

/// `status.showUntrackedFiles`, named once so the reader and the validity check
/// cannot drift apart.
const UNTRACKED_KEY: &str = "status.showUntrackedFiles";

/// `diff.ignoreSubmodules`, same.
const IGNORE_SUBMODULES_KEY: &str = "diff.ignoreSubmodules";

/// The [`super::OutputOpts`] values git takes from config when no flag sets them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[expect(clippy::struct_excessive_bools, reason = "matches git")]
pub struct ConfigDefaults {
    /// `status.showUntrackedFiles`
    pub untracked_files: UntrackedFiles,
    /// `diff.ignoreSubmodules`. Per-submodule `submodule.<name>.ignore` is
    /// libgit2's to apply and stays out of here.
    pub ignore_submodules: IgnoreSubmodules,
    /// `core.quotepath`
    pub quote_path: bool,
    /// `status.showStash`
    pub show_stash: bool,
    /// `status.relativePaths`
    pub relative_paths: bool,
    /// `advice.statusHints`
    pub status_hints: bool,
    /// `status.short`, the default output format when no format flag is given.
    pub short: bool,
    /// `status.branch`. Only reaches the short format. git leaves porcelain
    /// headers to an explicit `--branch`.
    pub branch: bool,
    /// `status.aheadBehind`. Only reaches the long format. Porcelain v2 keeps
    /// real counts unless `--no-ahead-behind` is passed.
    pub ahead_behind: bool,
}

impl ConfigDefaults {
    /// git's built-ins, used when the repository or its config is unreadable.
    pub const GIT: Self = Self {
        untracked_files: UntrackedFiles::Normal,
        ignore_submodules: IgnoreSubmodules::None,
        quote_path: true,
        show_stash: false,
        relative_paths: true,
        status_hints: true,
        short: false,
        branch: false,
        ahead_behind: true,
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
            ignore_submodules: ignore_submodules(&config).unwrap_or(Self::GIT.ignore_submodules),
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
            short: config.get_bool("status.short").unwrap_or(Self::GIT.short),
            branch: config.get_bool("status.branch").unwrap_or(Self::GIT.branch),
            ahead_behind: config
                .get_bool("status.aheadBehind")
                .unwrap_or(Self::GIT.ahead_behind),
        }
    }
}

/// Keys read as plain booleans, where anything git's boolean parser rejects is
/// fatal to git.
const BOOL_KEYS: &[&str] = &[
    "core.quotepath",
    "status.showStash",
    "status.relativePaths",
    "advice.statusHints",
    "status.short",
    "status.branch",
    "status.aheadBehind",
];

const INT_KEYS: &[&str] = &["status.renameLimit", "diff.renameLimit"];

/// A setting subspy cannot honor for a given request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnmodeledConfig {
    /// A key subspy reads holds a value git rejects outright, so git would
    /// fail where subspy would happily render a default.
    Invalid(&'static str),
    /// `status.submoduleSummary`, whose per-submodule commit listing subspy
    /// does not produce.
    SubmoduleSummary,
    /// `status.displayCommentPrefix`, which prefixes every long-format line.
    DisplayCommentPrefix,
}

impl std::fmt::Display for UnmodeledConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(key) => write!(f, "{key} holds a value git rejects"),
            Self::SubmoduleSummary => f.write_str("status.submoduleSummary is not implemented"),
            Self::DisplayCommentPrefix => {
                f.write_str("status.displayCommentPrefix is not implemented")
            }
        }
    }
}

/// The first setting this request cannot honor.
///
/// `long` gates the two keys that only change the long format. An unparseable
/// value is fatal to git in every format, so it is never gated.
#[must_use]
pub fn unmodeled(config: &git2::Config, long: bool) -> Option<UnmodeledConfig> {
    if let Some(key) = invalid_value(config) {
        return Some(UnmodeledConfig::Invalid(key));
    }
    if !long {
        return None;
    }
    if config.get_bool("status.submoduleSummary").unwrap_or(false) {
        return Some(UnmodeledConfig::SubmoduleSummary);
    }
    if config
        .get_bool("status.displayCommentPrefix")
        .unwrap_or(false)
    {
        return Some(UnmodeledConfig::DisplayCommentPrefix);
    }
    None
}

/// Whether the key is set at all. A value git cannot parse is only interesting
/// when the user actually wrote one.
fn is_set(config: &git2::Config, key: &str) -> bool {
    config.get_string(key).is_ok()
}

fn invalid_value(config: &git2::Config) -> Option<&'static str> {
    for key in BOOL_KEYS {
        if is_set(config, key) && config.get_bool(key).is_err() {
            return Some(key);
        }
    }
    for key in INT_KEYS {
        if is_set(config, key) && config.get_i32(key).is_err() {
            return Some(key);
        }
    }
    for key in [RenameKey::Status, RenameKey::Diff] {
        if is_set(config, key.name()) && configured_rename_detection(config, key).is_none() {
            return Some(key.name());
        }
    }
    if is_set(config, UNTRACKED_KEY) && untracked_files(config).is_none() {
        return Some(UNTRACKED_KEY);
    }
    if is_set(config, IGNORE_SUBMODULES_KEY) && ignore_submodules(config).is_none() {
        return Some(IGNORE_SUBMODULES_KEY);
    }
    if is_set(config, "core.abbrev") && !abbrev_is_valid(config) {
        return Some("core.abbrev");
    }
    None
}

/// `diff.ignoreSubmodules` takes the four mode names, lowercase only. git has no
/// boolean fallback here and dies on anything else.
fn ignore_submodules(config: &git2::Config) -> Option<IgnoreSubmodules> {
    match config.get_string(IGNORE_SUBMODULES_KEY).ok()?.as_str() {
        "none" => Some(IgnoreSubmodules::None),
        "untracked" => Some(IgnoreSubmodules::Untracked),
        "dirty" => Some(IgnoreSubmodules::Dirty),
        "all" => Some(IgnoreSubmodules::All),
        _ => None,
    }
}

/// `status.showUntrackedFiles` takes the three mode names, lowercase only, and
/// otherwise falls back to a boolean where true is `normal` and false is `no`.
/// That fallback is what makes `No` and `0` valid while `Normal` is not.
fn untracked_files(config: &git2::Config) -> Option<UntrackedFiles> {
    match config.get_string(UNTRACKED_KEY).ok()?.as_str() {
        "no" => Some(UntrackedFiles::No),
        "normal" => Some(UntrackedFiles::Normal),
        "all" => Some(UntrackedFiles::All),
        _ => match config.get_bool(UNTRACKED_KEY) {
            Ok(true) => Some(UntrackedFiles::Normal),
            Ok(false) => Some(UntrackedFiles::No),
            Err(_) => None,
        },
    }
}
