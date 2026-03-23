use std::borrow::Cow;

use anstyle::{Color, Style};
use bincode::{BorrowDecode, Encode};
use bitflags::bitflags;
use indicatif::{ProgressBar, ProgressStyle};

pub mod connection;
pub mod debug;
pub mod list;
pub mod prompt;
pub mod reindex;
pub mod shutdown;
pub mod status;
pub mod template;
pub mod watch;

pub const DOT_GITMODULES: &str = ".gitmodules";
pub const DOT_GIT: &str = ".git";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RepoKind {
    /// A git repository with "just" a `.git` folder.
    Normal,
    /// A git repository with a `.git` folder and a `.gitmodules` file.
    WithSubmodules,
    /// A git repository with a `.git` _file_ pointing to a parent `.git`
    /// subdirectory. May or may not have submodules of its own.
    Submodule,
}

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash, Encode, BorrowDecode)]
pub struct StatusSummary(u32);

impl std::fmt::Debug for StatusSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return write!(f, "CLEAN");
        }
        let mut first = true;
        for (name, _) in self.iter_names() {
            if !first {
                write!(f, " | ")?;
            }
            first = false;
            write!(f, "{name}")?;
        }
        Ok(())
    }
}

bitflags! {
    /// Represents the status of a submodule
    impl StatusSummary: u32 {
        const CLEAN             = 0b0000;
        const MODIFIED_CONTENT  = 0b0001;
        const UNTRACKED_CONTENT = 0b0010;
        const NEW_COMMITS       = 0b0100;
        const STAGED            = 0b1000;
        const LOCK_FAILURE      = 1 << 31;
    }
}

/// Formats the summary for the `status` command. `STAGED` is intentionally
/// omitted here because the `status` display handles staging separately;
/// see [`list::status_text`] for a variant that includes it.
impl std::fmt::Display for StatusSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.eq(&Self::CLEAN) {
            return Ok(());
        }

        let mut has_content = false;
        let mut add_info = |item: &str| -> std::fmt::Result {
            if has_content {
                write!(f, ", ")?;
            } else {
                write!(f, "(")?;
            }
            write!(f, "{item}")?;

            has_content = true;

            Ok(())
        };

        if self.contains(Self::MODIFIED_CONTENT) {
            add_info("modified content")?;
        }
        if self.contains(Self::UNTRACKED_CONTENT) {
            add_info("untracked content")?;
        }
        if self.contains(Self::NEW_COMMITS) {
            add_info("new commits")?;
        }
        if has_content {
            write!(f, ")")?;
        }

        Ok(())
    }
}

impl From<u32> for StatusSummary {
    fn from(value: u32) -> Self {
        Self(value & Self::all().bits())
    }
}

impl From<git2::SubmoduleStatus> for StatusSummary {
    fn from(value: git2::SubmoduleStatus) -> Self {
        let mut submod_status = Self::CLEAN;
        if value.contains(git2::SubmoduleStatus::WD_MODIFIED) {
            submod_status |= Self::NEW_COMMITS;
        }
        if value.contains(git2::SubmoduleStatus::WD_INDEX_MODIFIED)
            || value.contains(git2::SubmoduleStatus::WD_WD_MODIFIED)
        {
            submod_status |= Self::MODIFIED_CONTENT;
        }
        if value.contains(git2::SubmoduleStatus::WD_UNTRACKED) {
            submod_status |= Self::UNTRACKED_CONTENT;
        }

        if value.contains(
            git2::SubmoduleStatus::IN_HEAD
                | git2::SubmoduleStatus::IN_INDEX
                | git2::SubmoduleStatus::INDEX_MODIFIED,
        ) {
            submod_status |= Self::STAGED;
        }

        submod_status
    }
}

pub fn paint(color: Option<impl Into<Color>>, text: &str) -> String {
    let style = Style::new().fg_color(color.map(Into::into));
    format!("{style}{text}{style:#}")
}

/// Creates a new styled `indicatif::ProgressBar`
fn create_progress_bar(len: u64, prefix: impl Into<Cow<'static, str>>) -> indicatif::ProgressBar {
    ProgressBar::new(len)
        .with_style(
            ProgressStyle::with_template("{prefix:.cyan.bold}: {wide_bar:} {pos}/{len}").unwrap(),
        )
        .with_prefix(prefix)
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- StatusSummary Display --

    #[test]
    fn display_clean() {
        assert_eq!(StatusSummary::CLEAN.to_string(), "");
    }

    #[test]
    fn display_single_flag() {
        assert_eq!(
            StatusSummary::MODIFIED_CONTENT.to_string(),
            "(modified content)"
        );
    }

    #[test]
    fn display_multiple_flags() {
        let s = StatusSummary::MODIFIED_CONTENT | StatusSummary::NEW_COMMITS;
        assert_eq!(s.to_string(), "(modified content, new commits)");
    }

    #[test]
    fn display_omits_staged() {
        let s = StatusSummary::MODIFIED_CONTENT | StatusSummary::STAGED;
        assert_eq!(s.to_string(), "(modified content)");
    }

    #[test]
    fn display_all_visible_flags() {
        let s = StatusSummary::MODIFIED_CONTENT
            | StatusSummary::UNTRACKED_CONTENT
            | StatusSummary::NEW_COMMITS;
        assert_eq!(
            s.to_string(),
            "(modified content, untracked content, new commits)"
        );
    }

    // -- From<git2::SubmoduleStatus> --

    #[test]
    fn from_submodule_status_clean() {
        let s = StatusSummary::from(git2::SubmoduleStatus::empty());
        assert_eq!(s, StatusSummary::CLEAN);
    }

    #[test]
    fn from_submodule_status_wd_modified_is_new_commits() {
        let s = StatusSummary::from(git2::SubmoduleStatus::WD_MODIFIED);
        assert!(s.contains(StatusSummary::NEW_COMMITS));
    }

    #[test]
    fn from_submodule_status_wd_index_modified_is_modified_content() {
        let s = StatusSummary::from(git2::SubmoduleStatus::WD_INDEX_MODIFIED);
        assert!(s.contains(StatusSummary::MODIFIED_CONTENT));
    }

    #[test]
    fn from_submodule_status_wd_wd_modified_is_modified_content() {
        let s = StatusSummary::from(git2::SubmoduleStatus::WD_WD_MODIFIED);
        assert!(s.contains(StatusSummary::MODIFIED_CONTENT));
    }

    #[test]
    fn from_submodule_status_wd_untracked() {
        let s = StatusSummary::from(git2::SubmoduleStatus::WD_UNTRACKED);
        assert!(s.contains(StatusSummary::UNTRACKED_CONTENT));
    }

    #[test]
    fn from_submodule_status_staged() {
        let s = StatusSummary::from(
            git2::SubmoduleStatus::IN_HEAD
                | git2::SubmoduleStatus::IN_INDEX
                | git2::SubmoduleStatus::INDEX_MODIFIED,
        );
        assert!(s.contains(StatusSummary::STAGED));
    }

    #[test]
    fn from_submodule_status_combined() {
        let s = StatusSummary::from(
            git2::SubmoduleStatus::WD_MODIFIED
                | git2::SubmoduleStatus::WD_UNTRACKED
                | git2::SubmoduleStatus::WD_WD_MODIFIED,
        );
        assert!(s.contains(StatusSummary::NEW_COMMITS));
        assert!(s.contains(StatusSummary::UNTRACKED_CONTENT));
        assert!(s.contains(StatusSummary::MODIFIED_CONTENT));
    }
}
