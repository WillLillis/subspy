use std::borrow::Cow;

use anstyle::{Color, Style};
use bincode::{BorrowDecode, Encode};
use bitflags::bitflags;
use indicatif::{ProgressBar, ProgressStyle};

pub mod connection;
pub mod debug;
pub mod reindex;
pub mod shutdown;
pub mod status;
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

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Encode, BorrowDecode)]
pub struct StatusSummary(u32);

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
        Self(value & 0b1111)
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

pub(crate) fn paint(color: Option<impl Into<Color>>, text: &str) -> String {
    let style = Style::new().fg_color(color.map(Into::into));
    format!("{style}{text}{style:#}")
}

/// Creats a new styled `indicatif::ProgressBar`
fn create_progress_bar(len: u64, prefix: impl Into<Cow<'static, str>>) -> indicatif::ProgressBar {
    ProgressBar::new(len)
        .with_style(
            ProgressStyle::with_template("{prefix:.cyan.bold}: {wide_bar:} {pos}/{len}").unwrap(),
        )
        .with_prefix(prefix)
}
