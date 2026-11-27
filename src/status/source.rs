//! Where a repository's submodule statuses come from: its watch server when it
//! can host one, and computed in this process otherwise.

use std::path::Path;

use thiserror::Error;

use crate::{
    RepoKind, StatusSummary,
    connection::{
        IpcError,
        client::{recv_status_response, send_status_request},
    },
    git::path::GitPath,
};

use super::compute_local_statuses;

#[derive(Error, Debug)]
pub enum SourceError {
    #[error(transparent)]
    Ipc(#[from] IpcError),
    #[error(transparent)]
    Git(#[from] git2::Error),
}

/// Where a repository's submodule statuses come from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatusSource {
    /// The repository's watch server, started if it isn't running.
    Server,
    /// Computed in this process, for `--no-server` or a repository that
    /// cannot host a server.
    Local,
}

impl StatusSource {
    /// The watch server when the repository can host one and `no_server` is
    /// unset, local computation otherwise.
    #[must_use]
    pub const fn new(kind: RepoKind, no_server: bool) -> Self {
        if !no_server && kind.server_eligible() {
            Self::Server
        } else {
            Self::Local
        }
    }

    /// Reads the statuses of the repository at `root_path`: each submodule
    /// that is not clean, in path order, and how many submodules the index
    /// records. `display_progress` shows progress bars while a server starts
    /// or indexes.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the server exchange fails or the repository cannot be
    /// read.
    pub fn read(
        self,
        root_path: &Path,
        display_progress: bool,
    ) -> Result<(Vec<(GitPath, StatusSummary)>, usize), SourceError> {
        match self {
            Self::Server => {
                let mut conn = send_status_request(root_path, display_progress)?;
                let (changed, total) = recv_status_response(&mut conn, display_progress)?;
                Ok((changed, total as usize))
            }
            Self::Local => Ok(compute_local_statuses(root_path)?),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;
    use rstest_reuse::apply;
    use testutil::{HarnessBuilder, RefFormat};

    use crate::test_support::formats;

    #[test]
    fn server_only_for_eligible_repositories() {
        for kind in [RepoKind::WithSubmodules, RepoKind::WorktreeWithSubmodules] {
            assert_eq!(StatusSource::new(kind, false), StatusSource::Server);
            assert_eq!(StatusSource::new(kind, true), StatusSource::Local);
        }
        for kind in [
            RepoKind::Normal,
            RepoKind::Submodule,
            RepoKind::SubmoduleWithSubmodules,
            RepoKind::Worktree,
            RepoKind::OtherGitlink,
            RepoKind::OtherGitlinkWithSubmodules,
        ] {
            assert_eq!(StatusSource::new(kind, false), StatusSource::Local);
        }
    }

    /// A submodule the local reader cannot open reports as unreadable rather
    /// than failing the whole read.
    #[apply(formats)]
    fn local_status_of_an_unopenable_submodule_is_unreadable(ref_format: RefFormat) {
        let harness = HarnessBuilder::new()
            .no_server()
            .ref_format(ref_format)
            .submodule("sub_a")
            .submodule("sub_b")
            .build();
        let read = || {
            StatusSource::Local
                .read(harness.root().path(), false)
                .unwrap()
        };
        assert_eq!(read(), (Vec::new(), 2));

        harness.submodule("sub_a").declare_unsupported_extension();
        assert_eq!(
            read(),
            (vec![(GitPath::from("sub_a"), StatusSummary::UNREADABLE)], 2)
        );
    }
}
