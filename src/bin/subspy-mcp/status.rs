//! The `status` tool's interface: its arguments, and how they map onto
//! `subspy status`.

use std::{fmt::Write as _, path::PathBuf};

use rmcp::schemars::JsonSchema;
use serde::Deserialize;

use subspy::{
    cli::{RunError, get_project_path},
    status::{
        ConfigDefaults, PorcelainVersion, ResolvedStatusRequest, StatusFlags, StatusWarning, status,
    },
};

// The `status` tool's arguments: a small subset of `subspy status`'s flags,
// which `render_status` turns into `StatusFlags`.
#[derive(Debug, Default, Deserialize, JsonSchema)]
#[schemars(crate = "rmcp::schemars")]
pub struct StatusParams {
    /// The repository root or a directory inside it, defaulting to the server's
    /// working directory. Output paths are relative to it, as with `git -C <path> status`.
    path: Option<PathBuf>,
    /// The output format. Defaults to `long`.
    format: Option<Format>,
    /// Which untracked files to list. Defaults to the repository's
    /// `status.showUntrackedFiles`, else `normal`.
    untracked_files: Option<Untracked>,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Deserialize, JsonSchema)]
#[schemars(crate = "rmcp::schemars")]
#[serde(rename_all = "snake_case")]
enum Format {
    /// git's default human-readable layout, which spells out each submodule's
    /// changes (e.g. "new commits, modified content").
    #[default]
    Long,
    /// `git status --short --branch`.
    Short,
    /// `git status --porcelain=v2 --branch`.
    PorcelainV2,
}

impl From<Format> for subspy::status::OutputFormat {
    fn from(format: Format) -> Self {
        match format {
            Format::Long => Self::Long,
            Format::Short => Self::Short,
            Format::PorcelainV2 => Self::Porcelain(PorcelainVersion::V2),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, JsonSchema)]
#[schemars(crate = "rmcp::schemars")]
#[serde(rename_all = "snake_case")]
enum Untracked {
    /// Untracked files, collapsing untracked directories to one entry.
    Normal,
    /// Every untracked file, including those inside untracked directories.
    All,
    /// No untracked files.
    No,
}

impl From<Untracked> for subspy::status::UntrackedFiles {
    fn from(mode: Untracked) -> Self {
        match mode {
            Untracked::Normal => Self::Normal,
            Untracked::All => Self::All,
            Untracked::No => Self::No,
        }
    }
}

/// Renders status output exactly as the equivalent `subspy status` command
/// would, with the repository's config supplying every option left unset.
pub fn render_status(params: StatusParams) -> Result<(String, Vec<StatusWarning>), RunError> {
    let format = params.format.unwrap_or_default();
    let flags = StatusFlags {
        format: Some(format.into()),
        // The long format always shows branch info. The others need the flag.
        branch: format != Format::Long,
        untracked_files: params.untracked_files.map(Into::into),
        ..StatusFlags::default()
    };
    let project = get_project_path(params.path)?;
    let mut out = Vec::with_capacity(4 * 1024);
    let warnings = status(
        ResolvedStatusRequest {
            project: &project,
            no_server: false,
            display_progress: false,
            output: flags.resolve(ConfigDefaults::read(&project.repo_root)),
        },
        &mut out,
    )?;
    let output = String::from_utf8(out)
        .unwrap_or_else(|err| String::from_utf8_lossy(err.as_bytes()).into_owned());
    Ok((output, warnings))
}

pub fn format_warnings(warnings: &[StatusWarning]) -> String {
    let mut text = String::from("subspy warnings:");
    for warning in warnings {
        let _ = write!(text, "\n- {warning}");
    }
    text
}
