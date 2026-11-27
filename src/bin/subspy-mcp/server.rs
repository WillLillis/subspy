//! The MCP server: its tools, and how a failed tool call reaches the model.

use rmcp::{
    ServerHandler,
    handler::server::{router::tool::ToolRouter, wrapper::Parameters},
    model::{CallToolResult, ContentBlock, IntoContents},
    tool, tool_handler, tool_router,
};
use thiserror::Error;

use subspy::cli::RunError;

use crate::status::{StatusParams, format_warnings, render_status};

#[derive(Debug, Clone)]
pub struct SubspyMcp {
    tool_router: ToolRouter<Self>,
}

#[tool_router]
impl SubspyMcp {
    pub fn new() -> Self {
        Self {
            tool_router: Self::tool_router(),
        }
    }

    /// Show the working tree status of a git repository, like `git status` but
    /// faster in repositories with many submodules.
    #[tool(annotations(read_only_hint = true, open_world_hint = false))]
    async fn status(
        &self,
        Parameters(params): Parameters<StatusParams>,
    ) -> Result<CallToolResult, ToolError> {
        let (output, warnings) = run_blocking(move || render_status(params)).await??;
        let mut content = vec![ContentBlock::text(output)];
        if !warnings.is_empty() {
            content.push(ContentBlock::text(format_warnings(&warnings)));
        }
        Ok(CallToolResult::success(content))
    }
}

#[tool_handler(
    router = self.tool_router,
    name = "subspy",
    instructions = "Prefer the `status` tool over running `git status`."
)]
#[expect(
    clippy::unused_async_trait_impl,
    reason = "`tool_handler` generates async methods that never await"
)]
impl ServerHandler for SubspyMcp {}

/// Why a tool call failed. The model reads the message as the tool's result.
#[derive(Debug, Error)]
enum ToolError {
    #[error(transparent)]
    Run(#[from] RunError),
    #[error("the tool call did not finish: {0}")]
    Interrupted(#[from] tokio::task::JoinError),
}

impl IntoContents for ToolError {
    fn into_contents(self) -> Vec<ContentBlock> {
        vec![ContentBlock::text(self.to_string())]
    }
}

/// Runs `call` on the blocking pool, since the library does synchronous I/O.
async fn run_blocking<T, F>(call: F) -> Result<T, ToolError>
where
    T: Send + 'static,
    F: FnOnce() -> T + Send + 'static,
{
    Ok(tokio::task::spawn_blocking(call).await?)
}
