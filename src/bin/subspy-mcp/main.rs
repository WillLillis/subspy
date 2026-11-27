//! MCP (Model Context Protocol) server that serves subspy's cached statuses to
//! AI agents.

mod server;
mod status;

use std::{env, io, process::ExitCode};

use clap::Parser;
use rmcp::{
    ServiceExt as _,
    service::{QuitReason, ServerInitializeError},
};
use thiserror::Error;

use subspy::{
    entry::{INTERNAL_FLAG, exit_code, install_subspy_client_logger, subspy_entry},
    git::configure_git2,
};

use server::SubspyMcp;

/// Why the MCP server could not start or stopped abnormally.
#[derive(Debug, Error)]
enum McpServerError {
    #[error("failed to start the async runtime: {0}")]
    RuntimeInit(#[source] io::Error),
    #[error("MCP initialization failed: {0}")]
    Initialize(#[source] Box<ServerInitializeError>),
    #[error("the MCP service stopped unexpectedly: {0}")]
    Service(#[from] tokio::task::JoinError),
    #[error("the MCP service stopped for an unrecognized reason: {0:?}")]
    UnrecognizedQuit(QuitReason),
}

/// An MCP server exposing subspy's submodule-aware `git status` to AI agents.
#[derive(Parser)]
#[command(name = "subspy-mcp", version = env!("SUBSPY_VERSION"))]
struct Cli {}

fn main() -> ExitCode {
    if env::args_os()
        .nth(1)
        .is_some_and(|arg| arg == INTERNAL_FLAG)
    {
        return subspy_entry(env::args_os());
    }
    exit_code(run())
}

fn run() -> Result<(), McpServerError> {
    Cli::parse();
    configure_git2();
    install_subspy_client_logger();

    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_time()
        .build()
        .map_err(McpServerError::RuntimeInit)?;

    let result = runtime.block_on(serve());

    runtime.shutdown_background();
    result
}

/// Serves MCP over stdin and stdout until the client disconnects.
async fn serve() -> Result<(), McpServerError> {
    let service = SubspyMcp::new()
        .serve(rmcp::transport::stdio())
        .await
        .map_err(|err| McpServerError::Initialize(Box::new(err)))?;
    match service.waiting().await? {
        QuitReason::Closed => Ok(()),
        // Only the service's own token cancels the loop, and we never fire it.
        QuitReason::Cancelled => unreachable!(),
        QuitReason::JoinError(err) => Err(err.into()),
        reason => Err(McpServerError::UnrecognizedQuit(reason)),
    }
}
