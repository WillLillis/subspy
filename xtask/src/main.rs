mod rename_score_corpus;

use std::path::PathBuf;

use clap::{Args, FromArgMatches as _, Subcommand};

#[derive(Subcommand)]
#[command(about = "Run subspy maintenance tasks", author = env!("CARGO_PKG_AUTHORS"))]
enum Commands {
    /// Generate a clean-room Git rename-score observation corpus.
    RenameScoreCorpus(RenameScoreCorpusArgs),
}

#[derive(Args)]
struct RenameScoreCorpusArgs {
    /// Output CSV path.
    #[arg(long, default_value = "rename_score_corpus.csv")]
    output: PathBuf,

    /// Rename threshold passed to `git diff -M<N>%`.
    ///
    /// The default is intentionally low so the corpus captures scores below
    /// Git's normal 50% rename threshold. For status-parity analysis, rerun
    /// with `--threshold 50`.
    #[arg(long, default_value_t = 1)]
    threshold: u8,

    /// Keep per-case repositories under the system temp directory for manual inspection.
    #[arg(long)]
    keep_repos: bool,
}

fn main() {
    if let Err(err) = run() {
        eprintln!("{err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), XtaskError> {
    let cli = clap::Command::new("xtask")
        .help_template(
            "\
{before-help}{name}
{author-with-newline}{about-with-newline}
{usage-heading} {usage}

{all-args}{after-help}
",
        )
        .subcommand_required(true)
        .arg_required_else_help(true)
        .disable_help_subcommand(true)
        .disable_colored_help(false);
    let command = Commands::from_arg_matches(&Commands::augment_subcommands(cli).get_matches())?;

    match command {
        Commands::RenameScoreCorpus(args) => rename_score_corpus::run(&args)?,
    }
    Ok(())
}

#[derive(Debug, thiserror::Error)]
enum XtaskError {
    #[error(transparent)]
    Clap(#[from] clap::Error),
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Utf8(#[from] std::string::FromUtf8Error),
    #[error("--threshold must be between 0 and 100")]
    InvalidRenameThreshold,
    #[error("command failed: {command}\nstdout:\n{stdout}\nstderr:\n{stderr}")]
    CommandFailed {
        command: String,
        stdout: String,
        stderr: String,
    },
}
