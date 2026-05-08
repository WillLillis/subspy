//! Drop-in replacement for `git` that intercepts `git status` and routes it
//! through subspy for repositories with many submodules. Every other git
//! invocation is forwarded to real git unchanged.
//!
//! Designed to be configured as the "Path to git" in tools like
//! `GitExtensions`: point that setting at the absolute path of this binary
//! and the rest of the tool's git interactions are unaffected.

#[cfg(unix)]
use std::os::unix::process::CommandExt as _;

use std::{
    env,
    ffi::OsString,
    path::PathBuf,
    process::{Command, ExitCode},
};

use subspy::{
    cli::Status,
    status::{IgnoreSubmodules, PorcelainVersion, UntrackedFiles},
};

const REAL_GIT: &str = "git";

fn main() -> ExitCode {
    let argv: Vec<OsString> = env::args_os().skip(1).collect();
    #[expect(
        clippy::option_if_let_else,
        reason = "match is clearer than the map_or_else closure form here"
    )]
    match dispatch(&argv) {
        Some(intercept) => run_intercept(intercept),
        None => forward(&argv),
    }
}

/// Parsed result of an intercepted `git status` invocation.
#[derive(Debug, Default, PartialEq, Eq)]
struct Intercept {
    chdir: Option<PathBuf>,
    args: StatusArgs,
}

/// Mirrors the subset of `git status` flags subspy can serve. Kept separate
/// from `cli::Status` so it stays comparable in tests and never leaks
/// subspy-only flags into the shim's surface.
#[derive(Debug, Default, PartialEq, Eq)]
struct StatusArgs {
    porcelain: Option<PorcelainVersion>,
    null_terminate: bool,
    ignore_submodules: IgnoreSubmodules,
    untracked_files: Option<UntrackedFiles>,
    show_ignored: bool,
    branch: bool,
}

impl Intercept {
    fn into_status(self) -> Status {
        Status {
            dir: self.chdir,
            log_level: None,
            no_server: false,
            porcelain: self.args.porcelain,
            null_terminate: self.args.null_terminate,
            ignore_submodules: self.args.ignore_submodules,
            untracked_files: self.args.untracked_files,
            ignored: self.args.show_ignored,
            branch: self.args.branch,
        }
    }
}

/// Walk argv looking for an interceptable `status` invocation.
///
/// Returns `Some(intercept)` if every global option is one we know is safe
/// to honor or ignore AND the subcommand is `status` AND every status flag
/// is one subspy supports. Returns `None` for anything else - the caller
/// should forward the original argv to real git.
fn dispatch(argv: &[OsString]) -> Option<Intercept> {
    // Require UTF-8 throughout. Non-UTF-8 args (rare on modern systems) are
    // safer to forward than to misinterpret.
    let argv: Vec<&str> = argv
        .iter()
        .map(|s| s.to_str())
        .collect::<Option<Vec<_>>>()?;

    let mut intercept = Intercept::default();
    let mut i = 0;

    while i < argv.len() {
        let arg = argv[i];

        // First positional argument is the subcommand.
        if !arg.starts_with('-') {
            if arg != "status" {
                return None;
            }
            intercept.args = parse_status_args(&argv[i + 1..])?;
            return Some(intercept);
        }

        match consume_global(arg, argv.get(i + 1).copied(), &mut intercept)? {
            Consumed::One => i += 1,
            Consumed::Two => i += 2,
        }
    }

    // Reached end of args with no subcommand (e.g. bare `git`, or `git -p`).
    None
}

#[derive(Debug, Clone, Copy)]
enum Consumed {
    One,
    Two,
}

/// Try to consume a single global option. Returns `None` to forward to real git.
fn consume_global(arg: &str, next: Option<&str>, intercept: &mut Intercept) -> Option<Consumed> {
    // -C handling: -C path | -Cpath | -C=path
    if let Some(rest) = arg.strip_prefix("-C") {
        if rest.is_empty() {
            // Multiple -C is rare and composes oddly across relative paths;
            // just forward in that case rather than getting it subtly wrong.
            if intercept.chdir.is_some() {
                return None;
            }
            let path = next?;
            intercept.chdir = Some(PathBuf::from(path));
            return Some(Consumed::Two);
        }
        if intercept.chdir.is_some() {
            return None;
        }
        let path = rest.strip_prefix('=').unwrap_or(rest);
        intercept.chdir = Some(PathBuf::from(path));
        return Some(Consumed::One);
    }

    // -c handling: -c key=val | -ckey=val. We don't read git config from the
    // shim, but the value still has to be consumed correctly.
    if let Some(rest) = arg.strip_prefix("-c") {
        if rest.is_empty() {
            next?;
            return Some(Consumed::Two);
        }
        return Some(Consumed::One);
    }

    // Long options. Split off any `=value` so we can match on the bare name.
    if let Some(body) = arg.strip_prefix("--") {
        let (name, has_attached) = match body.split_once('=') {
            Some((n, _)) => (n, true),
            None => (body, false),
        };
        return classify_long_global(name, has_attached, next);
    }

    // Short flags without value.
    match arg {
        "-p" | "-P" => Some(Consumed::One),
        _ => None, // unknown short option: forward
    }
}

fn classify_long_global(name: &str, has_attached: bool, next: Option<&str>) -> Option<Consumed> {
    // Safe boolean globals - ignore.
    if matches!(
        name,
        "paginate"
            | "no-pager"
            | "no-optional-locks"
            | "no-lazy-fetch"
            | "no-advice"
            | "literal-pathspecs"
    ) {
        // These don't take values; if the caller wrote `--paginate=foo`, that's
        // malformed for git - forward and let git produce the error.
        return if has_attached { None } else { Some(Consumed::One) };
    }

    // --config-env=name=envvar | --config-env name=envvar -- ignore.
    if name == "config-env" {
        return if has_attached {
            Some(Consumed::One)
        } else {
            next?;
            Some(Consumed::Two)
        };
    }

    // Everything else either changes git semantics in ways we'd have to mirror
    // (--git-dir, --work-tree, --namespace, --exec-path, --super-prefix,
    // --list-cmds, --attr-source, --bare, pathspec globbing flags) or is a
    // terminal action (--help, --version, --html-path, etc.).
    None
}

/// Validate the args after `status`. Returns `None` if any flag is one
/// subspy doesn't support, or if a positional pathspec follows.
fn parse_status_args(args: &[&str]) -> Option<StatusArgs> {
    let mut out = StatusArgs::default();
    let mut i = 0;
    let mut seen_double_dash = false;

    while i < args.len() {
        let arg = args[i];

        if seen_double_dash {
            // Anything after `--` is a pathspec. Subspy doesn't filter by path.
            return None;
        }

        if arg == "--" {
            seen_double_dash = true;
            i += 1;
            continue;
        }

        // Bare positional after `status` -> pathspec, forward.
        if !arg.starts_with('-') {
            return None;
        }

        // --porcelain | --porcelain=N
        if arg == "--porcelain" {
            out.porcelain = Some(PorcelainVersion::V1);
            i += 1;
            continue;
        }
        if let Some(v) = arg.strip_prefix("--porcelain=") {
            out.porcelain = Some(parse_porcelain(v)?);
            i += 1;
            continue;
        }

        if arg == "-z" {
            out.null_terminate = true;
            i += 1;
            continue;
        }

        // --ignore-submodules[=WHEN]
        if arg == "--ignore-submodules" {
            out.ignore_submodules = IgnoreSubmodules::All;
            i += 1;
            continue;
        }
        if let Some(v) = arg.strip_prefix("--ignore-submodules=") {
            out.ignore_submodules = parse_ignore_submodules(v)?;
            i += 1;
            continue;
        }

        // --untracked-files[=MODE] | -u | -uMODE
        // Per git-status(1) the optional MODE defaults to `all`.
        if arg == "--untracked-files" || arg == "-u" {
            out.untracked_files = Some(UntrackedFiles::All);
            i += 1;
            continue;
        }
        if let Some(v) = arg.strip_prefix("--untracked-files=") {
            out.untracked_files = Some(parse_untracked(v)?);
            i += 1;
            continue;
        }
        if let Some(v) = arg.strip_prefix("-u") {
            out.untracked_files = Some(parse_untracked(v)?);
            i += 1;
            continue;
        }

        // --ignored (no =MODE form supported; subspy doesn't expose ignored modes)
        if arg == "--ignored" {
            out.show_ignored = true;
            i += 1;
            continue;
        }

        // --branch | -b: emit `# branch.*` headers in porcelain modes.
        if arg == "--branch" || arg == "-b" {
            out.branch = true;
            i += 1;
            continue;
        }

        // Anything else: forward to real git.
        return None;
    }

    Some(out)
}

fn parse_porcelain(s: &str) -> Option<PorcelainVersion> {
    match s {
        "1" | "v1" => Some(PorcelainVersion::V1),
        "2" | "v2" => Some(PorcelainVersion::V2),
        _ => None,
    }
}

fn parse_ignore_submodules(s: &str) -> Option<IgnoreSubmodules> {
    match s {
        "none" => Some(IgnoreSubmodules::None),
        "untracked" => Some(IgnoreSubmodules::Untracked),
        "dirty" => Some(IgnoreSubmodules::Dirty),
        "all" => Some(IgnoreSubmodules::All),
        _ => None,
    }
}

fn parse_untracked(s: &str) -> Option<UntrackedFiles> {
    match s {
        "normal" => Some(UntrackedFiles::Normal),
        "no" => Some(UntrackedFiles::No),
        "all" => Some(UntrackedFiles::All),
        _ => None,
    }
}

fn run_intercept(intercept: Intercept) -> ExitCode {
    let status = intercept.into_status();
    match status.run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("subspy-git: {err}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(unix)]
fn forward(argv: &[OsString]) -> ExitCode {
    let err = Command::new(REAL_GIT).args(argv).exec();
    eprintln!("subspy-git: failed to exec `{REAL_GIT}`: {err}");
    ExitCode::FAILURE
}

#[cfg(not(unix))]
fn forward(argv: &[OsString]) -> ExitCode {
    match Command::new(REAL_GIT).args(argv).status() {
        Ok(status) => status
            .code()
            .and_then(|c| u8::try_from(c).ok())
            .map_or(ExitCode::FAILURE, ExitCode::from),
        Err(err) => {
            eprintln!("subspy-git: failed to spawn `{REAL_GIT}`: {err}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn os(args: &[&str]) -> Vec<OsString> {
        args.iter().map(|s| OsString::from(*s)).collect()
    }

    fn intercept_with(args: StatusArgs, chdir: Option<&str>) -> Intercept {
        Intercept {
            chdir: chdir.map(PathBuf::from),
            args,
        }
    }

    #[test]
    fn bare_status_intercepts() {
        let got = dispatch(&os(&["status"])).unwrap();
        assert_eq!(got, Intercept::default());
    }

    #[test]
    fn status_porcelain_v2_intercepts() {
        let got = dispatch(&os(&["status", "--porcelain=2"])).unwrap();
        assert_eq!(
            got,
            intercept_with(
                StatusArgs {
                    porcelain: Some(PorcelainVersion::V2),
                    ..Default::default()
                },
                None,
            )
        );
    }

    #[test]
    fn status_porcelain_no_value_defaults_to_v1() {
        let got = dispatch(&os(&["status", "--porcelain"])).unwrap();
        assert_eq!(got.args.porcelain, Some(PorcelainVersion::V1));
    }

    #[test]
    fn status_z_flag() {
        let got = dispatch(&os(&["status", "-z"])).unwrap();
        assert!(got.args.null_terminate);
    }

    #[test]
    fn status_ignore_submodules_dirty() {
        let got = dispatch(&os(&["status", "--ignore-submodules=dirty"])).unwrap();
        assert_eq!(got.args.ignore_submodules, IgnoreSubmodules::Dirty);
    }

    #[test]
    fn status_ignore_submodules_no_value_means_all() {
        let got = dispatch(&os(&["status", "--ignore-submodules"])).unwrap();
        assert_eq!(got.args.ignore_submodules, IgnoreSubmodules::All);
    }

    #[test]
    fn status_untracked_files_no_value_means_all_via_short() {
        let got = dispatch(&os(&["status", "-u"])).unwrap();
        assert_eq!(got.args.untracked_files, Some(UntrackedFiles::All));
    }

    #[test]
    fn status_untracked_files_no_value_means_all_via_long() {
        let got = dispatch(&os(&["status", "--untracked-files"])).unwrap();
        assert_eq!(got.args.untracked_files, Some(UntrackedFiles::All));
    }

    #[test]
    fn status_untracked_files_all_bundled_short() {
        let got = dispatch(&os(&["status", "-uall"])).unwrap();
        assert_eq!(got.args.untracked_files, Some(UntrackedFiles::All));
    }

    #[test]
    fn status_untracked_files_long() {
        let got = dispatch(&os(&["status", "--untracked-files=no"])).unwrap();
        assert_eq!(got.args.untracked_files, Some(UntrackedFiles::No));
    }

    #[test]
    fn status_ignored_flag() {
        let got = dispatch(&os(&["status", "--ignored"])).unwrap();
        assert!(got.args.show_ignored);
    }

    #[test]
    fn dash_capital_c_separate_path() {
        let got = dispatch(&os(&["-C", "/some/path", "status"])).unwrap();
        assert_eq!(got.chdir, Some(PathBuf::from("/some/path")));
    }

    #[test]
    fn dash_capital_c_attached_path() {
        let got = dispatch(&os(&["-C/some/path", "status"])).unwrap();
        assert_eq!(got.chdir, Some(PathBuf::from("/some/path")));
    }

    #[test]
    fn dash_capital_c_equals_path() {
        let got = dispatch(&os(&["-C=/some/path", "status"])).unwrap();
        assert_eq!(got.chdir, Some(PathBuf::from("/some/path")));
    }

    #[test]
    fn multiple_dash_c_forwards() {
        // We don't try to compose multiple -C; just bail.
        assert!(dispatch(&os(&["-C", "/a", "-C", "b", "status"])).is_none());
    }

    #[test]
    fn dash_c_config_separate() {
        let got = dispatch(&os(&["-c", "user.name=Foo", "status"])).unwrap();
        assert_eq!(got, Intercept::default());
    }

    #[test]
    fn dash_c_config_attached() {
        let got = dispatch(&os(&["-cuser.name=Foo", "status"])).unwrap();
        assert_eq!(got, Intercept::default());
    }

    #[test]
    fn safe_paginate_flag_ignored() {
        let got = dispatch(&os(&["--paginate", "status"])).unwrap();
        assert_eq!(got, Intercept::default());
    }

    #[test]
    fn no_optional_locks_ignored() {
        let got = dispatch(&os(&["--no-optional-locks", "status"])).unwrap();
        assert_eq!(got, Intercept::default());
    }

    #[test]
    fn combined_globals_and_status_args() {
        let got = dispatch(&os(&[
            "-C",
            "/repo",
            "-c",
            "core.quotepath=false",
            "status",
            "--porcelain=2",
            "-z",
        ]))
        .unwrap();
        assert_eq!(got.chdir, Some(PathBuf::from("/repo")));
        assert_eq!(got.args.porcelain, Some(PorcelainVersion::V2));
        assert!(got.args.null_terminate);
    }

    #[test]
    fn git_dir_forwards() {
        assert!(dispatch(&os(&["--git-dir=/foo/.git", "status"])).is_none());
    }

    #[test]
    fn work_tree_forwards() {
        assert!(dispatch(&os(&["--work-tree", "/foo", "status"])).is_none());
    }

    #[test]
    fn bare_forwards() {
        assert!(dispatch(&os(&["--bare", "status"])).is_none());
    }

    #[test]
    fn help_forwards() {
        assert!(dispatch(&os(&["--help"])).is_none());
        assert!(dispatch(&os(&["-h"])).is_none());
    }

    #[test]
    fn version_forwards() {
        assert!(dispatch(&os(&["--version"])).is_none());
    }

    #[test]
    fn unknown_subcommand_forwards() {
        assert!(dispatch(&os(&["fetch", "origin"])).is_none());
        assert!(dispatch(&os(&["log", "--oneline"])).is_none());
        assert!(dispatch(&os(&["rev-parse", "HEAD"])).is_none());
    }

    #[test]
    fn empty_argv_forwards() {
        assert!(dispatch(&[]).is_none());
    }

    #[test]
    fn status_with_unknown_flag_forwards() {
        assert!(dispatch(&os(&["status", "--short"])).is_none());
        assert!(dispatch(&os(&["status", "-s"])).is_none());
        assert!(dispatch(&os(&["status", "--ahead-behind"])).is_none());
    }

    #[test]
    fn status_branch_long() {
        let got = dispatch(&os(&["status", "--branch"])).unwrap();
        assert!(got.args.branch);
    }

    #[test]
    fn status_branch_short() {
        let got = dispatch(&os(&["status", "-b"])).unwrap();
        assert!(got.args.branch);
    }

    #[test]
    fn status_branch_default_false() {
        let got = dispatch(&os(&["status"])).unwrap();
        assert!(!got.args.branch);
    }

    #[test]
    fn status_with_pathspec_forwards() {
        assert!(dispatch(&os(&["status", "src/"])).is_none());
        assert!(dispatch(&os(&["status", "--", "src/"])).is_none());
    }

    #[test]
    fn status_with_invalid_porcelain_value_forwards() {
        assert!(dispatch(&os(&["status", "--porcelain=3"])).is_none());
    }

    #[test]
    fn status_with_invalid_untracked_value_forwards() {
        assert!(dispatch(&os(&["status", "-uweird"])).is_none());
    }

    #[test]
    fn config_env_with_attached_value() {
        let got = dispatch(&os(&["--config-env=user.name=GIT_USER", "status"])).unwrap();
        assert_eq!(got, Intercept::default());
    }

    #[test]
    fn config_env_with_separate_value() {
        let got = dispatch(&os(&["--config-env", "user.name=GIT_USER", "status"])).unwrap();
        assert_eq!(got, Intercept::default());
    }

    #[test]
    fn paginate_with_value_forwards() {
        // --paginate doesn't take a value; forward malformed input.
        assert!(dispatch(&os(&["--paginate=foo", "status"])).is_none());
    }

    /// The exact arg sequence `GitExtensions` sends from the commit dialog.
    /// Source: `tests/app/UnitTests/GitCommands.Tests/Git/CommandsTests.cs`
    /// in `gitextensions/gitextensions`.
    #[test]
    fn gitextensions_commit_dialog_invocation() {
        let got = dispatch(&os(&[
            "-c",
            "diff.ignoresubmodules=none",
            "status",
            "--porcelain=2",
            "-z",
            "--untracked-files",
            "--ignore-submodules",
        ]))
        .unwrap();
        assert_eq!(got.chdir, None);
        assert_eq!(got.args.porcelain, Some(PorcelainVersion::V2));
        assert!(got.args.null_terminate);
        assert_eq!(got.args.untracked_files, Some(UntrackedFiles::All));
        assert_eq!(got.args.ignore_submodules, IgnoreSubmodules::All);
    }

    /// `GitExtensions`'s no-locks variant of the commit dialog invocation.
    #[test]
    fn gitextensions_no_locks_invocation() {
        let got = dispatch(&os(&[
            "--no-optional-locks",
            "-c",
            "diff.ignoresubmodules=none",
            "status",
            "--porcelain=2",
            "-z",
            "--untracked-files",
            "--ignore-submodules",
        ]))
        .unwrap();
        assert_eq!(got.args.untracked_files, Some(UntrackedFiles::All));
        assert_eq!(got.args.ignore_submodules, IgnoreSubmodules::All);
    }
}
