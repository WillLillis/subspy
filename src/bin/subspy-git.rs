//! Drop-in replacement for `git` that intercepts `git status` and routes it
//! through subspy. Every other git invocation is forwarded to git unchanged.
//!
//! Designed to be configured as the "Path to git" in tools like
//! `GitExtensions`, allowing subspy's accelerated status response while the
//! rest of the tool's git interactions are unaffected.

use std::{
    env,
    ffi::{OsStr, OsString},
    iter::Peekable,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

use subspy::{
    cli::Status,
    entry::{INTERNAL_FLAG, subspy_entry},
    status::{IgnoreSubmodules, PorcelainVersion, UntrackedFiles},
};

fn main() -> ExitCode {
    let mut args = env::args_os();
    let _ = args.next();
    let mut rest = args.peekable();

    // spawn_daemon prepends the sentinel so the shim hands off to subspy's
    // CLI no matter which binary `current_exe()` resolved to.
    if rest.peek().is_some_and(|arg| arg == INTERNAL_FLAG) {
        return subspy_entry(env::args_os());
    }

    // If the command is a status request that subspy can service, intercept it.
    #[expect(clippy::option_if_let_else, reason = "comment readability")]
    if let Some(intercept) = dispatch(rest) {
        shim_entry(intercept.into())
    } else {
        // Otherwise forward the command to git
        forward_entry(env::args_os().skip(1))
    }
}

/// Parsed result of an intercepted `git status` invocation.
#[derive(Debug, Default, PartialEq, Eq)]
struct Intercept {
    chdir: Option<PathBuf>,
    /// `-c core.quotepath=<bool>` if seen, else `None` (use git's default).
    quote_path: Option<bool>,
    args: StatusArgs,
}

/// Mirrors the subset of `git status` flags subspy can serve. Kept separate
/// from `cli::Status` so it stays comparable in tests and never leaks
/// subspy-only flags into the shim's surface.
#[derive(Debug, Default, PartialEq, Eq)]
struct StatusArgs {
    format: Option<FormatChoice>,
    null_terminate: bool,
    ignore_submodules: IgnoreSubmodules,
    untracked_files: Option<UntrackedFiles>,
    show_ignored: bool,
    branch: bool,
    /// `--ahead-behind` / `--no-ahead-behind`. `None` = git's default (on);
    /// only affects formats that emit upstream ahead/behind info.
    ahead_behind: Option<bool>,
}

/// User's explicit choice of `git status` output format. `None` in
/// `StatusArgs::format` means the user didn't pass any format flag, in
/// which case we render the default (long). Once set, a second
/// format-affecting flag is treated as a conflict and dispatch falls
/// back to forwarding so real git can emit its native error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormatChoice {
    Long,
    Short,
    Porcelain(PorcelainVersion),
}

impl From<Intercept> for Status {
    fn from(value: Intercept) -> Self {
        let (porcelain, short) = match value.args.format {
            Some(FormatChoice::Short) => (None, true),
            Some(FormatChoice::Porcelain(v)) => (Some(v), false),
            // Long and the absent case both map to the default long renderer.
            Some(FormatChoice::Long) | None => (None, false),
        };
        // `cli::Status` exposes both `--ahead-behind` and `--no-ahead-behind`
        // and reconciles them in `Status::run`. Mirror that representation
        // here, defaulting both off when the shim didn't see either form.
        let (ahead_behind, no_ahead_behind) = match value.args.ahead_behind {
            Some(true) => (true, false),
            Some(false) => (false, true),
            None => (false, false),
        };
        Self {
            dir: value.chdir,
            log_level: None,
            no_server: false,
            porcelain,
            short,
            null_terminate: value.args.null_terminate,
            ignore_submodules: value.args.ignore_submodules,
            untracked_files: value.args.untracked_files,
            ignored: value.args.show_ignored,
            branch: value.args.branch,
            ahead_behind,
            no_ahead_behind,
            // Set by parsing `-c core.quotepath=<bool>`; defaults to true
            // (git's default).
            quote_path: value.quote_path.unwrap_or(true),
        }
    }
}

/// Walk argv looking for an interceptable `status` invocation.
///
/// Returns `Some(intercept)` if every global option was one we know is
/// safe to honor or ignore, the subcommand was `status`, and every status
/// flag was one subspy supports. Returns `None` for anything else; the
/// caller should re-fetch argv from `env::args_os()` and forward to real
/// git (dispatch may have partially drained `rest` on its way to `None`).
fn dispatch<I>(mut rest: Peekable<I>) -> Option<Intercept>
where
    I: Iterator<Item = OsString>,
{
    let mut intercept = Intercept::default();

    while let Some(os_arg) = rest.next() {
        match classify_global(&os_arg, rest.peek(), &mut intercept).ok()? {
            GlobalAction::Skip => {}
            GlobalAction::SkipWithValue => {
                rest.next()?;
            }
            GlobalAction::StatusFollows => {
                intercept.args = parse_status_args(&mut rest)?;
                return Some(intercept);
            }
        }
    }
    // Reached end of args with no subcommand (e.g. bare `git`, or `git -p`).
    None
}

/// Marker returned as `Err` from parsing helpers when an arg can't be
/// faithfully honored locally. Dispatch unwinds and the original argv is
/// forwarded to real `git`.
struct Forward;

/// What dispatch should do after seeing a single arg in the global-option
/// stream. `Skip` and `SkipWithValue` mean dispatch keeps walking; the
/// latter signals that the next arg is the value (e.g. `-C <path>`).
enum GlobalAction {
    Skip,
    SkipWithValue,
    StatusFollows,
}

/// Classifies a single arg in the pre-subcommand stream. Peeks the next
/// arg only via `&str` so the caller still owns the iterator and can
/// decide whether to advance.
fn classify_global(
    os_arg: &OsStr,
    next: Option<&OsString>,
    intercept: &mut Intercept,
) -> Result<GlobalAction, Forward> {
    let arg = os_arg.to_str().ok_or(Forward)?;
    if !arg.starts_with('-') {
        return if arg == "status" {
            Ok(GlobalAction::StatusFollows)
        } else {
            Err(Forward)
        };
    }
    let next_str = next.and_then(|o| o.to_str());
    consume_global(arg, next_str, intercept)
}

/// Consume a single global option. Returns the action dispatch should
/// take, or `Err(Forward)` for anything that should fall through to
/// real git.
fn consume_global(
    arg: &str,
    next: Option<&str>,
    intercept: &mut Intercept,
) -> Result<GlobalAction, Forward> {
    // -C handling: -C path | -Cpath | -C=path
    if let Some(rest) = arg.strip_prefix("-C") {
        if rest.is_empty() {
            // Multiple -C is rare and composes oddly across relative paths;
            // just forward in that case rather than getting it subtly wrong.
            if intercept.chdir.is_some() {
                return Err(Forward);
            }
            let path = next.ok_or(Forward)?;
            intercept.chdir = Some(PathBuf::from(path));
            return Ok(GlobalAction::SkipWithValue);
        }
        if intercept.chdir.is_some() {
            return Err(Forward);
        }
        let path = rest.strip_prefix('=').unwrap_or(rest);
        intercept.chdir = Some(PathBuf::from(path));
        return Ok(GlobalAction::Skip);
    }

    // -c handling: -c key=val | -ckey=val. Most `-c` settings the shim
    // doesn't care about (it doesn't drive git's config system), but
    // `core.quotepath` affects path output, so we extract it and apply
    // it during rendering.
    if let Some(rest) = arg.strip_prefix("-c") {
        if rest.is_empty() {
            let value = next.ok_or(Forward)?;
            apply_minus_c(value, intercept);
            return Ok(GlobalAction::SkipWithValue);
        }
        apply_minus_c(rest, intercept);
        return Ok(GlobalAction::Skip);
    }

    // Long options. Split off any `=value` so we can match on the bare name.
    if let Some(body) = arg.strip_prefix("--") {
        let (name, has_attached) = body
            .split_once('=')
            .map_or((body, false), |(n, _)| (n, true));
        return classify_long_global(name, has_attached, next);
    }

    // Short flags without value.
    match arg {
        "-p" | "-P" => Ok(GlobalAction::Skip),
        _ => Err(Forward), // unknown short option: forward
    }
}

/// Inspects a `-c key=value` payload for settings the shim needs to
/// honor at render time. Currently only `core.quotepath` is plumbed
/// through; other config values are ignored at the shim level (they go
/// to git unchanged when we forward).
fn apply_minus_c(payload: &str, intercept: &mut Intercept) {
    let Some((key, value)) = payload.split_once('=') else {
        return;
    };
    if key.eq_ignore_ascii_case("core.quotepath") {
        intercept.quote_path = parse_git_bool(value);
    }
}

/// Parses a git-style boolean literal (case-insensitive `true`/`false`,
/// `on`/`off`, `yes`/`no`, or `1`/`0`). Returns `None` for anything
/// unrecognized, leaving the default behavior in place.
fn parse_git_bool(s: &str) -> Option<bool> {
    match s.to_ascii_lowercase().as_str() {
        "true" | "on" | "yes" | "1" => Some(true),
        "false" | "off" | "no" | "0" | "" => Some(false),
        _ => None,
    }
}

fn classify_long_global(
    name: &str,
    has_attached: bool,
    next: Option<&str>,
) -> Result<GlobalAction, Forward> {
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
        // If the caller wrote `--paginate=foo` (malformed), forward and let git
        // produce the error.
        return if has_attached {
            Err(Forward)
        } else {
            Ok(GlobalAction::Skip)
        };
    }

    // --config-env=name=envvar | --config-env name=envvar -- ignore.
    if name == "config-env" {
        return if has_attached {
            Ok(GlobalAction::Skip)
        } else if next.is_some() {
            Ok(GlobalAction::SkipWithValue)
        } else {
            Err(Forward)
        };
    }

    // Everything else either changes git semantics in ways we'd have to mirror
    // (--git-dir, --work-tree, --namespace, --exec-path, --super-prefix,
    // --list-cmds, --attr-source, --bare, pathspec globbing flags) or is a
    // terminal action (--help, --version, --html-path, etc.).
    Err(Forward)
}

/// Validate the args after `status`. Returns `None` if any flag is one
/// subspy doesn't support, or if a positional pathspec follows.
fn parse_status_args<I>(rest: &mut I) -> Option<StatusArgs>
where
    I: Iterator<Item = OsString>,
{
    let mut out = StatusArgs::default();
    let mut seen_double_dash = false;

    for os_arg in rest.by_ref() {
        let arg = os_arg.to_str()?;
        classify_status_arg(arg, &mut out, &mut seen_double_dash).ok()?;
    }
    Some(out)
}

/// Records the chosen output format. Repeated assignments of the same
/// format are idempotent (matches git: `git status --long --long` is
/// accepted). A different choice is a conflict; we forward so real git
/// emits its native error.
fn set_format(out: &mut StatusArgs, choice: FormatChoice) -> Result<(), Forward> {
    if let Some(existing) = out.format {
        if existing == choice {
            Ok(())
        } else {
            Err(Forward)
        }
    } else {
        out.format = Some(choice);
        Ok(())
    }
}

/// Per-arg classifier for status flags. `Ok(())` if the arg was
/// recognized (and `out` / `seen_double_dash` updated). `Err(Forward)`
/// for anything that should make dispatch fall back to forwarding.
fn classify_status_arg(
    arg: &str,
    out: &mut StatusArgs,
    seen_double_dash: &mut bool,
) -> Result<(), Forward> {
    // Anything after `--` is a pathspec. Subspy doesn't filter by path.
    if *seen_double_dash {
        return Err(Forward);
    }
    if arg == "--" {
        *seen_double_dash = true;
        return Ok(());
    }
    // Bare positional after `status` -> pathspec, forward.
    if !arg.starts_with('-') {
        return Err(Forward);
    }

    // Format flags. `set_format` returns `Err(Forward)` on a conflict
    // (e.g. `--short --long`); dispatch falls through and real git emits
    // its native error.
    if arg == "--porcelain" {
        return set_format(out, FormatChoice::Porcelain(PorcelainVersion::V1));
    }
    if let Some(v) = arg.strip_prefix("--porcelain=") {
        let version = parse_porcelain(v).ok_or(Forward)?;
        return set_format(out, FormatChoice::Porcelain(version));
    }
    if arg == "-s" || arg == "--short" {
        return set_format(out, FormatChoice::Short);
    }
    if arg == "--long" {
        return set_format(out, FormatChoice::Long);
    }

    if arg == "-z" {
        out.null_terminate = true;
        return Ok(());
    }

    // --ignore-submodules[=WHEN]
    if arg == "--ignore-submodules" {
        out.ignore_submodules = IgnoreSubmodules::All;
        return Ok(());
    }
    if let Some(v) = arg.strip_prefix("--ignore-submodules=") {
        out.ignore_submodules = parse_ignore_submodules(v).ok_or(Forward)?;
        return Ok(());
    }

    // --untracked-files[=MODE] | -u | -uMODE
    // Per git-status(1) the optional MODE defaults to `all`.
    if arg == "--untracked-files" || arg == "-u" {
        out.untracked_files = Some(UntrackedFiles::All);
        return Ok(());
    }
    if let Some(v) = arg
        .strip_prefix("--untracked-files=")
        .or_else(|| arg.strip_prefix("-u"))
    {
        out.untracked_files = Some(parse_untracked(v).ok_or(Forward)?);
        return Ok(());
    }

    // --ignored (no =MODE form supported; subspy doesn't expose ignored modes)
    if arg == "--ignored" {
        out.show_ignored = true;
        return Ok(());
    }

    // --branch | -b: emit `# branch.*` headers in porcelain modes.
    if arg == "--branch" || arg == "-b" {
        out.branch = true;
        return Ok(());
    }

    // --ahead-behind / --no-ahead-behind: detailed upstream divergence
    // counts. The two flags conflict; the second one signals Forward
    // so real git's error path runs.
    if arg == "--ahead-behind" {
        if out.ahead_behind == Some(false) {
            return Err(Forward);
        }
        out.ahead_behind = Some(true);
        return Ok(());
    }
    if arg == "--no-ahead-behind" {
        if out.ahead_behind == Some(true) {
            return Err(Forward);
        }
        out.ahead_behind = Some(false);
        return Ok(());
    }

    // Anything else: forward to real git.
    Err(Forward)
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

fn shim_entry(status_args: Status) -> ExitCode {
    match status_args.run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("subspy-git: {err}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(unix)]
fn forward_entry<I, S>(argv: I) -> ExitCode
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    use std::os::unix::process::CommandExt as _;
    let err = Command::new(git_target()).args(argv).exec();
    eprintln!("subspy-git: failed to exec `git`: {err}");
    ExitCode::FAILURE
}

#[cfg(windows)]
fn forward_entry<I, S>(argv: I) -> ExitCode
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    use std::io::IsTerminal as _;
    let mut cmd = Command::new(git_target());
    cmd.args(argv);
    if !std::io::stdout().is_terminal() {
        subspy::proc::configure_hidden_console(&mut cmd);
    }
    match cmd.status() {
        Ok(status) => status
            .code()
            .and_then(|c| u8::try_from(c).ok())
            .map_or(ExitCode::FAILURE, ExitCode::from),
        Err(err) => {
            eprintln!("subspy-git: failed to spawn `git`: {err}");
            ExitCode::FAILURE
        }
    }
}

/// Resolves the binary to invoke for forwarded git commands. Normally this
/// is just `"git"`, letting the OS do PATH resolution. However, when the shim
/// itself is renamed to `git`/`git.exe` (as `Sourcetree` requires), the OS will
/// resolve `"git"` back to us.
///
/// To avoid infinite recursion, walk `PATH` ourselves and pick the first match
/// that isn't us.
fn git_target() -> OsString {
    let me = env::current_exe().ok();
    let is_named_git = me
        .as_ref()
        .and_then(|p| p.file_stem())
        .and_then(|n| n.to_str())
        .is_some_and(|n| n.eq_ignore_ascii_case("git"));
    if !is_named_git {
        return "git".into();
    }
    find_real_git(me.as_deref()).map_or_else(|| "git".into(), OsString::from)
}

#[cfg(unix)]
const GIT_EXE: &str = "git";
#[cfg(windows)]
const GIT_EXE: &str = "git.exe";

/// Walks `PATH` for a `git`/`git.exe` whose canonical path differs from
/// `me`. Standard installations of Git on Windows use `git.exe`. Non-standard
/// wrappers (`.cmd`, `.bat`, ...) aren't supported until proven otherwise.
fn find_real_git(me: Option<&Path>) -> Option<PathBuf> {
    let me_canonical = me.and_then(|p| std::fs::canonicalize(p).ok());
    let path_var = env::var_os("PATH")?;
    for dir in env::split_paths(&path_var) {
        let candidate = dir.join(GIT_EXE);
        if !candidate.is_file() {
            continue;
        }
        let Ok(cand_canonical) = std::fs::canonicalize(&candidate) else {
            continue;
        };
        if Some(&cand_canonical) != me_canonical.as_ref() {
            return Some(candidate);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::{dispatch as dispatch_iter, *};

    /// Test-only adapter that materializes args into a peekable iterator
    /// so existing tests can keep passing `&[OsString]`.
    fn dispatch(argv: &[OsString]) -> Option<Intercept> {
        dispatch_iter(argv.iter().cloned().peekable())
    }

    fn os(args: &[&str]) -> Vec<OsString> {
        args.iter().map(|s| OsString::from(*s)).collect()
    }

    fn intercept_with(args: StatusArgs, chdir: Option<&str>) -> Intercept {
        Intercept {
            chdir: chdir.map(PathBuf::from),
            quote_path: None,
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
                    format: Some(FormatChoice::Porcelain(PorcelainVersion::V2)),
                    ..Default::default()
                },
                None,
            )
        );
    }

    #[test]
    fn status_porcelain_no_value_defaults_to_v1() {
        let got = dispatch(&os(&["status", "--porcelain"])).unwrap();
        assert_eq!(
            got.args.format,
            Some(FormatChoice::Porcelain(PorcelainVersion::V1))
        );
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
        assert_eq!(
            got.args.format,
            Some(FormatChoice::Porcelain(PorcelainVersion::V2))
        );
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
        assert!(dispatch(&os(&["status", "--column"])).is_none());
    }

    #[test]
    fn status_ahead_behind_intercepts() {
        let got = dispatch(&os(&["status", "--ahead-behind"])).unwrap();
        assert_eq!(got.args.ahead_behind, Some(true));
    }

    #[test]
    fn status_no_ahead_behind_intercepts() {
        let got = dispatch(&os(&["status", "--no-ahead-behind"])).unwrap();
        assert_eq!(got.args.ahead_behind, Some(false));
    }

    #[test]
    fn status_ahead_behind_conflict_forwards() {
        // Conflicting forms in either order fall through to real git so
        // its error path runs.
        assert!(dispatch(&os(&["status", "--ahead-behind", "--no-ahead-behind"])).is_none());
        assert!(dispatch(&os(&["status", "--no-ahead-behind", "--ahead-behind"])).is_none());
    }

    #[test]
    fn sourcetree_status_invocation_intercepts() {
        // The actual command Sourcetree issues on every poll.
        let got = dispatch(&os(&[
            "-c",
            "diff.mnemonicprefix=false",
            "-c",
            "core.quotepath=false",
            "--no-optional-locks",
            "status",
            "--porcelain",
            "--ignore-submodules=dirty",
            "--untracked-files=all",
            "--no-ahead-behind",
        ]))
        .unwrap();
        assert_eq!(
            got.args.format,
            Some(FormatChoice::Porcelain(PorcelainVersion::V1))
        );
        assert_eq!(got.args.ignore_submodules, IgnoreSubmodules::Dirty);
        assert_eq!(got.args.untracked_files, Some(UntrackedFiles::All));
        assert_eq!(got.args.ahead_behind, Some(false));
        assert_eq!(got.quote_path, Some(false));
    }

    #[test]
    fn core_quotepath_attached_form() {
        // `-c core.quotepath=true` (separate value) and `-ccore.quotepath=true`
        // (attached) should both be recognized.
        let got = dispatch(&os(&["-ccore.quotepath=true", "status"])).unwrap();
        assert_eq!(got.quote_path, Some(true));
    }

    #[test]
    fn core_quotepath_separate_form() {
        let got = dispatch(&os(&["-c", "core.quotepath=true", "status"])).unwrap();
        assert_eq!(got.quote_path, Some(true));
    }

    #[test]
    fn other_dash_c_settings_pass_through() {
        // We don't care about `diff.mnemonicprefix`; just consume it.
        let got = dispatch(&os(&["-c", "diff.mnemonicprefix=false", "status"])).unwrap();
        assert_eq!(got.quote_path, None);
    }

    #[test]
    fn status_short_intercepts() {
        for flag in &["-s", "--short"] {
            let got = dispatch(&os(&["status", flag])).unwrap();
            assert_eq!(
                got,
                intercept_with(
                    StatusArgs {
                        format: Some(FormatChoice::Short),
                        ..Default::default()
                    },
                    None,
                )
            );
        }
    }

    #[test]
    fn status_long_intercepts() {
        let got = dispatch(&os(&["status", "--long"])).unwrap();
        assert_eq!(got.args.format, Some(FormatChoice::Long));
    }

    #[test]
    fn status_long_intercept_runs_default_long_renderer() {
        // `--long` is the default; converting through `Status` should
        // emit neither `--short` nor `--porcelain`.
        let intercept = dispatch(&os(&["status", "--long"])).unwrap();
        let status: Status = intercept.into();
        assert!(!status.short);
        assert!(status.porcelain.is_none());
    }

    #[test]
    fn status_short_then_long_forwards() {
        assert!(dispatch(&os(&["status", "--short", "--long"])).is_none());
        assert!(dispatch(&os(&["status", "-s", "--long"])).is_none());
    }

    #[test]
    fn status_long_then_short_forwards() {
        assert!(dispatch(&os(&["status", "--long", "--short"])).is_none());
        assert!(dispatch(&os(&["status", "--long", "-s"])).is_none());
    }

    #[test]
    fn status_porcelain_then_long_forwards() {
        assert!(dispatch(&os(&["status", "--porcelain", "--long"])).is_none());
        assert!(dispatch(&os(&["status", "--porcelain=2", "--long"])).is_none());
    }

    #[test]
    fn status_long_then_porcelain_forwards() {
        assert!(dispatch(&os(&["status", "--long", "--porcelain"])).is_none());
        assert!(dispatch(&os(&["status", "--long", "--porcelain=2"])).is_none());
    }

    #[test]
    fn status_short_then_porcelain_forwards() {
        // Pre-existing conflict that now also falls through to forwarding.
        assert!(dispatch(&os(&["status", "--short", "--porcelain"])).is_none());
    }

    #[test]
    fn status_porcelain_then_short_forwards() {
        assert!(dispatch(&os(&["status", "--porcelain=2", "--short"])).is_none());
    }

    #[test]
    fn status_repeated_same_format_intercepts() {
        // `git status --long --long` is accepted by git (idempotent), and
        // we mirror that.
        let got = dispatch(&os(&["status", "--long", "--long"])).unwrap();
        assert_eq!(got.args.format, Some(FormatChoice::Long));

        let got = dispatch(&os(&["status", "--short", "--short"])).unwrap();
        assert_eq!(got.args.format, Some(FormatChoice::Short));

        let got = dispatch(&os(&["status", "--porcelain", "--porcelain"])).unwrap();
        assert_eq!(
            got.args.format,
            Some(FormatChoice::Porcelain(PorcelainVersion::V1))
        );
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
        assert_eq!(
            got.args.format,
            Some(FormatChoice::Porcelain(PorcelainVersion::V2))
        );
        assert!(got.args.null_terminate);
        assert_eq!(got.args.untracked_files, Some(UntrackedFiles::All));
        assert_eq!(got.args.ignore_submodules, IgnoreSubmodules::All);
    }

    /// The sentinel is routed by `main()` before `dispatch()` ever sees it.
    /// If a refactor ever lets it through, the git-intercept layer should
    /// still refuse to claim it instead of silently forwarding nonsense.
    #[test]
    fn internal_flag_is_not_intercepted_by_dispatch() {
        assert!(dispatch(&os(&[INTERNAL_FLAG, "start", "/path", "--foreground"])).is_none());
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
