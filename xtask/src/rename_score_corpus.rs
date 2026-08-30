use std::{
    fs,
    io::Write as _,
    path::{Path, PathBuf},
    process::Command as ProcessCommand,
};

use crate::{RenameScoreCorpusArgs, XtaskError};

// Clean-room rename-score corpus generation
// -----------------------------------------
//
// This xtask is intended to support a later Git-compatible scoring
// implementation without deriving that implementation from Git's or libgit2's
// source code. The corpus is generated only by observing command-line Git as a
// black box:
//
//   1. Create a fresh repository.
//   2. Commit `old.txt`.
//   3. Replace it with staged `delete old.txt` + `add new.txt`.
//   4. Ask `git diff --cached --raw -M<N>%` what rename status/score it emits.
//
// The output includes the exact old/new bytes as hex plus Git's raw status
// token (`R100`, `R086`, `D`, `A`, etc.). A future implementation should be
// inferred from this input/output data and from public documentation, with a
// separate regression step checking the inferred implementation against Git.
//
// Keep these boundaries sharp:
//
// - Do not port or translate scoring code from Git or libgit2.
// - Do not use comments or private implementation details from those projects
//   as the basis for the scoring rules.
// - It is fine to use Git and libgit2 as executable or library oracles through
//   their public interfaces. This first corpus records Git only because the
//   safe `git2` Rust binding does not currently expose `DiffDelta::similarity`.
// - Generated fixture data and observed scores are facts about program
//   behavior, not source-derived implementation material.
//
// Suggested use:
//
//   cargo xtask rename-score-corpus --output rename_score_corpus.csv
//   cargo xtask rename-score-corpus --threshold 50 --output rename_score_corpus_50.csv
//
// The default threshold is 1% to expose low scores that Git's normal status
// threshold would suppress. Use `--threshold 50` for the status-visible subset.
#[derive(Clone)]
struct RenameScoreCase {
    name: String,
    old: Vec<u8>,
    new: Vec<u8>,
}

struct GitRawObservation {
    raw_statuses: String,
    score: Option<u8>,
}

pub fn run(args: &RenameScoreCorpusArgs) -> Result<(), XtaskError> {
    if args.threshold > 100 {
        return Err(XtaskError::InvalidRenameThreshold);
    }

    let git_version = command_stdout(ProcessCommand::new("git").arg("--version"))?;
    let git_version = git_version.trim();
    let cases = rename_score_cases();

    let mut out = fs::File::create(&args.output)?;
    writeln!(
        out,
        "git_version,threshold,case,old_len,new_len,git_raw_statuses,git_score,old_hex,new_hex,repo_path"
    )?;

    let keep_root = args.keep_repos.then(|| {
        let root =
            std::env::temp_dir().join(format!("subspy-rename-score-corpus-{}", std::process::id()));
        fs::create_dir_all(&root).expect("failed to create keep-repos directory");
        root
    });

    for (idx, case) in cases.iter().enumerate() {
        let repo_owner = CaseRepo::new(keep_root.as_deref(), idx, &case.name)?;
        let observation = observe_git_rename_score(repo_owner.path(), case, args.threshold)?;
        let repo_path = if keep_root.is_some() {
            repo_owner.path().display().to_string()
        } else {
            Default::default()
        };
        writeln!(
            out,
            "{},{},{},{},{},{},{},{},{},{}",
            csv_field(git_version),
            args.threshold,
            csv_field(&case.name),
            case.old.len(),
            case.new.len(),
            csv_field(&observation.raw_statuses),
            observation
                .score
                .map_or_else(String::new, |s| s.to_string()),
            hex(&case.old),
            hex(&case.new),
            csv_field(&repo_path),
        )?;
    }

    println!("wrote {} cases to {}", cases.len(), args.output.display());
    if let Some(root) = keep_root {
        println!("kept repos under {}", root.display());
    }
    Ok(())
}

enum CaseRepo {
    Temp(tempfile::TempDir),
    Kept(PathBuf),
}

impl CaseRepo {
    fn new(keep_root: Option<&Path>, idx: usize, case_name: &str) -> Result<Self, XtaskError> {
        if let Some(root) = keep_root {
            let path = root.join(format!("{idx:03}-{}", sanitize_filename(case_name)));
            fs::create_dir(&path)?;
            Ok(Self::Kept(path))
        } else {
            Ok(Self::Temp(
                tempfile::Builder::new()
                    .prefix("subspy-rename-score-")
                    .tempdir()?,
            ))
        }
    }

    fn path(&self) -> &Path {
        match self {
            Self::Temp(dir) => dir.path(),
            Self::Kept(path) => path,
        }
    }
}

fn observe_git_rename_score(
    repo: &Path,
    case: &RenameScoreCase,
    threshold: u8,
) -> Result<GitRawObservation, XtaskError> {
    run_git(repo, &["init", "-q"])?;
    run_git(repo, &["config", "user.name", "Subspy Corpus"])?;
    run_git(
        repo,
        &["config", "user.email", "subspy-corpus@example.invalid"],
    )?;

    fs::write(repo.join("old.txt"), &case.old)?;
    run_git(repo, &["add", "old.txt"])?;
    run_git(repo, &["commit", "-qm", "base"])?;

    fs::remove_file(repo.join("old.txt"))?;
    fs::write(repo.join("new.txt"), &case.new)?;
    run_git(repo, &["add", "-A"])?;

    let find_renames = format!("-M{threshold}%");
    let raw = command_stdout(ProcessCommand::new("git").current_dir(repo).args([
        "diff",
        "--cached",
        "--raw",
        &find_renames,
        "--",
        "old.txt",
        "new.txt",
    ]))?;
    Ok(parse_git_raw_observation(&raw))
}

fn parse_git_raw_observation(raw: &str) -> GitRawObservation {
    let statuses: Vec<&str> = raw
        .lines()
        .filter_map(|line| line.split_whitespace().nth(4))
        .collect();
    let score = statuses.iter().find_map(|status| {
        status
            .strip_prefix('R')
            .and_then(|digits| digits.parse::<u8>().ok())
    });

    GitRawObservation {
        raw_statuses: statuses.join("+"),
        score,
    }
}

fn run_git(repo: &Path, args: &[&str]) -> Result<(), XtaskError> {
    command_stdout(ProcessCommand::new("git").current_dir(repo).args(args)).map(|_| ())
}

fn command_stdout(cmd: &mut ProcessCommand) -> Result<String, XtaskError> {
    let output = cmd.output()?;
    if !output.status.success() {
        return Err(XtaskError::CommandFailed {
            command: format!("{cmd:?}"),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }
    Ok(String::from_utf8(output.stdout)?)
}

fn rename_score_cases() -> Vec<RenameScoreCase> {
    let mut cases = Vec::new();
    push_case(
        &mut cases,
        "pure_rename",
        numbered_lines("line", 20),
        numbered_lines("line", 20),
    );
    push_case(&mut cases, "empty_to_empty", Vec::new(), Vec::new());
    push_case(
        &mut cases,
        "empty_to_one_line",
        Vec::new(),
        b"one\n".to_vec(),
    );
    push_case(
        &mut cases,
        "one_line_to_empty",
        b"one\n".to_vec(),
        Vec::new(),
    );
    push_case(
        &mut cases,
        "no_final_newline_same",
        b"one".to_vec(),
        b"one".to_vec(),
    );
    push_case(
        &mut cases,
        "no_final_newline_changed",
        b"one".to_vec(),
        b"two".to_vec(),
    );
    push_case(
        &mut cases,
        "long_line_one_byte_edit",
        repeat_byte(b'a', 4096),
        {
            let mut bytes = repeat_byte(b'a', 4096);
            bytes[2048] = b'b';
            bytes
        },
    );
    push_case(
        &mut cases,
        "binary_nul_one_byte_edit",
        binary_bytes(256, 17),
        {
            let mut bytes = binary_bytes(256, 17);
            bytes[100] ^= 0xff;
            bytes
        },
    );

    for changed in 1..=20 {
        let old = numbered_lines("line", 20);
        let mut new = Vec::new();
        for i in 0..20 {
            if i < 20 - changed {
                append_line(&mut new, "line", i);
            } else {
                append_line(&mut new, "changed", i);
            }
        }
        push_case(
            &mut cases,
            &format!("line_change_tail_{changed:02}_of_20"),
            old,
            new,
        );
    }

    for kept in 0..=20 {
        let old = numbered_lines("line", 20);
        let mut new = Vec::new();
        for i in 0..kept {
            append_line(&mut new, "line", i);
        }
        push_case(
            &mut cases,
            &format!("line_keep_prefix_{kept:02}_of_20"),
            old,
            new,
        );
    }

    for inserted in [1usize, 2, 5, 10, 20] {
        let old = numbered_lines("line", 20);
        let mut new = old.clone();
        for i in 0..inserted {
            append_line(&mut new, "inserted", i);
        }
        push_case(
            &mut cases,
            &format!("append_{inserted:02}_lines_to_20"),
            old,
            new,
        );
    }

    for removed in [1usize, 2, 5, 10, 19] {
        let old = numbered_lines("line", 20);
        let mut new = Vec::new();
        for i in 0..20 - removed {
            append_line(&mut new, "line", i);
        }
        push_case(
            &mut cases,
            &format!("remove_{removed:02}_tail_lines_from_20"),
            old,
            new,
        );
    }

    for moved in [1usize, 2, 5, 10] {
        let old = numbered_lines("line", 20);
        let mut new = Vec::new();
        for i in moved..20 {
            append_line(&mut new, "line", i);
        }
        for i in 0..moved {
            append_line(&mut new, "line", i);
        }
        push_case(
            &mut cases,
            &format!("rotate_{moved:02}_lines_of_20"),
            old,
            new,
        );
    }

    push_case(
        &mut cases,
        "repeated_lines_one_removed",
        repeated_lines("same", 20),
        repeated_lines("same", 19),
    );
    push_case(
        &mut cases,
        "repeated_lines_half_changed",
        repeated_lines("same", 20),
        {
            let mut new = repeated_lines("same", 10);
            new.extend(repeated_lines("different", 10));
            new
        },
    );

    cases
}

fn push_case(cases: &mut Vec<RenameScoreCase>, name: &str, old: Vec<u8>, new: Vec<u8>) {
    cases.push(RenameScoreCase {
        name: name.to_string(),
        old,
        new,
    });
}

fn numbered_lines(prefix: &str, count: usize) -> Vec<u8> {
    let mut bytes = Vec::new();
    for i in 0..count {
        append_line(&mut bytes, prefix, i);
    }
    bytes
}

fn append_line(bytes: &mut Vec<u8>, prefix: &str, i: usize) {
    bytes.extend_from_slice(format!("{prefix}-{i:02}\n").as_bytes());
}

fn repeated_lines(text: &str, count: usize) -> Vec<u8> {
    let mut bytes = Vec::new();
    for _ in 0..count {
        bytes.extend_from_slice(text.as_bytes());
        bytes.push(b'\n');
    }
    bytes
}

fn repeat_byte(byte: u8, count: usize) -> Vec<u8> {
    std::iter::repeat_n(byte, count).collect()
}

fn binary_bytes(count: usize, step: u8) -> Vec<u8> {
    (0..count).map(|i| (i as u8).wrapping_mul(step)).collect()
}

fn hex(bytes: &[u8]) -> String {
    const TABLE: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        out.push(TABLE[(byte >> 4) as usize] as char);
        out.push(TABLE[(byte & 0x0f) as usize] as char);
    }
    out
}

fn csv_field(value: &str) -> String {
    if value.contains([',', '"', '\n', '\r']) {
        format!("\"{}\"", value.replace('"', "\"\""))
    } else {
        value.to_string()
    }
}

fn sanitize_filename(value: &str) -> String {
    value
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}
