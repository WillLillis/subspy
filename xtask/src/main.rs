use std::{
    collections::{HashMap, HashSet},
    fmt,
    time::Duration,
};

use clap::Parser;
use git2::Repository;
use rand::{Rng, SeedableRng, rngs::StdRng, seq::IndexedRandom};
use subspy::StatusSummary;
use subspy::connection::client::request_debug;
use testutil::HarnessBuilder;

/// Fuzz the subspy watch server by performing random git operations and
/// verifying that the server's status matches ground truth after each step.
#[derive(Parser)]
struct FuzzArgs {
    /// Random seed for reproducibility. Omit for a random seed.
    #[arg(long)]
    seed: Option<u64>,

    /// Number of random operations to perform.
    #[arg(long, default_value_t = u32::MAX)]
    steps: u32,

    /// Number of initial submodules.
    #[arg(long, default_value_t = 3)]
    submodules: usize,

    /// Maximum number of operations to batch in rapid-fire mode.
    #[arg(long, default_value_t = 5)]
    max_burst: u32,

    /// Polling interval in milliseconds when waiting for server to settle.
    #[arg(long, default_value_t = 25)]
    poll_ms: u64,
}

/// Operations to be performed by the fuzzer
#[derive(Debug, Clone)]
enum Op {
    WriteNewFile {
        submodule: String,
        file: String,
    },
    OverwriteTrackedFile {
        submodule: String,
    },
    DeleteFile {
        submodule: String,
        file: String,
    },
    StageFile {
        submodule: String,
        file: String,
    },
    UnstageFile {
        submodule: String,
        file: String,
    },
    CommitInSubmodule {
        submodule: String,
    },
    StageSubmoduleGitlink {
        submodule: String,
    },
    CommitInParent,
    /// Perform N operations without waiting for the server between them.
    RapidFire {
        ops: Vec<Op>,
    },
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WriteNewFile { submodule, file } => {
                write!(f, "write new file {file} in {submodule}")
            }
            Self::OverwriteTrackedFile { submodule } => {
                write!(f, "overwrite README.md in {submodule}")
            }
            Self::DeleteFile { submodule, file } => {
                write!(f, "delete {file} in {submodule}")
            }
            Self::StageFile { submodule, file } => {
                write!(f, "stage {file} in {submodule}")
            }
            Self::UnstageFile { submodule, file } => {
                write!(f, "unstage {file} in {submodule}")
            }
            Self::CommitInSubmodule { submodule } => {
                write!(f, "commit in {submodule}")
            }
            Self::StageSubmoduleGitlink { submodule } => {
                write!(f, "stage gitlink for {submodule}")
            }
            Self::CommitInParent => write!(f, "commit in parent"),
            Self::RapidFire { ops } => {
                write!(f, "rapid-fire [")?;
                for (i, op) in ops.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{op}")?;
                }
                write!(f, "]")
            }
        }
    }
}

/// Operation kinds corresponding to `Op` (for weighted selection)
#[derive(Clone, Copy)]
enum OpKind {
    WriteNewFile,
    OverwriteTrackedFile,
    DeleteFile,
    StageFile,
    UnstageFile,
    CommitInSubmodule,
    StageSubmoduleGitlink,
    CommitInParent,
    RapidFire,
}

struct FuzzerState {
    rng: StdRng,
    harness: testutil::TestHarness,
    /// submodule name -> set of untracked files we created
    untracked_files: HashMap<String, HashSet<String>>,
    /// submodule name -> set of files we staged
    staged_files: HashMap<String, HashSet<String>>,
    /// submodules that have uncommitted changes (anything to `git add -A && git commit`)
    submodules_with_changes: HashSet<String>,
    /// submodules whose gitlink has been staged in the parent
    staged_gitlinks: HashSet<String>,
    /// counter for generating unique filenames
    file_counter: u32,
    /// operation log for replay on failure
    history: Vec<Op>,
    /// polling interval
    poll_interval: Duration,
    /// max burst size for rapid-fire
    max_burst: u32,
}

impl FuzzerState {
    fn new(args: &FuzzArgs, seed: u64) -> Self {
        let rng = StdRng::seed_from_u64(seed);
        let harness = HarnessBuilder::new().submodules(args.submodules).build();

        let submod_names: Vec<String> = harness.submodule_names().map(String::from).collect();
        let untracked_files: HashMap<String, HashSet<String>> = submod_names
            .iter()
            .map(|name| (name.clone(), HashSet::new()))
            .collect();
        let staged_files: HashMap<String, HashSet<String>> = submod_names
            .iter()
            .map(|name| (name.clone(), HashSet::new()))
            .collect();

        Self {
            rng,
            harness,
            untracked_files,
            staged_files,
            submodules_with_changes: HashSet::new(),
            staged_gitlinks: HashSet::new(),
            file_counter: 0,
            history: Vec::new(),
            poll_interval: Duration::from_millis(args.poll_ms),
            max_burst: args.max_burst,
        }
    }

    fn submodule_names(&self) -> Vec<String> {
        self.untracked_files.keys().cloned().collect()
    }

    fn pick_submodule(&mut self) -> String {
        let names = self.submodule_names();
        names.choose(&mut self.rng).unwrap().clone()
    }

    fn next_filename(&mut self) -> String {
        self.file_counter += 1;
        format!("fuzz_{}.txt", self.file_counter)
    }

    /// Select a weighted-random operation kind that is valid given current state.
    fn pick_op_kind(&mut self) -> OpKind {
        let mut candidates: Vec<(u32, OpKind)> = vec![
            (10, OpKind::WriteNewFile),
            (6, OpKind::OverwriteTrackedFile),
        ];

        let has_untracked = self.untracked_files.values().any(|files| !files.is_empty());
        if has_untracked {
            candidates.push((4, OpKind::DeleteFile));
            candidates.push((5, OpKind::StageFile));
        }

        if self.staged_files.values().any(|files| !files.is_empty()) {
            candidates.push((3, OpKind::UnstageFile));
        }

        if !self.submodules_with_changes.is_empty() {
            candidates.push((5, OpKind::CommitInSubmodule));
        }

        // Always allow — gitlink may or may not actually be dirty
        candidates.push((3, OpKind::StageSubmoduleGitlink));

        if !self.staged_gitlinks.is_empty() {
            candidates.push((2, OpKind::CommitInParent));
        }

        if self.max_burst >= 2 {
            candidates.push((3, OpKind::RapidFire));
        }

        let total_weight: u32 = candidates.iter().map(|(w, _)| w).sum();
        let mut roll = self.rng.random_range(0..total_weight);
        for (weight, kind) in &candidates {
            if roll < *weight {
                return *kind;
            }
            roll -= weight;
        }
        unreachable!()
    }

    /// Build a concrete `Op` from a selected `OpKind`, consuming RNG for parameters.
    fn build_op(&mut self, kind: OpKind) -> Op {
        match kind {
            OpKind::WriteNewFile => {
                let submodule = self.pick_submodule();
                let file = self.next_filename();
                Op::WriteNewFile { submodule, file }
            }
            OpKind::OverwriteTrackedFile => {
                let submodule = self.pick_submodule();
                Op::OverwriteTrackedFile { submodule }
            }
            OpKind::DeleteFile => {
                let eligible: Vec<String> = self
                    .untracked_files
                    .iter()
                    .filter(|(_, files)| !files.is_empty())
                    .map(|(name, _)| name.clone())
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                let files: Vec<String> = self.untracked_files[&submodule].iter().cloned().collect();
                let file = files.choose(&mut self.rng).unwrap().clone();
                Op::DeleteFile { submodule, file }
            }
            OpKind::StageFile => {
                let eligible: Vec<String> = self
                    .untracked_files
                    .iter()
                    .filter(|(_, files)| !files.is_empty())
                    .map(|(name, _)| name.clone())
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                let files: Vec<String> = self.untracked_files[&submodule].iter().cloned().collect();
                let file = files.choose(&mut self.rng).unwrap().clone();
                Op::StageFile { submodule, file }
            }
            OpKind::UnstageFile => {
                let eligible: Vec<String> = self
                    .staged_files
                    .iter()
                    .filter(|(_, files)| !files.is_empty())
                    .map(|(name, _)| name.clone())
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                let files: Vec<String> = self.staged_files[&submodule].iter().cloned().collect();
                let file = files.choose(&mut self.rng).unwrap().clone();
                Op::UnstageFile { submodule, file }
            }
            OpKind::CommitInSubmodule => {
                let eligible: Vec<String> = self.submodules_with_changes.iter().cloned().collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::CommitInSubmodule { submodule }
            }
            OpKind::StageSubmoduleGitlink => {
                let submodule = self.pick_submodule();
                Op::StageSubmoduleGitlink { submodule }
            }
            OpKind::CommitInParent => Op::CommitInParent,
            OpKind::RapidFire => unreachable!("RapidFire is handled by step()"),
        }
    }

    /// Generate, execute, and return one fuzzer step.
    ///
    /// For rapid-fire, sub-ops are generated and executed one at a time so each
    /// sub-op sees the state left by the previous one (fixing the stale-state bug
    /// where later sub-ops could reference files deleted by earlier ones).
    fn step(&mut self) -> Op {
        let kind = self.pick_op_kind();
        match kind {
            OpKind::RapidFire => {
                let n = self.rng.random_range(2..=self.max_burst);
                let saved = self.max_burst;
                self.max_burst = 0;
                let mut ops = Vec::with_capacity(n as usize);
                for _ in 0..n {
                    let sub_kind = self.pick_op_kind();
                    let sub_op = self.build_op(sub_kind);
                    self.execute_op(&sub_op);
                    ops.push(sub_op);
                }
                self.max_burst = saved;
                Op::RapidFire { ops }
            }
            _ => {
                let op = self.build_op(kind);
                self.execute_op(&op);
                op
            }
        }
    }

    /// Execute a single operation against the harness, updating internal state.
    fn execute_op(&mut self, op: &Op) {
        match op {
            Op::WriteNewFile { submodule, file } => {
                let content = format!("fuzz content {}\n", self.file_counter);
                self.harness.write_file(submodule, file, &content);
                self.untracked_files
                    .get_mut(submodule)
                    .unwrap()
                    .insert(file.clone());
                self.submodules_with_changes.insert(submodule.clone());
            }
            Op::OverwriteTrackedFile { submodule } => {
                let content = format!("modified {}\n", self.file_counter);
                self.harness.write_file(submodule, "README.md", &content);
                self.submodules_with_changes.insert(submodule.clone());
            }
            Op::DeleteFile { submodule, file } => {
                self.harness.remove_file(submodule, file);
                self.untracked_files
                    .get_mut(submodule)
                    .unwrap()
                    .remove(file);
            }
            Op::StageFile { submodule, file } => {
                self.harness.stage_file(submodule, file);
                self.untracked_files
                    .get_mut(submodule)
                    .unwrap()
                    .remove(file);
                self.staged_files
                    .get_mut(submodule)
                    .unwrap()
                    .insert(file.clone());
                self.submodules_with_changes.insert(submodule.clone());
            }
            Op::UnstageFile { submodule, file } => {
                self.harness.unstage_file(submodule, file);
                self.staged_files.get_mut(submodule).unwrap().remove(file);
                self.untracked_files
                    .get_mut(submodule)
                    .unwrap()
                    .insert(file.clone());
            }
            Op::CommitInSubmodule { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                testutil::git(&["-C", &path_str, "add", "-A"]);
                let output =
                    testutil::git_may_fail(&["-C", &path_str, "commit", "-m", "fuzz commit"]);
                if output.status.success() {
                    // After commit, all staged/untracked files in that submodule
                    // are resolved. The submodule now has "new commits" relative
                    // to the parent.
                    self.staged_files.get_mut(submodule).unwrap().clear();
                    self.untracked_files.get_mut(submodule).unwrap().clear();
                    self.submodules_with_changes.remove(submodule);
                }
            }
            Op::StageSubmoduleGitlink { submodule } => {
                self.harness.stage_submodule(submodule);
                self.staged_gitlinks.insert(submodule.clone());
            }
            Op::CommitInParent => {
                let output =
                    self.harness
                        .git_in_root_may_fail(&["commit", "-m", "fuzz parent commit"]);
                if output.status.success() {
                    self.staged_gitlinks.clear();
                }
            }
            Op::RapidFire { ops } => {
                for sub_op in ops {
                    self.execute_op(sub_op);
                }
            }
        }
    }

    /// Compute ground truth status for all submodules using git2.
    fn ground_truth(&self) -> Vec<(String, StatusSummary)> {
        let repo = Repository::open(self.harness.root_path())
            .expect("Failed to open root repo for ground truth");
        let submodules = repo.submodules().expect("Failed to list submodules");

        let mut statuses: Vec<(String, StatusSummary)> = Vec::new();
        for submod in &submodules {
            let path = submod.path().to_str().expect("Submodule path is not UTF-8");
            let git2_status = repo
                .submodule_status(path, git2::SubmoduleIgnore::None)
                .expect("Failed to get submodule status");
            let status: StatusSummary = git2_status.into();
            if status != StatusSummary::CLEAN {
                statuses.push((path.to_string(), status));
            }
        }
        statuses.sort_by(|a, b| a.0.cmp(&b.0));
        statuses
    }

    /// Wait for the server status to match ground truth.
    /// Returns Ok(()) on match, Err with details on timeout.
    fn verify(&self) -> Result<(), String> {
        let expected = self.ground_truth();
        let timeout = testutil::DEFAULT_TIMEOUT;
        let start = std::time::Instant::now();

        loop {
            let mut actual = self.harness.status();
            // Filter out LOCK_FAILURE — transient, not a real mismatch
            actual.retain(|(_, s)| !s.contains(StatusSummary::LOCK_FAILURE));
            actual.sort_by(|a, b| a.0.cmp(&b.0));

            if actual == expected {
                return Ok(());
            }

            if start.elapsed() >= timeout {
                // Re-compute ground truth at the moment of failure to confirm
                // it's stable (not a transient git2 read)
                let expected2 = self.ground_truth();
                let cli_check = self.cli_cross_check();
                return Err(format!(
                    "Status mismatch after {timeout:?}\n\
                     \n  ground truth (git2): {expected:?}\
                     \n  ground truth (re-read): {expected2:?}\
                     \n  server says:         {actual:?}\
                     \n\n  git CLI cross-check:\n{cli_check}"
                ));
            }
            std::thread::sleep(self.poll_interval);
        }
    }

    /// Run `git status --porcelain` and `git submodule status` for
    /// cross-checking on failure.
    fn cli_cross_check(&self) -> String {
        let root = self.harness.root_path().display().to_string();
        let porcelain = testutil::git_may_fail(&["-C", &root, "status", "--porcelain"]);
        let submod = testutil::git_may_fail(&["-C", &root, "submodule", "status"]);
        format!(
            "    [git status --porcelain]:\n    {}\n    [git submodule status]:\n    {}",
            String::from_utf8_lossy(&porcelain.stdout)
                .lines()
                .collect::<Vec<_>>()
                .join("\n    "),
            String::from_utf8_lossy(&submod.stdout)
                .lines()
                .collect::<Vec<_>>()
                .join("\n    "),
        )
    }
}

fn main() {
    let args = FuzzArgs::parse();
    let seed = args.seed.unwrap_or_else(rand::random);

    println!("=== subspy fuzzer ===");
    println!("seed:       {seed}");
    println!("steps:      {}", args.steps);
    println!("submodules: {}", args.submodules);
    println!("max_burst:  {}", args.max_burst);
    println!("poll_ms:    {}", args.poll_ms);
    println!();

    let mut state = FuzzerState::new(&args, seed);

    // Verify initial state is clean
    if let Err(e) = state.verify() {
        dump_failure(&state, 0, &e);
        std::process::exit(1);
    }
    println!("[step 0] initial state verified clean");

    for step in 1..=args.steps {
        let op = state.step();
        println!("[step {step}] {op}");
        state.history.push(op);

        if let Err(e) = state.verify() {
            dump_failure(&state, step, &e);
            std::process::exit(1);
        }
    }

    println!();
    println!(
        "All {steps} steps passed with seed {seed}.",
        steps = args.steps
    );
}

fn dump_failure(state: &FuzzerState, failed_step: u32, error: &str) {
    eprintln!();
    eprintln!(
        "Repo path: {} (preserved for inspection)",
        state.harness.root_path().display()
    );
    eprintln!("Reproduce: cargo xtask --seed <SEED> --steps {failed_step} --submodules <N>");
    eprintln!();
    match request_debug(state.harness.root_path()) {
        Ok(debug_state) => eprintln!("Server debug state:\n{debug_state}"),
        Err(e) => eprintln!("Failed to fetch server debug state: {e}"),
    }
    eprintln!();
    eprintln!("FAIL at step {failed_step}: {error}");
}
