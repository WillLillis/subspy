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

/// Operations the fuzzer can perform against the watch server.
#[derive(Debug, Clone)]
enum Op {
    /// Create a new untracked file in a submodule workdir.
    WriteNewFile { submodule: String, file: String },
    /// Overwrite README.md with unique content (modifies a tracked file).
    OverwriteTrackedFile { submodule: String },
    /// Delete an untracked file from a submodule workdir.
    DeleteFile { submodule: String, file: String },
    /// `git add <file>` — stage an untracked file.
    StageFile { submodule: String, file: String },
    /// `git reset HEAD -- <file>` — unstage a staged file back to untracked.
    UnstageFile { submodule: String, file: String },
    /// `git add -A && git commit` — commit all changes in a submodule.
    CommitInSubmodule { submodule: String },
    /// `git add <submodule>` in the parent — stage a submodule gitlink.
    StageSubmoduleGitlink { submodule: String },
    /// `git commit` in the parent — commit staged gitlinks.
    CommitInParent,
    /// `git clean -fd` — remove all untracked files in a submodule.
    CleanSubmodule { submodule: String },
    /// `git restore README.md` — discard working tree changes to a tracked file.
    RestoreFile { submodule: String },
    /// `git reset HEAD -- <submodule>` in the parent — unstage a gitlink.
    UnstageGitlink { submodule: String },
    /// `git reset --hard HEAD` — reset index and working tree, keeps untracked files.
    ResetHardInSubmodule { submodule: String },
    /// `git add -A && git commit --amend --no-edit` — amend the last commit.
    AmendInSubmodule { submodule: String },
    /// Request a server reindex (optionally replacing file watchers).
    Reindex { replace_watchers: bool },
    /// `git stash -u` — stash all changes including untracked files.
    StashInSubmodule { submodule: String },
    /// `git stash pop` — restore stashed changes (without --index).
    StashPopInSubmodule { submodule: String },
    /// `git reset --soft HEAD~1` — undo last commit, changes become staged.
    ResetSoftInSubmodule { submodule: String },
    /// `git reset HEAD~1` (mixed) — undo last commit, changes become unstaged.
    ResetMixedInSubmodule { submodule: String },
    /// Clean all submodules, then `git checkout <branch>` in the parent.
    /// Requires a subsequent `SubmoduleUpdate` before other operations.
    CheckoutBranch { to_feature: bool },
    /// `git submodule update` + create fresh branch in each submodule.
    SubmoduleUpdate,
    /// Perform N operations without waiting for the server between them.
    RapidFire { ops: Vec<Op> },
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
            Self::CleanSubmodule { submodule } => {
                write!(f, "git clean -fd in {submodule}")
            }
            Self::RestoreFile { submodule } => {
                write!(f, "git restore README.md in {submodule}")
            }
            Self::UnstageGitlink { submodule } => {
                write!(f, "unstage gitlink for {submodule}")
            }
            Self::ResetHardInSubmodule { submodule } => {
                write!(f, "git reset --hard HEAD in {submodule}")
            }
            Self::AmendInSubmodule { submodule } => {
                write!(f, "amend commit in {submodule}")
            }
            Self::Reindex { replace_watchers } => {
                write!(f, "reindex (replace_watchers={replace_watchers})")
            }
            Self::StashInSubmodule { submodule } => {
                write!(f, "git stash -u in {submodule}")
            }
            Self::StashPopInSubmodule { submodule } => {
                write!(f, "git stash pop in {submodule}")
            }
            Self::ResetSoftInSubmodule { submodule } => {
                write!(f, "git reset --soft HEAD~1 in {submodule}")
            }
            Self::ResetMixedInSubmodule { submodule } => {
                write!(f, "git reset HEAD~1 in {submodule}")
            }
            Self::CheckoutBranch { to_feature } => {
                let branch = if *to_feature { "feature" } else { "master" };
                write!(f, "git checkout {branch}")
            }
            Self::SubmoduleUpdate => write!(f, "git submodule update"),
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

/// State saved by `git stash -u` for later restoration via `git stash pop`.
#[derive(Clone)]
struct StashedState {
    readme_modified: bool,
    untracked_files: HashSet<String>,
    staged_files: HashSet<String>,
    /// History epoch at stash time — pop is only safe when the epoch still matches
    /// (i.e. no commits, amends, or resets have changed HEAD since the stash).
    history_epoch: u32,
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
    CleanSubmodule,
    RestoreFile,
    UnstageGitlink,
    ResetHardInSubmodule,
    AmendInSubmodule,
    Reindex,
    StashInSubmodule,
    StashPopInSubmodule,
    ResetSoftInSubmodule,
    ResetMixedInSubmodule,
    CheckoutBranch,
    SubmoduleUpdate,
    RapidFire,
}

// Weights for weighted-random operation selection in pick_op_kind.
// Higher weight = more likely to be picked.
const W_WRITE_NEW_FILE: u32 = 10;
const W_OVERWRITE_TRACKED: u32 = 6;
const W_DELETE_FILE: u32 = 4;
const W_STAGE_FILE: u32 = 5;
const W_CLEAN_SUBMODULE: u32 = 3;
const W_UNSTAGE_FILE: u32 = 3;
const W_RESTORE_FILE: u32 = 3;
const W_COMMIT_IN_SUBMODULE: u32 = 5;
const W_RESET_HARD: u32 = 2;
const W_STAGE_GITLINK: u32 = 3;
const W_COMMIT_IN_PARENT: u32 = 2;
const W_UNSTAGE_GITLINK: u32 = 3;
const W_AMEND_IN_SUBMODULE: u32 = 2;
const W_REINDEX: u32 = 2;
const W_STASH: u32 = 3;
const W_STASH_POP: u32 = 4;
const W_RESET_SOFT: u32 = 2;
const W_RESET_MIXED: u32 = 2;
const W_CHECKOUT_BRANCH: u32 = 3;
const W_RAPID_FIRE: u32 = 3;
const HISTORY_LEN: usize = 100;

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
    /// submodules where README.md has been modified but not committed/restored
    readme_modified: HashSet<String>,
    /// submodule -> number of local commits ahead of the parent gitlink
    local_commit_count: HashMap<String, u32>,
    /// submodule -> saved dirty state from `git stash -u`
    stash_stack: HashMap<String, StashedState>,
    /// monotonic counter per submodule, bumped on commit/amend/reset that
    /// changes HEAD — used to ensure stash pop only runs when HEAD matches
    /// the stash base
    history_epoch: HashMap<String, u32>,
    /// whether the root repo is on the feature branch
    on_feature_branch: bool,
    /// whether submodule workdirs need syncing after a branch checkout
    needs_submodule_update: bool,
    /// counter for generating unique filenames and branch names
    file_counter: u32,
    /// recent operation log (fixed ring buffer for diagnostics)
    history: [Option<Op>; HISTORY_LEN],
    history_idx: usize,
    /// polling interval
    poll_interval: Duration,
    /// max burst size for rapid-fire
    max_burst: u32,
}

impl FuzzerState {
    fn new(args: &FuzzArgs, seed: u64) -> Self {
        let rng = StdRng::seed_from_u64(seed);
        let mut harness = HarnessBuilder::new()
            .submodules(args.submodules)
            .no_server()
            .build();

        let submod_names: Vec<String> = harness.submodule_names().map(String::from).collect();

        // Create a feature branch with different submodule commits so that
        // CheckoutBranch can toggle between two known states.
        harness.git_in_root(&["checkout", "-b", "feature"]);
        for sub in &submod_names {
            harness.git_in_submodule(sub, &["checkout", "-b", "feature"]);
            harness.write_file(sub, "feature_file.txt", "feature content\n");
            harness.git_in_submodule(sub, &["add", "-A"]);
            harness.git_in_submodule(sub, &["commit", "-m", "feature commit"]);
            harness.stage_submodule(sub);
            harness.git_in_submodule(sub, &["checkout", "master"]);
        }
        harness.git_in_root(&["commit", "-m", "update submodules on feature"]);
        harness.git_in_root(&["checkout", "master"]);

        let untracked_files: HashMap<String, HashSet<String>> = submod_names
            .iter()
            .map(|name| (name.clone(), HashSet::new()))
            .collect();
        let staged_files: HashMap<String, HashSet<String>> = submod_names
            .iter()
            .map(|name| (name.clone(), HashSet::new()))
            .collect();

        harness.start_server();

        Self {
            rng,
            harness,
            untracked_files,
            staged_files,
            submodules_with_changes: HashSet::new(),
            staged_gitlinks: HashSet::new(),
            readme_modified: HashSet::new(),
            local_commit_count: HashMap::new(),
            stash_stack: HashMap::new(),
            history_epoch: HashMap::new(),
            on_feature_branch: false,
            needs_submodule_update: false,
            file_counter: 0,
            history: [const { None }; HISTORY_LEN],
            history_idx: 0,
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

    /// Query `git status --porcelain` to check if a submodule has any dirty
    /// state, and update `submodules_with_changes` accordingly. Used after
    /// operations like soft/mixed reset where we can't track the resulting
    /// dirty state at file granularity.
    fn sync_dirty_state(&mut self, submodule: &str) {
        let path = self.harness.submodule_path(submodule);
        let path_str = path.display().to_string();
        let output = testutil::git_may_fail(&["-C", &path_str, "status", "--porcelain"]);
        let stdout = String::from_utf8_lossy(&output.stdout);
        if stdout.trim().is_empty() {
            self.submodules_with_changes.remove(submodule);
        } else {
            self.submodules_with_changes.insert(submodule.to_string());
        }
    }

    /// Select a weighted-random operation kind that is valid given current state.
    fn pick_op_kind(&mut self) -> OpKind {
        // While waiting for submodule update, no other operations are valid.
        if self.needs_submodule_update {
            return OpKind::SubmoduleUpdate;
        }

        let mut candidates: Vec<(u32, OpKind)> = vec![
            (W_WRITE_NEW_FILE, OpKind::WriteNewFile),
            (W_OVERWRITE_TRACKED, OpKind::OverwriteTrackedFile),
        ];

        // Reindex replaces watchers which takes time to set up — exclude from
        // rapid-fire (max_burst==0 inside rapid-fire) to avoid losing events
        // that happen before new watchers are ready.
        if self.max_burst > 0 {
            candidates.push((W_REINDEX, OpKind::Reindex));
        }

        let has_untracked = self.untracked_files.values().any(|files| !files.is_empty());
        if has_untracked {
            candidates.push((W_DELETE_FILE, OpKind::DeleteFile));
            candidates.push((W_STAGE_FILE, OpKind::StageFile));
            candidates.push((W_CLEAN_SUBMODULE, OpKind::CleanSubmodule));
        }

        if self.staged_files.values().any(|files| !files.is_empty()) {
            candidates.push((W_UNSTAGE_FILE, OpKind::UnstageFile));
        }

        if !self.readme_modified.is_empty() {
            candidates.push((W_RESTORE_FILE, OpKind::RestoreFile));
        }

        if !self.submodules_with_changes.is_empty() {
            candidates.push((W_COMMIT_IN_SUBMODULE, OpKind::CommitInSubmodule));
            candidates.push((W_RESET_HARD, OpKind::ResetHardInSubmodule));
        }

        // Stash: requires a dirty submodule with no existing stash
        let has_stashable = self
            .submodules_with_changes
            .iter()
            .any(|sub| !self.stash_stack.contains_key(sub));
        if has_stashable {
            candidates.push((W_STASH, OpKind::StashInSubmodule));
        }

        // Stash pop: requires an existing stash, the submodule must be clean,
        // and HEAD must not have moved since the stash was created
        let has_poppable = self.stash_stack.iter().any(|(sub, stashed)| {
            !self.submodules_with_changes.contains(sub)
                && self.history_epoch.get(sub).copied().unwrap_or(0) == stashed.history_epoch
        });
        if has_poppable {
            candidates.push((W_STASH_POP, OpKind::StashPopInSubmodule));
        }

        // Always allow — gitlink may or may not actually be dirty
        candidates.push((W_STAGE_GITLINK, OpKind::StageSubmoduleGitlink));

        if !self.staged_gitlinks.is_empty() {
            candidates.push((W_COMMIT_IN_PARENT, OpKind::CommitInParent));
            candidates.push((W_UNSTAGE_GITLINK, OpKind::UnstageGitlink));
        }

        let has_local_commits = self.local_commit_count.values().any(|&c| c >= 1);
        if has_local_commits {
            candidates.push((W_RESET_SOFT, OpKind::ResetSoftInSubmodule));
            candidates.push((W_RESET_MIXED, OpKind::ResetMixedInSubmodule));
        }

        let has_amendable = self
            .local_commit_count
            .iter()
            .any(|(s, &c)| c >= 1 && self.submodules_with_changes.contains(s));
        if has_amendable {
            candidates.push((W_AMEND_IN_SUBMODULE, OpKind::AmendInSubmodule));
        }

        // Checkout cleans up all dirty state before switching, so it's always
        // valid. Exclude from rapid-fire — it's a heavyweight multi-step op.
        if self.max_burst > 0 {
            candidates.push((W_CHECKOUT_BRANCH, OpKind::CheckoutBranch));
        }

        if self.max_burst >= 2 {
            candidates.push((W_RAPID_FIRE, OpKind::RapidFire));
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
            OpKind::CleanSubmodule => {
                let eligible: Vec<String> = self
                    .untracked_files
                    .iter()
                    .filter(|(_, files)| !files.is_empty())
                    .map(|(name, _)| name.clone())
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::CleanSubmodule { submodule }
            }
            OpKind::RestoreFile => {
                let eligible: Vec<String> = self.readme_modified.iter().cloned().collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::RestoreFile { submodule }
            }
            OpKind::UnstageGitlink => {
                let eligible: Vec<String> = self.staged_gitlinks.iter().cloned().collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::UnstageGitlink { submodule }
            }
            OpKind::ResetHardInSubmodule => {
                let eligible: Vec<String> = self.submodules_with_changes.iter().cloned().collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::ResetHardInSubmodule { submodule }
            }
            OpKind::AmendInSubmodule => {
                let eligible: Vec<String> = self
                    .local_commit_count
                    .iter()
                    .filter(|(s, c)| **c >= 1 && self.submodules_with_changes.contains(*s))
                    .map(|(s, _)| s.clone())
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::AmendInSubmodule { submodule }
            }
            OpKind::Reindex => {
                let replace_watchers = self.rng.random_bool(0.5);
                Op::Reindex { replace_watchers }
            }
            OpKind::StashInSubmodule => {
                let eligible: Vec<String> = self
                    .submodules_with_changes
                    .iter()
                    .filter(|sub| !self.stash_stack.contains_key(*sub))
                    .cloned()
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::StashInSubmodule { submodule }
            }
            OpKind::StashPopInSubmodule => {
                let eligible: Vec<String> = self
                    .stash_stack
                    .iter()
                    .filter(|(sub, stashed)| {
                        !self.submodules_with_changes.contains(*sub)
                            && self.history_epoch.get(*sub).copied().unwrap_or(0)
                                == stashed.history_epoch
                    })
                    .map(|(s, _)| s.clone())
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::StashPopInSubmodule { submodule }
            }
            OpKind::ResetSoftInSubmodule => {
                let eligible: Vec<String> = self
                    .local_commit_count
                    .iter()
                    .filter(|(_, c)| **c >= 1)
                    .map(|(s, _)| s.clone())
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::ResetSoftInSubmodule { submodule }
            }
            OpKind::ResetMixedInSubmodule => {
                let eligible: Vec<String> = self
                    .local_commit_count
                    .iter()
                    .filter(|(_, c)| **c >= 1)
                    .map(|(s, _)| s.clone())
                    .collect();
                let submodule = eligible.choose(&mut self.rng).unwrap().clone();
                Op::ResetMixedInSubmodule { submodule }
            }
            OpKind::CheckoutBranch => Op::CheckoutBranch {
                to_feature: !self.on_feature_branch,
            },
            OpKind::SubmoduleUpdate => Op::SubmoduleUpdate,
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
                self.file_counter += 1;
                let content = format!("modified {}\n", self.file_counter);
                self.harness.write_file(submodule, "README.md", &content);
                self.submodules_with_changes.insert(submodule.clone());
                self.readme_modified.insert(submodule.clone());
            }
            Op::DeleteFile { submodule, file } => {
                self.harness.remove_file(submodule, file);
                self.untracked_files
                    .get_mut(submodule)
                    .unwrap()
                    .remove(file);
                if self.untracked_files[submodule].is_empty()
                    && self.staged_files[submodule].is_empty()
                    && !self.readme_modified.contains(submodule)
                {
                    self.sync_dirty_state(submodule);
                }
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
                testutil::git(&["-C", &path_str, "commit", "-m", "fuzz commit"]);
                self.staged_files.get_mut(submodule).unwrap().clear();
                self.untracked_files.get_mut(submodule).unwrap().clear();
                self.readme_modified.remove(submodule);
                self.submodules_with_changes.remove(submodule);
                *self
                    .local_commit_count
                    .entry(submodule.clone())
                    .or_insert(0) += 1;
                *self.history_epoch.entry(submodule.clone()).or_insert(0) += 1;
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
                    for sub in &self.staged_gitlinks {
                        self.local_commit_count.remove(sub);
                    }
                    self.staged_gitlinks.clear();
                }
            }
            Op::CleanSubmodule { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                testutil::git(&["-C", &path_str, "clean", "-fd"]);
                self.untracked_files.get_mut(submodule).unwrap().clear();
                self.sync_dirty_state(submodule);
            }
            Op::RestoreFile { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                testutil::git(&["-C", &path_str, "restore", "README.md"]);
                self.readme_modified.remove(submodule);
                self.sync_dirty_state(submodule);
            }
            Op::UnstageGitlink { submodule } => {
                let root = self.harness.root_path().display().to_string();
                testutil::git(&["-C", &root, "reset", "HEAD", "--", submodule]);
                self.staged_gitlinks.remove(submodule);
            }
            Op::ResetHardInSubmodule { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                testutil::git(&["-C", &path_str, "reset", "--hard", "HEAD"]);
                self.staged_files.get_mut(submodule).unwrap().clear();
                self.readme_modified.remove(submodule);
                self.sync_dirty_state(submodule);
            }
            Op::AmendInSubmodule { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                testutil::git(&["-C", &path_str, "add", "-A"]);
                let output =
                    testutil::git_may_fail(&["-C", &path_str, "commit", "--amend", "--no-edit"]);
                if output.status.success() {
                    self.staged_files.get_mut(submodule).unwrap().clear();
                    self.untracked_files.get_mut(submodule).unwrap().clear();
                    self.readme_modified.remove(submodule);
                    self.submodules_with_changes.remove(submodule);
                    *self.history_epoch.entry(submodule.clone()).or_insert(0) += 1;
                }
            }
            Op::Reindex { replace_watchers } => {
                self.harness.request_reindex(*replace_watchers);
            }
            Op::StashInSubmodule { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                let output = testutil::git_may_fail(&["-C", &path_str, "stash", "-u"]);
                if !output.status.success() {
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    // "No local changes to save" means our state model was
                    // stale — that's fine. Anything else (e.g. lock contention)
                    // is a real problem worth surfacing.
                    if !stderr.contains("No local changes to save") {
                        eprintln!("git stash -u in {submodule} failed unexpectedly: {stderr}");
                        std::process::exit(1);
                    }
                }
                if output.status.success() {
                    let stashed = StashedState {
                        readme_modified: self.readme_modified.remove(submodule),
                        untracked_files: std::mem::take(
                            self.untracked_files.get_mut(submodule).unwrap(),
                        ),
                        staged_files: std::mem::take(self.staged_files.get_mut(submodule).unwrap()),
                        history_epoch: self.history_epoch.get(submodule).copied().unwrap_or(0),
                    };
                    self.stash_stack.insert(submodule.clone(), stashed);
                    self.submodules_with_changes.remove(submodule);
                }
            }
            Op::StashPopInSubmodule { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                // Verify the stash actually exists before popping — if it
                // doesn't, the stash creation silently failed (e.g. server
                // held index lock) which is itself a bug to investigate.
                let list = testutil::git_may_fail(&["-C", &path_str, "stash", "list"]);
                let has_stash = !String::from_utf8_lossy(&list.stdout).trim().is_empty();
                if !has_stash {
                    eprintln!(
                        "BUG: stash_stack has {submodule} but git stash list is empty — \
                         the stash creation likely failed silently"
                    );
                    self.stash_stack.remove(submodule);
                    return;
                }
                testutil::git(&["-C", &path_str, "stash", "pop"]);
                let stashed = self.stash_stack.remove(submodule).unwrap();
                if stashed.readme_modified {
                    self.readme_modified.insert(submodule.clone());
                }
                // Pop without --index: untracked files stay untracked, but
                // staged new files remain staged (git preserves index for new files).
                self.untracked_files
                    .get_mut(submodule)
                    .unwrap()
                    .extend(stashed.untracked_files);
                self.staged_files
                    .get_mut(submodule)
                    .unwrap()
                    .extend(stashed.staged_files);
                self.submodules_with_changes.insert(submodule.clone());
            }
            Op::ResetSoftInSubmodule { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                testutil::git(&["-C", &path_str, "reset", "--soft", "HEAD~1"]);
                let count = self.local_commit_count.get_mut(submodule).unwrap();
                *count -= 1;
                if *count == 0 {
                    self.local_commit_count.remove(submodule);
                }
                self.sync_dirty_state(submodule);
                *self.history_epoch.entry(submodule.clone()).or_insert(0) += 1;
            }
            Op::ResetMixedInSubmodule { submodule } => {
                let path = self.harness.submodule_path(submodule);
                let path_str = path.display().to_string();
                testutil::git(&["-C", &path_str, "reset", "HEAD~1"]);
                let count = self.local_commit_count.get_mut(submodule).unwrap();
                *count -= 1;
                if *count == 0 {
                    self.local_commit_count.remove(submodule);
                }
                self.staged_files.get_mut(submodule).unwrap().clear();
                self.sync_dirty_state(submodule);
                *self.history_epoch.entry(submodule.clone()).or_insert(0) += 1;
            }
            Op::CheckoutBranch { to_feature } => {
                // Clean up all dirty state so the branch switch succeeds
                for sub in self.submodule_names() {
                    if self.stash_stack.contains_key(&sub) {
                        // Stash may have been silently lost; use may_fail
                        self.harness
                            .git_in_submodule_may_fail(&sub, &["stash", "drop"]);
                    }
                    self.harness
                        .git_in_submodule(&sub, &["reset", "--hard", "HEAD"]);
                    self.harness.git_in_submodule(&sub, &["clean", "-fd"]);
                }
                if !self.staged_gitlinks.is_empty() {
                    self.harness.git_in_root(&["reset", "HEAD"]);
                }

                let branch = if *to_feature { "feature" } else { "master" };
                self.harness.git_in_root(&["checkout", branch]);
                self.on_feature_branch = *to_feature;
                self.needs_submodule_update = true;
                // Clear all per-submodule state — will be rebuilt after SubmoduleUpdate
                for files in self.untracked_files.values_mut() {
                    files.clear();
                }
                for files in self.staged_files.values_mut() {
                    files.clear();
                }
                self.submodules_with_changes.clear();
                self.staged_gitlinks.clear();
                self.readme_modified.clear();
                self.local_commit_count.clear();
                self.stash_stack.clear();
                self.history_epoch.clear();
            }
            Op::SubmoduleUpdate => {
                self.harness.git_in_root(&["submodule", "update"]);
                // Create a fresh branch at the detached HEAD so subsequent commits
                // update refs/heads/ (which the server uses for commit detection)
                for sub in self.submodule_names() {
                    self.file_counter += 1;
                    let branch = format!("fuzz_br_{}", self.file_counter);
                    self.harness
                        .git_in_submodule(&sub, &["checkout", "-b", &branch]);
                }
                self.needs_submodule_update = false;
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
        state.history[state.history_idx % HISTORY_LEN] = Some(op);
        state.history_idx += 1;

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
