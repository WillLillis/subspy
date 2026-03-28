# Contributing to SubSpy

This document covers the project's architecture, conventions, and testing approach.
For what SubSpy does and how to use it, see the [README](README.md).

## Architecture

SubSpy is a client/server system. A background **watch server** (daemon) monitors a git
repository's filesystem and caches submodule status. CLI commands connect to the server
over IPC to retrieve or manipulate that cache.

```
  CLI (subspy status, prompt, list, ...)
      |
      | IPC (Unix domain socket / AF_UNIX on Windows)
      |
  Watch Server (background process)
      |
      +-- notify file watchers (recursive, per-submodule)
      +-- git2/libgit2 (submodule status computation)
      +-- BTreeMap<String, StatusSummary> (cached state)
```

### Lifecycle

1. `subspy status` (or `prompt`) connects to the server. If none is running, it spawns
   one via `spawn_daemon` and retries.
2. The server acquires a lock file, places recursive filesystem watchers on `.git/`,
   `.gitmodules`, and each submodule directory, then runs an initial indexing pass.
3. On filesystem events, the server re-computes status for affected submodules (debounced,
   with cancellation of in-flight tasks via `AtomicBool`).
4. Client requests are handled on the server's main thread. Status responses are
   serialized from the cached `BTreeMap`.
5. `subspy stop` sends a shutdown message; the server cleans up watchers and the socket file.

## Module Map

### Core (`src/`)

| File | Purpose |
|---|---|
| `main.rs` | Entry point: logging setup, CLI dispatch, error display |
| `cli.rs` | Clap argument structs, subcommand definitions, `RunError` |
| `lib.rs` | `StatusSummary` bitflags, ANSI paint helper, progress bar |
| `git.rs` | Lightweight git helpers (`parse_gitmodules` -- fast `.gitmodules` parser) |
| `watch.rs` | `spawn_daemon`, `LockFileGuard` (atomic lock file with fs-watcher wait) |
| `status.rs` | `display_status` output formatting, `HeaderState` enum, `compute_local_statuses` |
| `prompt.rs` | Shell prompt integration -- fast, silent on all errors (experimental; exposed primitives may change) |
| `list.rs` | `subspy list` -- submodule metadata with format templates |
| `template.rs` | Template parsing, validation, placeholder expansion |
| `shutdown.rs` | `subspy stop` command |
| `reindex.rs` | `subspy reindex` command |
| `debug.rs` | `subspy debug` -- dumps server internal state |

### Connection (`src/connection/`)

| File | Purpose |
|---|---|
| `mod.rs` | Shared IPC types (`ClientRequest`, `ClientMessage`, `ServerMessage`), wire format helpers (`read_full_message`, `write_full_message_fixed`, `encode_and_write`), `IpcError`, platform abstractions |
| `watch_server.rs` | Server event loop, watcher management, status computation, `InFlightTask` cancellation |
| `client_handler.rs` | Server-side IPC message dispatch, progress broadcasting |
| `client.rs` | Client-side IPC (connect, send request, receive response) |

### Testing

| Path | Purpose |
|---|---|
| `testutil/` | Shared test harness crate (`HarnessBuilder`, `TestHarness`, git helpers) |
| `tests/common/mod.rs` | Re-exports testutil, defines `repeat` template (runs each test 10x) |
| `tests/*.rs` | Integration tests organized by git operation (basic, rebase, merge, etc.) |
| `xtask/` | Fuzzer: random git operations with ground-truth verification |

## IPC Protocol

Messages are length-prefixed bincode with fixint encoding:

```
[4-byte LE length][bincode payload]
```

Every client message is wrapped in `ClientRequest { version: u8, message: ClientMessage }`.
The server checks `version` against `IPC_VERSION` and responds with
`ServerMessage::VersionMismatch` on mismatch, keeping the server alive for other clients.

Small fixed-size messages (status requests, shutdown ack, etc.) use stack buffers and
`write_full_message_fixed` for single-syscall writes. Large variable-size messages
(status responses, debug dumps) use `encode_and_write`, which prepends the length prefix
into a `Vec` and writes in a single `write_all`.

**Wire format stability**: The `wire_format_stability` test encodes every message variant
and asserts the exact byte sequence. If you change any IPC type, this test will fail --
bump `IPC_VERSION` and update the expected bytes.

## Design Decisions

**`StatusSummary` bitflags over structured types.** Submodule status is a compact `u8`
bitmask (`MODIFIED_CONTENT`, `UNTRACKED_CONTENT`, `NEW_COMMITS`, `STAGED`, `STAGED_NEW`,
`LOCK_FAILURE`). This keeps IPC payloads small and comparisons cheap.

**`parse_gitmodules` over `repo.submodules()`.** Calling `repo.submodules()` takes ~100ms
due to libgit2 overhead. Our custom `.gitmodules` parser takes ~600us when measured on
boost.

**Sequential watcher placement.** Creating `notify::RecommendedWatcher` instances
concurrently on rayon threads causes them to silently miss filesystem events. Watcher
placement must remain sequential -- do not attempt to parallelize it.

**`FxHashMap`/`FxHashSet` for internal maps.** We use rustc-hash for non-cryptographic
hashing where key distribution is predictable (submodule paths, watcher indices).
`BTreeMap` is used for the status map to ensure ordered output.

**`thread_local::ThreadLocal` for git2 `Repository`.** `git2::Repository` is `!Sync`,
so we cache one per rayon thread for parallel submodule status computation.

**`deleted_submodule_paths` is separate from `StatusSummary`.** When a submodule is
staged for deletion (`git rm <submodule>`), its gitlink is removed from the index but
remains in the HEAD tree. The watch server can't detect this through filesystem events
alone -- the submodule's directory is gone, so there's nothing to watch. Instead,
`deleted_submodule_paths` walks the HEAD tree at display time, comparing gitlink entries
against the index to find removals. This is computed client-side in `status.rs`, not
cached by the server. Tracking deletions server-side was explored but didn't work: the
server discovers submodules from `.gitmodules`, and a deleted submodule is absent from
`.gitmodules`. Detecting the deletion requires comparing old status map keys against new
`.gitmodules` entries during reindex, but then cleaning up stale `DELETED` entries after
a commit (which doesn't trigger a reindex) requires additional git operations on the
`RootGitOperation` hot path. The client-side tree walk is cheap and avoids this
complexity.

**`--no-server` fallback.** The `status`, `prompt`, and `list` commands support a
`--no-server` flag that computes submodule status locally via `compute_local_statuses`
instead of connecting to the watch server. This uses `parse_gitmodules` + parallel
`repo.submodule_status()` calls. It's slower than the server path but useful when no
server is desired (e.g. CI, one-off checks).

**No nested submodule support.** SubSpy must be run from the top-level repository.
Submodules that contain submodules of their own are not recursed into.

## Testing

SubSpy's correctness depends on the watch server tracking every filesystem and git state
change across arbitrarily many submodules. The testing strategy uses three layers:

### Unit tests

These cover pure logic that doesn't require a running server: `StatusSummary` flag predicates,
template parsing and expansion, `.gitmodules` parsing, display formatting, `HeaderState`
detection, IPC wire format stability, and IPC message round-trips.

### Integration tests (`tests/`)

Each test file exercises a specific category of git operation against a real watch server:

| File | Coverage |
|---|---|
| `basic.rs` | Core status detection: modified/untracked content, new commits, staging, nested paths |
| `checkout.rs` | Branch switches, `--recurse-submodules`, submodule update after checkout |
| `rebase.rs` | Rebase with/without conflicts, reindex during rebase (skip set clearing) |
| `merge.rs` | Merge with/without conflicts, both in root and submodules |
| `cherry_pick.rs` | Cherry-pick with/without conflicts, both in root and submodules |
| `reset.rs` | Soft, mixed, and hard resets; unstaging gitlinks in the parent |
| `stash.rs` | Stash save/restore for modified and untracked content |
| `amend.rs` | Commit amend detection |
| `clean.rs` | `git clean -fd` in submodules |
| `submodule_management.rs` | Adding/removing submodules at runtime (committed and uncommitted) |
| `lifecycle.rs` | Server shutdown, reindex, IPC version mismatch, stale socket recovery |

Tests aim to be deterministic: each test sets up a specific git state, performs an
operation, and asserts the expected `StatusSummary` flags. The watch server runs
in-process on a background thread (not as a spawned daemon), communicating over real
IPC sockets to a temp directory.

**Repeat macro**: Every integration test runs 10x via `#[apply(common::repeat)]` to
surface race conditions between filesystem events, watcher notifications, and status
computation. This is important because the server processes events asynchronously --
a test that passes once might fail on the 8th run due to timing.

**Test harness** (`testutil/`): `HarnessBuilder` creates a temp directory, initializes
a root repo with submodules (using local source repos, no network), and optionally starts
the watch server. `TestHarness` provides helpers for file operations, git commands, and
polling assertions (`assert_submodule_status`, `assert_all_clean`). The server is shut
down and the temp dir cleaned up on drop.

```rust
let harness = HarnessBuilder::new()
    .submodule("sub_a")
    .submodule("sub_b")
    .build(); // creates temp repo, starts watch server, waits for indexing

harness.write_file("sub_a", "new.txt", "content\n");
harness.assert_submodule_status("sub_a", StatusSummary::UNTRACKED_CONTENT);
harness.assert_submodule_status("sub_b", StatusSummary::clean());
// server is shut down and temp dir cleaned up on drop
```

**Thread count**: Limited to 4 in `.cargo/config.toml` because each test spins up a
real watch server with filesystem watchers. Too many concurrent servers exhaust
OS watcher limits (e.g. inotify instances on Linux).

### Fuzzer (`xtask/`)

The integration tests cover known scenarios deterministically, but can't cover the
combinatorial space of git operations happening in arbitrary order. The fuzzer fills
this gap by performing weighted-random operations and verifying server state against
`git submodule status` ground truth after each step.

**Operations covered**: write/delete files, stage/unstage, commit, amend, reset
(soft/mixed/hard), stash/pop, clean, stage/unstage/commit gitlinks, branch checkout
with submodule update, reindex, and rapid-fire bursts of multiple operations without
waiting for the server to settle between them.

**Operations NOT covered**: rebases, merges, and cherry-picks are not included in the
fuzzer because they require carefully constructed divergent history and conflict
resolution that is difficult to generate randomly while maintaining a consistent state
model. These are covered by deterministic integration tests instead.

```sh
cargo xtask fuzz --seed 42 --steps 100 --submodules 5
cargo xtask fuzz --collect-stats  # writes timing.csv + git_stats.csv
```

Use `--seed` to reproduce failures. The fuzzer prints the seed, the repo path, and the
server's debug state on failure.

**Known limitation -- git slowdown over time**: As the fuzzer runs, git object
accumulation (loose objects, pack files, dangling refs from amends and resets) causes
all git operations to slow down -- both the fuzzer's own `git add`/`commit`/`reset`
calls and the `git submodule status` ground truth checks. The fuzzer periodically
repacks (every 10,000 steps by default) to mitigate this, but very long runs will
still see increasing per-step times. The watch server itself is unaffected since it
uses filesystem events rather than scanning.

## Development

### Build and test

```sh
cargo build
cargo test          # unit + integration tests
cargo clippy        # lints (pedantic + nursery enabled)
cargo xtask fuzz    # randomized server fuzzing (runs indefinitely by default)
```

## Platform Notes

- **Linux**: Each watch server consumes inotify watches. For large repos, you may need
  `sudo sysctl fs.inotify.max_user_watches=<value>`.
- **Windows**: Uses `uds_windows` for AF_UNIX sockets (requires Windows 10 1809+).
  When `std::os::windows::net::UnixStream` stabilizes in std, the `uds_windows`
  dependency can be dropped.
- **macOS**: Uses Apple's FSEvents API via the `notify` crate. No special configuration needed.

## Common Pitfalls

### `index.lock` discipline

Git uses an atomic rename pattern: write to `index.lock`, delete the original `index`,
rename `index.lock` to `index`. The server must be careful about when it holds
`index.lock`:

- **During `populate_status_map`**: The root `index.lock` is held while calling
  `parse_gitmodules` (which reads `.gitmodules` via `git2::Config`). This prevents
  concurrent git operations from modifying the index mid-read. The lock is released
  before the parallel `submodule_status` calls.
- **During rayon status updates**: No lock is held. `submodule_status()` is read-only
  and never calls `git_index_write()`. Git's atomic rename guarantees the index is
  always consistent for readers. Holding the lock here would block user git operations.
- **During `get_submod_status`**: The submodule's `index.lock` (not the root's) is
  acquired. If it can't be acquired (git is actively writing), the server returns
  `LOCK_FAILURE` as a transient pseudo-status.

The key rule: **hold `index.lock` only during config/gitmodules reads, never during
`submodule_status` calls.** Getting this wrong either blocks user git operations
(holding too long) or produces corrupt reads (not holding when needed).

### `.gitmodules` change deferral

When `.gitmodules` changes, the server can't reindex immediately. The git operation
that modified `.gitmodules` (e.g. `git submodule add`) also updates the index as part
of the same command. If the server triggered a reindex on the `.gitmodules` event, it
would try to acquire `index.lock` before the git command releases it, causing the git
command to fail. The `GitmodulesTracker` defers the reindex until the git operation's
root events have settled.

### Transient read failures in rayon tasks

Between git deleting the old `index` and renaming `index.lock` to `index`, the file
is briefly absent. A `submodule_status()` call during this window fails. Three retry
paths cover this (documented in detail in `try_spawn_submod_update`): dirty retry (event
loop marks the in-flight task), new task spawn (event loop creates a fresh task after
the rename), and `SubmoduleLockRelease` safety net (for aborted git operations).

### Event ordering across platforms

`notify` delivers events differently per platform. On Linux (inotify), a `git add`
inside a submodule may produce only a `MOVED_TO index` rename event, not a write event.
The server's `get_event_type` has platform-specific carve-outs for these cases. When
adding new event handling, test on both Linux and Windows -- an event pattern that works
on one platform may be invisible on the other.

## Debugging

### Log files

The watch server logs to a file under the OS cache directory:
- **Linux**: `~/.cache/subspy/`
- **macOS**: `~/Library/Caches/subspy/`
- **Windows**: `%LocalAppData%/subspy/` (typically `C:\Users\<user>\AppData\Local\subspy\`)

The default log level is `info`. For more detail, start the server with
`--log-level trace` (or `debug`). Client commands log to stderr at `warn` by default.

To watch logs in real time while reproducing an issue:

```sh
subspy start /path/to/repo --foreground --log-level trace 2>&1
# In another terminal, perform the operation that triggers the bug
```

### `subspy debug`

Dumps the server's live internal state: watcher list with pending event counts,
skip set (submodules paused during rebase), in-flight rayon tasks, progress
subscribers, cached submodule statuses, and the last watcher error. This is the
first thing to check when the server reports incorrect status.

```sh
subspy debug
```

### Isolating a status mismatch

When `subspy status` shows wrong output, the first step is figuring out *where* the
mismatch is: the server's cached state, the event pipeline, or the display logic.

1. **Compare against git ground truth**: Run `subspy status --no-server` (uses libgit2
   directly) and `git status` side by side. If `--no-server` matches git but the server
   doesn't, the bug is in the server's event handling or status caching.
2. **Check the server's cached state**: Run `subspy debug` and look at the "Submodule
   statuses" section. If the cached flags are correct but `subspy status` displays them
   wrong, the bug is in `status.rs` display logic.
3. **Try a reindex**: `subspy reindex` rebuilds the status map from scratch without
   restarting the server. If this fixes the issue, the server missed or misclassified a
   filesystem event. Check the log file for watcher errors.
4. **Full restart**: `subspy stop` followed by a fresh `subspy status` (which auto-spawns
   a new server). If even this doesn't fix it, the bug is likely in the initial
   `populate_status_map` or in `submodule_status` itself.
5. **Check for pending events**: In `subspy debug` output, watchers with high pending
   event counts suggest the server is falling behind on processing, which can cause
   temporarily stale status.

### Fuzzer for reproducing race conditions

If a bug only manifests under specific timing, the fuzzer's `--seed` flag reproduces
the exact operation sequence. On failure it prints the seed, repo path (preserved for
inspection), and full `subspy debug` output. Use `--pause-on-failure` to keep the
server alive for manual investigation.
