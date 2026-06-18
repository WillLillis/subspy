//! Structured event tracing for the watch server.
//!
//! In a normal build this module is almost nothing: [`wtrace!`] expands to `{}`
//! and [`spawn_submod_task`] is a thin passthrough to `rayon::spawn`. Only
//! `--cfg trace_events` turns the machinery on,.
//!
//! # What it captures
//!
//! Every watch-server `wtrace!` site records a structured [`TraceEvent`].
//! Formatting (and any `Debug`/`Display` work) is deferred to drain time, off
//! the hot path. String and path fields are interned to `Arc<OsStr>` so the
//! same repeated paths (`index.lock`, `index`, the per-submodule metadata paths)
//! under an event burst cost one allocation the first time and a refcount bump
//! on every repeat.
//!
//! # Concurrency
//!
//! The event loop is the dominant producer; rayon workers (the submodule
//! re-reads) are occasional ones. Each thread accumulates into its OWN buffer
//! (and its own interner) via a [`thread_local::ThreadLocal`], so no two
//! threads ever share a synchronization primitive on the hot path. . A single
//! consumer drains every per-thread buffer at the end, after the server has been
//! shut down and joined (producers quiesced), then merges and sorts by timestamp
//! into one coherent timeline.
//!
//! # Lifecycle (tests)
//!
//! [`capture_for`] is called on the server thread before `watch()`; it installs
//! a sink on that thread and registers it by repo root. On test teardown the
//! harness calls [`dump_for`] (failure: write the trace to stderr, where
//! `libtest` attributes it to the failing test) or [`discard_for`] (success).

/// Records a structured [`TraceEvent`] for the watch server in builds made with
/// `--cfg trace_events`; otherwise expands to nothing and never evaluates its
/// arguments.
///
/// Three forms:
/// - `wtrace!(UnitVariant)` for payload-free events.
/// - `wtrace!(Variant { field: expr, .. })` for events with no interned strings.
/// - `wtrace!(|s| Variant { field: s.intern_str(..), .. })` to intern string or
///   path fields through the per-thread interner `s`.
#[cfg(trace_events)]
macro_rules! wtrace {
    (|$interner:ident| $variant:ident $($body:tt)*) => {
        $crate::connection::watch_server::trace::emit(
            |$interner| $crate::connection::watch_server::trace::TraceEvent::$variant $($body)*
        )
    };
    ($variant:ident { $($body:tt)* }) => {
        $crate::connection::watch_server::trace::emit(
            |_| $crate::connection::watch_server::trace::TraceEvent::$variant { $($body)* }
        )
    };
    ($variant:ident) => {
        $crate::connection::watch_server::trace::emit(
            |_| $crate::connection::watch_server::trace::TraceEvent::$variant
        )
    };
}
// Tracing disabled: drop the argument unevaluated. See the definition above.
#[cfg(not(trace_events))]
macro_rules! wtrace {
    ($($t:tt)*) => {};
}
pub(crate) use wtrace;

/// Spawns a submodule-update task onto rayon's global pool.
///
/// In a `trace_events` build this also propagates the current thread's trace
/// sink onto the worker, since rayon workers do not inherit thread-locals and
/// the pool is shared across tests. In a normal build it is exactly
/// `rayon::spawn`.
#[cfg_attr(not(trace_events), inline)]
pub(super) fn spawn_submod_task(task: impl FnOnce() + Send + 'static) {
    #[cfg(not(trace_events))]
    rayon::spawn(task);

    #[cfg(trace_events)]
    {
        // Capture this thread's sink so the pooled worker traces into the same
        // per-test buffers; cleared after the task so a finished test's sink is
        // not pinned into the next, unrelated task this worker happens to run.
        let sink = SINK.with(|s| s.borrow().clone());
        rayon::spawn(move || {
            if let Some(sink) = sink {
                install_on_current_thread(sink);
            }
            task();
            SINK.with(|s| *s.borrow_mut() = None);
        });
    }
}

#[cfg(trace_events)]
use std::{
    cell::RefCell,
    ffi::OsStr,
    fmt,
    path::{Path, PathBuf},
    sync::{Arc, LazyLock, Mutex, MutexGuard, PoisonError},
    time::Instant,
};

#[cfg(trace_events)]
use git2::{ErrorClass, ErrorCode};
#[cfg(trace_events)]
use notify::EventKind;
#[cfg(trace_events)]
use rustc_hash::{FxHashMap, FxHashSet};
#[cfg(trace_events)]
use thread_local::ThreadLocal;

#[cfg(trace_events)]
use super::classify::EventType;
#[cfg(trace_events)]
use super::debounce::DebounceKind;
#[cfg(trace_events)]
use crate::StatusSummary;

/// A single structured watch-server trace event. Stores cheap owned data
/// (scalars by value, strings/paths as interned `Arc<OsStr>`).
#[cfg(trace_events)]
pub(super) enum TraceEvent {
    /// A raw filesystem event was classified (`classify`).
    Classified {
        index: usize,
        rel: Arc<OsStr>,
        kind: EventKind,
        paths: Vec<Arc<OsStr>>,
        result: Option<EventType>,
    },
    /// A submodule workdir watch could not be armed because the dir was absent.
    WatchDisarmed { path: Arc<OsStr> },
    /// A non-recursive tripwire watch was placed on an ancestor directory.
    TripwirePlaced { path: Arc<OsStr> },
    /// The deferred-reindex debounce window expired; a reindex will run.
    ReindexExpired,
    /// A debounced reindex deadline was (re)armed; the reindex runs once the
    /// window elapses without further events. `kind` says which debounce.
    ReindexDeferred {
        kind: DebounceKind,
        deadline: Option<Instant>,
    },
    /// A tripwire event matched a submodule (or submodules) under a directory.
    TripwireFired {
        kind: EventKind,
        rel: Arc<OsStr>,
        idx: usize,
        reindex: bool,
    },
    /// A submodule status re-read succeeded.
    ReReadOk {
        rel: Arc<OsStr>,
        status: StatusSummary,
    },
    /// A submodule status re-read failed (transient lock/IO contention).
    ReReadFailed {
        rel: Arc<OsStr>,
        code: ErrorCode,
        class: ErrorClass,
        msg: Arc<OsStr>,
    },
    /// (Re)indexing started over `n` submodules.
    Reindexing { n: u32, place_watches: bool },
    /// A submodule workdir watch was placed during indexing.
    WatchSubmod { index: usize, path: Arc<OsStr> },
}

#[cfg(trace_events)]
impl fmt::Display for TraceEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Classified {
                index,
                rel,
                kind,
                paths,
                result,
            } => {
                write!(f, "watcher[{index}] ({}) {kind:?} ", rel.to_string_lossy())?;
                f.debug_list()
                    .entries(paths.iter().map(Path::new))
                    .finish()?;
                write!(f, " -> {result:?}")
            }
            Self::WatchDisarmed { path } => write!(
                f,
                "submod workdir {} absent; watch left disarmed",
                Path::new(path).display()
            ),
            Self::TripwirePlaced { path } => {
                write!(f, "tripwire {}", Path::new(path).display())
            }
            Self::ReindexExpired => f.write_str("reindex debounce expired -> reindexing"),
            Self::ReindexDeferred { kind, deadline } => {
                write!(f, "deferring {kind:?} reindex -> deadline {deadline:?}")
            }
            Self::TripwireFired {
                kind,
                rel,
                idx,
                reindex,
            } => write!(
                f,
                "tripwire {kind:?} {} -> submod[{idx}] (reindex={reindex})",
                Path::new(rel).display()
            ),
            Self::ReReadOk { rel, status } => {
                write!(f, "re-read {} -> {status:?}", rel.to_string_lossy())
            }
            Self::ReReadFailed {
                rel,
                code,
                class,
                msg,
            } => write!(
                f,
                "re-read {} FAILED -> code={code:?} class={class:?} msg={}",
                rel.to_string_lossy(),
                msg.to_string_lossy()
            ),
            Self::Reindexing { n, place_watches } => {
                write!(
                    f,
                    "(re)indexing {n} submodules (place_watches={place_watches})"
                )
            }
            Self::WatchSubmod { index, path } => {
                write!(f, "watch submod[{index}] {}", Path::new(path).display())
            }
        }
    }
}

/// A per-thread string/path interner returning `Arc<OsStr>`.
///
/// Lives inside a [`ThreadBuf`], so it is touched by exactly one thread and needs
/// no synchronization of its own.
#[cfg(trace_events)]
#[derive(Default)]
pub(super) struct Interner {
    seen: FxHashSet<Arc<OsStr>>,
}

#[cfg(trace_events)]
impl Interner {
    fn intern(&mut self, s: &OsStr) -> Arc<OsStr> {
        if let Some(existing) = self.seen.get(s) {
            return Arc::clone(existing);
        }
        let interned: Arc<OsStr> = Arc::from(s);
        self.seen.insert(Arc::clone(&interned));
        interned
    }

    /// Interns a UTF-8 string (e.g. a submodule relative path, an error message).
    pub(super) fn intern_str(&mut self, s: &str) -> Arc<OsStr> {
        self.intern(OsStr::new(s))
    }

    /// Interns a path losslessly
    pub(super) fn intern_path(&mut self, p: &Path) -> Arc<OsStr> {
        self.intern(p.as_os_str())
    }
}

/// One thread's accumulated trace records plus its interner. Created lazily the
/// first time a thread emits into a given sink.
#[cfg(trace_events)]
struct ThreadBuf {
    label: String,
    interner: Interner,
    records: Vec<(Instant, TraceEvent)>,
}

#[cfg(trace_events)]
impl ThreadBuf {
    fn new() -> Self {
        let current = std::thread::current();
        let label = current
            .name()
            .map_or_else(|| format!("{:?}", current.id()), ToString::to_string);
        Self {
            label,
            interner: Interner::default(),
            records: Vec::new(),
        }
    }
}

/// A capture sink: one per server (per test). Holds a per-thread buffer for
/// every thread that emits into it; drained once at the end.
#[cfg(trace_events)]
struct TraceSink {
    start: Instant,
    buffers: ThreadLocal<Mutex<ThreadBuf>>,
}

#[cfg(trace_events)]
impl TraceSink {
    fn new() -> Self {
        Self {
            start: Instant::now(),
            buffers: ThreadLocal::new(),
        }
    }

    /// This thread's buffer, creating it on first use. The mutex is per-thread,
    /// so it is uncontended on the hot path (only this thread pushes; the drain
    /// locks it once, after all producers have stopped).
    fn buffer_for_current_thread(&self) -> MutexGuard<'_, ThreadBuf> {
        self.buffers
            .get_or(|| Mutex::new(ThreadBuf::new()))
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// Merges every per-thread buffer, sorts by timestamp, and writes the
    /// timeline to stderr under `label`. Call only after producers have
    /// quiesced (server thread joined).
    fn dump(&self, label: &str) {
        let mut lines: Vec<(Instant, String)> = Vec::new();
        for cell in &self.buffers {
            let (thread_label, records) = {
                let mut buf = cell.lock().unwrap_or_else(PoisonError::into_inner);
                (
                    std::mem::take(&mut buf.label),
                    std::mem::take(&mut buf.records),
                )
            };
            for (at, event) in &records {
                lines.push((*at, format!("[{thread_label}] {event}")));
            }
        }
        lines.sort_by_key(|&(at, _)| at);

        eprintln!(
            "==== subspy watch-server trace [{label}] ({} events) ====",
            lines.len()
        );
        for (at, line) in &lines {
            let us = at.saturating_duration_since(self.start).as_micros();
            eprintln!("+{us:>9}us {line}");
        }
        eprintln!("==== end trace [{label}] ====");
    }
}

#[cfg(trace_events)]
thread_local! {
    /// The sink installed on the current thread, if any. `wtrace!` routes here;
    /// absent on threads we did not install on (then [`emit`] live-prints, which
    /// is the manual-daemon / fuzzer path).
    static SINK: RefCell<Option<Arc<TraceSink>>> = const { RefCell::new(None) };
}

/// Records a trace event on the current thread. The builder closure is handed
/// this thread's interner and only runs when a sink is installed (or, with no
/// sink, when we live-print) -- so the interning/cloning never happens off-CI.
#[cfg(trace_events)]
pub(super) fn emit(build: impl FnOnce(&mut Interner) -> TraceEvent) {
    SINK.with(|slot| {
        if let Some(sink) = slot.borrow().as_ref() {
            let at = Instant::now();
            let mut buf = sink.buffer_for_current_thread();
            let event = build(&mut buf.interner);
            buf.records.push((at, event));
        } else {
            // No sink: live print (manual `--cfg trace_events` daemon / fuzzer).
            let mut scratch = Interner::default();
            eprintln!("[subspy] {}", build(&mut scratch));
        }
    });
}

#[cfg(trace_events)]
fn install_on_current_thread(sink: Arc<TraceSink>) {
    SINK.with(|slot| *slot.borrow_mut() = Some(sink));
}

/// Maps a repo root to its sink, so the test harness (a different thread than
/// the server) can find and drain the capture by root path alone.
#[cfg(trace_events)]
static REGISTRY: LazyLock<Mutex<FxHashMap<PathBuf, Arc<TraceSink>>>> =
    LazyLock::new(|| Mutex::new(FxHashMap::default()));

/// Begins capturing watch-server traces for the server rooted at `root`, on the
/// CURRENT thread. Call from the server thread before `watch()`.
#[cfg(trace_events)]
pub fn capture_for(root: &Path) {
    let sink = Arc::new(TraceSink::new());
    install_on_current_thread(Arc::clone(&sink));
    REGISTRY
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .insert(root.to_path_buf(), sink);
}

/// Writes the captured trace for `root` to stderr under `label`, then discards
/// it. Call on test teardown when the test failed, after the server thread has
/// been joined.
#[cfg(trace_events)]
pub fn dump_for(root: &Path, label: &str) {
    let sink = REGISTRY
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .remove(root);
    if let Some(sink) = sink {
        sink.dump(label);
    }
}

/// Discards the captured trace for `root` without printing (passing test).
#[cfg(trace_events)]
pub fn discard_for(root: &Path) {
    REGISTRY
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .remove(root);
}
