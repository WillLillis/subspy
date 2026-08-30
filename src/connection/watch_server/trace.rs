//! Structured watch-server tracing enabled by `cfg(trace_events)`.
//!
//! Trace sites record [`TraceEvent`] values in per-thread buffers with local
//! string and path interning. Captures are merged, timestamp-sorted, and
//! formatted when drained by the test harness.
//!
//! In regular builds, [`wtrace!`] expands without evaluating its arguments and
//! [`spawn_submod_task`] delegates directly to `rayon::spawn`.

/// Records a [`TraceEvent`] for the watch server in `cfg(trace_events)` builds.
/// In regular builds, [`wtrace!`] expands to nothing and never evaluates its
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

/// Discards the invocation without evaluating its arguments.
#[cfg(not(trace_events))]
macro_rules! wtrace {
    ($($t:tt)*) => {};
}
pub(crate) use wtrace;

/// Spawns a submodule-update task onto rayon's global pool.
///
/// In a `cfg(trace_events)` build this also propagates the current thread's trace
/// sink onto the worker, since rayon workers do not inherit thread-locals and
/// the pool is shared across tests. In a normal build it is exactly
/// `rayon::spawn`.
#[cfg_attr(not(trace_events), inline)]
pub(super) fn spawn_submod_task(task: impl FnOnce() + Send + 'static) {
    #[cfg(not(trace_events))]
    rayon::spawn(task);

    #[cfg(trace_events)]
    {
        // Install the caller's trace sink on the pooled worker and clear it after
        // the task.
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

/// A single watch server trace event.
#[cfg(trace_events)]
pub(super) enum TraceEvent {
    /// A raw filesystem event was classified.
    Classified {
        index: usize,
        rel: Arc<OsStr>,
        kind: EventKind,
        paths: Vec<Arc<OsStr>>,
        result: Option<EventType>,
    },
    /// A submodule watch has no registered paths.
    WatchUnregistered { path: Arc<OsStr> },
    /// A non-recursive tripwire watch was placed on an ancestor directory.
    TripwirePlaced { path: Arc<OsStr> },
    /// The deferred-reindex debounce window expired. A reindex will run.
    ReindexExpired,
    /// A debounced reindex deadline was (re)armed. The reindex runs once the
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
    /// A submodule status re-read failed.
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
            Self::WatchUnregistered { path } => write!(
                f,
                "submod watch for {} has no registered paths",
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

    /// Interns a path losslessly.
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

/// A per-server capture sink holding one buffer for each producer thread.
/// The test harness drains it after the server finishes.
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

    /// Returns the current thread's buffer, creating it on first use.
    fn buffer_for_current_thread(&self) -> MutexGuard<'_, ThreadBuf> {
        self.buffers
            .get_or(|| Mutex::new(ThreadBuf::new()))
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// Merges every per-thread buffer, sorts by timestamp, and writes the
    /// timeline to stderr under `label`. Call only after producers have
    /// finished (server thread joined).
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
    /// The sink installed on the current thread. [`emit`] records events into it
    /// when present and prints them directly otherwise. Direct printing supports
    /// manual daemon runs.
    static SINK: RefCell<Option<Arc<TraceSink>>> = const { RefCell::new(None) };
}

/// Records a trace event on the current thread.
#[cfg(trace_events)]
pub(super) fn emit(build: impl FnOnce(&mut Interner) -> TraceEvent) {
    SINK.with(|slot| {
        if let Some(sink) = slot.borrow().as_ref() {
            let at = Instant::now();
            let mut buf = sink.buffer_for_current_thread();
            let event = build(&mut buf.interner);
            buf.records.push((at, event));
        } else {
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

/// Begins capturing watch server traces for `root` on the calling thread.
/// Call from the server thread before `watch()`.
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
