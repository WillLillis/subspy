//! Debounced-reindex deadline tracking for the watch server.
//!
//! Some filesystem events don't call for an immediate reindex but for one
//! *after* the dust settles. A `.gitmodules` edit kicks off a burst of
//! index/ref events from the same git operation, and a structural change to a
//! submodule workdir (a `rm -rf` then a re-checkout) likewise arrives as a
//! burst. Reindexing mid-burst reads a transient state and performs needless
//! work. [`ReindexDebounce`] defers the reindex until the burst goes quiet.

use std::time::{Duration, Instant};

use super::trace::wtrace;

/// Debounce window for a deferred reindex: the reindex fires once no further
/// filesystem event has arrived for this long. Sized to outlast the inter-event
/// gaps within a single git operation's burst, so the reindex reads the
/// operation's settled state rather than a mid-flight one.
const REINDEX_DEBOUNCE: Duration = Duration::from_millis(200);

/// Identifies the source of a [`ReindexDebounce`] in a `cfg(trace_events)` [`wtrace!`]
/// traces.
#[derive(Clone, Copy, Debug)]
pub(super) enum DebounceKind {
    /// Armed by a `.gitmodules` change, bumped by root git events.
    Gitmodules,
    /// Armed by a structural tripwire change, bumped by tripwire and root git events.
    Structural,
}

/// A debounced reindex deadline.
///
/// - [`arm`](Self::arm) starts the window
/// - [`bump`](Self::bump) pushes it out but only while already armed
///
/// The owning event loop reads [`deadline`](Self::deadline) to drive a
/// `select_deadline` and reindexes when it elapses.
pub(super) struct ReindexDebounce {
    deadline: Option<Instant>,
    /// Trace attribution only used by [`wtrace!`] under `cfg(trace_events)`
    #[cfg_attr(not(trace_events), allow(dead_code))]
    kind: DebounceKind,
}

impl ReindexDebounce {
    #[inline]
    pub(super) const fn new(kind: DebounceKind) -> Self {
        Self {
            deadline: None,
            kind,
        }
    }

    /// The current deadline, or `None` when no reindex is pending.
    #[inline]
    pub(super) const fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// Starts (or restarts) the debounce window. Use when an event first calls
    /// for a deferred reindex.
    #[inline]
    pub(super) fn arm(&mut self) {
        self.set();
    }

    /// Pushes the deadline out by another window, but only if one is already
    /// armed.
    #[inline]
    pub(super) fn bump(&mut self) {
        if self.deadline.is_some() {
            self.set();
        }
    }

    #[inline]
    fn set(&mut self) {
        self.deadline = Some(Instant::now() + REINDEX_DEBOUNCE);
        wtrace!(ReindexDeferred {
            kind: self.kind,
            deadline: self.deadline,
        });
    }
}

/// Returns the earlier of two optional deadlines (or `None` if both are absent).
pub(super) fn earliest_deadline(a: Option<Instant>, b: Option<Instant>) -> Option<Instant> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}
