//! Debounced-reindex deadline tracking for the watch server.
//!
//! Some filesystem events don't call for an immediate reindex but for one
//! *after* the dust settles. A `.gitmodules` edit kicks off a burst of
//! index/ref events from the same git operation, and a structural change to a
//! submodule workdir (a `rm -rf` then a re-checkout) likewise arrives as a
//! burst. Reindexing mid-burst reads a transient state and, because the reindex
//! acquires each submodule's `index.lock`, contends with the very operation
//! that triggered it. [`ReindexDebounce`] defers the reindex until the burst
//! goes quiet.
//!
//! The two callers differ only in *which* events they feed in. The `.gitmodules`
//! tracker is bumped by root git events, the structural tracker by every event
//! root git events and tripwire events.

use std::time::{Duration, Instant};

use super::trace::wtrace;

/// Debounce window for a deferred reindex: the reindex fires once no further
/// filesystem event has arrived for this long. Sized to outlast the inter-event
/// gaps within a single git operation's burst, so the reindex reads the
/// operation's settled state rather than a mid-flight one.
const REINDEX_DEBOUNCE: Duration = Duration::from_millis(200);

/// Which debounce a [`ReindexDebounce`] is. Both share one type and identical
/// deadline mechanics; this only attributes trace lines to the right one.
#[derive(Clone, Copy, Debug)]
pub(super) enum DebounceKind {
    /// Armed by a `.gitmodules` change, bumped by root git events.
    Gitmodules,
    /// Armed by a structural tripwire change, bumped by every event.
    Structural,
}

/// A debounced reindex deadline.
///
/// [`arm`](Self::arm) starts the window; [`bump`](Self::bump) pushes it out but
/// only while already armed, so feeding events to an unarmed tracker is a
/// no-op. The owning event loop reads [`deadline`](Self::deadline) to drive a
/// `select_deadline` and reindexes when it elapses.
pub(super) struct ReindexDebounce {
    deadline: Option<Instant>,
    /// Trace attribution only; read solely by `wtrace!` under
    /// `--cfg trace_events`.
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
    /// for a deferred reindex: a `.gitmodules` change, or a structural tripwire.
    #[inline]
    pub(super) fn arm(&mut self) {
        self.set();
    }

    /// Pushes the deadline out by another window, but only if one is already
    /// armed -- subsequent activity should keep the window open until things
    /// settle, but must not itself start a reindex. A no-op when unarmed, which
    /// is what stops an ordinary git op from arming the `.gitmodules` tracker.
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

/// Returns the earlier of two optional deadlines (the soonest concrete one, or
/// `None` if both are absent). The event loop selects on whichever debounce
/// fires first.
pub(super) fn earliest_deadline(a: Option<Instant>, b: Option<Instant>) -> Option<Instant> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bump_is_a_noop_when_unarmed() {
        // The load-bearing distinction the old state machine's `Idle` arm
        // encoded: events seen while no reindex is pending must not arm one.
        // This is what keeps an ordinary commit/checkout from triggering a full
        // reindex via the root-event-fed `.gitmodules` tracker.
        let mut d = ReindexDebounce::new(DebounceKind::Structural);
        d.bump();
        assert!(d.deadline().is_none());
    }

    #[test]
    fn bump_extends_an_armed_deadline() {
        let mut d = ReindexDebounce::new(DebounceKind::Structural);
        d.arm();
        let first = d.deadline().expect("armed");
        d.bump();
        let second = d.deadline().expect("still armed");
        assert!(second >= first);
    }

    #[test]
    fn earliest_deadline_picks_the_sooner_or_only_one() {
        let earlier = Instant::now();
        let later = earlier + Duration::from_secs(1);
        assert_eq!(earliest_deadline(None, None), None);
        assert_eq!(earliest_deadline(Some(earlier), None), Some(earlier));
        assert_eq!(earliest_deadline(None, Some(later)), Some(later));
        assert_eq!(earliest_deadline(Some(later), Some(earlier)), Some(earlier));
        assert_eq!(earliest_deadline(Some(earlier), Some(later)), Some(earlier));
    }
}
