//! A compact bitset optimized for small dense integer sets.
//!
//! Uses an inline `[u64; 8]` (512 bits, one cache line) for the common case (up
//! to 510 submodules. Falls back to a heap-allocated `Vec<u64>` for larger repos.

/// A compact bitset for tracking small dense integer sets (watcher indices).
///
/// All accesses use unchecked indexing since callers control the index range
/// (watcher indices are bounded by the watchers array length).
#[derive(Debug)]
pub enum BitSet {
    Inline([u64; Self::INLINE_WORDS]),
    /// Overflow storage for repos with > `INLINE_WORDS * 64` indices.
    /// Empty when the inline buffer suffices.
    Heap(Vec<u64>),
}

impl BitSet {
    const INLINE_WORDS: usize = 8; // 512 bits = 1 cache line

    #[inline]
    #[must_use]
    pub fn with_capacity(n: usize) -> Self {
        let needed = n.div_ceil(64);
        if needed <= Self::INLINE_WORDS {
            Self::Inline([0; Self::INLINE_WORDS])
        } else {
            Self::Heap(vec![0; needed])
        }
    }

    /// Returns a slice over the active word array (inline or overflow).
    #[inline]
    fn words(&self) -> &[u64] {
        match self {
            Self::Inline(buf) => buf,
            Self::Heap(buf) => buf,
        }
    }

    /// Returns a mutable slice over the active word array (inline or overflow).
    #[inline]
    fn words_mut(&mut self) -> &mut [u64] {
        match self {
            Self::Inline(buf) => buf,
            Self::Heap(buf) => buf,
        }
    }

    /// Returns whether the bit at index `i` is set.
    ///
    /// Safety:
    ///
    /// `i` must be less than the capacity of `self`.
    #[inline]
    #[must_use]
    pub fn contains(&self, i: usize) -> bool {
        // SAFETY: callers only pass watcher indices, which are bounded by the
        // capacity established in `with_capacity` / `clear_and_resize`.
        unsafe { *self.words().get_unchecked(i / 64) & (1u64 << (i % 64)) != 0 }
    }

    /// Set the bit at index `i`.
    ///
    /// Safety:
    ///
    /// `i` must be less than the capacity of `self`.
    #[inline]
    pub fn insert(&mut self, i: usize) {
        // SAFETY: same as `contains`
        unsafe { *self.words_mut().get_unchecked_mut(i / 64) |= 1u64 << (i % 64) }
    }

    /// Removes `i` from the set. Returns `true` if it was present.
    #[inline]
    pub fn remove(&mut self, i: usize) -> bool {
        // SAFETY: same as `contains`
        unsafe {
            let word = self.words_mut().get_unchecked_mut(i / 64);
            let mask = 1u64 << (i % 64);
            let was_set = *word & mask != 0;
            *word &= !mask;
            was_set
        }
    }

    /// Clears all bits and ensures capacity for at least `n` indices.
    #[inline]
    pub fn clear_and_resize(&mut self, n: usize) {
        let needed = n.div_ceil(64);
        if needed <= Self::INLINE_WORDS {
            if let Self::Inline(buf) = self {
                buf.fill(0);
            } else {
                *self = Self::Inline([0; Self::INLINE_WORDS]);
            }
        } else {
            if let Self::Heap(buf) = self {
                buf.resize(needed, 0);
                buf.fill(0);
            } else {
                *self = Self::Heap(vec![0; needed]);
            }
        }
    }

    /// Iterates over the indices of all set bits. Skips zero words entirely
    /// and uses `trailing_zeros()` within each word to jump to set bits.
    #[inline]
    #[must_use]
    #[expect(clippy::iter_without_into_iter, reason = "YAGNI")]
    pub fn iter(&self) -> BitSetIter<'_> {
        let data = self.words();
        BitSetIter {
            data,
            word_idx: 0,
            current_word: data.first().copied().unwrap_or(0),
        }
    }
}

pub struct BitSetIter<'a> {
    data: &'a [u64],
    word_idx: usize,
    current_word: u64,
}

impl Iterator for BitSetIter<'_> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        while self.current_word == 0 {
            self.word_idx += 1;
            if self.word_idx >= self.data.len() {
                return None;
            }
            self.current_word = self.data[self.word_idx];
        }
        let bit = self.current_word.trailing_zeros() as usize;
        self.current_word &= self.current_word - 1; // clear lowest set bit
        Some(self.word_idx * 64 + bit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_bitset() {
        let bs = BitSet::with_capacity(64);
        assert!(!bs.contains(0));
        assert!(!bs.contains(63));
        assert!(bs.iter().next().is_none());
    }

    #[test]
    fn insert_and_contains() {
        let mut bs = BitSet::with_capacity(256);
        bs.insert(0);
        bs.insert(42);
        bs.insert(255);
        assert!(bs.contains(0));
        assert!(bs.contains(42));
        assert!(bs.contains(255));
        assert!(!bs.contains(1));
        assert!(!bs.contains(41));
        assert!(!bs.contains(128));
    }

    #[test]
    fn remove_returns_presence() {
        let mut bs = BitSet::with_capacity(64);
        bs.insert(10);
        assert!(bs.remove(10));
        assert!(!bs.remove(10));
        assert!(!bs.contains(10));
    }

    #[test]
    fn clear_and_resize_resets_all() {
        let mut bs = BitSet::with_capacity(128);
        bs.insert(5);
        bs.insert(100);
        bs.clear_and_resize(128);
        assert!(!bs.contains(5));
        assert!(!bs.contains(100));
        assert!(bs.iter().next().is_none());
    }

    #[test]
    fn clear_and_resize_grows() {
        let mut bs = BitSet::with_capacity(64);
        bs.insert(10);
        bs.clear_and_resize(1024);
        assert!(!bs.contains(10));
        // Should be able to use indices in the new range
        bs.insert(900);
        assert!(bs.contains(900));
    }

    #[test]
    fn iter_yields_set_bits_in_order() {
        let mut bs = BitSet::with_capacity(256);
        bs.insert(200);
        bs.insert(5);
        bs.insert(130);
        bs.insert(63);
        bs.insert(64);
        let indices: Vec<usize> = bs.iter().collect();
        assert_eq!(indices, vec![5, 63, 64, 130, 200]);
    }

    #[test]
    fn word_boundary_bits() {
        let mut bs = BitSet::with_capacity(256);
        // Test bits at word boundaries
        bs.insert(63); // last bit of word 0
        bs.insert(64); // first bit of word 1
        bs.insert(127); // last bit of word 1
        bs.insert(128); // first bit of word 2
        assert!(bs.contains(63));
        assert!(bs.contains(64));
        assert!(bs.contains(127));
        assert!(bs.contains(128));
        assert!(!bs.contains(62));
        assert!(!bs.contains(65));
    }

    #[test]
    fn overflow_to_heap() {
        // Force heap allocation (> 512 bits)
        let mut bs = BitSet::with_capacity(1024);
        bs.insert(600);
        bs.insert(999);
        assert!(bs.contains(600));
        assert!(bs.contains(999));
        assert!(!bs.contains(601));
        let indices: Vec<usize> = bs.iter().collect();
        assert_eq!(indices, vec![600, 999]);
    }

    #[test]
    fn overflow_clear_and_resize_back_to_inline() {
        let mut bs = BitSet::with_capacity(1024);
        bs.insert(600);
        // Shrink back to inline range
        bs.clear_and_resize(256);
        assert!(!bs.contains(5));
        bs.insert(5);
        assert!(bs.contains(5));
    }
}
