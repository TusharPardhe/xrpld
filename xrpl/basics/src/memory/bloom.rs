//! A blocked Bloom filter for node-store key membership testing.
//!
//! # What this is
//!
//! A Bloom filter is a compact, probabilistic set membership structure. It
//! answers one question: *"might this key be in the set?"* with two possible
//! verdicts:
//!
//! - [`Membership::DefinitelyAbsent`] — the key is guaranteed **not** present.
//! - [`Membership::PossiblyPresent`] — the key **might** be present (or this is
//!   a false positive).
//!
//! Crucially, a Bloom filter never produces a false negative: if a key was
//! inserted, [`BloomFilter::probe`] will always return
//! [`Membership::PossiblyPresent`] for it. Only false *positives* are possible,
//! and their rate is bounded by the configured bits-per-key.
//!
//! This property makes the filter safe as a *skip gate* in front of expensive
//! lookups: a `DefinitelyAbsent` verdict can be trusted to skip the real
//! lookup entirely, while `PossiblyPresent` falls through to the authoritative
//! store read (exactly what would have happened without the filter).
//!
//! # Why "blocked"
//!
//! A classic Bloom filter scatters each key's `k` bits across the entire bit
//! array, so a single probe touches `k` random cache lines. A *blocked* Bloom
//! filter first hashes the key to one fixed-size block (one cache line) and
//! sets/tests all `k` bits within that single block. This keeps each insert or
//! probe to one cache line, which matters on the hot node-store paths.
//!
//! # Node-store keys
//!
//! Node-store keys are 256-bit cryptographic hashes ([`Uint256`]). Because the
//! key material is already uniformly distributed, we do not run a general
//! purpose hash function; we derive the block index and the `k` in-block bit
//! positions directly from disjoint slices of the key using cheap mixing. This
//! is standard practice for hash-keyed Bloom filters.

use crate::base_uint::Uint256;
use std::sync::atomic::{AtomicU64, Ordering};

/// One block is 512 bits = 64 bytes = one common cache line. Each key's bits
/// are confined to a single block for cache locality.
const BLOCK_BITS: usize = 512;
const BLOCK_WORDS: usize = BLOCK_BITS / 64;

/// The result of a membership probe.
///
/// See the module documentation for the false-positive / no-false-negative
/// guarantee that makes [`Membership::DefinitelyAbsent`] safe to act on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Membership {
    /// The key was never inserted. Guaranteed correct: safe to skip the real
    /// lookup.
    DefinitelyAbsent,
    /// The key might have been inserted. May be a false positive; the caller
    /// must perform the authoritative lookup to be sure.
    PossiblyPresent,
}

/// A concurrent, fixed-capacity blocked Bloom filter keyed by [`Uint256`].
///
/// Inserts are lock-free atomic bit sets; probes are lock-free atomic loads.
/// A probe that races a concurrent insert may miss a just-set bit and return
/// [`Membership::PossiblyPresent`] via fall-through only in the safe direction:
/// it can never wrongly claim `DefinitelyAbsent` for a key whose bits are fully
/// set, because bit sets use `fetch_or` with `Release`/`Acquire` ordering.
///
/// The filter is sized once at construction from an expected key count and a
/// bits-per-key budget; it does not grow. Inserting well beyond the planned
/// capacity raises the false-positive rate but never affects correctness.
pub struct BloomFilter {
    /// Backing bit array, addressed as 64-bit words. Length is a multiple of
    /// [`BLOCK_WORDS`].
    words: Box<[AtomicU64]>,
    /// Number of 512-bit blocks (`words.len() / BLOCK_WORDS`).
    block_count: usize,
    /// Number of bit probes per key (`k`).
    hashes: u32,
}

impl BloomFilter {
    /// Builds a filter sized for `expected_keys` at approximately
    /// `bits_per_key` bits each.
    ///
    /// - `expected_keys`: planned number of distinct keys. A value of zero is
    ///   clamped to one so the filter always has at least one block.
    /// - `bits_per_key`: memory/accuracy trade-off. Ten bits per key yields an
    ///   approximate 1% false-positive rate with the derived optimal `k`.
    ///   Clamped to the range `[4, 20]`.
    ///
    /// The optimal number of hashes is `k = round(bits_per_key * ln 2)`,
    /// clamped to a value that fits inside a single 512-bit block.
    pub fn with_capacity(expected_keys: usize, bits_per_key: usize) -> Self {
        let expected = expected_keys.max(1);
        let bpk = bits_per_key.clamp(4, 20);

        // Total bits requested, rounded up to a whole number of blocks.
        let total_bits = expected.saturating_mul(bpk).max(BLOCK_BITS);
        let block_count = total_bits.div_ceil(BLOCK_BITS).max(1);
        let word_count = block_count * BLOCK_WORDS;

        // k = bits_per_key * ln(2), rounded to nearest, clamped to [1, 16].
        // The upper clamp keeps every probe inside one block comfortably.
        let hashes = ((bpk as f64) * std::f64::consts::LN_2).round().clamp(1.0, 16.0) as u32;

        let mut words = Vec::with_capacity(word_count);
        words.resize_with(word_count, || AtomicU64::new(0));

        Self {
            words: words.into_boxed_slice(),
            block_count,
            hashes,
        }
    }

    /// Returns the resident heap size of the bit array in bytes. Useful for
    /// reporting and for deciding when to evict a transient filter.
    pub fn memory_bytes(&self) -> usize {
        self.words.len() * std::mem::size_of::<u64>()
    }

    /// Returns the configured number of bit probes per key (`k`).
    pub fn hashes(&self) -> u32 {
        self.hashes
    }

    /// Derives the base hash pair for a key.
    ///
    /// The node-store key is already a 256-bit cryptographic hash, so its bytes
    /// are uniformly distributed. We read two disjoint 64-bit little-endian
    /// words from the key and mix each with a `splitmix64` finalizer to
    /// decorrelate them. `h1` selects the block; `(h1, h2)` seed the
    /// double-hashing scheme `g_i = h1 + i*h2` used for the in-block bits.
    #[inline]
    fn base_hashes(key: &Uint256) -> (u64, u64) {
        let bytes = key.data();
        let read_u64 = |offset: usize| -> u64 {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&bytes[offset..offset + 8]);
            u64::from_le_bytes(buf)
        };
        (splitmix64(read_u64(0)), splitmix64(read_u64(16)))
    }

    /// Iterates the `(block, bit_within_block)` positions for a key, invoking
    /// `visit` once per probe. Shared by [`Self::insert`] and [`Self::probe`]
    /// so the two can never diverge on how positions are computed.
    #[inline]
    fn for_each_position(&self, key: &Uint256, mut visit: impl FnMut(usize, usize)) {
        let (h1, h2) = Self::base_hashes(key);
        let block = (h1 % self.block_count as u64) as usize;
        // Double hashing: g_i = h1 + i*h2 (mod 2^64). Enough independence for
        // Bloom bit selection from two base hashes (Kirsch-Mitzenmacher).
        let mut acc = h1;
        for _ in 0..self.hashes {
            let bit = (acc % BLOCK_BITS as u64) as usize;
            visit(block, bit);
            acc = acc.wrapping_add(h2);
        }
    }

    /// Inserts a key. Idempotent and safe to call concurrently.
    pub fn insert(&self, key: &Uint256) {
        self.for_each_position(key, |block, bit| {
            let word_index = block * BLOCK_WORDS + (bit / 64);
            let mask = 1u64 << (bit % 64);
            // Release so a subsequent Acquire probe on another thread observes
            // the set bit.
            self.words[word_index].fetch_or(mask, Ordering::Release);
        });
    }

    /// Tests membership.
    ///
    /// Returns [`Membership::DefinitelyAbsent`] if any of the key's bits is
    /// clear (guaranteed correct), otherwise [`Membership::PossiblyPresent`].
    pub fn probe(&self, key: &Uint256) -> Membership {
        let mut present = true;
        self.for_each_position(key, |block, bit| {
            if !present {
                return;
            }
            let word_index = block * BLOCK_WORDS + (bit / 64);
            let mask = 1u64 << (bit % 64);
            if self.words[word_index].load(Ordering::Acquire) & mask == 0 {
                present = false;
            }
        });
        if present {
            Membership::PossiblyPresent
        } else {
            Membership::DefinitelyAbsent
        }
    }

    /// Convenience predicate: `true` unless the key is definitely absent. This
    /// matches the sense of a "must I check the real store?" gate.
    pub fn may_contain(&self, key: &Uint256) -> bool {
        matches!(self.probe(key), Membership::PossiblyPresent)
    }
}

/// `splitmix64` finalizer: a fast, well-distributed 64-bit mixer used to
/// decorrelate the two base hashes derived from the key bytes.
#[inline]
fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}
