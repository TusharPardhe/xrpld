//! Tests for the node-store blocked Bloom filter.
//!
//! The most important guarantee is exercised by
//! [`no_false_negatives_over_random_keys`]: any inserted key must always probe
//! as `PossiblyPresent`. A false negative would be a correctness bug, because
//! callers trust `DefinitelyAbsent` to skip the authoritative store lookup.

use basics::base_uint::Uint256;
use basics::memory::bloom::{BloomFilter, Membership};

/// Builds a deterministic pseudo-random 256-bit key from a seed so tests are
/// reproducible without a crng dependency.
fn key_from_seed(seed: u64) -> Uint256 {
    let mut bytes = [0u8; 32];
    let mut x = seed;
    for chunk in bytes.chunks_mut(8) {
        // xorshift64* step for spread.
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        chunk.copy_from_slice(&x.to_le_bytes());
    }
    Uint256::from(bytes)
}

#[test]
fn empty_filter_reports_absent() {
    let filter = BloomFilter::with_capacity(1_000, 10);
    assert_eq!(filter.probe(&key_from_seed(42)), Membership::DefinitelyAbsent);
    assert!(!filter.may_contain(&key_from_seed(42)));
}

#[test]
fn inserted_key_is_possibly_present() {
    let filter = BloomFilter::with_capacity(1_000, 10);
    let key = key_from_seed(7);
    filter.insert(&key);
    assert_eq!(filter.probe(&key), Membership::PossiblyPresent);
    assert!(filter.may_contain(&key));
}

#[test]
fn no_false_negatives_over_random_keys() {
    // Insert many keys, then assert every one probes as possibly present.
    let count = 50_000;
    let filter = BloomFilter::with_capacity(count, 10);
    for i in 0..count as u64 {
        filter.insert(&key_from_seed(i));
    }
    for i in 0..count as u64 {
        assert_eq!(
            filter.probe(&key_from_seed(i)),
            Membership::PossiblyPresent,
            "false negative for inserted key seed {i}"
        );
    }
}

#[test]
fn false_positive_rate_is_bounded_at_ten_bits() {
    // Insert `count` keys, then probe a disjoint set of never-inserted keys.
    // At 10 bits/key the theoretical FPR is ~1%; allow generous headroom for
    // the blocked layout and finite sample.
    let count = 50_000usize;
    let filter = BloomFilter::with_capacity(count, 10);
    for i in 0..count as u64 {
        filter.insert(&key_from_seed(i));
    }

    let probes = 50_000u64;
    let mut false_positives = 0u64;
    for i in 0..probes {
        // Disjoint seed space from the inserted keys.
        let key = key_from_seed(1_000_000 + i);
        if filter.may_contain(&key) {
            false_positives += 1;
        }
    }
    let fpr = false_positives as f64 / probes as f64;
    assert!(
        fpr < 0.05,
        "false-positive rate {fpr:.4} exceeded 5% bound ({false_positives}/{probes})"
    );
}

#[test]
fn zero_capacity_is_clamped_and_usable() {
    let filter = BloomFilter::with_capacity(0, 10);
    let key = key_from_seed(3);
    assert_eq!(filter.probe(&key), Membership::DefinitelyAbsent);
    filter.insert(&key);
    assert_eq!(filter.probe(&key), Membership::PossiblyPresent);
}

#[test]
fn memory_scales_with_capacity() {
    let small = BloomFilter::with_capacity(1_000, 10);
    let large = BloomFilter::with_capacity(1_000_000, 10);
    assert!(large.memory_bytes() > small.memory_bytes());
    // ~10 bits/key for 1M keys ≈ 1.25 MB, rounded up to whole blocks.
    assert!(large.memory_bytes() >= 1_000_000 * 10 / 8);
}

#[test]
fn hashes_within_block_bounds() {
    let filter = BloomFilter::with_capacity(1_000, 10);
    // k for 10 bits/key = round(10 * ln2) = 7.
    assert_eq!(filter.hashes(), 7);
}

#[test]
fn serialize_round_trip_preserves_membership() {
    let count = 20_000usize;
    let filter = BloomFilter::with_capacity(count, 10);
    for i in 0..count as u64 {
        filter.insert(&key_from_seed(i));
    }
    let bytes = filter.to_bytes();
    let restored = BloomFilter::from_bytes(&bytes).expect("round-trip must decode");
    // Every inserted key must still be possibly-present after reload.
    for i in 0..count as u64 {
        assert_eq!(
            restored.probe(&key_from_seed(i)),
            Membership::PossiblyPresent,
            "reloaded filter lost inserted key seed {i}"
        );
    }
    assert_eq!(restored.hashes(), filter.hashes());
    assert_eq!(restored.memory_bytes(), filter.memory_bytes());
}

#[test]
fn from_bytes_rejects_corrupt_or_mismatched_images() {
    let filter = BloomFilter::with_capacity(1_000, 10);
    let good = filter.to_bytes();
    // Too short.
    assert!(BloomFilter::from_bytes(&good[..16]).is_none());
    // Bad magic.
    let mut bad_magic = good.clone();
    bad_magic[0] = b'X';
    assert!(BloomFilter::from_bytes(&bad_magic).is_none());
    // Truncated body (drop trailing words).
    assert!(BloomFilter::from_bytes(&good[..good.len() - 8]).is_none());
    // Empty buffer.
    assert!(BloomFilter::from_bytes(&[]).is_none());
    // A valid image still decodes.
    assert!(BloomFilter::from_bytes(&good).is_some());
}
