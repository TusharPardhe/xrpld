//! Integration tests that mirror the current C++ behavior more explicitly.
//!
//! Why keep these in `tests/` instead of inline unit tests only?
//! - Unit tests are great for testing a module from the inside.
//! - Integration tests are closer to how another crate would use the API.
//! - For migration work, they are a good place to encode "this matches the
//!   external behavior of the current C++ implementation."

use basics::algorithm::{generalized_set_intersection, remove_if_intersect_or_match};
use basics::base_uint::{
    BaseUInt, Uint256, to_short_string as base_uint_to_short_string,
    to_string as base_uint_to_string,
};
use basics::base64::{base64_decode, base64_encode, base64_encode_str};
use basics::basic_config::{
    BasicConfig, IniFileSections, LegacyValueError, Section, get, get_if_exists,
    get_if_exists_bool, get_string, set, set_with_default,
};
use basics::blob::Blob;
use basics::buffer::Buffer;
use basics::byte_utilities::{kilobytes, megabytes};
use basics::chrono::{
    EPOCH_OFFSET_SECONDS, NetClockTimePoint, days, epoch_offset, to_string as chrono_to_string,
    to_string_iso as chrono_to_string_iso, weeks,
};
use basics::comparators::{EqualTo, Less};
use basics::contract::{rethrow, throw};
use basics::counted_object::{Counted, CountedObject, CountedObjects, Counter};
use basics::expected::{BadExpectedAccess, Expected, Unexpected};
use basics::file_utilities::{FileUtilitiesError, get_file_contents, write_file_contents};
use basics::hardened_hash::HardenedHashBuilder;
use basics::intrusive_pointer::{
    IntrusiveObject, SharedIntrusive, SharedWeakUnion, WeakIntrusive, make_shared_intrusive,
};
use basics::intrusive_ref_counts::{
    IntrusiveRefCounts, ReleaseStrongRefAction, ReleaseWeakRefAction,
};
use basics::join::{Joined, join};
use basics::local_value::LocalValue;
use basics::math_utilities::calculate_percent;
use basics::mul_div::mul_div;
use basics::number::{
    MantissaScale, NumberArithmeticError, NumberMantissaScaleGuard, NumberParts,
    NumberRoundModeGuard, RoundingMode, abs_number, current_mantissa_log, current_mantissa_max,
    current_mantissa_min, current_number_lowest, current_number_max, current_number_min,
    mantissa_scale_to_string, power, power_fraction, root, root2, squelch_number,
};
use basics::partitioned_unordered_map::{PartitionKey, PartitionedUnorderedMap};
use basics::random::{
    XorShiftEngine, rand_bool_with, rand_byte_with, rand_int_full_with, rand_int_range_with,
    rand_int_to_with,
};
use basics::range_set::{
    RangeSet, from_string as range_set_from_string, prev_missing, range, to_string_range_set,
};
use basics::safe_cast::{safe_cast, unsafe_cast};
use basics::scope::{ScopeExit, ScopeFail, ScopeSuccess};
use basics::sha_map_hash::SHAMapHash;
use basics::shared_weak_cache_pointer::SharedWeakCachePointer;
use basics::slice::{Slice, make_slice};
use basics::str_hex::{str_hex, str_hex_iter};
use basics::string_utilities::{
    ParsedUrl, is_properly_formed_toml_domain, parse_url, sql_blob_literal, str_unhex,
    str_view_unhex, to_uint64, trim_whitespace,
};
use basics::tagged_cache::{KeyCache, ManualClock, TaggedCache};
use basics::tagged_integer::TaggedInteger;
use basics::to_string::to_string as basics_to_string;
use basics::unordered_containers::{
    HardenedHashMap, HardenedPartitionedHashMap, HashMap as UnorderedHashMap,
    HashSet as UnorderedHashSet,
};
use basics::uptime_clock::{UptimeClock, UptimeTimePoint};
use rand::RngCore;
use std::any::Any;
use std::error::Error;
use std::fmt;
use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering};
use std::thread;
use time::Duration;

struct TempDirGuard {
    path: PathBuf,
}

impl TempDirGuard {
    fn new(prefix: &str) -> Self {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock should be after unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "xrpl-rust-migration-{prefix}-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&path).expect("temp directory should be created");
        Self { path }
    }

    fn join(&self, name: &str) -> PathBuf {
        self.path.join(name)
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IntrusiveLifecycle {
    Alive = 1,
    PartiallyDeleted = 2,
    Deleted = 3,
}

impl IntrusiveLifecycle {
    fn load(state: &AtomicU8) -> Self {
        match state.load(Ordering::SeqCst) {
            1 => Self::Alive,
            2 => Self::PartiallyDeleted,
            3 => Self::Deleted,
            other => panic!("unexpected intrusive lifecycle state: {other}"),
        }
    }
}

#[derive(Debug)]
struct IntrusiveTracker {
    lifecycle: AtomicU8,
}

impl IntrusiveTracker {
    fn new() -> Self {
        Self {
            lifecycle: AtomicU8::new(IntrusiveLifecycle::Alive as u8),
        }
    }
}

#[derive(Debug)]
struct TestIntrusiveNode {
    ref_counts: IntrusiveRefCounts,
    tracker: Arc<IntrusiveTracker>,
}

impl TestIntrusiveNode {
    fn new(tracker: Arc<IntrusiveTracker>) -> Self {
        Self {
            ref_counts: IntrusiveRefCounts::new(),
            tracker,
        }
    }
}

unsafe impl IntrusiveObject for TestIntrusiveNode {
    type Owner = basics::intrusive_pointer::ErasedIntrusiveOwner;

    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        &self.ref_counts
    }

    fn partial_destructor(&self) {
        self.tracker
            .lifecycle
            .store(IntrusiveLifecycle::PartiallyDeleted as u8, Ordering::SeqCst);
    }
}

impl Drop for TestIntrusiveNode {
    fn drop(&mut self) {
        self.tracker
            .lifecycle
            .store(IntrusiveLifecycle::Deleted as u8, Ordering::SeqCst);
    }
}

#[test]
fn mul_div_reference_cases() {
    let max = u64::MAX;
    let max32 = u32::MAX as u64;

    let cases = [
        (85, 20, 5, Some(340)),
        (20, 85, 5, Some(340)),
        (0, max - 1, max - 3, Some(0)),
        (max - 1, 0, max - 3, Some(0)),
        (max, 2, max / 2, Some(4)),
        (max, 1000, max / 1000, Some(1_000_000)),
        (max, 1000, max / 1001, Some(1_001_000)),
        (max32 + 1, max32 + 1, 5, Some(3_689_348_814_741_910_323)),
        (max - 1, max - 2, 5, None),
    ];

    for (value, mul, div, expected) in cases {
        assert_eq!(mul_div(value, mul, div), expected);
    }
}

#[test]
fn base64_reference_cases() {
    let text_cases = [
        ("", ""),
        ("f", "Zg=="),
        ("fo", "Zm8="),
        ("foo", "Zm9v"),
        ("foob", "Zm9vYg=="),
        ("fooba", "Zm9vYmE="),
        ("foobar", "Zm9vYmFy"),
        (
            "Man is distinguished, not only by his reason, but by this singular passion from other animals, which is a lust of the mind, that by a perseverance of delight in the continued and indefatigable generation of knowledge, exceeds the short vehemence of any carnal pleasure.",
            "TWFuIGlzIGRpc3Rpbmd1aXNoZWQsIG5vdCBvbmx5IGJ5IGhpcyByZWFzb24sIGJ1dCBieSB0aGlzIHNpbmd1bGFyIHBhc3Npb24gZnJvbSBvdGhlciBhbmltYWxzLCB3aGljaCBpcyBhIGx1c3Qgb2YgdGhlIG1pbmQsIHRoYXQgYnkgYSBwZXJzZXZlcmFuY2Ugb2YgZGVsaWdodCBpbiB0aGUgY29udGludWVkIGFuZCBpbmRlZmF0aWdhYmxlIGdlbmVyYXRpb24gb2Yga25vd2xlZGdlLCBleGNlZWRzIHRoZSBzaG9ydCB2ZWhlbWVuY2Ugb2YgYW55IGNhcm5hbCBwbGVhc3VyZS4=",
        ),
    ];

    for (plain, encoded) in text_cases {
        assert_eq!(base64_encode_str(plain), encoded);
        assert_eq!(base64_encode(plain.as_bytes()), encoded);
        assert_eq!(base64_decode(encoded), plain.as_bytes());
    }

    // This mirrors the current C++ behavior where decode stops at the first
    // invalid character sequence.
    assert_eq!(base64_decode("not_base64!!"), base64_decode("not"));
}

#[test]
fn intrusive_ref_counts_match_cpp_release_roles() {
    let counts = IntrusiveRefCounts::new();
    assert_eq!(counts.use_count(), 1);

    counts.add_weak_ref();
    assert_eq!(
        counts.release_strong_ref(),
        ReleaseStrongRefAction::PartialDestroy
    );
    assert!(counts.expired());

    counts.partial_destructor_finished();
    assert_eq!(counts.release_weak_ref(), ReleaseWeakRefAction::Destroy);
}

#[test]
fn intrusive_pointer_basic_lifecycle_roles() {
    let tracker = Arc::new(IntrusiveTracker::new());
    let shared = make_shared_intrusive(TestIntrusiveNode::new(Arc::clone(&tracker)));
    let strong_copies: Vec<SharedIntrusive<TestIntrusiveNode>> =
        (0..10).map(|_| shared.clone()).collect();

    assert_eq!(shared.use_count(), 11);
    drop(strong_copies);
    assert_eq!(
        IntrusiveLifecycle::load(&tracker.lifecycle),
        IntrusiveLifecycle::Alive
    );
    drop(shared);
    assert_eq!(
        IntrusiveLifecycle::load(&tracker.lifecycle),
        IntrusiveLifecycle::Deleted
    );

    let tracker = Arc::new(IntrusiveTracker::new());
    let mut shared = make_shared_intrusive(TestIntrusiveNode::new(Arc::clone(&tracker)));
    let mut weak = WeakIntrusive::from_shared(&shared);

    let locked = weak.lock();
    assert!(!locked.is_null());
    assert_eq!(locked.use_count(), 2);

    shared.reset();
    assert_eq!(
        IntrusiveLifecycle::load(&tracker.lifecycle),
        IntrusiveLifecycle::Alive
    );

    drop(locked);
    assert_eq!(
        IntrusiveLifecycle::load(&tracker.lifecycle),
        IntrusiveLifecycle::PartiallyDeleted
    );
    assert!(weak.expired());
    assert!(weak.lock().is_null());

    weak.reset();
    assert_eq!(
        IntrusiveLifecycle::load(&tracker.lifecycle),
        IntrusiveLifecycle::Deleted
    );
}

#[test]
fn intrusive_shared_weak_union_and_tagged_cache_match_cpp_reference_role() {
    let tracker = Arc::new(IntrusiveTracker::new());
    let mut strong = SharedWeakUnion::from(make_shared_intrusive(TestIntrusiveNode::new(
        Arc::clone(&tracker),
    )));

    assert!(strong.is_strong());
    assert_eq!(strong.use_count(), 1);

    let mut weak = strong.clone();
    assert!(weak.convert_to_weak());
    assert!(weak.is_weak());
    assert_eq!(strong.use_count(), 1);

    let restored = weak.lock();
    assert!(!restored.is_null());
    assert_eq!(restored.use_count(), 2);
    drop(restored);
    strong.reset();
    assert_eq!(
        IntrusiveLifecycle::load(&tracker.lifecycle),
        IntrusiveLifecycle::PartiallyDeleted
    );
    assert!(weak.expired());
    assert!(!weak.convert_to_strong());
    weak.reset();
    assert_eq!(
        IntrusiveLifecycle::load(&tracker.lifecycle),
        IntrusiveLifecycle::Deleted
    );

    let clock = ManualClock::new(0);
    let cache = TaggedCache::<
        u32,
        TestIntrusiveNode,
        _,
        HardenedHashBuilder,
        SharedWeakUnion<TestIntrusiveNode>,
        SharedIntrusive<TestIntrusiveNode>,
    >::new("intrusive-cache", 1, Duration::seconds(1), clock);
    let tracker = Arc::new(IntrusiveTracker::new());

    assert!(!cache.insert(1, TestIntrusiveNode::new(Arc::clone(&tracker))));
    let held = cache.fetch(&1).expect("intrusive cache entry should exist");
    cache.clock().advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.get_cache_size(), 0);
    assert_eq!(cache.get_track_size(), 1);
    drop(held);
    cache.clock().advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.get_track_size(), 0);
    assert_eq!(
        IntrusiveLifecycle::load(&tracker.lifecycle),
        IntrusiveLifecycle::Deleted
    );
}

#[test]
fn base_uint_reference_role() {
    type Test96 = BaseUInt<12>;

    let raw = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
    let u = Test96::from_array(raw);
    assert_eq!(Test96::BYTES, raw.len());
    assert_eq!(base_uint_to_string(&u), "0102030405060708090A0B0C");
    assert_eq!(base_uint_to_short_string(&u), "01020304...");
    assert_eq!(u.data()[0], 1);
    assert_eq!(u.signum(), 1);
    assert!(u.is_non_zero());

    let v = !u;
    assert_eq!(base_uint_to_string(&v), "FEFDFCFBFAF9F8F7F6F5F4F3");
    assert!(u < v);

    let mut n = Test96::zero();
    n.increment();
    assert_eq!(n, Test96::from_u64(1));
    n.decrement();
    assert_eq!(n, Test96::zero());
    n.decrement();
    assert_eq!(base_uint_to_string(&n), "FFFFFFFFFFFFFFFFFFFFFFFF");

    let mut parsed = Test96::zero();
    assert!(parsed.parse_hex("0102030405060708090A0B0C"));
    assert_eq!(parsed, u);
    assert!(!parsed.parse_hex("0102030405060708090A0B0G"));
}

#[test]
fn basic_config_reference_role() {
    let mut section = Section::new("test");
    section.append_lines([
        "alpha = one",
        "beta = two # trailing",
        "value line",
        "escaped\\#hash",
        "# full comment",
        "gamma = three\\#kept # stripped",
        "empty =    ",
    ]);

    assert_eq!(
        section.lines(),
        &[
            "alpha = one".to_owned(),
            "beta = two".to_owned(),
            "value line".to_owned(),
            "escaped#hash".to_owned(),
            "gamma = three#kept".to_owned(),
            "empty =    ".to_owned(),
        ]
    );
    assert_eq!(
        section.values(),
        &[
            "value line".to_owned(),
            "escaped#hash".to_owned(),
            "empty =    ".to_owned(),
        ]
    );
    assert!(section.had_trailing_comments());
    assert_eq!(
        section.get::<String>("alpha").unwrap(),
        Some("one".to_owned())
    );
    assert_eq!(
        section.get::<String>("beta").unwrap(),
        Some("two".to_owned())
    );
    assert_eq!(
        section.get::<String>("gamma").unwrap(),
        Some("three#kept".to_owned())
    );
    assert!(!section.exists("empty"));

    let mut helper_section = Section::new("helpers");
    helper_section.set("threads", "16");
    helper_section.set("enabled", "1");
    helper_section.set("broken", "abc");

    let mut threads = 0usize;
    assert!(set(&mut threads, "threads", &helper_section));
    assert_eq!(threads, 16);
    assert!(!set(&mut threads, "broken", &helper_section));
    assert_eq!(threads, 16);
    assert!(!set_with_default(
        &mut threads,
        8usize,
        "missing",
        &helper_section
    ));
    assert_eq!(threads, 8);
    assert_eq!(get(&helper_section, "threads", 4usize), 16);
    assert_eq!(get(&helper_section, "broken", 4usize), 4);
    assert_eq!(get_string(&helper_section, "missing", "sqlite"), "sqlite");

    let mut enabled = false;
    assert!(get_if_exists_bool(&helper_section, "enabled", &mut enabled));
    assert!(enabled);

    let mut parsed_threads = 0usize;
    assert!(get_if_exists(
        &helper_section,
        "threads",
        &mut parsed_threads
    ));
    assert_eq!(parsed_threads, 16);

    let mut config = BasicConfig::new();
    let mut sections = IniFileSections::new();
    sections.insert(
        "server".to_owned(),
        vec!["port = 51234".to_owned(), "admin".to_owned()],
    );
    sections.insert(
        "database_path".to_owned(),
        vec!["/var/lib/xrpld".to_owned()],
    );
    sections.insert("commented".to_owned(), vec!["value # strip".to_owned()]);

    config.build(&sections);

    assert!(config.exists("server"));
    assert_eq!(
        config.section("server").get::<u16>("port").unwrap(),
        Some(51234)
    );
    assert_eq!(config.section("server").values(), &["admin".to_owned()]);
    assert_eq!(config.legacy("database_path").unwrap(), "/var/lib/xrpld");
    assert!(config.had_trailing_comments());

    config.overwrite("server", "ip", "127.0.0.1");
    assert_eq!(
        config.section("server").get::<String>("ip").unwrap(),
        Some("127.0.0.1".to_owned())
    );

    config.set_legacy("single", "value");
    assert_eq!(config.legacy("single").unwrap(), "value");

    config.section_mut("single").append("second");
    assert_eq!(
        config.legacy("single").unwrap_err(),
        LegacyValueError::MultipleLines {
            section: "single".to_owned()
        }
    );

    config.deprecated_clear_section("server");
    assert!(config.section("server").empty());
    assert!(config.section("server").lines().is_empty());
}

#[test]
fn slice_reference_cases() {
    const DATA: [u8; 32] = [
        0xa8, 0xa1, 0x38, 0x45, 0x23, 0xec, 0xe4, 0x23, 0x71, 0x6d, 0x2a, 0x18, 0xb4, 0x70, 0xcb,
        0xf5, 0xac, 0x2d, 0x89, 0x4d, 0x19, 0x9c, 0xf0, 0x2c, 0x15, 0xd1, 0xf9, 0x9b, 0x66, 0xd2,
        0x30, 0xd3,
    ];

    let s0 = Slice::default();
    assert!(s0.empty());
    assert_eq!(s0.size(), 0);
    assert!(s0.as_ptr().is_null());

    let mut unchecked = Slice::new(&DATA[..8]);
    unchecked.remove_prefix(3);
    assert_eq!(unchecked.data(), &DATA[3..8]);
    unchecked.remove_suffix(2);
    assert_eq!(unchecked.data(), &DATA[3..6]);

    for i in 0..DATA.len() {
        let s1 = Slice::new(&DATA[..i]);
        assert_eq!(s1.size(), i);

        for j in 0..DATA.len() {
            let s2 = Slice::new(&DATA[..j]);

            if i == j {
                assert_eq!(s1, s2);
            } else {
                assert_ne!(s1, s2);
            }
        }
    }

    let mut a = DATA;
    let mut b = DATA;
    assert_eq!(make_slice(&a), make_slice(&b));
    b[7] = b[7].wrapping_add(1);
    assert_ne!(make_slice(&a), make_slice(&b));
    a[7] = a[7].wrapping_add(1);
    assert_eq!(make_slice(&a), make_slice(&b));

    let advance_payload = catch_unwind(AssertUnwindSafe(|| {
        let mut slice = Slice::new(&DATA[..4]);
        slice.advance(5);
    }))
    .expect_err("advance past end should unwind");
    let advance_error = advance_payload
        .downcast::<basics::slice::SliceAdvanceError>()
        .expect("expected SliceAdvanceError");
    assert_eq!(advance_error.to_string(), "too small");

    let substr_payload = catch_unwind(AssertUnwindSafe(|| {
        let slice = Slice::new(&DATA[..4]);
        let _ = slice.substr(5, 1);
    }))
    .expect_err("substr past end should unwind");
    let substr_error = substr_payload
        .downcast::<basics::slice::SliceSubsliceError>()
        .expect("expected SliceSubsliceError");
    assert_eq!(
        substr_error.to_string(),
        "Requested sub-slice is out of bounds"
    );
}

#[test]
fn scope_guards_match_cpp_reference_cases() {
    let mut i = 0;
    {
        let _x = ScopeExit::new(|| i = 1);
    }
    assert_eq!(i, 1);

    {
        let _ = catch_unwind(AssertUnwindSafe(|| {
            let _x = ScopeFail::new(|| i = 2);
            panic!("forced panic");
        }));
    }
    assert_eq!(i, 2);

    {
        let _x = ScopeSuccess::new(|| i = 3);
    }
    assert_eq!(i, 3);
}

#[test]
fn tagged_integer_reference_cases() {
    #[derive(Debug)]
    struct Tag1;

    type TagInt = TaggedInteger<i32, Tag1>;

    let zero = TagInt::new(0);
    let one = TagInt::new(1);

    assert_eq!(one, one);
    assert_ne!(one, zero);
    assert!(zero < one);
    assert!(one > zero);
    assert!(one >= one);
    assert!(zero <= one);

    // Rust intentionally does not have ++/--, so `+= 1` is the direct
    // equivalent to the C++ increment/decrement behavior we are mirroring.
    let mut step = TagInt::new(0);
    step += TagInt::from(1u8);
    assert_eq!(step, one);
    step -= TagInt::from(1u8);
    assert_eq!(step, zero);

    assert_eq!(TagInt::new(-3) + TagInt::new(4), TagInt::new(1));
    assert_eq!(TagInt::new(-3) - TagInt::new(4), TagInt::new(-7));
    assert_eq!(TagInt::new(-3) * TagInt::new(4), TagInt::new(-12));
    assert_eq!(TagInt::new(8) / TagInt::new(4), TagInt::new(2));
    assert_eq!(TagInt::new(7) % TagInt::new(4), TagInt::new(3));
    assert_eq!(!TagInt::new(8), TagInt::new(!8));
    assert_eq!(TagInt::new(6) & TagInt::new(3), TagInt::new(2));
    assert_eq!(TagInt::new(6) | TagInt::new(3), TagInt::new(7));
    assert_eq!(TagInt::new(6) ^ TagInt::new(3), TagInt::new(5));
    assert_eq!(TagInt::new(4) << TagInt::new(2), TagInt::new(16));
    assert_eq!(TagInt::new(16) >> TagInt::new(2), TagInt::new(4));
}

#[test]
fn contract_helpers_match_cpp_reference_cases() {
    #[derive(Debug)]
    struct RuntimeError(String);

    impl fmt::Display for RuntimeError {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str(&self.0)
        }
    }

    impl Error for RuntimeError {}

    let first_payload = catch_unwind(AssertUnwindSafe(|| {
        throw(RuntimeError("Throw test".to_owned()));
    }))
    .expect_err("throw should unwind");

    let first_error = first_payload
        .downcast::<RuntimeError>()
        .expect("expected RuntimeError payload");
    assert_eq!(first_error.to_string(), "Throw test");

    let second_payload = catch_unwind(AssertUnwindSafe(|| {
        rethrow(first_error as Box<dyn Any + Send>);
    }))
    .expect_err("rethrow should unwind");

    let second_error = second_payload
        .downcast::<RuntimeError>()
        .expect("expected RuntimeError payload");
    assert_eq!(second_error.to_string(), "Throw test");
}

#[test]
fn byte_utilities_match_cpp_reference_cases() {
    assert_eq!(kilobytes(2u32), 2048u32);
    assert_eq!(megabytes(3u32), 3_145_728u32);
    assert_eq!(kilobytes(32usize), 32 * 1024);
    assert_eq!(megabytes(1usize), 1024 * 1024);
}

#[test]
fn str_hex_reference_cases() {
    let bytes = [0xa8, 0xa1, 0x38, 0x45, 0x23, 0xec, 0xe4, 0x23];

    assert_eq!(str_hex([]), "");
    assert_eq!(str_hex([0x00]), "00");
    assert_eq!(str_hex(bytes), "A8A1384523ECE423");
    assert_eq!(str_hex(&bytes[..4]), "A8A13845");
    assert_eq!(str_hex_iter(bytes.iter()), "A8A1384523ECE423");
}

#[test]
fn join_reference_cases() {
    assert_eq!(join(std::iter::empty::<i32>(), ", "), "");
    assert_eq!(join([1, 2, 3], ", "), "1, 2, 3");
    assert_eq!(
        join(["xrpl", "rust", "migration"], "::"),
        "xrpl::rust::migration"
    );

    let values = [10, 20, 30];
    assert_eq!(format!("{}", Joined::new(&values, " | ")), "10 | 20 | 30");
}

#[test]
fn algorithm_helpers_match_cpp_reference_cases() {
    let left = [1, 2, 3, 5, 8];
    let right = [0, 2, 3, 4, 8, 13];
    let mut seen = Vec::new();

    generalized_set_intersection(&left, &right, |a, b| seen.push((*a, *b)), |a, b| a < b);
    assert_eq!(seen, vec![(2, 2), (3, 3), (8, 8)]);

    let mut to_filter = vec![1, 2, 3, 4, 5, 6];
    let filter_against = [2, 4, 6, 8];
    let new_len = remove_if_intersect_or_match(
        &mut to_filter,
        &filter_against,
        |value| value % 5 == 0,
        |a, b| a < b,
    );

    assert_eq!(new_len, 2);
    assert_eq!(to_filter, vec![1, 3]);
}

#[test]
fn math_utilities_match_cpp_reference_cases() {
    assert_eq!(calculate_percent(1, 2), 50);
    assert_eq!(calculate_percent(0, 100), 0);
    assert_eq!(calculate_percent(100, 100), 100);
    assert_eq!(calculate_percent(200, 100), 100);
    assert_eq!(calculate_percent(1, 99), 2);
    assert_eq!(calculate_percent(50_000_001, 100_000_000), 51);
}

#[test]
fn to_string_reference_cases() {
    assert_eq!(basics_to_string(true), "true");
    assert_eq!(basics_to_string(false), "false");
    assert_eq!(basics_to_string('x'), "x");
    assert_eq!(basics_to_string("xrpl"), "xrpl");
    assert_eq!(basics_to_string(String::from("rust")), "rust");
    assert_eq!(basics_to_string(42), "42");
    assert_eq!(basics_to_string(-7), "-7");
}

#[test]
fn number_to_string_reference_cases() {
    assert_eq!(NumberParts::zero().to_string(), "0");
    assert_eq!(NumberParts::unchecked(true, 0, 0).to_string(), "-0");

    let fixed = NumberParts::unchecked(false, 1_000_000_000_000_000_000, -19);
    assert_eq!(fixed.to_string(), "0.1");

    let scientific = NumberParts::unchecked(false, 12_340_000, -7);
    assert_eq!(scientific.to_string(), "1234e-3");

    let scale_sensitive = NumberParts::unchecked(false, 1_234_567, -7);
    {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Small);
        assert_eq!(scale_sensitive.to_string(), "123456700");
    }
    {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Large);
        assert_eq!(scale_sensitive.to_string(), "1234567e-7");
    }
}

#[test]
fn number_public_helper_surface_roles() {
    {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Small);
        let value = NumberParts::unchecked(true, 1_000_000_000_000_000, -15);
        let limit = NumberParts::unchecked(false, 2_000_000_000_000_000, -15);

        assert_eq!(current_number_min(), NumberParts::min(MantissaScale::Small));
        assert_eq!(current_number_max(), NumberParts::max(MantissaScale::Small));
        assert_eq!(
            current_number_lowest(),
            NumberParts::lowest(MantissaScale::Small)
        );
        assert_eq!(current_mantissa_min(), 1_000_000_000_000_000);
        assert_eq!(current_mantissa_max(), 9_999_999_999_999_999);
        assert_eq!(current_mantissa_log(), 15);
        assert_eq!(
            abs_number(value),
            NumberParts::unchecked(false, 1_000_000_000_000_000, -15)
        );
        assert_eq!(squelch_number(value, limit), NumberParts::zero());
    }

    {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Large);
        assert_eq!(current_number_min(), NumberParts::min(MantissaScale::Large));
        assert_eq!(current_number_max(), NumberParts::max(MantissaScale::Large));
        assert_eq!(
            current_number_lowest(),
            NumberParts::lowest(MantissaScale::Large)
        );
        assert_eq!(current_mantissa_min(), 1_000_000_000_000_000_000);
        assert_eq!(current_mantissa_max(), 9_999_999_999_999_999_999);
        assert_eq!(current_mantissa_log(), 18);
    }
    assert_eq!(mantissa_scale_to_string(MantissaScale::Small), "small");
    assert_eq!(mantissa_scale_to_string(MantissaScale::Large), "large");
}

#[test]
fn number_add_sub_match_cpp_reference_cases() {
    {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Small);
        assert_eq!(
            NumberParts::unchecked(false, 1_000_000_000_000_000, -15)
                + NumberParts::unchecked(false, 6_555_555_555_555_555, -29),
            NumberParts::unchecked(false, 1_000_000_000_000_066, -15)
        );
        assert_eq!(
            NumberParts::unchecked(false, 1_000_000_000_000_000, -15)
                - NumberParts::unchecked(false, 6_555_555_555_555_555, -29),
            NumberParts::unchecked(false, 9_999_999_999_999_344, -16)
        );
    }
    {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Large);
        let lhs =
            NumberParts::try_from_external_parts(1_000_000_000_000_000, -15, MantissaScale::Large)
                .expect("large lhs should normalize");
        let rhs =
            NumberParts::try_from_external_parts(6_555_555_555_555_555, -29, MantissaScale::Large)
                .expect("large rhs should normalize");
        assert_eq!(
            lhs + rhs,
            NumberParts::try_from_external_parts(
                1_000_000_000_000_065_556,
                -18,
                MantissaScale::Large
            )
            .expect("large sum should normalize")
        );
        assert_eq!(
            lhs - rhs,
            NumberParts::try_from_external_parts(
                999_999_999_999_934_444,
                -18,
                MantissaScale::Large
            )
            .expect("large difference should normalize")
        );
    }
}

#[test]
fn number_mul_div_match_cpp_reference_cases() {
    {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Small);
        let _round_guard = NumberRoundModeGuard::new(RoundingMode::ToNearest);
        assert_eq!(
            NumberParts::unchecked(false, 1_414_213_562_373_095, -15)
                * NumberParts::unchecked(false, 1_414_213_562_373_095, -15),
            NumberParts::unchecked(false, 2_000_000_000_000_000, -15)
        );
        assert_eq!(
            NumberParts::unchecked(false, 2, 0) / NumberParts::unchecked(false, 3, 0),
            NumberParts::unchecked(false, 6_666_666_666_666_667, -16)
        );
    }
    {
        let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Large);
        let _round_guard = NumberRoundModeGuard::new(RoundingMode::ToNearest);
        let sqrt2 = NumberParts::try_from_external_parts(
            1_414_213_562_373_095_049,
            -18,
            MantissaScale::Large,
        )
        .expect("large sqrt2 should normalize");
        assert_eq!(
            sqrt2 * sqrt2,
            NumberParts::try_from_external_parts(
                2_000_000_000_000_000_001,
                -18,
                MantissaScale::Large
            )
            .expect("large product should normalize")
        );
        assert_eq!(
            NumberParts::try_from_external_parts(2, 0, MantissaScale::Large)
                .expect("large numerator should normalize")
                / NumberParts::try_from_external_parts(3, 0, MantissaScale::Large)
                    .expect("large denominator should normalize"),
            NumberParts::try_from_external_parts(
                6_666_666_666_666_666_667,
                -19,
                MantissaScale::Large
            )
            .expect("large quotient should normalize")
        );
    }
}

fn normalized_number(mantissa: i64, exponent: i32, scale: MantissaScale) -> NumberParts {
    NumberParts::unchecked(mantissa < 0, mantissa.unsigned_abs(), exponent)
        .try_mul(NumberParts::one(scale))
        .expect("test number should normalize with current rounding")
}

fn internal_number(
    negative: bool,
    mantissa: u64,
    exponent: i32,
    scale: MantissaScale,
) -> NumberParts {
    NumberParts::unchecked(negative, mantissa, exponent)
        .try_mul(NumberParts::one(scale))
        .expect("test number should normalize with current rounding")
}

#[test]
fn number_power_reference_cases() {
    let scale = MantissaScale::Small;
    let _scale_guard = NumberMantissaScaleGuard::new(scale);

    let cases = [
        (
            normalized_number(64, 0, scale),
            0,
            normalized_number(1, 0, scale),
        ),
        (
            normalized_number(64, 0, scale),
            1,
            normalized_number(64, 0, scale),
        ),
        (
            normalized_number(64, 0, scale),
            2,
            normalized_number(4096, 0, scale),
        ),
        (
            normalized_number(-64, 0, scale),
            2,
            normalized_number(4096, 0, scale),
        ),
        (
            normalized_number(64, 0, scale),
            3,
            normalized_number(262_144, 0, scale),
        ),
        (
            normalized_number(-64, 0, scale),
            3,
            normalized_number(-262_144, 0, scale),
        ),
        (
            normalized_number(64, 0, scale),
            11,
            normalized_number(7_378_697_629_483_820_646, 1, scale),
        ),
        (
            normalized_number(-64, 0, scale),
            11,
            normalized_number(-7_378_697_629_483_820_646, 1, scale),
        ),
    ];

    for (value, exponent, expected) in cases {
        assert_eq!(
            power(value, exponent).expect("power should succeed"),
            expected
        );
    }

    let large_scale = MantissaScale::Large;
    let _scale_guard = NumberMantissaScaleGuard::new(large_scale);
    let _round_guard = NumberRoundModeGuard::new(RoundingMode::TowardsZero);
    let max = internal_number(false, 9_999_999_999_999_999_999, 0, large_scale);
    assert_eq!(
        power(max, 2).expect("large-scale power should succeed"),
        internal_number(false, 999_999_999_999_999_998, 20, large_scale)
    );
}

#[test]
fn number_root_and_root2_match_cpp_reference_cases() {
    let scale = MantissaScale::Small;
    let _scale_guard = NumberMantissaScaleGuard::new(scale);
    let _round_guard = NumberRoundModeGuard::new(RoundingMode::ToNearest);

    let cases = [
        (
            normalized_number(2, 0, scale),
            2,
            normalized_number(1_414_213_562_373_095_049, -18, scale),
        ),
        (
            normalized_number(2_000_000, 0, scale),
            2,
            normalized_number(1_414_213_562_373_095_049, -15, scale),
        ),
        (
            normalized_number(2, -30, scale),
            2,
            normalized_number(1_414_213_562_373_095_049, -33, scale),
        ),
        (
            normalized_number(-27, 0, scale),
            3,
            normalized_number(-3, 0, scale),
        ),
        (
            normalized_number(1, 0, scale),
            5,
            normalized_number(1, 0, scale),
        ),
        (
            normalized_number(-1, 0, scale),
            0,
            normalized_number(1, 0, scale),
        ),
        (
            normalized_number(5, -1, scale),
            0,
            normalized_number(0, 0, scale),
        ),
        (
            normalized_number(0, 0, scale),
            5,
            normalized_number(0, 0, scale),
        ),
        (
            normalized_number(5_625, -4, scale),
            2,
            normalized_number(75, -2, scale),
        ),
    ];

    for (value, divisor, expected) in cases {
        assert_eq!(root(value, divisor).expect("root should succeed"), expected);
        if divisor == 2 {
            assert_eq!(root2(value).expect("root2 should succeed"), expected);
        }
    }

    let large_scale = MantissaScale::Large;
    let _scale_guard = NumberMantissaScaleGuard::new(large_scale);
    let _round_guard = NumberRoundModeGuard::new(RoundingMode::TowardsZero);
    let large_cases = [
        (
            internal_number(false, 9_999_999_999_999_999_990, -1, large_scale),
            normalized_number(999_999_999_999_999_999, -9, large_scale),
        ),
        (
            internal_number(false, 9_999_999_999_999_999_990, 0, large_scale),
            normalized_number(3_162_277_660_168_379_330, -9, large_scale),
        ),
        (
            normalized_number(9_223_372_036_854_775_807, 0, large_scale),
            normalized_number(3_037_000_499_976_049_692, -9, large_scale),
        ),
    ];

    for (value, expected) in large_cases {
        assert_eq!(root(value, 2).expect("large root should succeed"), expected);
        assert_eq!(root2(value).expect("large root2 should succeed"), expected);
    }

    assert!(matches!(
        root(normalized_number(-2, 0, scale), 0),
        Err(NumberArithmeticError::Overflow)
    ));
    assert!(matches!(
        root(normalized_number(-2, 0, scale), 4),
        Err(NumberArithmeticError::Overflow)
    ));
    assert!(matches!(
        root2(normalized_number(-2, 0, scale)),
        Err(NumberArithmeticError::Overflow)
    ));
}

#[test]
fn number_power_fraction_reference_cases() {
    let scale = MantissaScale::Small;
    let _scale_guard = NumberMantissaScaleGuard::new(scale);

    let cases = [
        (
            normalized_number(1, 0, scale),
            3,
            7,
            normalized_number(1, 0, scale),
        ),
        (
            normalized_number(-1, 0, scale),
            1,
            0,
            normalized_number(1, 0, scale),
        ),
        (
            normalized_number(-1, -1, scale),
            1,
            0,
            normalized_number(0, 0, scale),
        ),
        (
            normalized_number(16, 0, scale),
            0,
            5,
            normalized_number(1, 0, scale),
        ),
        (
            normalized_number(34, 0, scale),
            3,
            3,
            normalized_number(34, 0, scale),
        ),
        (
            normalized_number(4, 0, scale),
            3,
            2,
            normalized_number(8, 0, scale),
        ),
    ];

    for (value, n, d, expected) in cases {
        assert_eq!(
            power_fraction(value, n, d).expect("fractional power should succeed"),
            expected
        );
    }

    assert!(matches!(
        power_fraction(normalized_number(7, 0, scale), 0, 0),
        Err(NumberArithmeticError::Overflow)
    ));
    assert!(matches!(
        power_fraction(normalized_number(7, 0, scale), 1, 0),
        Err(NumberArithmeticError::Overflow)
    ));
    assert!(matches!(
        power_fraction(normalized_number(-1, -1, scale), 3, 2),
        Err(NumberArithmeticError::Overflow)
    ));
}

#[test]
fn number_to_i64_rounding_reference_cases() {
    let positive_half = NumberParts::unchecked(false, 15, -1);
    let negative_half = NumberParts::unchecked(true, 15, -1);

    {
        let _round_guard = NumberRoundModeGuard::new(RoundingMode::ToNearest);
        assert_eq!(positive_half.try_to_i64().expect("round half to even"), 2);
        assert_eq!(negative_half.try_to_i64().expect("round half to even"), -2);
    }
    {
        let _round_guard = NumberRoundModeGuard::new(RoundingMode::TowardsZero);
        assert_eq!(positive_half.try_to_i64().expect("truncate toward zero"), 1);
        assert_eq!(
            negative_half.try_to_i64().expect("truncate toward zero"),
            -1
        );
    }
    {
        let _round_guard = NumberRoundModeGuard::new(RoundingMode::Downward);
        assert_eq!(positive_half.try_to_i64().expect("downward positive"), 1);
        assert_eq!(negative_half.try_to_i64().expect("downward negative"), -2);
    }
    {
        let _round_guard = NumberRoundModeGuard::new(RoundingMode::Upward);
        assert_eq!(positive_half.try_to_i64().expect("upward positive"), 2);
        assert_eq!(negative_half.try_to_i64().expect("upward negative"), -1);
    }
}

#[test]
fn number_increment_and_decrement_match_cpp_operator_roles() {
    let _scale_guard = NumberMantissaScaleGuard::new(MantissaScale::Small);
    let one = NumberParts::one(MantissaScale::Small);
    let negative_one = NumberParts::unchecked(true, 1_000_000_000_000_000, -15);

    let mut value = NumberParts::zero();
    assert_eq!(value.post_increment(), NumberParts::zero());
    assert_eq!(value, one);

    value.decrement();
    assert_eq!(value, NumberParts::zero());

    assert_eq!(value.post_decrement(), NumberParts::zero());
    assert_eq!(value, negative_one);

    value.increment();
    assert_eq!(value, NumberParts::zero());
}

#[test]
fn blob_alias_reference_role() {
    let blob: Blob = vec![0xde, 0xad, 0xbe, 0xef];
    assert_eq!(blob.len(), 4);
    assert_eq!(str_hex(&blob), "DEADBEEF");
}

#[test]
fn comparators_match_reference_role() {
    let less = Less;
    let equal_to = EqualTo;

    assert!(less.compare(&1, &2));
    assert!(!less.compare(&2, &1));
    assert!(equal_to.compare(&"xrpl", &"xrpl"));
    assert!(!equal_to.compare(&"xrpl", &"rust"));
}

#[test]
fn safe_cast_matches_reference_role() {
    let widened_u64: u64 = safe_cast(255u8);
    let widened_i64: i64 = safe_cast(255u8);
    let widened_i32: i32 = safe_cast(-7i8);

    assert_eq!(widened_u64, 255u64);
    assert_eq!(widened_i64, 255i64);
    assert_eq!(widened_i32, -7i32);

    let narrowed: u8 = unsafe_cast(300u16);
    let wrapped_unsigned: u8 = unsafe_cast(-1i8);
    let wrapped_signed: i8 = unsafe_cast(255u8);

    assert_eq!(narrowed, 44u8);
    assert_eq!(wrapped_unsigned, 255u8);
    assert_eq!(wrapped_signed, -1i8);
}

#[test]
fn expected_matches_reference_role() {
    #[derive(Debug, Clone, PartialEq, Eq)]
    struct TestError(&'static str);

    impl fmt::Display for TestError {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str(self.0)
        }
    }

    let mut ok: Expected<String, TestError> = Expected::from_value("xrpl");
    assert!(ok.has_value());
    assert_eq!(ok.value(), "xrpl");
    ok.value_mut().push_str("-rust");
    assert_eq!(ok.value(), "xrpl-rust");

    let err: Expected<String, TestError> = Unexpected::new(TestError("boom")).into();
    assert!(!err.has_value());
    assert_eq!(err.error(), &TestError("boom"));

    let payload = catch_unwind(AssertUnwindSafe(|| {
        let _ = err.value();
    }))
    .expect_err("invalid value access should unwind");
    let bad = payload
        .downcast::<BadExpectedAccess>()
        .expect("expected BadExpectedAccess");
    assert_eq!(bad.to_string(), "bad expected access");

    let void_ok = Expected::<(), TestError>::default();
    assert!(void_ok.has_value());
    assert!(void_ok.as_bool());
    assert!(bool::from(&void_ok));

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Marker(u8);

    let marker_err: Expected<u32, Marker> = Unexpected::new(Marker(3)).into();
    assert_eq!(marker_err.error(), &Marker(3));
    assert!(!marker_err.as_bool());
    assert!(!bool::from(&marker_err));
}

#[test]
fn buffer_matches_reference_role() {
    let empty = Buffer::new();
    assert!(empty.empty());
    assert_eq!(empty.size(), 0);

    let copied = Buffer::from_bytes(&[1, 2, 3, 4]);
    assert_eq!(copied.data(), &[1, 2, 3, 4]);

    let cloned = copied.clone();
    assert_eq!(cloned, copied);

    let mut assigned = Buffer::new();
    assigned.assign_slice(Slice::new(&[9, 8, 7]));
    assert_eq!(assigned.data(), &[9, 8, 7]);

    let mut resized = Buffer::from_bytes(&[1, 2, 3]);
    assert_eq!(resized.alloc(5), &[0, 0, 0, 0, 0]);
    assert_eq!(resized.size(), 5);

    let slice_view: Slice<'_> = (&copied).into();
    assert_eq!(slice_view.data(), &[1, 2, 3, 4]);
}

#[test]
fn chrono_reference_cases() {
    assert_eq!(epoch_offset(), Duration::seconds(EPOCH_OFFSET_SECONDS));
    assert_eq!(EPOCH_OFFSET_SECONDS, 946_684_800);
    assert_eq!(days(1), Duration::hours(24));
    assert_eq!(weeks(1), Duration::hours(24 * 7));

    let network_time = NetClockTimePoint::new(20);
    assert_eq!(network_time.time_since_epoch(), Duration::seconds(20));
    assert_eq!(chrono_to_string(network_time), "2000-Jan-01 00:00:20 UTC");
    assert_eq!(chrono_to_string_iso(network_time), "2000-01-01T00:00:20Z");

    let system_time = NetClockTimePoint::new(10).to_datetime();
    assert_eq!(chrono_to_string(system_time), "2000-Jan-01 00:00:10 UTC");
    assert_eq!(chrono_to_string_iso(system_time), "2000-01-01T00:00:10Z");
}

#[test]
fn random_reference_role() {
    let mut seeded_1977 = XorShiftEngine::new(1977);
    assert_eq!(seeded_1977.next_u64(), 3_238_484_970_499_989_659);
    assert_eq!(seeded_1977.next_u64(), 18_388_379_945_704_714_460);

    let mut seeded_one = XorShiftEngine::new(1);
    assert_eq!(seeded_one.next_u64(), 3_787_875_997_830_008_111);
    assert_eq!(seeded_one.next_u64(), 7_110_081_793_310_507_210);

    let mut rng = XorShiftEngine::new(1977);
    for _ in 0..128 {
        let ranged = rand_int_range_with(&mut rng, -5i32, 15i32);
        assert!((-5..=15).contains(&ranged));

        let to = rand_int_to_with(&mut rng, 7u32);
        assert!((0..=7).contains(&to));

        let full: u32 = rand_int_full_with(&mut rng);
        let _ = full;

        let _byte = rand_byte_with(&mut rng);
        let _bool = rand_bool_with(&mut rng);
    }
}

#[test]
fn range_set_reference_cases() {
    let mut set = RangeSet::<u32>::new();

    for i in 0..10 {
        set.insert_interval(range(10 * i, 10 * i + 5));
    }

    for i in 1..100 {
        let expected = if i <= 6 {
            None
        } else {
            Some(if (i % 10) > 6 {
                i - 1
            } else {
                (10 * (i / 10)) - 1
            })
        };
        assert_eq!(prev_missing(&set, i, 0), expected);
    }

    let mut styled = RangeSet::<u32>::new();
    assert_eq!(to_string_range_set(&styled), "empty");

    styled.insert(1);
    assert_eq!(to_string_range_set(&styled), "1");

    styled.insert_interval(range(4u32, 6u32));
    assert_eq!(to_string_range_set(&styled), "1,4-6");

    styled.insert(2);
    assert_eq!(to_string_range_set(&styled), "1-2,4-6");

    styled.erase_interval(range(4u32, 5u32));
    assert_eq!(to_string_range_set(&styled), "1-2,6");

    let mut parsed = RangeSet::<u32>::new();
    assert!(!range_set_from_string(&mut parsed, ""));
    assert_eq!(parsed.length(), 0);

    assert!(!range_set_from_string(&mut parsed, "#"));
    assert_eq!(parsed.length(), 0);

    assert!(!range_set_from_string(&mut parsed, ","));
    assert_eq!(parsed.length(), 0);

    assert!(!range_set_from_string(&mut parsed, ",-"));
    assert_eq!(parsed.length(), 0);

    assert!(!range_set_from_string(&mut parsed, "1,,2"));
    assert_eq!(parsed.length(), 0);

    assert!(range_set_from_string(&mut parsed, "1"));
    assert_eq!(parsed.length(), 1);
    assert_eq!(parsed.first(), Some(1));

    assert!(range_set_from_string(&mut parsed, "1,1"));
    assert_eq!(parsed.length(), 1);
    assert_eq!(parsed.first(), Some(1));

    assert!(range_set_from_string(&mut parsed, "1-1"));
    assert_eq!(parsed.length(), 1);
    assert_eq!(parsed.first(), Some(1));

    assert!(range_set_from_string(&mut parsed, "1,4-6"));
    assert_eq!(parsed.length(), 4);
    assert_eq!(parsed.first(), Some(1));
    assert!(!parsed.contains(2));
    assert!(!parsed.contains(3));
    assert!(parsed.contains(4));
    assert!(parsed.contains(5));
    assert_eq!(parsed.last(), Some(6));

    assert!(range_set_from_string(&mut parsed, "1-2,4-6"));
    assert_eq!(parsed.length(), 5);
    assert_eq!(parsed.first(), Some(1));
    assert!(parsed.contains(2));
    assert!(parsed.contains(4));
    assert_eq!(parsed.last(), Some(6));

    assert!(range_set_from_string(&mut parsed, "1-2,6"));
    assert_eq!(parsed.length(), 3);
    assert_eq!(parsed.first(), Some(1));
    assert!(parsed.contains(2));
    assert_eq!(parsed.last(), Some(6));
}

#[test]
fn unordered_container_slice_matches_approved_migration_role() {
    let mut plain = UnorderedHashMap::<String, usize>::default();
    let mut set = UnorderedHashSet::<String>::default();

    assert_eq!(plain.insert(String::from("ledger"), 1), None);
    assert!(set.insert(String::from("ledger")));
    assert_eq!(plain.insert(String::from("ledger"), 2), Some(1));
    assert!(!set.insert(String::from("ledger")));
    assert_eq!(plain.get("ledger"), Some(&2));
    assert!(set.contains("ledger"));

    let mut hardened = HardenedHashMap::with_hasher(HardenedHashBuilder::from_seed(17));
    assert_eq!(hardened.insert(String::from("owner"), 3), None);
    assert_eq!(hardened.get("owner"), Some(&3));

    let mut partitioned =
        HardenedPartitionedHashMap::with_hasher(Some(4), HardenedHashBuilder::from_seed(17));
    let key = String::from("cache");
    let partition = partitioned.partition_for(key.as_str());
    partitioned.insert(key, 5);

    assert_eq!(partitioned.partitions(), 4);
    assert_eq!(partitioned.map()[partition].get("cache"), Some(&5));

    let plain_partitioned = PartitionedUnorderedMap::<u32, usize>::new(Some(3));
    assert_eq!(plain_partitioned.partition_for(&8), 2);
}

#[test]
fn shamap_hash_reference_role() {
    let hash =
        Uint256::from_hex("0102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F20")
            .expect("hex should parse");
    let wrapped = SHAMapHash::new(hash);

    assert_eq!(wrapped.as_uint256(), &hash);
    assert!(wrapped.is_non_zero());
    assert!(!wrapped.is_zero());
    assert_eq!(
        wrapped.to_string(),
        "0102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F20"
    );

    let partitioned = PartitionedUnorderedMap::<SHAMapHash, usize>::new(Some(4));
    assert_eq!(
        partitioned.partition_for(&wrapped),
        hash.partition_key() % 4
    );
}

#[test]
fn shared_weak_cache_pointer_matches_reference_role() {
    let strong = Arc::new(String::from("node"));
    let mut pointer = SharedWeakCachePointer::from_arc(Arc::clone(&strong));

    assert!(pointer.is_strong());
    assert_eq!(
        pointer.get().map(|value| value.to_owned()),
        Some(String::from("node"))
    );
    assert!(pointer.use_count() >= 2);

    assert!(pointer.convert_to_weak());
    assert!(pointer.is_weak());
    assert!(!pointer.expired());
    assert!(pointer.lock().is_some());

    drop(strong);
    assert!(pointer.expired());
    assert!(!pointer.convert_to_strong());

    pointer.reset();
    assert!(pointer.is_weak());
    assert!(!pointer.expired());
    assert_eq!(pointer.lock(), None);

    let default_pointer = SharedWeakCachePointer::<String>::new();
    assert!(default_pointer.is_weak());
    assert!(!default_pointer.expired());
    assert_eq!(default_pointer.lock(), None);
}

#[test]
fn tagged_cache_reference_role() {
    let clock = Arc::new(ManualClock::new(0));
    let cache =
        TaggedCache::<u32, String, _>::new("test", 1, Duration::seconds(1), Arc::clone(&clock));

    assert_eq!(cache.get_cache_size(), 0);
    assert_eq!(cache.get_track_size(), 0);
    assert!(!cache.insert(1, String::from("one")));
    assert_eq!(cache.retrieve(&1), Some(String::from("one")));

    cache.touch_if_exists(&1);
    clock.advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.get_cache_size(), 0);
    assert_eq!(cache.get_track_size(), 0);

    assert!(!cache.insert(2, String::from("two")));
    let kept = cache.fetch(&2).expect("value should exist");
    clock.advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.get_cache_size(), 0);
    assert_eq!(cache.get_track_size(), 1);
    drop(kept);
    clock.advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.get_track_size(), 0);

    assert!(!cache.insert(3, String::from("three")));
    let first = cache.fetch(&3).expect("cached value should exist");
    let mut second = Arc::new(String::from("three"));
    assert!(cache.canonicalize_replace_client(&3, &mut second));
    assert!(Arc::ptr_eq(&first, &second));

    let uint_key =
        Uint256::from_hex("0102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F20")
            .expect("hex should parse");
    let uint_cache = TaggedCache::<Uint256, String, _>::new(
        "uint-cache",
        1,
        Duration::seconds(1),
        Arc::new(ManualClock::new(0)),
    );
    assert!(!uint_cache.insert(uint_key, String::from("blob")));
    assert_eq!(uint_cache.retrieve(&uint_key), Some(String::from("blob")));

    let shamap_key = SHAMapHash::new(
        Uint256::from_hex("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")
            .expect("hex should parse"),
    );
    let shamap_cache = TaggedCache::<SHAMapHash, Blob, _>::new(
        "node-cache",
        1,
        Duration::seconds(1),
        Arc::new(ManualClock::new(0)),
    );
    assert!(!shamap_cache.insert(shamap_key, vec![1, 2, 3]));
    assert_eq!(shamap_cache.retrieve(&shamap_key), Some(vec![1, 2, 3]));
}

#[test]
fn tagged_cache_extended_helpers_match_reference_role() {
    let clock = Arc::new(ManualClock::new(0));
    let cache =
        TaggedCache::<u32, String, _>::new("test", 1, Duration::seconds(1), Arc::clone(&clock));

    let first = cache
        .fetch_with(&1, || Some(Arc::new(String::from("one"))))
        .expect("handler should create value");
    let second = cache
        .fetch_with(&1, || Some(Arc::new(String::from("two"))))
        .expect("cached value should be reused");
    assert!(Arc::ptr_eq(&first, &second));

    assert!(cache.del(&1, false));
    assert_eq!(cache.get_track_size(), 0);

    let replacement = Arc::new(String::from("uno"));
    assert!(!cache.canonicalize_replace_cache(&2, &replacement));
    assert!(cache.canonicalize_replace_cache(&2, &Arc::new(String::from("eins"))));
    assert_eq!(
        cache.fetch(&2).map(|value| value.as_str().to_owned()),
        Some(String::from("eins"))
    );

    let mut keys = cache.get_keys();
    keys.sort_unstable();
    assert_eq!(keys, vec![2]);

    let _ = cache.fetch(&999);
    assert!(cache.get_hit_rate() >= 0.0);
    assert!(cache.rate() >= 0.0);

    cache.clear();
    assert_eq!(cache.get_track_size(), 0);
    cache.reset();
    assert_eq!(cache.get_cache_size(), 0);
}

#[test]
fn key_cache_reference_role() {
    let clock = Arc::new(ManualClock::new(0));
    let cache = KeyCache::<String, _>::new("test", 2, Duration::seconds(2), Arc::clone(&clock));

    assert_eq!(cache.size(), 0);
    assert!(cache.insert(String::from("one")));
    assert!(!cache.insert(String::from("one")));
    assert!(cache.touch_if_exists("one"));
    clock.advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.size(), 1);
    clock.advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.size(), 0);

    assert!(cache.insert(String::from("one")));
    assert!(cache.insert(String::from("two")));
    clock.advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.size(), 2);
    assert!(cache.touch_if_exists("two"));
    clock.advance_seconds(1);
    cache.sweep();
    assert_eq!(cache.size(), 1);
}

#[test]
fn counted_object_reference_role() {
    #[derive(Debug, Clone)]
    struct Transaction {
        _counted: CountedObject<Transaction>,
    }

    impl Transaction {
        fn new() -> Self {
            Self {
                _counted: CountedObject::new_named("Transaction"),
            }
        }
    }

    let baseline = CountedObjects::get_instance()
        .get_counts(0)
        .into_iter()
        .find_map(|(name, count)| (name == "Transaction").then_some(count))
        .unwrap_or(0);

    let first = Transaction::new();
    assert_eq!(first._counted.counter().get_name(), "Transaction");
    assert_eq!(
        CountedObjects::get_instance()
            .get_counts(0)
            .into_iter()
            .find_map(|(name, count)| (name == "Transaction").then_some(count)),
        Some(baseline + 1)
    );

    let second = first.clone();
    assert_eq!(
        CountedObjects::get_instance()
            .get_counts(0)
            .into_iter()
            .find_map(|(name, count)| (name == "Transaction").then_some(count)),
        Some(baseline + 2)
    );

    let wrapped = Counted::new_named(String::from("ledger"), "LedgerName");
    let wrapped_clone = wrapped.clone();
    assert_eq!(&*wrapped, "ledger");
    assert_eq!(&*wrapped_clone, "ledger");
    assert_eq!(wrapped.counter().get_name(), "LedgerName");

    drop(second);
    drop(first);
    drop(wrapped_clone);
    drop(wrapped);

    let hit_counter = Counter::new("CachedView::hit");
    let miss_counter = Counter::new("CachedView::miss");
    hit_counter.increment();
    hit_counter.increment();
    miss_counter.increment();

    let filtered = CountedObjects::get_instance().get_counts(2);
    assert!(
        filtered
            .iter()
            .any(|(name, count)| name == "CachedView::hit" && *count == 2)
    );
    assert!(!filtered.iter().any(|(name, _)| name == "CachedView::miss"));

    let duplicate_left = Counter::new("DuplicateCounter");
    let duplicate_right = Counter::new("DuplicateCounter");
    duplicate_left.increment();
    duplicate_right.increment();

    let duplicate_entries = CountedObjects::get_instance()
        .get_counts(1)
        .into_iter()
        .filter(|(name, count)| name == "DuplicateCounter" && *count == 1)
        .count();
    assert_eq!(duplicate_entries, 2);

    hit_counter.decrement();
    hit_counter.decrement();
    miss_counter.decrement();
    duplicate_left.decrement();
    duplicate_right.decrement();
}

#[test]
fn file_utilities_match_cpp_reference_role() {
    let temp = TempDirGuard::new("file-utilities-parity");
    let path = temp.join("test.txt");
    let expected = b"This file is very short. That's all we need.";

    write_file_contents(&path, expected).unwrap();

    let no_limit = get_file_contents(&path, None).unwrap();
    assert_eq!(no_limit, expected);

    let with_large_limit = get_file_contents(&path, Some(kilobytes(1usize))).unwrap();
    assert_eq!(with_large_limit, expected);

    let too_small = get_file_contents(&path, Some(16)).unwrap_err();
    assert!(matches!(
        too_small,
        FileUtilitiesError::FileTooLarge {
            size: _,
            max_size: 16
        }
    ));

    let overwritten = b"next";
    write_file_contents(&path, overwritten).unwrap();
    assert_eq!(get_file_contents(&path, None).unwrap(), overwritten);

    let missing = temp.path().join("missing.txt");
    let missing_error = get_file_contents(missing, None).unwrap_err();
    assert_eq!(missing_error.io_kind(), Some(std::io::ErrorKind::NotFound));
}

#[test]
fn local_value_matches_thread_local_default_role() {
    let value = Arc::new(LocalValue::new(-1));

    // Default behavior is thread-local.
    assert_eq!(value.get_cloned(), -1);
    let thread_value = {
        let value = Arc::clone(&value);
        thread::spawn(move || {
            assert_eq!(value.get_cloned(), -1);
            value.set(-2);
            value.get_cloned()
        })
    }
    .join()
    .expect("thread should complete");
    assert_eq!(thread_value, -2);
    assert_eq!(value.get_cloned(), -1);
}

#[test]
fn uptime_clock_matches_reference_role() {
    let first = UptimeClock::now();
    let second = UptimeClock::now();

    assert!(second >= first);

    let point = UptimeTimePoint::new(12);
    assert_eq!(point.time_since_epoch().as_secs(), 12);
    assert_eq!((point + std::time::Duration::from_secs(3)).as_seconds(), 15);
    assert_eq!((point - std::time::Duration::from_secs(2)).as_seconds(), 10);
    assert_eq!(point - UptimeTimePoint::new(4), Duration::seconds(8));
    assert_eq!(UptimeTimePoint::new(4) - point, Duration::seconds(-8));
}

#[test]
fn string_utilities_match_reference_role() {
    assert_eq!(str_unhex("526970706c6544").unwrap(), b"RippleD");
    assert_eq!(str_unhex("A").unwrap(), b"\n");
    assert!(str_unhex("XRP").is_none());
    assert_eq!(str_view_unhex("0D0A").unwrap(), b"\r\n");
    assert_eq!(
        sql_blob_literal(&vec![0xde, 0xad, 0xbe, 0xef]),
        "X'DEADBEEF'"
    );

    let parsed = parse_url("scheme://user:pass@domain:123/abc:321").unwrap();
    assert_eq!(
        parsed,
        ParsedUrl {
            scheme: "scheme".into(),
            username: "user".into(),
            password: "pass".into(),
            domain: "domain".into(),
            port: Some(123),
            path: "/abc:321".into(),
        }
    );

    let weird_ipv6 = parse_url("http://::1:1234/validators").unwrap();
    assert_eq!(weird_ipv6.domain, "::0.1.18.52");
    assert_eq!(weird_ipv6.port, None);
    assert_eq!(weird_ipv6.path, "/validators");

    assert!(parse_url("UPPER://domain:0/").is_none());
    assert_eq!(trim_whitespace("  hello \n".to_owned()), "hello");
    assert_eq!(
        trim_whitespace("\u{00a0} hello \u{00a0}".to_owned()),
        "\u{00a0} hello \u{00a0}"
    );
    assert_eq!(to_uint64("42"), Some(42));
    assert_eq!(to_uint64("-1"), None);
    assert!(is_properly_formed_toml_domain("example.com"));
    assert!(!is_properly_formed_toml_domain("example.123"));
}
