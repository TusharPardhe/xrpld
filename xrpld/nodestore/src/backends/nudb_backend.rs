use crate::{
    Backend, Batch, DecodedBlob, EncodedBlob, Factory, JournalLevel, NodeObject, NodeStoreJournal,
    NuDbContext, Scheduler, Status, nodeobject_compress, nodeobject_decompress,
};
use arc_swap::ArcSwapOption;
use basics::base_uint::Uint256;
use basics::basic_config::Section;
use basics::memory::bloom::BloomFilter;
use dashmap::DashMap;
use rayon::prelude::*;
use std::any::Any;
#[cfg(test)]
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use xxhash_rust::xxh64::xxh64;

pub const NUDB_APPNUM: u64 = 1;
pub const NUDB_DEFAULT_BLOCK_SIZE: usize = 4096;
pub const NUDB_MIN_BLOCK_SIZE: usize = 4096;
pub const NUDB_MAX_BLOCK_SIZE: usize = 32_768;
pub const NUDB_TARGET_LOAD_FACTOR: f64 = 0.50;
pub const NUDB_CURRENT_VERSION: u16 = 2;
pub const NUDB_DATA_FILE_TYPE: &[u8; 8] = b"nudb.dat";
pub const NUDB_KEY_FILE_TYPE: &[u8; 8] = b"nudb.key";
pub const NUDB_LOG_FILE_TYPE: &[u8; 8] = b"nudb.log";
pub const NUDB_DATA_FILE_HEADER_SIZE: usize = 92;
/// Max buckets to keep in the in-memory bucket cache.
/// Each bucket is ~4KB; 4096 entries = ~16MB. Prevents OOM on large NuDB.
const MAX_BUCKET_CACHE_ENTRIES: usize = 4096;
/// Bound synchronous c0/c1 commits until the native NuDB asynchronous writer
/// pool is implemented. The configured 40,000 burst is a rate/burst hint in
/// reference NuDB, not permission to hold the foreground mutation fence while
/// logging and flushing 40,000 objects at once.
const MAX_SYNCHRONOUS_BURST_WRITES: usize = 1024;

#[cfg(test)]
fn evict_one_cached_bucket<V>(bucket_cache: &DashMap<u32, V>) {
    let evict_key = bucket_cache.iter().next().map(|entry| *entry.key());
    if let Some(evict_key) = evict_key {
        bucket_cache.remove(&evict_key);
    }
}

fn evict_one_clean_cached_bucket(bucket_cache: &DashMap<u32, CachedBucket>) {
    let evict_key = bucket_cache
        .iter()
        .find_map(|entry| (!entry.value().dirty).then(|| *entry.key()));
    if let Some(evict_key) = evict_key {
        bucket_cache.remove(&evict_key);
    }
}

pub const NUDB_KEY_FILE_HEADER_SIZE: usize = 104;
pub const NUDB_LOG_FILE_HEADER_SIZE: usize = 62;
const NUDB_BUCKET_COUNT_SIZE: usize = 2;
const NUDB_BUCKET_SPILL_SIZE: usize = 6;
const NUDB_BUCKET_ENTRY_SIZE: usize = 18;
const NUDB_SPILL_RECORD_HEADER_SIZE: usize = 8;
const NUDB_U48_MAX: u64 = 0x0000_FFFF_FFFF_FFFF;

#[cfg(test)]
#[derive(Clone, Copy)]
enum NuDbTestCrashPoint {
    PrimaryBucket,
    Split,
}

#[cfg(test)]
#[derive(Clone, Copy)]
enum NuDbTestBatchErrorPoint {
    AfterAppend,
    IndexInsert(usize),
}

#[cfg(test)]
thread_local! {
    static NUDB_TEST_CRASH_AFTER_PRIMARY_BUCKET: Cell<bool> = const { Cell::new(false) };
    static NUDB_TEST_CRASH_AFTER_SPLIT: Cell<bool> = const { Cell::new(false) };
    static NUDB_TEST_BATCH_ERROR_AFTER_APPEND: Cell<bool> = const { Cell::new(false) };
    static NUDB_TEST_BATCH_ERROR_INDEX_INSERT: Cell<Option<usize>> = const { Cell::new(None) };
}

#[cfg(test)]
fn set_nudb_test_batch_error(point: NuDbTestBatchErrorPoint) {
    match point {
        NuDbTestBatchErrorPoint::AfterAppend => {
            NUDB_TEST_BATCH_ERROR_AFTER_APPEND.with(|flag| flag.set(true));
        }
        NuDbTestBatchErrorPoint::IndexInsert(index) => {
            NUDB_TEST_BATCH_ERROR_INDEX_INSERT.with(|value| value.set(Some(index)));
        }
    }
}

#[cfg(test)]
fn nudb_test_batch_error_after_append() -> Result<(), String> {
    if NUDB_TEST_BATCH_ERROR_AFTER_APPEND.with(|flag| flag.replace(false)) {
        Err("injected checked-batch failure after coalesced append".to_owned())
    } else {
        Ok(())
    }
}

#[cfg(test)]
fn nudb_test_batch_error_before_index_insert(index: usize) -> Result<(), String> {
    let requested = NUDB_TEST_BATCH_ERROR_INDEX_INSERT.with(|value| value.get());
    if requested == Some(index) {
        NUDB_TEST_BATCH_ERROR_INDEX_INSERT.with(|value| value.set(None));
        Err(format!(
            "injected checked-batch failure during index insert {index}"
        ))
    } else {
        Ok(())
    }
}

#[cfg(test)]
fn set_nudb_test_crash(point: NuDbTestCrashPoint) {
    match point {
        NuDbTestCrashPoint::PrimaryBucket => {
            NUDB_TEST_CRASH_AFTER_PRIMARY_BUCKET.with(|flag| flag.set(true));
        }
        NuDbTestCrashPoint::Split => {
            NUDB_TEST_CRASH_AFTER_SPLIT.with(|flag| flag.set(true));
        }
    }
}

#[cfg(test)]
fn nudb_test_crash_if_requested(point: NuDbTestCrashPoint, description: &str) {
    let requested = match point {
        NuDbTestCrashPoint::PrimaryBucket => {
            NUDB_TEST_CRASH_AFTER_PRIMARY_BUCKET.with(|flag| flag.replace(false))
        }
        NuDbTestCrashPoint::Split => NUDB_TEST_CRASH_AFTER_SPLIT.with(|flag| flag.replace(false)),
    };
    if requested {
        panic!("NuDB test crash after {description}");
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NuDbFileSetState {
    Missing,
    Complete,
    Partial,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NuDbLayout {
    pub base_path: PathBuf,
    pub data_path: PathBuf,
    pub key_path: PathBuf,
    pub log_path: PathBuf,
}

impl NuDbLayout {
    pub fn from_base_path(path: impl AsRef<Path>) -> Self {
        let base_path = path.as_ref().to_path_buf();
        Self {
            data_path: base_path.join("nudb.dat"),
            key_path: base_path.join("nudb.key"),
            log_path: base_path.join("nudb.log"),
            base_path,
        }
    }

    pub fn file_set_state(&self) -> NuDbFileSetState {
        let existing = [
            self.data_path.exists(),
            self.key_path.exists(),
            self.log_path.exists(),
        ];
        let count = existing.into_iter().filter(|present| *present).count();
        match count {
            0 => NuDbFileSetState::Missing,
            3 => NuDbFileSetState::Complete,
            _ => NuDbFileSetState::Partial,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NuDbOpenArgs {
    pub app_type: u64,
    pub uid: u64,
    pub salt: u64,
}

impl NuDbOpenArgs {
    pub const fn deterministic(app_type: u64, uid: u64, salt: u64) -> Self {
        Self {
            app_type,
            uid,
            salt,
        }
    }

    /// Use Quaxar's NuDB application number. The value is intentionally kept
    /// compatible with existing rippled/Quaxar databases.
    pub const fn quaxar_default(uid: u64, salt: u64) -> Self {
        Self::deterministic(NUDB_APPNUM, uid, salt)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NuDbMetadataHeader {
    pub appnum: u64,
    pub uid: u64,
    pub salt: u64,
    pub key_bytes: usize,
    pub block_size: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NuDbKeyFileHeader {
    pub version: u16,
    pub uid: u64,
    pub appnum: u64,
    pub key_size: u16,
    pub salt: u64,
    pub pepper: u64,
    pub block_size: u16,
    pub load_factor: u16,
    pub capacity: u16,
    pub buckets: u32,
    pub modulus: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NuDbDataFileHeader {
    pub version: u16,
    pub uid: u64,
    pub appnum: u64,
    pub key_size: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NuDbLogFileHeader {
    pub version: u16,
    pub uid: u64,
    pub appnum: u64,
    pub key_size: u16,
    pub salt: u64,
    pub pepper: u64,
    pub block_size: u16,
    pub key_file_size: u64,
    pub dat_file_size: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NuDbBucketEntry {
    offset: u64,
    size: u64,
    hash_prefix: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NuDbBucket {
    block_size: usize,
    capacity: usize,
    spill: u64,
    entries: Vec<NuDbBucketEntry>,
}

impl NuDbKeyFileHeader {
    pub fn from_metadata(header: NuDbMetadataHeader) -> Result<Self, String> {
        let key_size =
            u16::try_from(header.key_bytes).map_err(|_| "NuDB key size exceeds u16".to_owned())?;
        let block_size = u16::try_from(header.block_size)
            .map_err(|_| "NuDB block size exceeds u16".to_owned())?;
        let capacity = nudb_bucket_capacity(block_size);
        Ok(Self {
            version: NUDB_CURRENT_VERSION,
            uid: header.uid,
            appnum: header.appnum,
            key_size,
            salt: header.salt,
            pepper: nudb_pepper(header.salt),
            block_size,
            load_factor: nudb_encode_load_factor(NUDB_TARGET_LOAD_FACTOR)?,
            capacity,
            buckets: 0,
            modulus: 1,
        })
    }

    pub fn validate_basic(&self) -> Result<(), String> {
        if self.version != NUDB_CURRENT_VERSION {
            return Err(format!(
                "Unsupported NuDB key header version: {}",
                self.version
            ));
        }
        if usize::from(self.key_size) < 1 {
            return Err("Invalid NuDB key header key_size".to_owned());
        }
        validate_nudb_block_size(usize::from(self.block_size))?;
        if self.pepper != nudb_pepper(self.salt) {
            return Err("Invalid NuDB key header pepper".to_owned());
        }
        if self.load_factor < 1 {
            return Err("Invalid NuDB key header load_factor".to_owned());
        }
        Ok(())
    }

    pub const fn metadata_header(&self) -> NuDbMetadataHeader {
        NuDbMetadataHeader::new(
            self.appnum,
            self.uid,
            self.salt,
            self.key_size as usize,
            self.block_size as usize,
        )
    }
}

impl NuDbDataFileHeader {
    pub fn from_metadata(header: NuDbMetadataHeader) -> Result<Self, String> {
        let key_size =
            u16::try_from(header.key_bytes).map_err(|_| "NuDB key size exceeds u16".to_owned())?;
        Ok(Self {
            version: NUDB_CURRENT_VERSION,
            uid: header.uid,
            appnum: header.appnum,
            key_size,
        })
    }

    pub fn validate_basic(&self) -> Result<(), String> {
        if self.version != NUDB_CURRENT_VERSION {
            return Err(format!(
                "Unsupported NuDB data header version: {}",
                self.version
            ));
        }
        if usize::from(self.key_size) < 1 {
            return Err("Invalid NuDB data header key_size".to_owned());
        }
        Ok(())
    }

    pub fn validate_against_key(&self, key_header: &NuDbKeyFileHeader) -> Result<(), String> {
        if self.uid != key_header.uid {
            return Err("NuDB data header uid mismatch".to_owned());
        }
        if self.appnum != key_header.appnum {
            return Err("NuDB data header appnum mismatch".to_owned());
        }
        if self.key_size != key_header.key_size {
            return Err("NuDB data header key_size mismatch".to_owned());
        }
        Ok(())
    }
}

impl NuDbLogFileHeader {
    pub fn from_key_header(
        key_header: &NuDbKeyFileHeader,
        key_file_size: u64,
        dat_file_size: u64,
    ) -> Self {
        Self {
            version: key_header.version,
            uid: key_header.uid,
            appnum: key_header.appnum,
            key_size: key_header.key_size,
            salt: key_header.salt,
            pepper: key_header.pepper,
            block_size: key_header.block_size,
            key_file_size,
            dat_file_size,
        }
    }

    pub fn validate_basic(&self) -> Result<(), String> {
        if self.version != NUDB_CURRENT_VERSION {
            return Err(format!(
                "Unsupported NuDB log header version: {}",
                self.version
            ));
        }
        if usize::from(self.key_size) < 1 {
            return Err("Invalid NuDB log header key_size".to_owned());
        }
        if self.pepper != nudb_pepper(self.salt) {
            return Err("Invalid NuDB log header pepper".to_owned());
        }
        validate_nudb_block_size(usize::from(self.block_size))?;
        Ok(())
    }

    pub fn validate_against_key(&self, key_header: &NuDbKeyFileHeader) -> Result<(), String> {
        if self.uid != key_header.uid {
            return Err("NuDB log header uid mismatch".to_owned());
        }
        if self.appnum != key_header.appnum {
            return Err("NuDB log header appnum mismatch".to_owned());
        }
        if self.key_size != key_header.key_size {
            return Err("NuDB log header key_size mismatch".to_owned());
        }
        if self.salt != key_header.salt {
            return Err("NuDB log header salt mismatch".to_owned());
        }
        if self.pepper != key_header.pepper {
            return Err("NuDB log header pepper mismatch".to_owned());
        }
        if self.block_size != key_header.block_size {
            return Err("NuDB log header block_size mismatch".to_owned());
        }
        Ok(())
    }
}

impl NuDbBucket {
    fn empty(block_size: usize, capacity: usize) -> Self {
        Self {
            block_size,
            capacity,
            spill: 0,
            entries: Vec::new(),
        }
    }

    fn read_full_block(block_size: usize, capacity: usize, bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < block_size {
            return Err("NuDB bucket block is truncated".to_owned());
        }
        Self::read_compact(block_size, capacity, &bytes[..block_size])
    }

    fn read_compact(block_size: usize, capacity: usize, bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < NUDB_BUCKET_COUNT_SIZE + NUDB_BUCKET_SPILL_SIZE {
            return Err("NuDB bucket record is truncated".to_owned());
        }
        let mut offset = 0usize;
        let count = usize::from(read_u16_be(bytes, &mut offset)?);
        let spill = read_u48_be(bytes, &mut offset)?;
        if count > capacity {
            return Err("NuDB bucket entry count exceeds capacity".to_owned());
        }
        let needed = offset
            .checked_add(
                count
                    .checked_mul(NUDB_BUCKET_ENTRY_SIZE)
                    .ok_or_else(|| "NuDB bucket size overflow".to_owned())?,
            )
            .ok_or_else(|| "NuDB bucket size overflow".to_owned())?;
        if bytes.len() < needed {
            return Err("NuDB bucket entries are truncated".to_owned());
        }
        let mut entries = Vec::with_capacity(count);
        let mut previous_hash = None;
        for _ in 0..count {
            let entry = NuDbBucketEntry {
                offset: read_u48_be(bytes, &mut offset)?,
                size: read_u48_be(bytes, &mut offset)?,
                hash_prefix: read_u48_be(bytes, &mut offset)?,
            };
            if let Some(previous_hash) = previous_hash
                && entry.hash_prefix < previous_hash
            {
                return Err("NuDB bucket entries are not sorted by hash prefix".to_owned());
            }
            previous_hash = Some(entry.hash_prefix);
            entries.push(entry);
        }
        Ok(Self {
            block_size,
            capacity,
            spill,
            entries,
        })
    }

    fn actual_size(&self) -> usize {
        NUDB_BUCKET_COUNT_SIZE
            + NUDB_BUCKET_SPILL_SIZE
            + self.entries.len() * NUDB_BUCKET_ENTRY_SIZE
    }

    fn is_full(&self) -> bool {
        self.entries.len() >= self.capacity
    }

    fn lower_bound(&self, hash_prefix: u64) -> usize {
        self.entries
            .partition_point(|entry| entry.hash_prefix < hash_prefix)
    }

    fn insert_sorted(&mut self, entry: NuDbBucketEntry) {
        let index = self.lower_bound(entry.hash_prefix);
        self.entries.insert(index, entry);
    }

    fn encode_compact(&self) -> Result<Vec<u8>, String> {
        if self.entries.len() > self.capacity {
            return Err("NuDB bucket overflows configured capacity".to_owned());
        }
        let actual_size = self.actual_size();
        let mut bytes = vec![0u8; actual_size];
        let mut offset = 0usize;
        write_u16_be(
            &mut bytes,
            &mut offset,
            u16::try_from(self.entries.len())
                .map_err(|_| "NuDB bucket entry count exceeds u16".to_owned())?,
        );
        write_u48_be(&mut bytes, &mut offset, self.spill)?;
        for entry in &self.entries {
            write_u48_be(&mut bytes, &mut offset, entry.offset)?;
            write_u48_be(&mut bytes, &mut offset, entry.size)?;
            write_u48_be(&mut bytes, &mut offset, entry.hash_prefix)?;
        }
        Ok(bytes)
    }

    fn encode_key_block(&self) -> Result<Vec<u8>, String> {
        let actual = self.encode_compact()?;
        if self.block_size < actual.len() {
            return Err("NuDB key bucket block is smaller than encoded bucket".to_owned());
        }
        let mut bytes = vec![0u8; self.block_size];
        bytes[..actual.len()].copy_from_slice(&actual);
        Ok(bytes)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NuDbOpenAction {
    CreateNew,
    OpenExisting,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NuDbOpenPlan {
    pub action: NuDbOpenAction,
    pub open_args: NuDbOpenArgs,
    pub metadata_header: NuDbMetadataHeader,
    pub layout: NuDbLayout,
    pub create_if_missing: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NuDbOpenState {
    header: NuDbMetadataHeader,
    delete_path: bool,
    is_open: bool,
}

impl NuDbOpenState {
    pub const fn new(header: NuDbMetadataHeader) -> Self {
        Self {
            header,
            delete_path: false,
            is_open: false,
        }
    }

    pub const fn header(&self) -> NuDbMetadataHeader {
        self.header
    }

    pub const fn is_open(&self) -> bool {
        self.is_open
    }

    pub const fn delete_path(&self) -> bool {
        self.delete_path
    }

    pub fn open(&mut self, expected_appnum: u64) -> Result<(), String> {
        if self.is_open {
            return Err("NuDB backend is already open".to_owned());
        }
        if self.header.appnum != expected_appnum {
            return Err("nodestore: unknown appnum".to_owned());
        }
        self.header.validate_for_quaxar()?;
        self.is_open = true;
        Ok(())
    }

    pub fn close(&mut self) {
        self.is_open = false;
    }

    pub fn set_delete_path(&mut self) {
        self.delete_path = true;
    }
}

impl NuDbMetadataHeader {
    pub const fn new(
        appnum: u64,
        uid: u64,
        salt: u64,
        key_bytes: usize,
        block_size: usize,
    ) -> Self {
        Self {
            appnum,
            uid,
            salt,
            key_bytes,
            block_size,
        }
    }

    pub fn validate_for_quaxar(&self) -> Result<(), String> {
        if self.appnum != NUDB_APPNUM {
            return Err("nodestore: unknown appnum".to_owned());
        }
        validate_nudb_block_size(self.block_size)?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NuDbBackendConfig {
    pub key_bytes: usize,
    pub burst_size: usize,
    pub path: String,
    pub block_size: usize,
    pub layout: NuDbLayout,
    /// When true, the backend maintains an in-memory Bloom filter of stored
    /// keys so callers can skip authoritative reads for guaranteed-absent
    /// keys. Default false: no behavior change unless explicitly enabled via
    /// `bloom_filter = 1` in the node_db section.
    pub bloom_enabled: bool,
    /// Bits per key for the Bloom filter sizing (accuracy vs memory). Default
    /// 10 (~1% false-positive rate). Ignored when `bloom_enabled` is false.
    pub bloom_bits_per_key: usize,
    /// Expected key count used to size the Bloom filter at open time when the
    /// live count is not yet known. Default 0 lets the backend derive size
    /// from the on-disk key count during the build pass.
    pub bloom_expected_keys: usize,
}

impl NuDbBackendConfig {
    pub fn from_section(
        key_bytes: usize,
        parameters: &Section,
        burst_size: usize,
        journal: &dyn NodeStoreJournal,
    ) -> Result<Self, String> {
        let path = parameters
            .get::<String>("path")
            .ok()
            .flatten()
            .unwrap_or_default();
        if path.is_empty() {
            return Err("nodestore: Missing path in NuDB backend".to_owned());
        }

        let block_size = parse_nudb_block_size(parameters, journal)?;
        let layout = NuDbLayout::from_base_path(&path);

        // Bloom filter is opt-in and defaults off so behavior is unchanged
        // unless an operator enables it. `bloom_filter` accepts 1/true; any
        // other value (or absence) leaves it disabled.
        let bloom_enabled = parameters
            .get::<String>("bloom_filter")
            .ok()
            .flatten()
            .map(|value| matches!(value.trim(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false);
        let bloom_bits_per_key = parameters
            .get::<usize>("bloom_bits_per_key")
            .ok()
            .flatten()
            .filter(|bits| *bits > 0)
            .unwrap_or(10);
        let bloom_expected_keys = parameters
            .get::<usize>("bloom_expected_keys")
            .ok()
            .flatten()
            .unwrap_or(0);

        Ok(Self {
            key_bytes,
            burst_size,
            path,
            block_size,
            layout,
            bloom_enabled,
            bloom_bits_per_key,
            bloom_expected_keys,
        })
    }

    pub const fn metadata_header(&self, open_args: NuDbOpenArgs) -> NuDbMetadataHeader {
        NuDbMetadataHeader::new(
            open_args.app_type,
            open_args.uid,
            open_args.salt,
            self.key_bytes,
            self.block_size,
        )
    }

    pub fn build_open_plan(
        &self,
        create_if_missing: bool,
        open_args: NuDbOpenArgs,
    ) -> Result<NuDbOpenPlan, String> {
        let action = match self.layout.file_set_state() {
            NuDbFileSetState::Complete => NuDbOpenAction::OpenExisting,
            NuDbFileSetState::Missing if create_if_missing => NuDbOpenAction::CreateNew,
            NuDbFileSetState::Missing => {
                return Err(format!("Unable to open/create NuDB backend: {}", self.path));
            }
            NuDbFileSetState::Partial => {
                return Err(format!(
                    "Incomplete NuDB file set at {}. Expected nudb.dat, nudb.key, and nudb.log",
                    self.path
                ));
            }
        };

        Ok(NuDbOpenPlan {
            action,
            open_args,
            metadata_header: self.metadata_header(open_args),
            layout: self.layout.clone(),
            create_if_missing,
        })
    }

    pub fn create_empty_file_set_for_tests(&self) -> Result<(), String> {
        fs::create_dir_all(&self.layout.base_path).map_err(|error| error.to_string())?;
        for path in [
            &self.layout.data_path,
            &self.layout.key_path,
            &self.layout.log_path,
        ] {
            fs::write(path, []).map_err(|error| error.to_string())?;
        }
        Ok(())
    }

    pub fn write_key_file_header_for_tests(
        &self,
        header: &NuDbKeyFileHeader,
    ) -> Result<(), String> {
        fs::create_dir_all(&self.layout.base_path).map_err(|error| error.to_string())?;
        let mut file =
            fs::File::create(&self.layout.key_path).map_err(|error| error.to_string())?;
        let bytes = encode_nudb_key_file_header(header)?;
        file.write_all(&bytes).map_err(|error| error.to_string())?;
        file.flush().map_err(|error| error.to_string())
    }

    pub fn write_data_file_header_for_tests(
        &self,
        header: &NuDbDataFileHeader,
    ) -> Result<(), String> {
        fs::create_dir_all(&self.layout.base_path).map_err(|error| error.to_string())?;
        let mut file =
            fs::File::create(&self.layout.data_path).map_err(|error| error.to_string())?;
        let bytes = encode_nudb_data_file_header(header)?;
        file.write_all(&bytes).map_err(|error| error.to_string())?;
        file.flush().map_err(|error| error.to_string())
    }

    pub fn write_log_file_header_for_tests(
        &self,
        header: &NuDbLogFileHeader,
    ) -> Result<(), String> {
        fs::create_dir_all(&self.layout.base_path).map_err(|error| error.to_string())?;
        let mut file =
            fs::File::create(&self.layout.log_path).map_err(|error| error.to_string())?;
        let bytes = encode_nudb_log_file_header(header)?;
        file.write_all(&bytes).map_err(|error| error.to_string())?;
        file.flush().map_err(|error| error.to_string())
    }
}

#[derive(Debug)]
struct NuDbBackendRuntime {
    open_state: NuDbOpenState,
    key_header: Option<NuDbKeyFileHeader>,
    split_fraction: u64,
    split_threshold: u64,
    burst_pending_writes: usize,
    burst_checkpoint_active: bool,
    fail_stop_error: Option<String>,
}

/// Original key buckets touched by the active burst.
///
/// NuDB's recovery log contains the pre-mutation version of only the buckets
/// changed by a commit (its `c0` cache), not a snapshot of the complete key
/// file. `store_mutex` serializes all mutation of this map; the separate mutex
/// exists because split processing already holds `runtime` while updating key
/// buckets.
#[derive(Default)]
struct NuDbBurstOriginals {
    active: bool,
    original_bucket_count: u32,
    buckets: BTreeMap<u32, NuDbBucket>,
}

impl NuDbBackendRuntime {
    fn new(initial_header: NuDbMetadataHeader) -> Self {
        Self {
            open_state: NuDbOpenState::new(initial_header),
            key_header: None,
            split_fraction: 0,
            split_threshold: 0,
            burst_pending_writes: 0,
            burst_checkpoint_active: false,
            fail_stop_error: None,
        }
    }
}

#[derive(Default, Debug)]
pub struct NuDbMetrics {
    pub mmap_hits: AtomicUsize,
    pub dirty_overlay_hits: AtomicUsize,
    pub spill_reads: AtomicUsize,
    pub batch_fetch_count: AtomicUsize,
    pub batch_fetch_parallel_count: AtomicUsize,
    pub batch_grouping_efficiency_pct: AtomicUsize,
    pub fused_read_bytes: AtomicUsize,
    pub store_batch_coalesced_bytes: AtomicUsize,
    pub store_lock_wait_ns: AtomicU64,
    pub store_lock_hold_ns: AtomicU64,
    pub burst_checkpoint_ns: AtomicU64,
    pub burst_flush_ns: AtomicU64,
    pub burst_sync_ns: AtomicU64,
    pub burst_commit_count: AtomicUsize,
    /// Number of fetches short-circuited to NotFound by the Bloom skip gate
    /// (guaranteed-absent keys that avoided a bucket/data read).
    pub bloom_skipped_reads: AtomicUsize,
}

struct StoreLockTiming<'a> {
    metrics: &'a NuDbMetrics,
    started: Instant,
}

impl<'a> StoreLockTiming<'a> {
    fn new(metrics: &'a NuDbMetrics) -> Self {
        Self {
            metrics,
            started: Instant::now(),
        }
    }
}

impl Drop for StoreLockTiming<'_> {
    fn drop(&mut self) {
        self.metrics
            .store_lock_hold_ns
            .fetch_add(self.started.elapsed().as_nanos() as u64, Ordering::Relaxed);
    }
}

#[derive(Clone)]
struct CachedBucket {
    bucket: NuDbBucket,
    dirty: bool,
}

pub struct NuDbBackend {
    config: NuDbBackendConfig,
    journal: Arc<dyn NodeStoreJournal>,
    runtime: Mutex<NuDbBackendRuntime>,
    store_mutex: Mutex<()>,
    /// Prevent readers from observing a partially rewritten on-disk key bucket.
    key_bucket_io: RwLock<()>,
    default_open_args: Option<NuDbOpenArgs>,
    persistent_fds: ArcSwapOption<NuDbPersistentFds>,
    /// Bucket cache matching reference NuDB's detail::cache. Clean entries
    /// avoid pread calls; only bulk-import entries remain dirty for a later
    /// write-back flush.
    bucket_cache: DashMap<u32, CachedBucket>,
    burst_originals: Mutex<NuDbBurstOriginals>,
    /// Track data/key file sizes in memory to avoid fstat() syscalls.
    data_file_size: AtomicU64,
    key_file_size: AtomicU64,
    /// When true, store() skips existence checks and burst checkpoints for fast bulk loading.
    bulk_importing: AtomicBool,
    /// Optional in-memory Bloom filter of stored keys. Present only when
    /// `config.bloom_enabled` is true. Consulted in `fetch`/`fetch_batch`/
    /// `may_contain` to skip guaranteed-absent reads, and updated on every
    /// successful store. Wrapped in `ArcSwapOption` so it can be rebuilt at
    /// open time and evicted (set to `None`) to reclaim RAM when no longer
    /// needed (for example after history backfill completes).
    bloom: ArcSwapOption<BloomFilter>,
    pub metrics: Arc<NuDbMetrics>,
}

/// Persistent file descriptors for NuDB key and data files.
/// Uses pread/pwrite for thread-safe positional I/O without seeking.
struct NuDbPersistentFds {
    key_read: fs::File,
    key_write: fs::File,
    data_read: fs::File,
    data_write: fs::File,
    key_mmap: Option<memmap2::Mmap>,
}

impl NuDbPersistentFds {
    fn open(layout: &NuDbLayout) -> Result<Self, String> {
        let key_read =
            fs::File::open(&layout.key_path).map_err(|e| format!("NuDB open key_read: {e}"))?;
        let key_write = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&layout.key_path)
            .map_err(|e| format!("NuDB open key_write: {e}"))?;
        let data_read =
            fs::File::open(&layout.data_path).map_err(|e| format!("NuDB open data_read: {e}"))?;
        let data_write = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&layout.data_path)
            .map_err(|e| format!("NuDB open data_write: {e}"))?;

        // Load mmap for key file
        let key_mmap = unsafe { memmap2::MmapOptions::new().map(&key_read).ok() };

        Ok(Self {
            key_read,
            key_write,
            data_read,
            data_write,
            key_mmap,
        })
    }
}

impl NuDbBackend {
    pub fn new(
        key_bytes: usize,
        parameters: &Section,
        burst_size: usize,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Self, String> {
        Self::new_with_default_open_args(key_bytes, parameters, burst_size, journal, None)
    }

    pub fn new_with_default_open_args(
        key_bytes: usize,
        parameters: &Section,
        burst_size: usize,
        journal: Arc<dyn NodeStoreJournal>,
        default_open_args: Option<NuDbOpenArgs>,
    ) -> Result<Self, String> {
        let config =
            NuDbBackendConfig::from_section(key_bytes, parameters, burst_size, journal.as_ref())?;
        let initial_header = config.metadata_header(
            default_open_args.unwrap_or_else(|| NuDbOpenArgs::quaxar_default(0, 0)),
        );
        Ok(Self {
            config,
            journal,
            runtime: Mutex::new(NuDbBackendRuntime::new(initial_header)),
            store_mutex: Mutex::new(()),
            key_bucket_io: RwLock::new(()),
            default_open_args,
            persistent_fds: ArcSwapOption::empty(),
            bucket_cache: DashMap::new(),
            burst_originals: Mutex::new(NuDbBurstOriginals::default()),
            data_file_size: AtomicU64::new(0),
            key_file_size: AtomicU64::new(0),
            bulk_importing: AtomicBool::new(false),
            bloom: ArcSwapOption::empty(),
            metrics: Arc::new(NuDbMetrics::default()),
        })
    }

    /// Read from the key file at a specific offset using pread (no seek needed).
    /// pread is thread-safe — no locking needed for concurrent reads.
    fn pread_key(&self, offset: u64, buf: &mut [u8]) -> Result<(), String> {
        #[cfg(unix)]
        {
            let fds_arc = self.persistent_fds.load();
            if let Some(fds) = fds_arc.as_deref() {
                // Mmap hit path
                if let Some(mmap) = &fds.key_mmap {
                    let len = buf.len();
                    let offset_usize = offset as usize;
                    if offset_usize + len <= mmap.len() {
                        buf.copy_from_slice(&mmap[offset_usize..offset_usize + len]);
                        self.metrics.mmap_hits.fetch_add(1, Ordering::Relaxed);
                        return Ok(());
                    }
                }

                use std::os::unix::fs::FileExt;
                return fds
                    .key_read
                    .read_exact_at(buf, offset)
                    .map_err(|e| format!("NuDB pread key @{offset}: {e}"));
            }
        }
        let mut file = fs::File::open(&self.config.layout.key_path).map_err(|e| e.to_string())?;
        file.seek(SeekFrom::Start(offset))
            .map_err(|e| e.to_string())?;
        file.read_exact(buf).map_err(|e| e.to_string())
    }

    /// Read from the data file at a specific offset using pread.
    fn pread_data(&self, offset: u64, buf: &mut [u8]) -> Result<(), String> {
        #[cfg(unix)]
        {
            let fds_arc = self.persistent_fds.load();
            if let Some(fds) = fds_arc.as_deref() {
                use std::os::unix::fs::FileExt;
                return fds
                    .data_read
                    .read_exact_at(buf, offset)
                    .map_err(|e| format!("NuDB pread data @{offset}: {e}"));
            }
        }
        let mut file = fs::File::open(&self.config.layout.data_path).map_err(|e| e.to_string())?;
        file.seek(SeekFrom::Start(offset))
            .map_err(|e| e.to_string())?;
        file.read_exact(buf).map_err(|e| e.to_string())
    }

    /// Write to the key file at a specific offset using pwrite.
    fn pwrite_key(&self, offset: u64, buf: &[u8]) -> Result<(), String> {
        let fds_arc = self.persistent_fds.load();
        if let Some(fds) = fds_arc.as_deref() {
            #[cfg(unix)]
            {
                use std::os::unix::fs::FileExt;
                return fds
                    .key_write
                    .write_all_at(buf, offset)
                    .map_err(|e| format!("NuDB pwrite key @{offset}: {e}"));
            }
        }
        let mut file = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&self.config.layout.key_path)
            .map_err(|e| e.to_string())?;
        file.seek(SeekFrom::Start(offset))
            .map_err(|e| e.to_string())?;
        file.write_all(buf).map_err(|e| e.to_string())?;
        file.flush().map_err(|e| e.to_string())
    }

    /// Append to the data file, returning the offset where data was written.
    fn append_data(&self, buf: &[u8]) -> Result<u64, String> {
        let fds_arc = self.persistent_fds.load();
        if let Some(fds) = fds_arc.as_deref() {
            #[cfg(unix)]
            {
                use std::os::unix::fs::FileExt;
                let offset = self.data_file_size.load(Ordering::Relaxed);
                fds.data_write
                    .write_all_at(buf, offset)
                    .map_err(|e| format!("NuDB append data @{offset}: {e}"))?;
                self.data_file_size
                    .store(offset + buf.len() as u64, Ordering::Relaxed);
                return Ok(offset);
            }
        }
        let mut file = fs::OpenOptions::new()
            .append(true)
            .open(&self.config.layout.data_path)
            .map_err(|e| e.to_string())?;
        let offset = file.seek(SeekFrom::End(0)).map_err(|e| e.to_string())?;
        file.write_all(buf).map_err(|e| e.to_string())?;
        file.flush().map_err(|e| e.to_string())?;
        Ok(offset)
    }

    /// Append to the key file, returning the offset where data was written.
    fn append_key(&self, buf: &[u8]) -> Result<u64, String> {
        let fds_arc = self.persistent_fds.load();
        if let Some(fds) = fds_arc.as_deref() {
            #[cfg(unix)]
            {
                use std::os::unix::fs::FileExt;
                let offset = self.key_file_size.load(Ordering::Relaxed);
                fds.key_write
                    .write_all_at(buf, offset)
                    .map_err(|e| format!("NuDB append key @{offset}: {e}"))?;
                self.key_file_size
                    .store(offset + buf.len() as u64, Ordering::Relaxed);
                return Ok(offset);
            }
        }
        let mut file = fs::OpenOptions::new()
            .append(true)
            .open(&self.config.layout.key_path)
            .map_err(|e| e.to_string())?;
        let offset = file.seek(SeekFrom::End(0)).map_err(|e| e.to_string())?;
        file.write_all(buf).map_err(|e| e.to_string())?;
        file.flush().map_err(|e| e.to_string())?;
        Ok(offset)
    }

    fn build_random_open_args(&self) -> NuDbOpenArgs {
        static NONCE_COUNTER: AtomicU64 = AtomicU64::new(1);
        let now_nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos() as u64;
        let counter = NONCE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = u64::from(std::process::id());
        let uid = now_nanos ^ counter.rotate_left(17) ^ (pid << 32);
        let salt = now_nanos.rotate_left(7) ^ counter.rotate_left(29) ^ pid;
        NuDbOpenArgs::quaxar_default(uid.max(1), salt.max(1))
    }

    /// Builds the in-memory Bloom filter from the current on-disk key set when
    /// `config.bloom_enabled` is true. Called after the backend is open (so the
    /// runtime lock is released and `for_each` can acquire its own locks). This
    /// is O(number of stored keys); it is a no-op when the filter is disabled.
    ///
    /// The filter is sized from `bloom_expected_keys` if configured, otherwise
    /// from a first counting pass over the store, so it is right-sized without
    /// requiring the operator to know the key count.
    fn build_bloom_if_enabled(&self) {
        if !self.config.bloom_enabled {
            return;
        }
        let started = Instant::now();

        // Determine capacity: prefer the configured hint, else count keys.
        let expected = if self.config.bloom_expected_keys > 0 {
            self.config.bloom_expected_keys
        } else {
            let mut count = 0usize;
            self.for_each(&mut |_object| {
                count += 1;
            });
            count.max(1)
        };

        let filter = BloomFilter::with_capacity(expected, self.config.bloom_bits_per_key);
        let mut inserted = 0usize;
        self.for_each(&mut |object| {
            filter.insert(object.get_hash());
            inserted += 1;
        });
        let memory_bytes = filter.memory_bytes();
        self.bloom.store(Some(Arc::new(filter)));
        tracing::info!(
            target: "nodestore",
            path = %self.config.path,
            keys = inserted,
            memory_bytes,
            bits_per_key = self.config.bloom_bits_per_key,
            elapsed_ms = started.elapsed().as_millis() as u64,
            "NuDB bloom filter built"
        );
    }

    /// Records a key into the Bloom filter if one is active. Cheap no-op when
    /// the filter is disabled or not yet built. Called on every successful
    /// store so the filter never lags behind the durable key set.
    #[inline]
    fn bloom_insert(&self, hash: &Uint256) {
        if let Some(filter) = self.bloom.load().as_deref() {
            filter.insert(hash);
        }
    }

    /// Evicts the Bloom filter, freeing its RAM. Used when a transient filter
    /// (for example one built to accelerate history backfill) is no longer
    /// needed. Safe to call at any time: subsequent `may_contain` calls simply
    /// return `true` (must-check) until a filter is rebuilt.
    pub fn evict_bloom(&self) {
        if self.bloom.load().is_some() {
            self.bloom.store(None);
            tracing::info!(target: "nodestore", path = %self.config.path, "NuDB bloom filter evicted");
        }
    }

    /// Returns whether a Bloom filter is currently active for this backend.
    pub fn has_bloom(&self) -> bool {
        self.bloom.load().is_some()
    }

    /// Returns the Bloom filter's resident bytes, or 0 when none is active.
    pub fn bloom_memory_bytes(&self) -> usize {
        self.bloom
            .load()
            .as_deref()
            .map(BloomFilter::memory_bytes)
            .unwrap_or(0)
    }

    fn create_file_set(&self, plan: &NuDbOpenPlan) -> Result<NuDbKeyFileHeader, String> {
        fs::create_dir_all(&plan.layout.base_path).map_err(|error| error.to_string())?;

        let key_header = NuDbKeyFileHeader::from_metadata(plan.metadata_header)?;
        let data_header = NuDbDataFileHeader::from_metadata(plan.metadata_header)?;
        let data_bytes = encode_nudb_data_file_header(&data_header)?;
        let key_bytes = encode_nudb_key_file_header(&key_header)?;
        fs::write(&plan.layout.data_path, data_bytes).map_err(|error| error.to_string())?;
        let mut key_file =
            fs::File::create(&plan.layout.key_path).map_err(|error| error.to_string())?;
        key_file
            .write_all(&key_bytes)
            .map_err(|error| error.to_string())?;
        key_file.flush().map_err(|error| error.to_string())?;
        fs::File::create(&plan.layout.log_path).map_err(|error| error.to_string())?;

        read_nudb_key_file_header(&plan.layout.key_path)
    }

    fn clear_log_file(&self) -> Result<(), String> {
        // Do not truncate the active log inode in place. A stale descriptor can
        // otherwise append at its former offset after the truncate, turning an
        // empty log into a large zero-filled file that fails header validation
        // on the next open. Replacing the pathname atomically leaves any such
        // stale writer attached to the unlinked old inode instead.
        let temporary_path = self
            .config
            .layout
            .log_path
            .with_extension(format!("log.clear-{}", std::process::id()));
        let file = fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&temporary_path)
            .map_err(|error| error.to_string())?;
        file.sync_all().map_err(|error| error.to_string())?;
        fs::rename(&temporary_path, &self.config.layout.log_path)
            .map_err(|error| error.to_string())?;

        // Persist the directory entry as well as the empty replacement file.
        // Opening a directory is supported on the Unix deployment targets.
        #[cfg(unix)]
        {
            fs::File::open(&self.config.layout.base_path)
                .and_then(|directory| directory.sync_all())
                .map_err(|error| error.to_string())
        }

        #[cfg(not(unix))]
        Ok(())
    }

    fn write_log_checkpoint(&self, key_header: &NuDbKeyFileHeader) -> Result<(), String> {
        let key_file_size = fs::metadata(&self.config.layout.key_path)
            .map_err(|error| error.to_string())?
            .len();
        let dat_file_size = fs::metadata(&self.config.layout.data_path)
            .map_err(|error| error.to_string())?
            .len();
        let log_header =
            NuDbLogFileHeader::from_key_header(key_header, key_file_size, dat_file_size);
        let header_bytes = encode_nudb_log_file_header(&log_header)?;

        let mut file = fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(true)
            .open(&self.config.layout.log_path)
            .map_err(|error| error.to_string())?;
        file.write_all(&header_bytes)
            .map_err(|error| error.to_string())?;
        file.flush().map_err(|error| error.to_string())?;
        file.sync_all().map_err(|error| error.to_string())
    }

    /// Append the pre-burst versions of the buckets that will be overwritten.
    /// The header checkpoint is already durable before any data/key-file
    /// growth. These records are made durable immediately before dirty buckets
    /// are flushed, preserving NuDB's c0 -> log -> c1 ordering.
    fn append_burst_originals_to_log(&self) -> Result<(), String> {
        let originals = self
            .burst_originals
            .lock()
            .expect("nudb burst originals mutex must not be poisoned");
        if originals.buckets.is_empty() {
            return Ok(());
        }
        let mut file = fs::OpenOptions::new()
            .append(true)
            .open(&self.config.layout.log_path)
            .map_err(|error| error.to_string())?;
        for (bucket_index, bucket) in &originals.buckets {
            file.write_all(&u64::from(*bucket_index).to_be_bytes())
                .map_err(|error| error.to_string())?;
            file.write_all(&bucket.encode_compact()?)
                .map_err(|error| error.to_string())?;
        }
        file.flush().map_err(|error| error.to_string())?;
        file.sync_all().map_err(|error| error.to_string())
    }

    fn recover_from_log_if_needed(&self, key_header: &NuDbKeyFileHeader) -> Result<(), String> {
        let log_size = fs::metadata(&self.config.layout.log_path)
            .map_err(|error| error.to_string())?
            .len();
        if log_size == 0 {
            return Ok(());
        }
        if log_size < NUDB_LOG_FILE_HEADER_SIZE as u64 {
            return self.clear_log_file();
        }

        let log_header = read_nudb_log_file_header(&self.config.layout.log_path)?;
        log_header.validate_against_key(key_header)?;

        let mut log_file =
            fs::File::open(&self.config.layout.log_path).map_err(|error| error.to_string())?;
        log_file
            .seek(SeekFrom::Start(NUDB_LOG_FILE_HEADER_SIZE as u64))
            .map_err(|error| error.to_string())?;

        let mut key_file = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&self.config.layout.key_path)
            .map_err(|error| error.to_string())?;

        let mut offset = NUDB_LOG_FILE_HEADER_SIZE as u64;
        while offset < log_size {
            let remaining = log_size - offset;
            if remaining < 8 {
                break;
            }
            let bucket_index = read_u64_be_from_reader(&mut log_file, "NuDB log bucket index")?;
            offset += 8;
            let bucket_index = u32::try_from(bucket_index)
                .map_err(|_| "NuDB log bucket index exceeds u32".to_owned())?;

            let bucket_start = log_file
                .stream_position()
                .map_err(|error| error.to_string())?;
            let mut bucket_prefix = [0u8; NUDB_BUCKET_COUNT_SIZE + NUDB_BUCKET_SPILL_SIZE];
            match log_file.read_exact(&mut bucket_prefix) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::UnexpectedEof => {
                    break;
                }
                Err(error) => return Err(error.to_string()),
            }
            let mut bucket_offset = 0usize;
            let count = usize::from(read_u16_be(&bucket_prefix, &mut bucket_offset)?);
            let compact_size = NUDB_BUCKET_COUNT_SIZE
                + NUDB_BUCKET_SPILL_SIZE
                + count
                    .checked_mul(NUDB_BUCKET_ENTRY_SIZE)
                    .ok_or_else(|| "NuDB log bucket size overflow".to_owned())?;
            log_file
                .seek(SeekFrom::Start(bucket_start))
                .map_err(|error| error.to_string())?;
            let mut compact = vec![0u8; compact_size];
            match log_file.read_exact(&mut compact) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::UnexpectedEof => {
                    break;
                }
                Err(error) => return Err(error.to_string()),
            }
            offset += u64::try_from(compact_size).expect("compact size must fit u64");

            let bucket = NuDbBucket::read_compact(
                usize::from(key_header.block_size),
                usize::from(key_header.capacity),
                &compact,
            )?;
            let key_offset = u64::from(bucket_index + 1) * u64::from(key_header.block_size);
            key_file
                .seek(SeekFrom::Start(key_offset))
                .map_err(|error| error.to_string())?;
            key_file
                .write_all(&bucket.encode_key_block()?)
                .map_err(|error| error.to_string())?;
        }

        key_file.flush().map_err(|error| error.to_string())?;
        key_file.sync_all().map_err(|error| error.to_string())?;

        // Bucket records are selective c0 preimages, not a dense snapshot of
        // the key file. Their highest index therefore says nothing about the
        // saved file extent. Always restore the exact checkpoint size; this
        // also discards buckets appended by an interrupted split.
        let recovered_key_file_size = log_header.key_file_size;

        let key_file = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&self.config.layout.key_path)
            .map_err(|error| error.to_string())?;
        key_file
            .set_len(recovered_key_file_size)
            .map_err(|error| error.to_string())?;
        key_file.sync_all().map_err(|error| error.to_string())?;

        let data_file = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&self.config.layout.data_path)
            .map_err(|error| error.to_string())?;
        data_file
            .set_len(log_header.dat_file_size)
            .map_err(|error| error.to_string())?;
        data_file.sync_all().map_err(|error| error.to_string())?;

        self.clear_log_file()
    }

    fn read_existing_header(&self, plan: &NuDbOpenPlan) -> Result<NuDbKeyFileHeader, String> {
        let mut key_header = read_nudb_key_file_header(&plan.layout.key_path)?;
        if usize::from(key_header.key_size) != self.config.key_bytes {
            return Err(format!(
                "NuDB key file key_size mismatch: expected {} got {}",
                self.config.key_bytes, key_header.key_size
            ));
        }
        let data_header = read_nudb_data_file_header(&plan.layout.data_path)?;
        data_header.validate_against_key(&key_header)?;

        self.recover_from_log_if_needed(&key_header)?;
        key_header = read_nudb_key_file_header(&plan.layout.key_path)?;
        read_nudb_data_file_header(&plan.layout.data_path)?.validate_against_key(&key_header)?;

        Ok(key_header)
    }

    fn open_with_args(
        &self,
        create_if_missing: bool,
        open_args: NuDbOpenArgs,
    ) -> Result<(), String> {
        // Check for incomplete bulk import (crash recovery marker)
        let marker_path = self
            .config
            .layout
            .base_path
            .join(".bulk_import_in_progress");
        if marker_path.exists() {
            return Err(
                "NuDB bulk import was interrupted. Delete NuDB files and re-import.".to_owned(),
            );
        }

        let mut runtime = self
            .runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned");
        if runtime.open_state.is_open() {
            return Err("NuDB backend is already open".to_owned());
        }

        let plan = self.config.build_open_plan(create_if_missing, open_args)?;
        let header = match plan.action {
            NuDbOpenAction::CreateNew => self.create_file_set(&plan)?,
            NuDbOpenAction::OpenExisting => self.read_existing_header(&plan)?,
        };

        let delete_path = runtime.open_state.delete_path();
        let mut open_state = NuDbOpenState::new(header.metadata_header());
        if delete_path {
            open_state.set_delete_path();
        }
        open_state.open(open_args.app_type)?;

        // Open persistent file descriptors for pread/pwrite I/O.
        let fds = NuDbPersistentFds::open(&plan.layout)?;
        // Initialize file size tracking from actual file sizes
        let data_size = fds.data_write.metadata().map_err(|e| e.to_string())?.len();
        let key_size = fds.key_write.metadata().map_err(|e| e.to_string())?.len();
        self.data_file_size.store(data_size, Ordering::Relaxed);
        self.key_file_size.store(key_size, Ordering::Relaxed);
        self.persistent_fds.store(Some(Arc::new(fds)));

        // Publish the recovered/open runtime only after fresh descriptors are
        // installed. Until this point concurrent callers still observe the
        // closed, fail-stopped generation.
        runtime.open_state = open_state;
        runtime.key_header = Some(header);
        runtime.split_threshold = nudb_split_threshold(&header);
        runtime.split_fraction = runtime.split_threshold / 2;
        runtime.burst_pending_writes = 0;
        runtime.burst_checkpoint_active = false;
        runtime.fail_stop_error = None;
        {
            let mut originals = self
                .burst_originals
                .lock()
                .expect("nudb burst originals mutex must not be poisoned");
            originals.active = false;
            originals.original_bucket_count = 0;
            originals.buckets.clear();
        }

        tracing::info!(target: "nodestore", path = %self.config.path, "Database opened");

        Ok(())
    }

    fn burst_commit_limit(&self) -> usize {
        self.config
            .burst_size
            .max(1)
            .min(MAX_SYNCHRONOUS_BURST_WRITES)
    }

    fn fail_stop_error(&self) -> Option<String> {
        self.runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned")
            .fail_stop_error
            .clone()
    }

    fn ensure_not_fail_stopped(&self) -> Result<(), String> {
        match self.fail_stop_error() {
            Some(error) => Err(format!("NuDB backend is fail-stopped: {error}")),
            None => Ok(()),
        }
    }

    fn fail_stop_write_if_checkpointed(&self, error: String) -> String {
        let fail_stop = {
            let mut runtime = self
                .runtime
                .lock()
                .expect("nudb backend runtime mutex must not be poisoned");
            if runtime.burst_checkpoint_active {
                let fail_stop = runtime
                    .fail_stop_error
                    .get_or_insert_with(|| error.clone())
                    .clone();
                Some(fail_stop)
            } else {
                None
            }
        };
        if let Some(fail_stop) = fail_stop {
            let message = format!(
                "NuDB checked batch failed after recovery checkpoint; backend is fail-stopped: {fail_stop}"
            );
            self.journal.log(JournalLevel::Fatal, &message);
            tracing::error!(target: "nodestore", error = %fail_stop, "NuDB backend entered fail-stop state");
        }
        error
    }

    /// Flush only buckets that bulk import intentionally kept in memory.
    fn flush_bucket_cache(&self) -> Result<(), String> {
        let key_header = self.current_key_header()?;
        let mut buckets: Vec<(u32, NuDbBucket)> = self
            .bucket_cache
            .iter()
            .filter_map(|entry| {
                (entry.value().dirty && *entry.key() < key_header.buckets)
                    .then(|| (*entry.key(), entry.value().bucket.clone()))
            })
            .collect();
        buckets.sort_unstable_by_key(|(idx, _)| *idx);
        for (bucket_index, bucket) in &buckets {
            let offset = u64::from(*bucket_index + 1) * u64::from(key_header.block_size);
            let bytes = bucket.encode_key_block()?;
            self.pwrite_key(offset, &bytes)?;
        }
        for (bucket_index, _) in buckets {
            if let Some(mut cached) = self.bucket_cache.get_mut(&bucket_index) {
                cached.dirty = false;
            }
        }
        Ok(())
    }

    fn begin_burst_checkpoint_if_needed(
        &self,
        key_header: &NuDbKeyFileHeader,
    ) -> Result<(), String> {
        let should_write_checkpoint = {
            let mut runtime = self
                .runtime
                .lock()
                .expect("nudb backend runtime mutex must not be poisoned");
            if !runtime.open_state.is_open() {
                return Err("NuDB backend is not open".to_owned());
            }
            if runtime.burst_checkpoint_active {
                false
            } else {
                runtime.burst_checkpoint_active = true;
                true
            }
        };

        if !should_write_checkpoint {
            return Ok(());
        }

        let checkpoint_started = Instant::now();
        if let Err(error) = self.write_log_checkpoint(key_header) {
            self.runtime
                .lock()
                .expect("nudb backend runtime mutex must not be poisoned")
                .burst_checkpoint_active = false;
            return Err(error);
        }
        {
            let mut originals = self
                .burst_originals
                .lock()
                .expect("nudb burst originals mutex must not be poisoned");
            originals.original_bucket_count = key_header.buckets;
            originals.active = true;
            originals.buckets.clear();
        }
        self.metrics.burst_checkpoint_ns.fetch_add(
            checkpoint_started.elapsed().as_nanos() as u64,
            Ordering::Relaxed,
        );
        Ok(())
    }

    fn sync_data_files(&self) -> Result<(), String> {
        let fds_arc = self.persistent_fds.load();
        let Some(fds) = fds_arc.as_deref() else {
            return Ok(());
        };
        fds.data_write
            .sync_data()
            .map_err(|error| format!("NuDB sync data file: {error}"))?;
        fds.key_write
            .sync_data()
            .map_err(|error| format!("NuDB sync key file: {error}"))
    }

    fn finish_burst_writes(&self, write_count: usize) -> Result<(), String> {
        self.ensure_not_fail_stopped()?;
        let should_commit = {
            let mut runtime = self
                .runtime
                .lock()
                .expect("nudb backend runtime mutex must not be poisoned");
            if !runtime.open_state.is_open() {
                return Err("NuDB backend is not open".to_owned());
            }
            runtime.burst_pending_writes = runtime.burst_pending_writes.saturating_add(write_count);
            runtime.burst_pending_writes >= self.burst_commit_limit()
        };

        if should_commit {
            self.append_burst_originals_to_log()?;
            let flush_started = Instant::now();
            self.flush_bucket_cache()?;
            self.metrics
                .burst_flush_ns
                .fetch_add(flush_started.elapsed().as_nanos() as u64, Ordering::Relaxed);
            let sync_started = Instant::now();
            self.sync_data_files()?;
            self.metrics
                .burst_sync_ns
                .fetch_add(sync_started.elapsed().as_nanos() as u64, Ordering::Relaxed);
            self.clear_log_file()?;
            self.metrics
                .burst_commit_count
                .fetch_add(1, Ordering::Relaxed);
            let mut runtime = self
                .runtime
                .lock()
                .expect("nudb backend runtime mutex must not be poisoned");
            runtime.burst_pending_writes = 0;
            runtime.burst_checkpoint_active = false;
            let mut originals = self
                .burst_originals
                .lock()
                .expect("nudb burst originals mutex must not be poisoned");
            originals.active = false;
            originals.buckets.clear();
        }
        Ok(())
    }

    fn finish_burst_write(&self) -> Result<(), String> {
        self.finish_burst_writes(1)
    }

    fn commit_active_burst_if_needed(&self) -> Result<(), String> {
        self.ensure_not_fail_stopped()?;
        let should_commit = {
            let runtime = self
                .runtime
                .lock()
                .expect("nudb backend runtime mutex must not be poisoned");
            runtime.open_state.is_open() && runtime.burst_checkpoint_active
        };

        let result = (|| {
            if should_commit {
                self.append_burst_originals_to_log()?;
                let flush_started = Instant::now();
                self.flush_bucket_cache()?;
                self.metrics
                    .burst_flush_ns
                    .fetch_add(flush_started.elapsed().as_nanos() as u64, Ordering::Relaxed);
                let sync_started = Instant::now();
                self.sync_data_files()?;
                self.metrics
                    .burst_sync_ns
                    .fetch_add(sync_started.elapsed().as_nanos() as u64, Ordering::Relaxed);
                self.clear_log_file()?;
                self.metrics
                    .burst_commit_count
                    .fetch_add(1, Ordering::Relaxed);
                let mut runtime = self
                    .runtime
                    .lock()
                    .expect("nudb backend runtime mutex must not be poisoned");
                runtime.burst_pending_writes = 0;
                runtime.burst_checkpoint_active = false;
                let mut originals = self
                    .burst_originals
                    .lock()
                    .expect("nudb burst originals mutex must not be poisoned");
                originals.active = false;
                originals.buckets.clear();
            }
            Ok(())
        })();
        result.map_err(|error| self.fail_stop_write_if_checkpointed(error))
    }

    fn close_fail_stopped_generation(&self, error: &str) -> String {
        let mut runtime = self
            .runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned");
        runtime.open_state.close();
        runtime.key_header = None;
        runtime.split_fraction = 0;
        runtime.split_threshold = 0;
        runtime.burst_pending_writes = 0;
        runtime.burst_checkpoint_active = false;
        drop(runtime);
        self.persistent_fds.store(None);
        self.bucket_cache.clear();
        format!("NuDB backend is fail-stopped: {error}")
    }

    pub fn open_state(&self) -> NuDbOpenState {
        self.runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned")
            .open_state
            .clone()
    }

    pub fn key_file_header(&self) -> Option<NuDbKeyFileHeader> {
        self.runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned")
            .key_header
    }

    fn current_key_header(&self) -> Result<NuDbKeyFileHeader, String> {
        let runtime = self
            .runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned");
        if !runtime.open_state.is_open() {
            return Err("NuDB backend is not open".to_owned());
        }
        // Serve from in-memory runtime header — reference nudb::store keeps this
        // in memory for the lifetime of the open store. Never re-read from disk.
        runtime
            .key_header
            .ok_or_else(|| "NuDB key header not loaded".to_owned())
    }

    fn key_hash_prefix(&self, key: &[u8]) -> Result<u64, String> {
        let key_header = self.current_key_header()?;
        if key.len() != usize::from(key_header.key_size) {
            return Err("NuDB key size mismatch".to_owned());
        }
        Ok((xxh64(key, key_header.salt) >> 16) & NUDB_U48_MAX)
    }

    fn bucket_index(&self, hash_prefix: u64, key_header: &NuDbKeyFileHeader) -> u32 {
        nudb_bucket_index(hash_prefix, key_header.buckets, key_header.modulus)
    }

    fn read_key_bucket(&self, bucket_index: u32) -> Result<NuDbBucket, String> {
        let key_header = self.current_key_header()?;
        self.read_key_bucket_with_header(bucket_index, &key_header)
    }

    fn read_key_bucket_with_header(
        &self,
        bucket_index: u32,
        key_header: &NuDbKeyFileHeader,
    ) -> Result<NuDbBucket, String> {
        if bucket_index >= key_header.buckets {
            return Err(format!(
                "NuDB key bucket index {bucket_index} exceeds {} buckets",
                key_header.buckets
            ));
        }
        // Check bucket cache first (matching reference NuDB detail::cache)
        if let Some(cached) = self.bucket_cache.get(&bucket_index) {
            return Ok(cached.value().bucket.clone());
        }
        let offset = u64::from(bucket_index + 1) * u64::from(key_header.block_size);
        let mut bytes = vec![0u8; usize::from(key_header.block_size)];
        let _read_guard = self
            .key_bucket_io
            .read()
            .expect("nudb key bucket read lock");
        self.pread_key(offset, &mut bytes)?;
        drop(_read_guard);
        let bucket = NuDbBucket::read_full_block(
            usize::from(key_header.block_size),
            usize::from(key_header.capacity),
            &bytes,
        )?;
        if self.bucket_cache.len() >= MAX_BUCKET_CACHE_ENTRIES {
            // Drop both the DashMap iterator and its shard guard before remove.
            evict_one_clean_cached_bucket(&self.bucket_cache);
        }
        self.bucket_cache.insert(
            bucket_index,
            CachedBucket {
                bucket: bucket.clone(),
                dirty: false,
            },
        );
        Ok(bucket)
    }

    fn write_key_bucket(&self, bucket_index: u32, bucket: &NuDbBucket) -> Result<(), String> {
        let key_header = self.current_key_header()?;
        self.write_key_bucket_with_header(bucket_index, bucket, &key_header)
    }

    fn write_key_bucket_with_header(
        &self,
        bucket_index: u32,
        bucket: &NuDbBucket,
        key_header: &NuDbKeyFileHeader,
    ) -> Result<(), String> {
        if bucket_index > key_header.buckets {
            return Err(format!(
                "NuDB key bucket index {bucket_index} exceeds writable bound {}",
                key_header.buckets
            ));
        }
        let bulk_importing = self.bulk_importing.load(Ordering::Acquire);
        let mut originals = self
            .burst_originals
            .lock()
            .expect("nudb burst originals mutex must not be poisoned");
        let burst_active = originals.active;
        if burst_active
            && bucket_index < originals.original_bucket_count
            && !originals.buckets.contains_key(&bucket_index)
        {
            let original = if let Some(cached) = self.bucket_cache.get(&bucket_index) {
                cached.value().bucket.clone()
            } else {
                let offset = u64::from(bucket_index + 1) * u64::from(key_header.block_size);
                let mut bytes = vec![0u8; usize::from(key_header.block_size)];
                let _read_guard = self
                    .key_bucket_io
                    .read()
                    .expect("nudb key bucket read lock");
                self.pread_key(offset, &mut bytes)?;
                NuDbBucket::read_full_block(
                    usize::from(key_header.block_size),
                    usize::from(key_header.capacity),
                    &bytes,
                )?
            };
            originals.buckets.insert(bucket_index, original);
        }
        drop(originals);
        // Cap cache size to prevent unbounded RAM growth (each bucket ~4KB).
        // Dirty burst/bulk-import entries remain pinned until commit.
        if !bulk_importing && !burst_active && self.bucket_cache.len() >= MAX_BUCKET_CACHE_ENTRIES {
            // Drop both the DashMap iterator and its shard guard before remove.
            evict_one_clean_cached_bucket(&self.bucket_cache);
        }
        if bulk_importing || burst_active {
            self.bucket_cache.insert(
                bucket_index,
                CachedBucket {
                    bucket: bucket.clone(),
                    dirty: true,
                },
            );
            return Ok(());
        }
        let offset = u64::from(bucket_index + 1) * u64::from(key_header.block_size);
        let bytes = bucket.encode_key_block()?;
        let _write_guard = self
            .key_bucket_io
            .write()
            .expect("nudb key bucket write lock");
        self.pwrite_key(offset, &bytes)?;
        drop(_write_guard);
        self.bucket_cache.insert(
            bucket_index,
            CachedBucket {
                bucket: bucket.clone(),
                dirty: false,
            },
        );
        Ok(())
    }

    fn read_spill_bucket(&self, spill_offset: u64) -> Result<NuDbBucket, String> {
        if spill_offset < NUDB_SPILL_RECORD_HEADER_SIZE as u64 {
            return Err("NuDB spill offset is invalid".to_owned());
        }
        let key_header = self.current_key_header()?;
        self.read_spill_bucket_with_header(spill_offset, &key_header)
    }

    fn read_spill_bucket_with_header(
        &self,
        spill_offset: u64,
        key_header: &NuDbKeyFileHeader,
    ) -> Result<NuDbBucket, String> {
        let record_start = spill_offset - NUDB_SPILL_RECORD_HEADER_SIZE as u64;
        let mut header_buf = [0u8; NUDB_SPILL_RECORD_HEADER_SIZE];
        self.pread_data(record_start, &mut header_buf)?;
        let mut off = 0usize;
        let zero = read_u48_be(&header_buf, &mut off)?;
        if zero != 0 {
            return Err("NuDB spill record marker is not zero".to_owned());
        }
        let compact_size = usize::from(read_u16_be(&header_buf, &mut off)?);
        let minimum = NUDB_BUCKET_COUNT_SIZE + NUDB_BUCKET_SPILL_SIZE;
        let maximum = nudb_bucket_size(key_header.capacity);
        if compact_size < minimum || compact_size > maximum {
            return Err("NuDB spill bucket size is invalid".to_owned());
        }
        let mut bytes = vec![0u8; compact_size];
        self.pread_data(spill_offset, &mut bytes)?;
        NuDbBucket::read_compact(
            usize::from(key_header.block_size),
            usize::from(key_header.capacity),
            &bytes,
        )
    }

    fn append_spill_bucket(&self, bucket: &NuDbBucket) -> Result<u64, String> {
        let bytes = bucket.encode_compact()?;
        let spill_size = u16::try_from(bytes.len())
            .map_err(|_| "NuDB spill bucket size exceeds u16".to_owned())?;
        let mut record = Vec::with_capacity(NUDB_SPILL_RECORD_HEADER_SIZE + bytes.len());
        record.resize(6, 0); // zero marker
        let mut off = 0usize;
        write_u48_be(&mut record, &mut off, 0)?;
        record.extend_from_slice(&spill_size.to_be_bytes());
        record.extend_from_slice(&bytes);
        let record_offset = self.append_data(&record)?;
        Ok(record_offset + NUDB_SPILL_RECORD_HEADER_SIZE as u64)
    }

    fn ensure_primary_bucket(&self, runtime: &mut NuDbBackendRuntime) -> Result<(), String> {
        let Some(header) = runtime.key_header.as_mut() else {
            return Err("NuDB backend key header is missing".to_owned());
        };
        if header.buckets != 0 {
            return Ok(());
        }

        let empty = NuDbBucket::empty(usize::from(header.block_size), usize::from(header.capacity));
        self.append_key(&empty.encode_key_block()?)?;

        header.buckets = 1;
        header.modulus = 1;
        runtime.split_threshold = nudb_split_threshold(header);
        runtime.split_fraction = runtime.split_threshold / 2;
        #[cfg(test)]
        nudb_test_crash_if_requested(NuDbTestCrashPoint::PrimaryBucket, "primary bucket creation");
        Ok(())
    }

    fn maybe_spill_bucket(&self, bucket: &mut NuDbBucket) -> Result<(), String> {
        if !bucket.is_full() {
            return Ok(());
        }
        let spill_offset = self.append_spill_bucket(bucket)?;
        bucket.entries.clear();
        bucket.spill = spill_offset;
        Ok(())
    }

    fn collect_bucket_chain_entries(
        &self,
        bucket: &NuDbBucket,
    ) -> Result<Vec<NuDbBucketEntry>, String> {
        let mut entries = bucket.entries.clone();
        let mut spill = bucket.spill;
        let mut seen_spills = BTreeSet::new();
        while spill != 0 {
            if !seen_spills.insert(spill) {
                return Err("NuDB spill chain contains a cycle".to_owned());
            }
            let spilled = self.read_spill_bucket(spill)?;
            entries.extend(spilled.entries.iter().copied());
            spill = spilled.spill;
        }
        Ok(entries)
    }

    fn collect_bucket_chain_entries_with_header(
        &self,
        bucket: &NuDbBucket,
        key_header: &NuDbKeyFileHeader,
    ) -> Result<Vec<NuDbBucketEntry>, String> {
        let mut entries = bucket.entries.clone();
        let mut spill = bucket.spill;
        let mut seen_spills = BTreeSet::new();
        while spill != 0 {
            if !seen_spills.insert(spill) {
                return Err("NuDB spill chain contains a cycle".to_owned());
            }
            let spilled = self.read_spill_bucket_with_header(spill, key_header)?;
            entries.extend(spilled.entries.iter().copied());
            spill = spilled.spill;
        }
        Ok(entries)
    }

    fn split_one_bucket(&self, runtime: &mut NuDbBackendRuntime) -> Result<(), String> {
        let Some(header) = runtime.key_header.as_mut() else {
            return Err("NuDB backend key header is missing".to_owned());
        };
        if header.buckets == 0 {
            return Ok(());
        }

        let mut new_modulus = header.modulus.max(1);
        if header.buckets == new_modulus {
            new_modulus = new_modulus
                .checked_mul(2)
                .ok_or_else(|| "NuDB modulus overflow".to_owned())?;
        }
        let left_index = header
            .buckets
            .checked_sub(new_modulus / 2)
            .ok_or_else(|| "NuDB split index underflow".to_owned())?;
        let right_index = header.buckets;
        let new_buckets = header
            .buckets
            .checked_add(1)
            .ok_or_else(|| "NuDB bucket count overflow".to_owned())?;

        let source = self.read_key_bucket_with_header(left_index, header)?;
        let entries = self.collect_bucket_chain_entries_with_header(&source, header)?;
        let mut left =
            NuDbBucket::empty(usize::from(header.block_size), usize::from(header.capacity));
        let mut right =
            NuDbBucket::empty(usize::from(header.block_size), usize::from(header.capacity));
        for entry in entries {
            if nudb_bucket_index(entry.hash_prefix, new_buckets, new_modulus) == right_index {
                self.maybe_spill_bucket(&mut right)?;
                right.insert_sorted(entry);
            } else {
                self.maybe_spill_bucket(&mut left)?;
                left.insert_sorted(entry);
            }
        }

        let empty = NuDbBucket::empty(usize::from(header.block_size), usize::from(header.capacity));
        self.append_key(&empty.encode_key_block()?)?;

        header.buckets = new_buckets;
        header.modulus = new_modulus;
        self.write_key_bucket_with_header(left_index, &left, header)?;
        self.write_key_bucket_with_header(right_index, &right, header)?;
        #[cfg(test)]
        nudb_test_crash_if_requested(NuDbTestCrashPoint::Split, "bucket split");

        Ok(())
    }

    fn read_data_record_key(&self, offset: u64) -> Result<Vec<u8>, String> {
        let key_header = self.current_key_header()?;
        self.read_data_record_key_with_key_size(offset, usize::from(key_header.key_size))
    }

    fn read_data_record_key_with_key_size(
        &self,
        offset: u64,
        key_size: usize,
    ) -> Result<Vec<u8>, String> {
        let mut key = vec![0u8; key_size];
        self.pread_data(offset + 6, &mut key)?;
        Ok(key)
    }

    fn read_data_record_value(&self, entry: NuDbBucketEntry) -> Result<Vec<u8>, String> {
        let key_header = self.current_key_header()?;
        self.read_data_record_value_with_key_size(entry, usize::from(key_header.key_size))
    }

    fn read_data_record_value_with_key_size(
        &self,
        entry: NuDbBucketEntry,
        key_size: usize,
    ) -> Result<Vec<u8>, String> {
        let value_len = usize::try_from(entry.size)
            .map_err(|_| "NuDB data record value size exceeds usize".to_owned())?;
        let total_size = 6 + key_size + value_len;
        let mut full_buf = vec![0u8; total_size];
        // Fused read: if it fails (e.g. corrupted size causes read past EOF),
        // fall back to reading just the header to produce the correct error.
        if self.pread_data(entry.offset, &mut full_buf).is_err() {
            let mut hdr = [0u8; 6];
            self.pread_data(entry.offset, &mut hdr)?;
            let mut off = 0usize;
            let stored_size = read_u48_be(&hdr, &mut off)?;
            if stored_size != entry.size {
                return Err("NuDB data record size does not match key bucket metadata".to_owned());
            }
            return Err(format!(
                "NuDB pread data @{}: failed to fill whole buffer",
                entry.offset
            ));
        }

        let mut off = 0usize;
        let stored_size = read_u48_be(&full_buf, &mut off)?;
        if stored_size != entry.size {
            return Err("NuDB data record size does not match key bucket metadata".to_owned());
        }
        self.metrics
            .fused_read_bytes
            .fetch_add(total_size, Ordering::Relaxed);
        let value = full_buf[6 + key_size..].to_vec();
        Ok(value)
    }

    fn find_bucket_entry(&self, key: &[u8]) -> Result<Option<NuDbBucketEntry>, String> {
        let key_header = self.current_key_header()?;
        let hash_prefix = self.key_hash_prefix(key)?;
        if key_header.buckets == 0 {
            return Ok(None);
        }
        let bucket_index = self.bucket_index(hash_prefix, &key_header);
        let mut bucket = self.read_key_bucket(bucket_index)?;
        loop {
            #[cfg(target_os = "linux")]
            {
                if bucket.spill > 0 {
                    let fds_arc = self.persistent_fds.load();
                    if let Some(fds) = fds_arc.as_deref() {
                        use std::os::unix::io::AsRawFd;
                        let fd = fds.key_read.as_raw_fd();
                        let offset = bucket.spill as i64 * key_header.block_size as i64;
                        unsafe {
                            libc::posix_fadvise(
                                fd,
                                offset,
                                key_header.block_size as i64,
                                libc::POSIX_FADV_WILLNEED,
                            );
                        }
                    }
                }
            }

            for entry in bucket.entries.iter().skip(bucket.lower_bound(hash_prefix)) {
                if entry.hash_prefix != hash_prefix {
                    break;
                }
                let stored_key = self.read_data_record_key(entry.offset)?;
                if stored_key == key {
                    return Ok(Some(*entry));
                }
            }
            if bucket.spill == 0 {
                return Ok(None);
            }
            bucket = self.read_spill_bucket(bucket.spill)?;
        }
    }

    fn insert_bucket_entry(&self, bucket_index: u32, entry: NuDbBucketEntry) -> Result<(), String> {
        let mut bucket = self.read_key_bucket(bucket_index)?;
        self.maybe_spill_bucket(&mut bucket)?;
        bucket.insert_sorted(entry);
        self.write_key_bucket(bucket_index, &bucket)
    }

    #[allow(clippy::type_complexity)]
    fn scan_data_record_entries(&self) -> Result<Vec<(u64, Uint256, u64, Vec<u8>)>, String> {
        let key_header = self.current_key_header()?;
        let mut file =
            fs::File::open(&self.config.layout.data_path).map_err(|error| error.to_string())?;
        let file_size = file.metadata().map_err(|error| error.to_string())?.len();
        let mut offset = NUDB_DATA_FILE_HEADER_SIZE as u64;
        let mut records = Vec::new();

        while offset < file_size {
            file.seek(SeekFrom::Start(offset))
                .map_err(|error| error.to_string())?;
            let value_size = read_u48_be_from_reader(&mut file, "NuDB data record size")?;
            if value_size == 0 {
                let compact_size =
                    u64::from(read_u16_be_from_reader(&mut file, "NuDB spill size")?);
                if compact_size
                    < u64::try_from(NUDB_BUCKET_COUNT_SIZE + NUDB_BUCKET_SPILL_SIZE)
                        .expect("constant fits u64")
                {
                    return Err("NuDB spill record is too small".to_owned());
                }
                offset = offset
                    .checked_add(NUDB_SPILL_RECORD_HEADER_SIZE as u64)
                    .and_then(|value| value.checked_add(compact_size))
                    .ok_or_else(|| "NuDB spill record offset overflow".to_owned())?;
                continue;
            }
            let next = offset
                .checked_add(6)
                .and_then(|value| value.checked_add(u64::from(key_header.key_size)))
                .and_then(|value| value.checked_add(value_size))
                .ok_or_else(|| "NuDB data record offset overflow".to_owned())?;
            if next > file_size {
                return Err("NuDB data record is truncated".to_owned());
            }

            let mut key = vec![0u8; usize::from(key_header.key_size)];
            file.read_exact(&mut key)
                .map_err(|error| error.to_string())?;
            let value_len = usize::try_from(value_size)
                .map_err(|_| "NuDB data record is too large".to_owned())?;
            let mut value = vec![0u8; value_len];
            file.read_exact(&mut value)
                .map_err(|error| error.to_string())?;
            records.push((
                offset,
                Uint256::from_slice(&key).ok_or_else(|| "NuDB key size mismatch".to_owned())?,
                value_size,
                value,
            ));
            offset = next;
        }

        Ok(records)
    }

    #[allow(dead_code)]
    fn scan_indexed_records(&self) -> Result<Vec<(Uint256, Vec<u8>)>, String> {
        let key_header = self.current_key_header()?;
        let key_size = usize::from(key_header.key_size);
        let mut records = Vec::new();
        for bucket_index in 0..key_header.buckets {
            let bucket = self.read_key_bucket_with_header(bucket_index, &key_header)?;
            for entry in self.collect_bucket_chain_entries_with_header(&bucket, &key_header)? {
                let key_bytes = self.read_data_record_key_with_key_size(entry.offset, key_size)?;
                let key = Uint256::from_slice(&key_bytes)
                    .ok_or_else(|| "NuDB key size mismatch".to_owned())?;
                let value = self.read_data_record_value_with_key_size(entry, key_size)?;
                records.push((key, value));
            }
        }
        Ok(records)
    }

    #[allow(dead_code)]
    fn append_encoded_record(&self, object: &Arc<NodeObject>) -> Result<NuDbBucketEntry, String> {
        let key_header = self.current_key_header()?;
        let encoded = EncodedBlob::new(object);
        let compressed = nodeobject_compress(encoded.get_data())?;
        if encoded.get_key().len() != usize::from(key_header.key_size) {
            return Err("NuDB record key size mismatch".to_owned());
        }
        if compressed.len() > usize::try_from(NUDB_U48_MAX).expect("constant fits usize") {
            return Err("NuDB data record exceeds 48-bit size field".to_owned());
        }

        let size_val = u64::try_from(compressed.len()).expect("record size must fit u64");
        let mut record = Vec::with_capacity(6 + encoded.get_key().len() + compressed.len());
        record.resize(6, 0);
        let mut off = 0usize;
        write_u48_be(&mut record, &mut off, size_val)?;
        record.extend_from_slice(encoded.get_key());
        record.extend_from_slice(&compressed);
        let offset = self.append_data(&record)?;
        Ok(NuDbBucketEntry {
            offset,
            size: size_val,
            hash_prefix: self.key_hash_prefix(encoded.get_key())?,
        })
    }

    pub fn verify_backend(&self) -> Result<(), String> {
        let _store_guard = self
            .store_mutex
            .lock()
            .expect("nudb backend store mutex must not be poisoned");
        self.ensure_not_fail_stopped()?;
        // Commit the active c0/c1 transaction before dropping its dirty view;
        // verification then reads only the durable key file.
        self.commit_active_burst_if_needed()?;
        self.bucket_cache.clear();
        // Read key header from DISK (not memory cache) to detect corruption
        let key_header = read_nudb_key_file_header(&self.config.layout.key_path)?;
        let key_size = usize::from(key_header.key_size);
        read_nudb_data_file_header(&self.config.layout.data_path)?
            .validate_against_key(&key_header)?;
        let log_size = fs::metadata(&self.config.layout.log_path)
            .map_err(|error| error.to_string())?
            .len();
        if log_size != 0 {
            return Err("NuDB verify requires an empty log file".to_owned());
        }

        let mut indexed = BTreeMap::new();
        for bucket_index in 0..key_header.buckets {
            let bucket = self.read_key_bucket(bucket_index)?;
            for entry in self.collect_bucket_chain_entries(&bucket)? {
                let key_bytes = self.read_data_record_key_with_key_size(entry.offset, key_size)?;
                let key: [u8; 32] = key_bytes
                    .as_slice()
                    .try_into()
                    .map_err(|_| "NuDB key size mismatch".to_owned())?;
                if indexed.insert(key, entry).is_some() {
                    return Err("NuDB key file contains duplicate keys".to_owned());
                }
                let value = self.read_data_record_value_with_key_size(entry, key_size)?;
                let decompressed = nodeobject_decompress(&value)?;
                if !DecodedBlob::new(&key, &decompressed).was_ok() {
                    return Err("NuDB key entry points at corrupt data".to_owned());
                }
            }
        }

        let mut seen_offsets = BTreeSet::new();
        for (offset, key, value_size, value) in self.scan_data_record_entries()? {
            let key_bytes = *key.data();
            let Some(entry) = indexed.get(&key_bytes) else {
                return Err("NuDB data file contains an orphan value record".to_owned());
            };
            if entry.offset != offset || entry.size != value_size {
                return Err("NuDB key metadata does not match data-file record".to_owned());
            }
            if !seen_offsets.insert(offset) {
                return Err("NuDB data file contains duplicate record offsets".to_owned());
            }
            let decompressed = nodeobject_decompress(&value)?;
            if !DecodedBlob::new(&key_bytes, &decompressed).was_ok() {
                return Err("NuDB data file contains a corrupt value record".to_owned());
            }
        }

        if indexed.len() != seen_offsets.len() {
            return Err("NuDB key/data entry counts do not match".to_owned());
        }

        Ok(())
    }

    fn traverse_objects(
        &self,
        callback: &mut dyn FnMut(Arc<NodeObject>),
        fail_fast: bool,
    ) -> Result<(), String> {
        let _store_guard = self
            .store_mutex
            .lock()
            .expect("nudb backend store mutex must not be poisoned");
        if let Err(error) = self.ensure_not_fail_stopped() {
            if fail_fast {
                return Err(error);
            }
            self.journal.log(JournalLevel::Error, &error);
            return Ok(());
        }
        if let Err(error) = self.commit_active_burst_if_needed() {
            if fail_fast {
                return Err(error);
            }
            self.journal.log(JournalLevel::Error, &error);
            return Ok(());
        }
        let key_header = match self.current_key_header() {
            Ok(header) => header,
            Err(error) => {
                if fail_fast {
                    return Err(error);
                }
                self.journal.log(JournalLevel::Error, &error);
                return Ok(());
            }
        };
        let key_size = usize::from(key_header.key_size);

        for bucket_index in 0..key_header.buckets {
            let bucket = match self.read_key_bucket_with_header(bucket_index, &key_header) {
                Ok(bucket) => bucket,
                Err(error) => {
                    if fail_fast {
                        return Err(error);
                    }
                    self.journal.log(JournalLevel::Error, &error);
                    continue;
                }
            };
            let entries = match self.collect_bucket_chain_entries_with_header(&bucket, &key_header)
            {
                Ok(entries) => entries,
                Err(error) => {
                    if fail_fast {
                        return Err(error);
                    }
                    self.journal.log(JournalLevel::Error, &error);
                    continue;
                }
            };
            for entry in entries {
                let key_bytes =
                    match self.read_data_record_key_with_key_size(entry.offset, key_size) {
                        Ok(key) => key,
                        Err(error) => {
                            if fail_fast {
                                return Err(error);
                            }
                            self.journal.log(JournalLevel::Error, &error);
                            continue;
                        }
                    };
                let value = match self.read_data_record_value_with_key_size(entry, key_size) {
                    Ok(value) => value,
                    Err(error) => {
                        if fail_fast {
                            return Err(error);
                        }
                        self.journal.log(JournalLevel::Error, &error);
                        continue;
                    }
                };
                let decompressed = match nodeobject_decompress(&value) {
                    Ok(bytes) => bytes,
                    Err(error) => {
                        if fail_fast {
                            return Err(error);
                        }
                        self.journal.log(JournalLevel::Error, &error);
                        continue;
                    }
                };
                let key = match Uint256::from_slice(&key_bytes) {
                    Some(key) => key,
                    None => {
                        let error = "NuDB data record key is not a Uint256".to_owned();
                        if fail_fast {
                            return Err(error);
                        }
                        self.journal.log(JournalLevel::Error, &error);
                        continue;
                    }
                };
                let decoded = DecodedBlob::new(key.data(), &decompressed);
                if decoded.was_ok() {
                    callback(decoded.create_object());
                } else {
                    let error = "NuDB data record failed to decode".to_owned();
                    if fail_fast {
                        return Err(error);
                    }
                    self.journal.log(JournalLevel::Error, &error);
                }
            }
        }

        Ok(())
    }
}

impl Backend for NuDbBackend {
    fn get_name(&self) -> String {
        self.config.path.clone()
    }

    fn get_block_size(&self) -> Option<usize> {
        let runtime = self
            .runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned");
        Some(
            runtime
                .key_header
                .map(|header| usize::from(header.block_size))
                .unwrap_or(self.config.block_size),
        )
    }

    fn open(&self, create_if_missing: bool) -> Result<(), String> {
        self.open_with_args(
            create_if_missing,
            self.default_open_args
                .unwrap_or_else(|| self.build_random_open_args()),
        )?;
        self.build_bloom_if_enabled();
        Ok(())
    }

    fn open_deterministic(
        &self,
        create_if_missing: bool,
        app_type: u64,
        uid: u64,
        salt: u64,
    ) -> Result<(), String> {
        self.open_with_args(
            create_if_missing,
            NuDbOpenArgs::deterministic(app_type, uid, salt),
        )?;
        self.build_bloom_if_enabled();
        Ok(())
    }

    fn is_open(&self) -> bool {
        self.runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned")
            .open_state
            .is_open()
    }

    fn close(&self) -> Result<(), String> {
        let _store_guard = self
            .store_mutex
            .lock()
            .expect("nudb backend store mutex must not be poisoned");
        if !self
            .runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned")
            .open_state
            .is_open()
        {
            return Ok(());
        }

        if let Some(error) = self.fail_stop_error() {
            // Do not commit or clear the recovery log. Drop all live views of
            // the partially mutated generation so a later reopen is forced
            // through normal NuDB log recovery.
            return Err(self.close_fail_stopped_generation(&error));
        }

        if let Err(error) = self.commit_active_burst_if_needed() {
            self.journal.log(JournalLevel::Error, &error);
            let fail_stop = self.fail_stop_error().unwrap_or(error);
            return Err(self.close_fail_stopped_generation(&fail_stop));
        }

        let mut runtime = self
            .runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned");
        if !runtime.open_state.is_open() {
            return Ok(());
        }
        let delete_path = runtime.open_state.delete_path();
        runtime.open_state.close();
        runtime.key_header = None;
        runtime.split_fraction = 0;
        runtime.split_threshold = 0;
        runtime.burst_pending_writes = 0;
        runtime.burst_checkpoint_active = false;
        runtime.fail_stop_error = None;
        {
            let mut originals = self
                .burst_originals
                .lock()
                .expect("nudb burst originals mutex must not be poisoned");
            originals.active = false;
            originals.original_bucket_count = 0;
            originals.buckets.clear();
        }
        drop(runtime);

        // Close persistent file descriptors before potential file deletion.
        self.persistent_fds.store(None);
        self.flush_bucket_cache().ok();
        self.bucket_cache.clear();

        tracing::info!(target: "nodestore", "Database closed");

        if delete_path {
            match fs::remove_dir_all(&self.config.layout.base_path) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => {
                    self.journal.log(
                        JournalLevel::Fatal,
                        &format!(
                            "Filesystem remove_all of {} failed with: {error}",
                            self.config.path
                        ),
                    );
                }
            }
        }

        Ok(())
    }

    fn fetch(&self, _hash: &Uint256) -> (Option<Arc<NodeObject>>, Status) {
        let hash = _hash;
        // Bloom skip gate: when a filter is active and proves the key absent,
        // return NotFound without touching the bucket/data files. No false
        // negatives, so this is safe; a false positive simply falls through to
        // the normal lookup below.
        if let Some(filter) = self.bloom.load().as_deref() {
            if !filter.may_contain(hash) {
                self.metrics.bloom_skipped_reads.fetch_add(1, Ordering::Relaxed);
                return (None, Status::NotFound);
            }
        }
        match self.find_bucket_entry(hash.data()) {
            Ok(Some(entry)) => {
                let value = match self.read_data_record_value(entry) {
                    Ok(value) => value,
                    Err(error) => {
                        tracing::error!(target: "nodestore", hash = %hash, error = %error, "Node store read failed");
                        self.journal.log(JournalLevel::Error, &error);
                        return (None, Status::DataCorrupt);
                    }
                };
                let decompressed = match nodeobject_decompress(&value) {
                    Ok(bytes) => bytes,
                    Err(error) => {
                        tracing::error!(target: "nodestore", hash = %hash, error = %error, "Node store read failed");
                        self.journal.log(JournalLevel::Error, &error);
                        return (None, Status::DataCorrupt);
                    }
                };
                let decoded = DecodedBlob::new(hash.data(), &decompressed);
                if !decoded.was_ok() {
                    return (None, Status::DataCorrupt);
                }
                let size_bytes = decompressed.len();
                tracing::debug!(target: "nodestore", hash = %hash, size_bytes, "Node object fetched");
                (Some(decoded.create_object()), Status::Ok)
            }
            Ok(None) => (None, Status::NotFound),
            Err(error) => {
                tracing::error!(target: "nodestore", hash = %hash, error = %error, "Node store read failed");
                self.journal.log(JournalLevel::Error, &error);
                (None, Status::BackendError)
            }
        }
    }

    fn may_contain(&self, hash: &Uint256) -> bool {
        // Only answers `false` when a filter is active and proves absence.
        // Without a filter, defaults to `true` (must check), matching the
        // trait default.
        match self.bloom.load().as_deref() {
            Some(filter) => filter.may_contain(hash),
            None => true,
        }
    }

    fn evict_membership_filter(&self) {
        self.evict_bloom();
    }

    fn fetch_batch(&self, hashes: &[Uint256]) -> (Vec<Option<Arc<NodeObject>>>, Status) {
        self.metrics
            .batch_fetch_count
            .fetch_add(1, Ordering::Relaxed);
        let threshold = 64; // Fallback to sequential for small batches
        if hashes.len() < threshold {
            let mut results = Vec::with_capacity(hashes.len());
            let mut overall = Status::Ok;
            for hash in hashes {
                let (object, status) = self.fetch(hash);
                if status == Status::Ok {
                    results.push(object);
                } else {
                    results.push(None);
                    if !matches!(status, Status::Ok | Status::NotFound) && overall == Status::Ok {
                        overall = status;
                    }
                }
            }
            return (results, overall);
        }

        self.metrics
            .batch_fetch_parallel_count
            .fetch_add(1, Ordering::Relaxed);
        let key_header = match self.current_key_header() {
            Ok(h) => h,
            Err(error) => {
                tracing::error!(target: "nodestore", error = %error, "NuDB fetch_batch failed to get key header");
                self.journal.log(JournalLevel::Error, &error);
                return (vec![None; hashes.len()], Status::BackendError);
            }
        };

        if key_header.buckets == 0 {
            return (vec![None; hashes.len()], Status::NotFound);
        }

        let mut grouped: HashMap<u32, Vec<(usize, Uint256)>> = HashMap::new();
        for (i, hash) in hashes.iter().enumerate() {
            if let Ok(prefix) = self.key_hash_prefix(hash.data()) {
                let bucket_index = self.bucket_index(prefix, &key_header);
                grouped.entry(bucket_index).or_default().push((i, *hash));
            }
        }

        let unique_buckets = grouped.len();
        if unique_buckets > 0 {
            let eff = (hashes.len() * 100) / unique_buckets;
            self.metrics
                .batch_grouping_efficiency_pct
                .store(eff, Ordering::Relaxed);
        }

        let flat_results: Vec<(usize, Option<Arc<NodeObject>>, Status)> = grouped
            .into_par_iter()
            .flat_map(|(bucket_index, queries)| {
                let mut out = Vec::with_capacity(queries.len());
                let bucket = match self.read_key_bucket_with_header(bucket_index, &key_header) {
                    Ok(b) => b,
                    Err(_) => {
                        for (i, _) in queries {
                            out.push((i, None, Status::BackendError));
                        }
                        return out;
                    }
                };

                let mut chain = vec![bucket];
                let mut current_spill = chain[0].spill;
                while current_spill != 0 {
                    if let Ok(spill) = self.read_spill_bucket(current_spill) {
                        current_spill = spill.spill;
                        chain.push(spill);
                    } else {
                        break;
                    }
                }

                for (i, hash) in queries {
                    let prefix = self.key_hash_prefix(hash.data()).unwrap();
                    let mut found_entry = None;
                    'search: for b in &chain {
                        for entry in b.entries.iter().skip(b.lower_bound(prefix)) {
                            if entry.hash_prefix != prefix {
                                break;
                            }
                            if let Ok(stored_key) = self.read_data_record_key(entry.offset)
                                && stored_key == hash.data()
                            {
                                found_entry = Some(*entry);
                                break 'search;
                            }
                        }
                    }

                    if let Some(entry) = found_entry {
                        let value = match self.read_data_record_value(entry) {
                            Ok(v) => v,
                            Err(_) => {
                                out.push((i, None, Status::DataCorrupt));
                                continue;
                            }
                        };
                        let decompressed = match nodeobject_decompress(&value) {
                            Ok(v) => v,
                            Err(_) => {
                                out.push((i, None, Status::DataCorrupt));
                                continue;
                            }
                        };
                        let decoded = DecodedBlob::new(hash.data(), &decompressed);
                        if decoded.was_ok() {
                            out.push((i, Some(decoded.create_object()), Status::Ok));
                        } else {
                            out.push((i, None, Status::DataCorrupt));
                        }
                    } else {
                        out.push((i, None, Status::NotFound));
                    }
                }
                out
            })
            .collect();

        let mut results = vec![None; hashes.len()];
        let mut overall = Status::Ok;
        for (i, obj, status) in flat_results {
            results[i] = obj;
            if !matches!(status, Status::Ok | Status::NotFound) && overall == Status::Ok {
                overall = status;
            }
        }

        (results, overall)
    }

    fn store(&self, object: Arc<NodeObject>) -> Result<(), String> {
        self.ensure_not_fail_stopped()?;
        // Pure encoding/compression stays outside the serialized mutation
        // section. A second poison check follows after acquiring the fence.
        let encoded = EncodedBlob::new(&object);
        let compressed = nodeobject_compress(encoded.get_data()).map_err(|error| {
            tracing::error!(target: "nodestore", error = %error, "Node store write failed");
            self.journal.log(JournalLevel::Error, &error);
            error
        })?;
        let hash_prefix = self
            .key_hash_prefix(encoded.get_key())
            .inspect_err(|error| {
                self.journal.log(JournalLevel::Error, error);
            })?;
        let lock_started = Instant::now();
        let _store_guard = self
            .store_mutex
            .lock()
            .expect("nudb backend store mutex must not be poisoned");
        self.metrics
            .store_lock_wait_ns
            .fetch_add(lock_started.elapsed().as_nanos() as u64, Ordering::Relaxed);
        let _store_timing = StoreLockTiming::new(self.metrics.as_ref());
        self.ensure_not_fail_stopped()?;
        let result = (|| {
            let bulk_importing = self.bulk_importing.load(Ordering::Acquire);

            let initial_key_header = {
                let runtime = self
                    .runtime
                    .lock()
                    .expect("nudb backend runtime mutex must not be poisoned");
                if !runtime.open_state.is_open() {
                    let error = "NuDB backend is not open".to_owned();
                    self.journal.log(JournalLevel::Error, &error);
                    return Err(error);
                }
                runtime
                    .key_header
                    .expect("nudb runtime header must exist while open")
            };
            match self.find_bucket_entry(encoded.get_key()) {
                Ok(Some(_)) => return Ok(()),
                Ok(None) => {}
                Err(error) => {
                    self.journal.log(JournalLevel::Error, &error);
                    return Err(error);
                }
            }
            if !bulk_importing {
                // The checkpoint must be durable before primary-bucket creation,
                // a split, or any subsequent data/key-file mutation. It records
                // the pre-mutation file sizes and bucket state for recovery.
                self.begin_burst_checkpoint_if_needed(&initial_key_header)
                    .inspect_err(|error| {
                        self.journal.log(JournalLevel::Error, error);
                    })?;
            }
            let key_header = {
                let mut runtime = self
                    .runtime
                    .lock()
                    .expect("nudb backend runtime mutex must not be poisoned");
                self.ensure_primary_bucket(&mut runtime)
                    .inspect_err(|error| {
                        self.journal.log(JournalLevel::Error, error);
                    })?;
                if !bulk_importing {
                    runtime.split_fraction = runtime.split_fraction.saturating_add(65_536);
                    if runtime.split_fraction >= runtime.split_threshold {
                        runtime.split_fraction -= runtime.split_threshold;
                        self.split_one_bucket(&mut runtime).inspect_err(|error| {
                            self.journal.log(JournalLevel::Error, error);
                        })?;
                    }
                }
                runtime
                    .key_header
                    .expect("nudb runtime header must exist after primary bucket and split")
            };
            // Use pre-computed compressed data — no re-encoding under the lock.
            let key_size = usize::from(key_header.key_size);
            if encoded.get_key().len() != key_size {
                let error = "NuDB record key size mismatch".to_owned();
                self.journal.log(JournalLevel::Error, &error);
                return Err(error);
            }
            let size_val = u64::try_from(compressed.len()).expect("record size must fit u64");
            let mut record = Vec::with_capacity(6 + key_size + compressed.len());
            record.resize(6, 0);
            let mut off = 0usize;
            write_u48_be(&mut record, &mut off, size_val).inspect_err(|error| {
                self.journal.log(JournalLevel::Error, error);
            })?;
            record.extend_from_slice(encoded.get_key());
            record.extend_from_slice(&compressed);
            let offset = self.append_data(&record).inspect_err(|error| {
                self.journal.log(JournalLevel::Error, error);
            })?;
            let entry = NuDbBucketEntry {
                offset,
                size: size_val,
                hash_prefix,
            };
            let bucket_index =
                nudb_bucket_index(entry.hash_prefix, key_header.buckets, key_header.modulus);
            self.insert_bucket_entry(bucket_index, entry)
                .inspect_err(|error| {
                    tracing::error!(target: "nodestore", error = %error, "Node store write failed");
                    self.journal.log(JournalLevel::Error, error);
                })?;
            let size_bytes = compressed.len();
            tracing::debug!(target: "nodestore", hash = %object.hash(), size_bytes, "Node object stored");
            if !bulk_importing {
                self.finish_burst_write().inspect_err(|error| {
                    self.journal.log(JournalLevel::Error, error);
                })?;
            }
            Ok(())
        })();
        // On a successful (or already-present) store, record the key in the
        // Bloom filter so subsequent skip-gate probes observe it. No-op when
        // the filter is disabled.
        if result.is_ok() {
            self.bloom_insert(object.get_hash());
        }
        result.map_err(|error| self.fail_stop_write_if_checkpointed(error))
    }

    fn store_batch(&self, batch: &Batch) {
        if let Err(error) = self.store_batch_result(batch) {
            tracing::error!(target: "nodestore", %error, "NuDB batch write failed");
            self.journal.log(JournalLevel::Error, &error);
        }
    }

    fn store_batch_result(&self, batch: &Batch) -> Result<(), String> {
        self.ensure_not_fail_stopped()?;
        // Stable first-wins encoding and compression are CPU-only and happen
        // before the mutation fence. The checked mutation below rechecks
        // fail-stop state after acquiring the fence.
        let mut batch_size_bytes = 0usize;
        let mut seen_batch_keys = BTreeSet::new();
        let mut to_write = Vec::with_capacity(batch.len());
        for object in batch {
            batch_size_bytes += object.data().len();
            let encoded = EncodedBlob::new(object);
            let key = encoded.get_key().to_vec();
            if !seen_batch_keys.insert(key.clone()) {
                continue;
            }
            let compressed = nodeobject_compress(encoded.get_data())?;
            let hash_prefix = self.key_hash_prefix(&key)?;
            to_write.push((key, hash_prefix, compressed));
        }
        if to_write.is_empty() {
            return Ok(());
        }
        let lock_started = Instant::now();
        let _store_guard = self
            .store_mutex
            .lock()
            .expect("nudb backend store mutex must not be poisoned");
        self.metrics
            .store_lock_wait_ns
            .fetch_add(lock_started.elapsed().as_nanos() as u64, Ordering::Relaxed);
        let _store_timing = StoreLockTiming::new(self.metrics.as_ref());
        self.ensure_not_fail_stopped()?;
        let result = (|| {
            let bulk_importing = self.bulk_importing.load(Ordering::Acquire);

            let initial_key_header = {
                let runtime = self
                    .runtime
                    .lock()
                    .expect("nudb backend runtime mutex must not be poisoned");
                if !runtime.open_state.is_open() {
                    return Err("NuDB backend is not open".to_owned());
                }
                runtime.key_header.expect("header must be present")
            };

            // Check the persisted index while holding the store lock. Existing
            // keys are no-ops, precisely matching NuDBFactory::doInsert's
            // key_exists handling, and are excluded before any data append.
            let mut pending = Vec::with_capacity(to_write.len());
            for (key, hash_prefix, compressed) in to_write {
                match self.find_bucket_entry(&key) {
                    Ok(Some(_)) => continue,
                    Ok(None) => pending.push((key, hash_prefix, compressed)),
                    Err(error) => return Err(error),
                }
            }
            if pending.is_empty() {
                return Ok(());
            }

            // NuDB saves the pre-write key/data sizes before it can append data.
            // Recovery restores this checkpoint if a later append or index update
            // is interrupted.
            if !bulk_importing {
                self.begin_burst_checkpoint_if_needed(&initial_key_header)?;
            }

            let key_header = {
                let mut runtime = self
                    .runtime
                    .lock()
                    .expect("nudb backend runtime mutex must not be poisoned");
                self.ensure_primary_bucket(&mut runtime)?;
                if !bulk_importing {
                    runtime.split_fraction = runtime
                        .split_fraction
                        .saturating_add(65_536 * pending.len() as u64);
                    while runtime.split_fraction >= runtime.split_threshold {
                        runtime.split_fraction -= runtime.split_threshold;
                        self.split_one_bucket(&mut runtime)?;
                    }
                }
                runtime.key_header.expect("header must be present")
            };

            let mut coalesced_buffer = Vec::new();
            let total_bytes = pending
                .iter()
                .map(|(key, _, compressed)| 6 + key.len() + compressed.len())
                .sum();
            coalesced_buffer.reserve_exact(total_bytes);
            let mut entries = Vec::with_capacity(pending.len());
            let mut relative_offset = 0u64;
            for (key, hash_prefix, compressed) in pending {
                if key.len() != usize::from(key_header.key_size) {
                    return Err("NuDB record key size mismatch".to_owned());
                }
                let record_size = match u64::try_from(compressed.len()) {
                    Ok(record_size) if record_size <= NUDB_U48_MAX => record_size,
                    _ => return Err("NuDB data record exceeds 48-bit size field".to_owned()),
                };
                let mut record_header = [0u8; 6];
                let mut record_header_offset = 0usize;
                write_u48_be(&mut record_header, &mut record_header_offset, record_size)?;
                coalesced_buffer.extend_from_slice(&record_header);
                coalesced_buffer.extend_from_slice(&key);
                coalesced_buffer.extend_from_slice(&compressed);
                entries.push((hash_prefix, record_size, relative_offset));
                relative_offset += u64::try_from(6 + key.len() + compressed.len())
                    .expect("NuDB record length must fit u64");
            }

            let base_offset = self.append_data(&coalesced_buffer)?;
            #[cfg(test)]
            nudb_test_batch_error_after_append()?;
            self.metrics
                .store_batch_coalesced_bytes
                .fetch_add(coalesced_buffer.len(), Ordering::Relaxed);

            for (_index, (hash_prefix, size, relative_offset)) in
                entries.iter().copied().enumerate()
            {
                #[cfg(test)]
                nudb_test_batch_error_before_index_insert(_index + 1)?;
                let entry = NuDbBucketEntry {
                    offset: base_offset + relative_offset,
                    size,
                    hash_prefix,
                };
                let bucket_index = self.bucket_index(hash_prefix, &key_header);
                self.insert_bucket_entry(bucket_index, entry)?;
            }

            if !bulk_importing {
                self.finish_burst_writes(entries.len())?;
            }
            let objects_written = entries.len();
            // rippled does not emit one INFO record per NuDB insert/batch.
            // Catch-up can produce thousands of these per minute; journald then
            // competes with the database for I/O precisely while consensus
            // needs its reserved close-path writes. Keep the diagnostic at
            // debug level and expose aggregate write metrics separately.
            tracing::debug!(target: "nodestore", objects_written, batch_size_bytes, "Batch flush complete");
            Ok(())
        })();
        // Record every batched key in the Bloom filter on success. Idempotent
        // and a no-op when the filter is disabled. Keeps the filter consistent
        // for the high-volume acquisition/backfill write path.
        if result.is_ok() {
            if let Some(filter) = self.bloom.load().as_deref() {
                for object in batch {
                    filter.insert(object.get_hash());
                }
            }
        }
        result.map_err(|error| self.fail_stop_write_if_checkpointed(error))
    }

    fn sync(&self) {
        if let Err(error) = self.sync_result() {
            self.journal.log(JournalLevel::Error, &error);
        }
    }

    fn sync_result(&self) -> Result<(), String> {
        // A batch holds `store_mutex` from its recovery checkpoint through
        // the final bucket insertion.  Synchronizing without the same fence
        // could flush and clear that checkpoint halfway through the batch,
        // leaving later index mutations unprotected after a crash.
        let _store_guard = self
            .store_mutex
            .lock()
            .expect("nudb backend store mutex must not be poisoned");
        self.commit_active_burst_if_needed()
            .and_then(|()| self.sync_data_files())
    }

    fn bulk_import_start(&self, estimated_nodes: u64) -> Result<(), String> {
        tracing::info!(target: "nodestore", estimated_nodes, "NuDB bulk import mode started — pre-allocating buckets");

        // Write crash recovery marker
        let marker_path = self
            .config
            .layout
            .base_path
            .join(".bulk_import_in_progress");
        fs::write(&marker_path, b"")
            .map_err(|e| format!("Failed to write bulk import marker: {e}"))?;

        self.bulk_importing.store(true, Ordering::Release);

        // Pre-allocate buckets so entries distribute correctly
        let _store_guard = self
            .store_mutex
            .lock()
            .expect("nudb backend store mutex must not be poisoned");
        let mut runtime = self
            .runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned");
        self.ensure_primary_bucket(&mut runtime)?;
        let header = runtime
            .key_header
            .as_mut()
            .ok_or_else(|| "NuDB key header missing after ensure_primary_bucket".to_owned())?;

        let capacity = u64::from(header.capacity.max(1));
        let needed_buckets = estimated_nodes.div_ceil(capacity).max(1) as u32;
        if needed_buckets > header.buckets {
            let block_size = usize::from(header.block_size);
            let cap = usize::from(header.capacity);
            let empty_block = NuDbBucket::empty(block_size, cap).encode_key_block()?;
            let to_add = needed_buckets - header.buckets;
            for _ in 0..to_add {
                self.append_key(&empty_block)?;
            }
            header.buckets = needed_buckets;
            header.modulus = nudb_ceil_pow2(needed_buckets);
            let h = *header;
            runtime.split_threshold = nudb_split_threshold(&h);
            runtime.split_fraction = runtime.split_threshold / 2;
            drop(runtime);

            // Persist updated header to disk
            let header_bytes = encode_nudb_key_file_header(&h)?;
            self.pwrite_key(0, &header_bytes)?;
        }

        tracing::info!(target: "nodestore", needed_buckets, "NuDB bucket pre-allocation complete");
        Ok(())
    }

    fn bulk_import_finish(&self) -> Result<(), String> {
        tracing::info!(target: "nodestore", "NuDB bulk import finishing — flushing bucket cache");
        self.bulk_importing.store(false, Ordering::Release);
        self.flush_bucket_cache()?;
        self.sync_result()?;

        // Remove crash recovery marker
        let marker_path = self
            .config
            .layout
            .base_path
            .join(".bulk_import_in_progress");
        let _ = fs::remove_file(&marker_path);

        tracing::info!(target: "nodestore", "NuDB bulk import complete");
        Ok(())
    }

    fn bulk_import_abort(&self) {
        self.bulk_importing.store(false, Ordering::Release);
        let marker_path = self
            .config
            .layout
            .base_path
            .join(".bulk_import_in_progress");
        if let Err(error) = fs::write(&marker_path, b"") {
            self.journal.log(
                JournalLevel::Error,
                &format!("Failed to restore bulk import marker after import failure: {error}"),
            );
        }
        self.sync();
    }

    fn for_each(&self, callback: &mut dyn FnMut(Arc<NodeObject>)) {
        let _ = self.traverse_objects(callback, false);
    }

    fn for_each_result(&self, callback: &mut dyn FnMut(Arc<NodeObject>)) -> Result<(), String> {
        self.traverse_objects(callback, true)
    }

    fn get_write_load(&self) -> i32 {
        0
    }

    fn set_delete_path(&self) {
        self.runtime
            .lock()
            .expect("nudb backend runtime mutex must not be poisoned")
            .open_state
            .set_delete_path();
    }

    fn verify(&self) {
        if let Err(error) = self.verify_backend() {
            self.journal.log(JournalLevel::Error, &error);
        }
    }

    fn fd_required(&self) -> i32 {
        3
    }
}

#[derive(Debug, Default)]
pub struct NuDbFactory;

impl NuDbFactory {
    pub fn new() -> Self {
        Self
    }

    fn build_backend(
        &self,
        key_bytes: usize,
        parameters: &Section,
        burst_size: usize,
        journal: Arc<dyn NodeStoreJournal>,
        default_open_args: Option<NuDbOpenArgs>,
    ) -> Result<Box<dyn Backend>, String> {
        let backend = NuDbBackend::new_with_default_open_args(
            key_bytes,
            parameters,
            burst_size,
            journal,
            default_open_args,
        )?;
        Ok(Box::new(backend))
    }
}

impl Factory for NuDbFactory {
    fn get_name(&self) -> String {
        "NuDB".to_owned()
    }

    fn create_instance(
        &self,
        key_bytes: usize,
        parameters: &Section,
        burst_size: usize,
        _scheduler: Arc<dyn Scheduler>,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> crate::factory::BackendResult {
        self.build_backend(key_bytes, parameters, burst_size, journal, None)
    }

    fn create_instance_with_nudb_context(
        &self,
        key_bytes: usize,
        parameters: &Section,
        burst_size: usize,
        _scheduler: Arc<dyn Scheduler>,
        context: &mut NuDbContext,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Option<crate::factory::BackendResult> {
        Some(self.build_backend(
            key_bytes,
            parameters,
            burst_size,
            journal,
            Some(NuDbOpenArgs::deterministic(
                context.app_type(),
                context.uid(),
                context.salt(),
            )),
        ))
    }

    fn create_instance_with_context(
        &self,
        key_bytes: usize,
        parameters: &Section,
        burst_size: usize,
        _scheduler: Arc<dyn Scheduler>,
        context: &mut dyn Any,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Option<crate::factory::BackendResult> {
        if let Some(&(app_type, uid, salt)) = context.downcast_ref::<(u64, u64, u64)>() {
            return Some(self.build_backend(
                key_bytes,
                parameters,
                burst_size,
                journal,
                Some(NuDbOpenArgs::deterministic(app_type, uid, salt)),
            ));
        }

        if let Some(values) = context.downcast_ref::<[u64; 3]>() {
            return Some(self.build_backend(
                key_bytes,
                parameters,
                burst_size,
                journal,
                Some(NuDbOpenArgs::deterministic(values[0], values[1], values[2])),
            ));
        }

        if let Some(context) = context.downcast_mut::<NuDbContext>() {
            return Some(self.build_backend(
                key_bytes,
                parameters,
                burst_size,
                journal,
                Some(NuDbOpenArgs::deterministic(
                    context.app_type(),
                    context.uid(),
                    context.salt(),
                )),
            ));
        }

        None
    }
}

pub type NuDbCompatibilityFactory = NuDbFactory;

pub fn validate_nudb_block_size(block_size: usize) -> Result<(), String> {
    if !(NUDB_MIN_BLOCK_SIZE..=NUDB_MAX_BLOCK_SIZE).contains(&block_size)
        || (block_size & (block_size - 1)) != 0
    {
        return Err(format!(
            "Invalid nudb_block_size: {block_size}. Must be power of 2 between 4096 and 32768."
        ));
    }
    Ok(())
}

pub fn parse_nudb_block_size(
    parameters: &Section,
    journal: &dyn NodeStoreJournal,
) -> Result<usize, String> {
    let Some(value) = parameters.get::<String>("nudb_block_size").ok().flatten() else {
        return Ok(NUDB_DEFAULT_BLOCK_SIZE);
    };

    let parsed = value
        .parse::<usize>()
        .map_err(|error| format!("Invalid nudb_block_size value: {value}. Error: {error}"))?;
    validate_nudb_block_size(parsed)?;
    journal.log(
        JournalLevel::Info,
        &format!("Using custom NuDB block size: {parsed} bytes"),
    );
    Ok(parsed)
}

pub fn nudb_encode_load_factor(load_factor: f64) -> Result<u16, String> {
    if !(0.0..1.0).contains(&load_factor) {
        return Err("NuDB load_factor must be between 0 and 1".to_owned());
    }
    let scaled = (65536.0 * load_factor).floor() as u64;
    Ok(u16::try_from(scaled.min(u64::from(u16::MAX))).expect("u16 bounds already enforced"))
}

pub fn nudb_decode_load_factor(encoded: u16) -> f64 {
    f64::from(encoded) / 65536.0
}

pub fn nudb_pepper(salt: u64) -> u64 {
    let little = salt.to_le_bytes();
    xxh64(&little, salt)
}

pub fn nudb_bucket_capacity(block_size: u16) -> u16 {
    let block_size = usize::from(block_size);
    let size = NUDB_BUCKET_COUNT_SIZE + NUDB_BUCKET_SPILL_SIZE;
    let entry_size = NUDB_BUCKET_ENTRY_SIZE;
    if block_size < NUDB_KEY_FILE_HEADER_SIZE || block_size < size {
        return 0;
    }
    let n = (block_size - size) / entry_size;
    n.min(usize::from(u16::MAX)) as u16
}

pub fn nudb_bucket_size(capacity: u16) -> usize {
    NUDB_BUCKET_COUNT_SIZE + NUDB_BUCKET_SPILL_SIZE + usize::from(capacity) * NUDB_BUCKET_ENTRY_SIZE
}

pub fn nudb_ceil_pow2(mut x: u32) -> u32 {
    if x <= 1 {
        return 1;
    }
    x -= 1;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    x + 1
}

pub fn nudb_bucket_index(hash_prefix: u64, buckets: u32, modulus: u32) -> u32 {
    let modulus = u64::from(modulus.max(1));
    let mut index = hash_prefix % modulus;
    if index >= u64::from(buckets) {
        index -= modulus / 2;
    }
    index as u32
}

pub fn nudb_split_threshold(header: &NuDbKeyFileHeader) -> u64 {
    std::cmp::max(
        65_536,
        u64::from(header.load_factor) * u64::from(header.capacity.max(1)),
    )
}

pub fn encode_nudb_data_file_header(header: &NuDbDataFileHeader) -> Result<Vec<u8>, String> {
    let mut bytes = vec![0u8; NUDB_DATA_FILE_HEADER_SIZE];
    let mut offset = 0usize;
    bytes[offset..offset + 8].copy_from_slice(NUDB_DATA_FILE_TYPE);
    offset += 8;
    write_u16_be(&mut bytes, &mut offset, header.version);
    write_u64_be(&mut bytes, &mut offset, header.uid);
    write_u64_be(&mut bytes, &mut offset, header.appnum);
    write_u16_be(&mut bytes, &mut offset, header.key_size);
    Ok(bytes)
}

pub fn encode_nudb_key_file_header(header: &NuDbKeyFileHeader) -> Result<Vec<u8>, String> {
    if usize::from(header.block_size) < NUDB_KEY_FILE_HEADER_SIZE {
        return Err("NuDB key header block_size is smaller than header size".to_owned());
    }
    let mut bytes = vec![0u8; usize::from(header.block_size)];
    let mut offset = 0usize;
    bytes[offset..offset + 8].copy_from_slice(NUDB_KEY_FILE_TYPE);
    offset += 8;
    write_u16_be(&mut bytes, &mut offset, header.version);
    write_u64_be(&mut bytes, &mut offset, header.uid);
    write_u64_be(&mut bytes, &mut offset, header.appnum);
    write_u16_be(&mut bytes, &mut offset, header.key_size);
    write_u64_be(&mut bytes, &mut offset, header.salt);
    write_u64_be(&mut bytes, &mut offset, header.pepper);
    write_u16_be(&mut bytes, &mut offset, header.block_size);
    write_u16_be(&mut bytes, &mut offset, header.load_factor);
    Ok(bytes)
}

pub fn encode_nudb_log_file_header(header: &NuDbLogFileHeader) -> Result<Vec<u8>, String> {
    let mut bytes = vec![0u8; NUDB_LOG_FILE_HEADER_SIZE];
    let mut offset = 0usize;
    bytes[offset..offset + 8].copy_from_slice(NUDB_LOG_FILE_TYPE);
    offset += 8;
    write_u16_be(&mut bytes, &mut offset, header.version);
    write_u64_be(&mut bytes, &mut offset, header.uid);
    write_u64_be(&mut bytes, &mut offset, header.appnum);
    write_u16_be(&mut bytes, &mut offset, header.key_size);
    write_u64_be(&mut bytes, &mut offset, header.salt);
    write_u64_be(&mut bytes, &mut offset, header.pepper);
    write_u16_be(&mut bytes, &mut offset, header.block_size);
    write_u64_be(&mut bytes, &mut offset, header.key_file_size);
    write_u64_be(&mut bytes, &mut offset, header.dat_file_size);
    Ok(bytes)
}

pub fn read_nudb_data_file_header(path: &Path) -> Result<NuDbDataFileHeader, String> {
    let mut file = fs::File::open(path).map_err(|error| error.to_string())?;
    let file_size = file.metadata().map_err(|error| error.to_string())?.len() as usize;
    if file_size < NUDB_DATA_FILE_HEADER_SIZE {
        return Err("NuDB data file is too short".to_owned());
    }
    let mut bytes = vec![0u8; NUDB_DATA_FILE_HEADER_SIZE];
    file.read_exact(&mut bytes)
        .map_err(|error| error.to_string())?;

    let mut offset = 0usize;
    let mut type_tag = [0u8; 8];
    type_tag.copy_from_slice(&bytes[offset..offset + 8]);
    offset += 8;
    if &type_tag != NUDB_DATA_FILE_TYPE {
        return Err("NuDB data file type tag mismatch".to_owned());
    }

    let header = NuDbDataFileHeader {
        version: read_u16_be(&bytes, &mut offset)?,
        uid: read_u64_be(&bytes, &mut offset)?,
        appnum: read_u64_be(&bytes, &mut offset)?,
        key_size: read_u16_be(&bytes, &mut offset)?,
    };
    header.validate_basic()?;
    Ok(header)
}

pub fn read_nudb_key_file_header(path: &Path) -> Result<NuDbKeyFileHeader, String> {
    let mut file = fs::File::open(path).map_err(|error| error.to_string())?;
    let file_size = file.metadata().map_err(|error| error.to_string())?.len() as usize;
    if file_size < NUDB_KEY_FILE_HEADER_SIZE {
        return Err("NuDB key file is too short".to_owned());
    }
    let mut bytes = vec![0u8; NUDB_KEY_FILE_HEADER_SIZE];
    file.read_exact(&mut bytes)
        .map_err(|error| error.to_string())?;

    let mut offset = 0usize;
    let mut type_tag = [0u8; 8];
    type_tag.copy_from_slice(&bytes[offset..offset + 8]);
    offset += 8;
    if &type_tag != NUDB_KEY_FILE_TYPE {
        return Err("NuDB key file type tag mismatch".to_owned());
    }

    let version = read_u16_be(&bytes, &mut offset)?;
    let uid = read_u64_be(&bytes, &mut offset)?;
    let appnum = read_u64_be(&bytes, &mut offset)?;
    let key_size = read_u16_be(&bytes, &mut offset)?;
    let salt = read_u64_be(&bytes, &mut offset)?;
    let pepper = read_u64_be(&bytes, &mut offset)?;
    let block_size = read_u16_be(&bytes, &mut offset)?;
    let load_factor = read_u16_be(&bytes, &mut offset)?;
    let capacity = nudb_bucket_capacity(block_size);
    let buckets = if file_size > usize::from(block_size) && block_size > 0 {
        ((file_size - usize::from(block_size)) / usize::from(block_size)) as u32
    } else {
        0
    };
    let modulus = nudb_ceil_pow2(buckets);

    let header = NuDbKeyFileHeader {
        version,
        uid,
        appnum,
        key_size,
        salt,
        pepper,
        block_size,
        load_factor,
        capacity,
        buckets,
        modulus,
    };
    header.validate_basic()?;
    Ok(header)
}

pub fn read_nudb_log_file_header(path: &Path) -> Result<NuDbLogFileHeader, String> {
    let mut file = fs::File::open(path).map_err(|error| error.to_string())?;
    let file_size = file.metadata().map_err(|error| error.to_string())?.len() as usize;
    if file_size < NUDB_LOG_FILE_HEADER_SIZE {
        return Err("NuDB log file is too short".to_owned());
    }
    let mut bytes = vec![0u8; NUDB_LOG_FILE_HEADER_SIZE];
    file.read_exact(&mut bytes)
        .map_err(|error| error.to_string())?;

    let mut offset = 0usize;
    let mut type_tag = [0u8; 8];
    type_tag.copy_from_slice(&bytes[offset..offset + 8]);
    offset += 8;
    if &type_tag != NUDB_LOG_FILE_TYPE {
        return Err("NuDB log file type tag mismatch".to_owned());
    }

    let header = NuDbLogFileHeader {
        version: read_u16_be(&bytes, &mut offset)?,
        uid: read_u64_be(&bytes, &mut offset)?,
        appnum: read_u64_be(&bytes, &mut offset)?,
        key_size: read_u16_be(&bytes, &mut offset)?,
        salt: read_u64_be(&bytes, &mut offset)?,
        pepper: read_u64_be(&bytes, &mut offset)?,
        block_size: read_u16_be(&bytes, &mut offset)?,
        key_file_size: read_u64_be(&bytes, &mut offset)?,
        dat_file_size: read_u64_be(&bytes, &mut offset)?,
    };
    header.validate_basic()?;
    Ok(header)
}

fn write_u16_be(bytes: &mut [u8], offset: &mut usize, value: u16) {
    bytes[*offset..*offset + 2].copy_from_slice(&value.to_be_bytes());
    *offset += 2;
}

fn write_u64_be(bytes: &mut [u8], offset: &mut usize, value: u64) {
    bytes[*offset..*offset + 8].copy_from_slice(&value.to_be_bytes());
    *offset += 8;
}

fn write_u48_be(bytes: &mut [u8], offset: &mut usize, value: u64) -> Result<(), String> {
    if value > NUDB_U48_MAX {
        return Err(format!(
            "NuDB 48-bit value overflow: {value} (0x{value:016X})"
        ));
    }
    bytes[*offset..*offset + 6].copy_from_slice(&[
        ((value >> 40) & 0xff) as u8,
        ((value >> 32) & 0xff) as u8,
        ((value >> 24) & 0xff) as u8,
        ((value >> 16) & 0xff) as u8,
        ((value >> 8) & 0xff) as u8,
        (value & 0xff) as u8,
    ]);
    *offset += 6;
    Ok(())
}

#[allow(dead_code)]
fn write_u48_be_to_writer(writer: &mut dyn Write, value: u64) -> Result<(), String> {
    if value > NUDB_U48_MAX {
        return Err(format!(
            "NuDB 48-bit value overflow: {value} (0x{value:016X})"
        ));
    }
    let bytes = [
        ((value >> 40) & 0xff) as u8,
        ((value >> 32) & 0xff) as u8,
        ((value >> 24) & 0xff) as u8,
        ((value >> 16) & 0xff) as u8,
        ((value >> 8) & 0xff) as u8,
        (value & 0xff) as u8,
    ];
    writer.write_all(&bytes).map_err(|error| error.to_string())
}

fn read_u16_be(bytes: &[u8], offset: &mut usize) -> Result<u16, String> {
    let end = *offset + 2;
    let slice = bytes
        .get(*offset..end)
        .ok_or_else(|| "NuDB key header ended unexpectedly".to_owned())?;
    *offset = end;
    Ok(u16::from_be_bytes([slice[0], slice[1]]))
}

fn read_u16_be_from_reader(reader: &mut dyn Read, field_name: &str) -> Result<u16, String> {
    let mut bytes = [0u8; 2];
    reader
        .read_exact(&mut bytes)
        .map_err(|error| format!("{field_name} read failed: {error}"))?;
    Ok(u16::from_be_bytes(bytes))
}

fn read_u64_be_from_reader(reader: &mut dyn Read, field_name: &str) -> Result<u64, String> {
    let mut bytes = [0u8; 8];
    reader
        .read_exact(&mut bytes)
        .map_err(|error| format!("{field_name} read failed: {error}"))?;
    Ok(u64::from_be_bytes(bytes))
}

fn read_u64_be(bytes: &[u8], offset: &mut usize) -> Result<u64, String> {
    let end = *offset + 8;
    let slice = bytes
        .get(*offset..end)
        .ok_or_else(|| "NuDB key header ended unexpectedly".to_owned())?;
    *offset = end;
    Ok(u64::from_be_bytes([
        slice[0], slice[1], slice[2], slice[3], slice[4], slice[5], slice[6], slice[7],
    ]))
}

fn read_u48_be(bytes: &[u8], offset: &mut usize) -> Result<u64, String> {
    let end = *offset + 6;
    let slice = bytes
        .get(*offset..end)
        .ok_or_else(|| "NuDB bucket record ended unexpectedly".to_owned())?;
    *offset = end;
    Ok((u64::from(slice[0]) << 40)
        | (u64::from(slice[1]) << 32)
        | (u64::from(slice[2]) << 24)
        | (u64::from(slice[3]) << 16)
        | (u64::from(slice[4]) << 8)
        | u64::from(slice[5]))
}

fn read_u48_be_from_reader(reader: &mut dyn Read, field_name: &str) -> Result<u64, String> {
    let mut bytes = [0u8; 6];
    reader
        .read_exact(&mut bytes)
        .map_err(|error| format!("{field_name} read failed: {error}"))?;
    Ok((u64::from(bytes[0]) << 40)
        | (u64::from(bytes[1]) << 32)
        | (u64::from(bytes[2]) << 24)
        | (u64::from(bytes[3]) << 16)
        | (u64::from(bytes[4]) << 8)
        | u64::from(bytes[5]))
}

#[cfg(test)]
mod tests {
    use super::{
        NUDB_APPNUM, NUDB_CURRENT_VERSION, NUDB_DATA_FILE_HEADER_SIZE, NUDB_DEFAULT_BLOCK_SIZE,
        NUDB_KEY_FILE_HEADER_SIZE, NUDB_KEY_FILE_TYPE, NUDB_TARGET_LOAD_FACTOR, NuDbBackendConfig,
        NuDbFileSetState, NuDbKeyFileHeader, NuDbLayout, NuDbMetadataHeader, NuDbOpenAction,
        NuDbOpenArgs, NuDbOpenState, NuDbTestBatchErrorPoint, NuDbTestCrashPoint,
        encode_nudb_key_file_header, nudb_bucket_capacity, nudb_decode_load_factor,
        nudb_encode_load_factor, nudb_pepper, parse_nudb_block_size, read_nudb_key_file_header,
        read_nudb_log_file_header, set_nudb_test_batch_error, set_nudb_test_crash,
        validate_nudb_block_size,
    };
    use crate::{
        Backend, JournalLevel, NodeObject, NodeObjectType, NodeStoreJournal, NuDbBackend, Status,
    };
    use basics::base_uint::Uint256;
    use basics::basic_config::Section;
    use dashmap::DashMap;
    use std::fs;
    use std::panic::{self, AssertUnwindSafe};
    use std::sync::{Arc, Mutex};
    use tempfile::TempDir;

    #[derive(Default)]
    struct RecordingJournal {
        entries: Mutex<Vec<(JournalLevel, String)>>,
    }

    impl RecordingJournal {
        fn take(&self) -> Vec<(JournalLevel, String)> {
            self.entries
                .lock()
                .expect("recording journal mutex must not be poisoned")
                .clone()
        }
    }

    impl NodeStoreJournal for RecordingJournal {
        fn log(&self, level: JournalLevel, message: &str) {
            self.entries
                .lock()
                .expect("recording journal mutex must not be poisoned")
                .push((level, message.to_owned()));
        }
    }

    fn test_nudb_section(path: &std::path::Path) -> Section {
        let mut section = Section::new("node_db");
        section.set("path", path.to_string_lossy().into_owned());
        section
    }

    fn test_object(fill: u8, payload: &[u8]) -> Arc<NodeObject> {
        Arc::new(NodeObject::new(
            NodeObjectType::Ledger,
            payload.to_vec(),
            Uint256::from_array([fill; 32]),
        ))
    }

    fn test_object_seq(sequence: u32) -> Arc<NodeObject> {
        let mut hash = [0u8; 32];
        hash[..4].copy_from_slice(&sequence.to_be_bytes());
        hash[4..8].copy_from_slice(&sequence.wrapping_mul(0x9E37_79B9).to_be_bytes());
        Arc::new(NodeObject::new(
            NodeObjectType::Ledger,
            format!("object-{sequence}").into_bytes(),
            Uint256::from_array(hash),
        ))
    }

    #[test]
    fn nudb_synchronous_burst_commit_limit_is_bounded_without_raising_small_configs() {
        let large = TempDir::new().expect("large tempdir");
        let large_backend = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(large.path()),
            40_000,
            Arc::new(RecordingJournal::default()),
        )
        .expect("large backend");
        assert_eq!(
            large_backend.burst_commit_limit(),
            super::MAX_SYNCHRONOUS_BURST_WRITES
        );

        let small = TempDir::new().expect("small tempdir");
        let small_backend = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(small.path()),
            64,
            Arc::new(RecordingJournal::default()),
        )
        .expect("small backend");
        assert_eq!(small_backend.burst_commit_limit(), 64);
    }

    #[test]
    fn nudb_active_burst_defers_key_writes_and_logs_only_modified_buckets() {
        let temp = TempDir::new().expect("tempdir");
        let backend = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(temp.path()),
            10_000,
            Arc::new(RecordingJournal::default()),
        )
        .expect("backend");
        backend
            .open_deterministic(true, NUDB_APPNUM, 90_001, 90_002)
            .expect("open");

        for sequence in 0..700 {
            backend
                .store(test_object_seq(sequence))
                .expect("seed store");
        }
        backend.sync_result().expect("seed commit");
        let key_path = temp.path().join("nudb.key");
        let log_path = temp.path().join("nudb.log");
        let committed_key = fs::read(&key_path).expect("committed key file");
        assert!(committed_key.len() > 3 * NUDB_DEFAULT_BLOCK_SIZE);

        // Keep this insertion away from a split so it changes one existing
        // primary bucket and gives the amplification assertion a tight bound.
        {
            let mut runtime = backend.runtime.lock().expect("runtime");
            runtime.split_fraction = 0;
            runtime.split_threshold = u64::MAX;
        }
        let pending = test_object_seq(10_000);
        backend.store(Arc::clone(&pending)).expect("pending store");
        assert_eq!(backend.fetch(pending.hash()).1, Status::Ok);
        assert_eq!(
            fs::read(&key_path).expect("key file before commit"),
            committed_key,
            "active burst must expose c1 through memory without rewriting key buckets"
        );
        assert_eq!(
            fs::metadata(&log_path).expect("log metadata").len(),
            super::NUDB_LOG_FILE_HEADER_SIZE as u64,
            "initial checkpoint contains only the recovery header"
        );

        backend
            .append_burst_originals_to_log()
            .expect("append selective c0");
        let selective_log_size = fs::metadata(&log_path).expect("log metadata").len();
        assert!(
            selective_log_size
                <= (super::NUDB_LOG_FILE_HEADER_SIZE + 8 + NUDB_DEFAULT_BLOCK_SIZE) as u64,
            "one modified bucket must not snapshot the complete key database"
        );
        assert!(selective_log_size < committed_key.len() as u64);
        backend.sync_result().expect("commit pending burst");
        assert_eq!(fs::metadata(&log_path).expect("log metadata").len(), 0);
    }

    #[test]
    fn nudb_selective_log_recovery_preserves_exact_key_extent_and_untouched_buckets() {
        let temp = TempDir::new().expect("tempdir");
        let backend = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(temp.path()),
            10_000,
            Arc::new(RecordingJournal::default()),
        )
        .expect("backend");
        backend
            .open_deterministic(true, NUDB_APPNUM, 90_101, 90_102)
            .expect("open");
        let preserved: Vec<_> = (0..700).map(test_object_seq).collect();
        for object in &preserved {
            backend.store(Arc::clone(object)).expect("seed store");
        }
        backend.sync_result().expect("seed commit");
        let key_path = temp.path().join("nudb.key");
        let original_key_size = fs::metadata(&key_path).expect("key metadata").len();

        {
            let mut runtime = backend.runtime.lock().expect("runtime");
            runtime.split_fraction = 0;
            runtime.split_threshold = u64::MAX;
        }
        let interrupted = test_object_seq(20_000);
        backend
            .store(Arc::clone(&interrupted))
            .expect("interrupted store");
        backend
            .append_burst_originals_to_log()
            .expect("durable selective c0");
        backend
            .flush_bucket_cache()
            .expect("simulate partial c1 flush");
        {
            let mut runtime = backend.runtime.lock().expect("runtime");
            runtime.fail_stop_error = Some("simulated crash during c1 flush".to_owned());
        }
        assert!(backend.close().is_err());
        drop(backend);

        let reopened = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(temp.path()),
            10_000,
            Arc::new(RecordingJournal::default()),
        )
        .expect("reopened backend");
        reopened
            .open_deterministic(false, NUDB_APPNUM, 90_101, 90_102)
            .expect("selective recovery");
        assert_eq!(
            fs::metadata(&key_path)
                .expect("recovered key metadata")
                .len(),
            original_key_size,
            "selective records must not shrink the key file to their highest index"
        );
        for object in preserved.iter().step_by(37) {
            assert_eq!(reopened.fetch(object.hash()).1, Status::Ok);
        }
        assert_eq!(reopened.fetch(interrupted.hash()).1, Status::NotFound);
        reopened
            .verify_backend()
            .expect("recovered backend verifies");
    }

    #[test]
    fn nudb_primary_bucket_creation_has_durable_pre_mutation_checkpoint() {
        let temp = TempDir::new().expect("tempdir");
        let backend = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(temp.path()),
            64,
            Arc::new(RecordingJournal::default()),
        )
        .expect("backend");
        backend
            .open_deterministic(true, NUDB_APPNUM, 91_001, 92_001)
            .expect("open");

        let initial_header = backend
            .key_file_header()
            .expect("initial zero-bucket header");
        assert_eq!(initial_header.buckets, 0);
        let block_size = usize::from(initial_header.block_size);
        assert_eq!(
            fs::metadata(temp.path().join("nudb.key"))
                .expect("initial key metadata")
                .len(),
            block_size as u64,
            "an empty NuDB key file contains only its header block"
        );

        set_nudb_test_crash(NuDbTestCrashPoint::PrimaryBucket);
        let crash = panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = backend.store(test_object(0x91, b"primary-ordering"));
        }));
        assert!(
            crash.is_err(),
            "test failpoint must stop after primary mutation"
        );
        drop(backend);

        let checkpoint = read_nudb_log_file_header(&temp.path().join("nudb.log"))
            .expect("durable checkpoint must precede primary creation");
        assert_eq!(checkpoint.key_file_size, block_size as u64);
        assert_eq!(checkpoint.dat_file_size, NUDB_DATA_FILE_HEADER_SIZE as u64);
        assert!(
            fs::metadata(temp.path().join("nudb.key"))
                .expect("key metadata")
                .len()
                > checkpoint.key_file_size,
            "the primary bucket mutation must occur after the checkpoint"
        );
    }

    #[test]
    fn nudb_split_crash_recovers_to_pre_split_checkpoint() {
        let temp = TempDir::new().expect("tempdir");
        let backend = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(temp.path()),
            64,
            Arc::new(RecordingJournal::default()),
        )
        .expect("backend");
        backend
            .open_deterministic(true, NUDB_APPNUM, 93_001, 94_001)
            .expect("open");
        let committed = test_object(0x93, b"committed-before-split");
        let interrupted = test_object(0x94, b"interrupted-during-split");
        backend
            .store(Arc::clone(&committed))
            .expect("initial store");
        backend.sync_result().expect("commit initial store");

        {
            let mut runtime = backend.runtime.lock().expect("runtime");
            runtime.split_fraction = runtime.split_threshold - 65_536;
        }
        set_nudb_test_crash(NuDbTestCrashPoint::Split);
        let crash = panic::catch_unwind(AssertUnwindSafe(|| {
            let _ = backend.store(Arc::clone(&interrupted));
        }));
        assert!(
            crash.is_err(),
            "test failpoint must stop after split mutation"
        );
        drop(backend);

        let checkpoint = read_nudb_log_file_header(&temp.path().join("nudb.log"))
            .expect("durable checkpoint must precede split");
        assert_eq!(
            fs::metadata(temp.path().join("nudb.key"))
                .expect("key metadata")
                .len(),
            checkpoint.key_file_size + u64::from(checkpoint.block_size),
            "the split adds one key bucket after the checkpoint"
        );

        let reopened = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(temp.path()),
            64,
            Arc::new(RecordingJournal::default()),
        )
        .expect("reopened backend");
        reopened
            .open_deterministic(false, NUDB_APPNUM, 93_001, 94_001)
            .expect("recovery must reopen the pre-split checkpoint");
        assert_eq!(reopened.fetch(committed.hash()).1, Status::Ok);
        assert_eq!(reopened.fetch(interrupted.hash()).1, Status::NotFound);
        reopened.verify_backend().expect("recovered store verifies");
        assert_eq!(
            fs::metadata(temp.path().join("nudb.key"))
                .expect("recovered key metadata")
                .len(),
            checkpoint.key_file_size
        );
        assert_eq!(
            fs::metadata(temp.path().join("nudb.dat"))
                .expect("recovered data metadata")
                .len(),
            checkpoint.dat_file_size
        );
    }

    fn assert_checked_batch_fail_stop_recovers(point: NuDbTestBatchErrorPoint, uid: u64) {
        let temp = TempDir::new().expect("tempdir");
        let backend = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(temp.path()),
            64,
            Arc::new(RecordingJournal::default()),
        )
        .expect("backend");
        backend
            .open_deterministic(true, NUDB_APPNUM, uid, uid + 1)
            .expect("open");
        let committed = test_object(0xA0, b"committed-before-failed-batch");
        backend
            .store(Arc::clone(&committed))
            .expect("initial store");
        backend.sync_result().expect("commit initial object");

        let interrupted = vec![
            test_object(0xA1, b"failed-batch-one"),
            test_object(0xA2, b"failed-batch-two"),
            test_object(0xA3, b"failed-batch-three"),
        ];
        set_nudb_test_batch_error(point);
        let error = backend
            .store_batch_result(&interrupted)
            .expect_err("failpoint must reject checked batch");
        assert!(error.contains("injected checked-batch failure"));
        assert!(
            fs::metadata(temp.path().join("nudb.log"))
                .expect("recovery log metadata")
                .len()
                > 0,
            "fail-stop must preserve the active recovery checkpoint"
        );
        assert!(backend.sync_result().unwrap_err().contains("fail-stopped"));
        assert!(
            backend
                .store(test_object(0xA4, b"write-after-fail-stop"))
                .unwrap_err()
                .contains("fail-stopped")
        );
        assert!(
            backend
                .verify_backend()
                .unwrap_err()
                .contains("fail-stopped")
        );
        let mut visited = Vec::new();
        assert!(
            backend
                .for_each_result(&mut |object| visited.push(object))
                .unwrap_err()
                .contains("fail-stopped")
        );
        assert!(backend.close().unwrap_err().contains("fail-stopped"));
        assert!(!backend.is_open());
        assert!(
            fs::metadata(temp.path().join("nudb.log"))
                .expect("preserved recovery log metadata")
                .len()
                > 0
        );
        drop(backend);

        let reopened = NuDbBackend::new(
            NodeObject::KEY_BYTES,
            &test_nudb_section(temp.path()),
            64,
            Arc::new(RecordingJournal::default()),
        )
        .expect("reopened backend");
        reopened
            .open_deterministic(false, NUDB_APPNUM, uid, uid + 1)
            .expect("log recovery reopen");
        assert_eq!(reopened.fetch(committed.hash()).1, Status::Ok);
        for object in interrupted {
            assert_eq!(reopened.fetch(object.hash()).1, Status::NotFound);
        }
        reopened
            .verify_backend()
            .expect("recovered backend verifies");
    }

    #[test]
    fn checked_batch_failure_after_append_fail_stops_and_recovers() {
        assert_checked_batch_fail_stop_recovers(NuDbTestBatchErrorPoint::AfterAppend, 95_001);
    }

    #[test]
    fn checked_batch_failure_during_index_insert_fail_stops_and_recovers() {
        assert_checked_batch_fail_stop_recovers(NuDbTestBatchErrorPoint::IndexInsert(2), 96_001);
    }

    #[test]
    fn nudb_cache_eviction_releases_the_dashmap_iterator_guard() {
        let cache = DashMap::new();
        for index in 0..super::MAX_BUCKET_CACHE_ENTRIES as u32 {
            cache.insert(index, ());
        }

        super::evict_one_cached_bucket(&cache);

        assert_eq!(cache.len(), super::MAX_BUCKET_CACHE_ENTRIES - 1);
    }

    #[test]
    fn nudb_layout_uses_the_cpp_three_file_names() {
        let layout = NuDbLayout::from_base_path("/tmp/example");
        assert_eq!(
            layout.data_path,
            std::path::PathBuf::from("/tmp/example/nudb.dat")
        );
        assert_eq!(
            layout.key_path,
            std::path::PathBuf::from("/tmp/example/nudb.key")
        );
        assert_eq!(
            layout.log_path,
            std::path::PathBuf::from("/tmp/example/nudb.log")
        );
        assert_eq!(layout.file_set_state(), NuDbFileSetState::Missing);
    }

    #[test]
    fn nudb_block_size_defaults_to_4k_without_override() {
        let section = Section::new("node_db");
        let journal = RecordingJournal::default();
        assert_eq!(
            parse_nudb_block_size(&section, &journal).expect("default block size"),
            NUDB_DEFAULT_BLOCK_SIZE
        );
        assert!(journal.take().is_empty());
    }

    #[test]
    fn nudb_block_size_logs_custom_values() {
        let mut section = Section::new("node_db");
        section.set("nudb_block_size", "8192");
        let journal = RecordingJournal::default();
        assert_eq!(
            parse_nudb_block_size(&section, &journal).expect("custom block size"),
            8192
        );
        assert_eq!(
            journal.take(),
            vec![(
                JournalLevel::Info,
                "Using custom NuDB block size: 8192 bytes".to_owned()
            )]
        );
    }

    #[test]
    fn nudb_block_size_rejects_malformed_and_out_of_range_values() {
        let mut malformed = Section::new("node_db");
        malformed.set("nudb_block_size", "invalid");
        let journal = RecordingJournal::default();
        assert_eq!(
            parse_nudb_block_size(&malformed, &journal).expect_err("invalid string"),
            "Invalid nudb_block_size value: invalid. Error: invalid digit found in string"
        );

        let mut out_of_range = Section::new("node_db");
        out_of_range.set("nudb_block_size", "5000");
        assert_eq!(
            parse_nudb_block_size(&out_of_range, &journal).expect_err("invalid power of two"),
            "Invalid nudb_block_size: 5000. Must be power of 2 between 4096 and 32768."
        );
        assert!(journal.take().is_empty());
    }

    #[test]
    fn nudb_backend_config_requires_path_and_preserves_cpp_defaults() {
        let mut section = Section::new("node_db");
        section.set("path", "/tmp/nudb");
        let journal = RecordingJournal::default();

        let config =
            NuDbBackendConfig::from_section(crate::NodeObject::KEY_BYTES, &section, 64, &journal)
                .expect("config");

        assert_eq!(config.key_bytes, crate::NodeObject::KEY_BYTES);
        assert_eq!(config.burst_size, 64);
        assert_eq!(config.block_size, NUDB_DEFAULT_BLOCK_SIZE);
        assert_eq!(config.layout, NuDbLayout::from_base_path("/tmp/nudb"));
    }

    #[test]
    fn nudb_backend_config_rejects_missing_path() {
        let section = Section::new("node_db");
        let journal = RecordingJournal::default();
        assert_eq!(
            NuDbBackendConfig::from_section(crate::NodeObject::KEY_BYTES, &section, 64, &journal)
                .expect_err("missing path should fail"),
            "nodestore: Missing path in NuDB backend"
        );
    }

    #[test]
    fn nudb_open_args_and_metadata_preserve_rippled_appnum_contract() {
        let open_args = NuDbOpenArgs::quaxar_default(11, 22);
        assert_eq!(open_args.app_type, NUDB_APPNUM);

        let header = NuDbMetadataHeader::new(NUDB_APPNUM, 11, 22, 32, 4096);
        header.validate_for_quaxar().expect("Quaxar header");

        let wrong = NuDbMetadataHeader::new(99, 11, 22, 32, 4096);
        assert_eq!(
            wrong.validate_for_quaxar().expect_err("wrong appnum"),
            "nodestore: unknown appnum"
        );
    }

    #[test]
    fn nudb_metadata_builder_preserves_deterministic_open_values() {
        let mut section = Section::new("node_db");
        section.set("path", "/tmp/nudb");
        let journal = RecordingJournal::default();
        let config =
            NuDbBackendConfig::from_section(crate::NodeObject::KEY_BYTES, &section, 32, &journal)
                .expect("config");
        let header = config.metadata_header(NuDbOpenArgs::deterministic(7, 8, 9));

        assert_eq!(
            header,
            NuDbMetadataHeader::new(7, 8, 9, crate::NodeObject::KEY_BYTES, 4096)
        );
    }

    #[test]
    fn nudb_open_plan_creates_new_only_when_file_set_is_missing() {
        let temp = TempDir::new().expect("tempdir");
        let mut section = Section::new("node_db");
        section.set("path", temp.path().to_string_lossy().into_owned());
        let journal = RecordingJournal::default();
        let config =
            NuDbBackendConfig::from_section(crate::NodeObject::KEY_BYTES, &section, 32, &journal)
                .expect("config");

        let create_plan = config
            .build_open_plan(true, NuDbOpenArgs::deterministic(7, 8, 9))
            .expect("create plan");
        assert_eq!(create_plan.action, NuDbOpenAction::CreateNew);

        assert_eq!(
            config
                .build_open_plan(false, NuDbOpenArgs::deterministic(7, 8, 9))
                .expect_err("missing file set should fail without create"),
            format!("Unable to open/create NuDB backend: {}", config.path)
        );
    }

    #[test]
    fn nudb_open_plan_rejects_partial_file_sets() {
        let temp = TempDir::new().expect("tempdir");
        let mut section = Section::new("node_db");
        section.set("path", temp.path().to_string_lossy().into_owned());
        let journal = RecordingJournal::default();
        let config =
            NuDbBackendConfig::from_section(crate::NodeObject::KEY_BYTES, &section, 32, &journal)
                .expect("config");
        std::fs::create_dir_all(temp.path()).expect("dir");
        std::fs::write(temp.path().join("nudb.dat"), []).expect("data file");

        assert_eq!(config.layout.file_set_state(), NuDbFileSetState::Partial);
        assert_eq!(
            config
                .build_open_plan(true, NuDbOpenArgs::deterministic(7, 8, 9))
                .expect_err("partial file set should fail"),
            format!(
                "Incomplete NuDB file set at {}. Expected nudb.dat, nudb.key, and nudb.log",
                config.path
            )
        );
    }

    #[test]
    fn nudb_open_plan_opens_existing_complete_file_sets() {
        let temp = TempDir::new().expect("tempdir");
        let mut section = Section::new("node_db");
        section.set("path", temp.path().to_string_lossy().into_owned());
        let journal = RecordingJournal::default();
        let config =
            NuDbBackendConfig::from_section(crate::NodeObject::KEY_BYTES, &section, 32, &journal)
                .expect("config");
        config.create_empty_file_set_for_tests().expect("file set");

        let plan = config
            .build_open_plan(false, NuDbOpenArgs::deterministic(7, 8, 9))
            .expect("open existing");
        assert_eq!(config.layout.file_set_state(), NuDbFileSetState::Complete);
        assert_eq!(plan.action, NuDbOpenAction::OpenExisting);
    }

    #[test]
    fn nudb_open_state_tracks_open_close_and_delete_path_without_reopening() {
        let header = NuDbMetadataHeader::new(NUDB_APPNUM, 11, 22, 32, 4096);
        let mut state = NuDbOpenState::new(header);

        assert!(!state.is_open());
        state.open(NUDB_APPNUM).expect("open");
        assert!(state.is_open());
        assert_eq!(
            state
                .open(NUDB_APPNUM)
                .expect_err("second open should fail"),
            "NuDB backend is already open"
        );
        state.set_delete_path();
        assert!(state.delete_path());
        state.close();
        assert!(!state.is_open());
    }

    #[test]
    fn nudb_key_header_round_trips_exact_cpp_disk_layout() {
        let header = NuDbKeyFileHeader {
            version: NUDB_CURRENT_VERSION,
            uid: 11,
            appnum: NUDB_APPNUM,
            key_size: 32,
            salt: 22,
            pepper: nudb_pepper(22),
            block_size: 4096,
            load_factor: nudb_encode_load_factor(0.5).expect("load factor"),
            capacity: nudb_bucket_capacity(4096),
            buckets: 0,
            modulus: 1,
        };
        let bytes = encode_nudb_key_file_header(&header).expect("encode");

        assert_eq!(bytes.len(), 4096);
        assert_eq!(&bytes[..8], NUDB_KEY_FILE_TYPE);
        assert!(
            bytes[NUDB_KEY_FILE_HEADER_SIZE..]
                .iter()
                .all(|byte| *byte == 0)
        );
    }

    #[test]
    fn nudb_key_header_file_read_matches_written_values() {
        let temp = TempDir::new().expect("tempdir");
        let mut section = Section::new("node_db");
        section.set("path", temp.path().to_string_lossy().into_owned());
        let journal = RecordingJournal::default();
        let config =
            NuDbBackendConfig::from_section(crate::NodeObject::KEY_BYTES, &section, 32, &journal)
                .expect("config");

        let disk_header = NuDbKeyFileHeader::from_metadata(
            config.metadata_header(NuDbOpenArgs::deterministic(NUDB_APPNUM, 55, 66)),
        )
        .expect("disk header");
        let mut key_file = encode_nudb_key_file_header(&disk_header).expect("encode key header");
        key_file.extend_from_slice(&vec![0u8; usize::from(disk_header.block_size)]);
        fs::write(&config.layout.key_path, key_file).expect("write key header and bucket");

        let read = read_nudb_key_file_header(&config.layout.key_path).expect("read key header");
        assert_eq!(read.version, NUDB_CURRENT_VERSION);
        assert_eq!(read.uid, 55);
        assert_eq!(read.appnum, NUDB_APPNUM);
        assert_eq!(read.key_size, crate::NodeObject::KEY_BYTES as u16);
        assert_eq!(read.salt, 66);
        assert_eq!(read.pepper, nudb_pepper(66));
        assert_eq!(read.block_size, 4096);
        assert_eq!(read.capacity, nudb_bucket_capacity(4096));
        assert_eq!(nudb_decode_load_factor(read.load_factor), 0.5);
    }

    #[test]
    fn nudb_key_header_accepts_zero_bucket_initial_state() {
        let temp = TempDir::new().expect("tempdir");
        let path = temp.path().join("nudb.key");
        let header = NuDbKeyFileHeader {
            version: NUDB_CURRENT_VERSION,
            uid: 1,
            appnum: NUDB_APPNUM,
            key_size: 32,
            salt: 2,
            pepper: nudb_pepper(2),
            block_size: 4096,
            load_factor: nudb_encode_load_factor(0.5).expect("load factor"),
            capacity: nudb_bucket_capacity(4096),
            buckets: 0,
            modulus: 1,
        };
        fs::write(&path, encode_nudb_key_file_header(&header).expect("encode"))
            .expect("write zero-bucket header");

        let read = read_nudb_key_file_header(&path).expect("zero-bucket initial header");
        assert_eq!(read.buckets, 0);
        assert_eq!(read.modulus, 1);
    }

    #[test]
    fn nudb_key_header_rejects_wrong_type_and_invalid_pepper() {
        let temp = TempDir::new().expect("tempdir");
        let path = temp.path().join("nudb.key");
        let mut bytes = vec![0u8; 4096];
        bytes[..8].copy_from_slice(b"badb.key");
        fs::write(&path, &bytes).expect("write wrong type");
        assert_eq!(
            read_nudb_key_file_header(&path).expect_err("wrong type"),
            "NuDB key file type tag mismatch"
        );

        let header = NuDbKeyFileHeader {
            version: NUDB_CURRENT_VERSION,
            uid: 1,
            appnum: NUDB_APPNUM,
            key_size: 32,
            salt: 2,
            pepper: 999,
            block_size: 4096,
            load_factor: nudb_encode_load_factor(0.5).expect("load factor"),
            capacity: nudb_bucket_capacity(4096),
            buckets: 0,
            modulus: 1,
        };
        fs::write(&path, encode_nudb_key_file_header(&header).expect("encode"))
            .expect("write invalid pepper");
        assert_eq!(
            read_nudb_key_file_header(&path).expect_err("invalid pepper"),
            "Invalid NuDB key header pepper"
        );
    }

    #[test]
    fn nudb_block_size_validation_bounds() {
        validate_nudb_block_size(4096).expect("min");
        validate_nudb_block_size(32768).expect("max");
        assert_eq!(NUDB_TARGET_LOAD_FACTOR, 0.50);
    }
}
