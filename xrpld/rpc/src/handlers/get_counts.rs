//! Narrow `get_counts` RPC handler port.
//!
//! This keeps the reference control flow shape:
//! - read `min_count` from already-parsed params,
//! - read counted-object entries from the real global registry,
//! - format uptime with the same descending unit order,
//! - and delegate app-owned metrics through an explicit source seam.

use std::collections::BTreeMap;
use std::time::Duration;

use basics::counted_object::CountedObjects;
use basics::memory::malloc_trim::jemalloc_stats;
use basics::uptime_clock::{UptimeClock, UptimeTimePoint};
use protocol::JsonValue;

const DEFAULT_MIN_COUNT: u32 = 10;

pub trait GetCountsSource {
    fn use_tx_tables(&self) -> bool;

    fn db_kb_total(&self) -> u64;

    fn db_kb_ledger(&self) -> u64;

    fn db_kb_transaction(&self) -> u64;

    fn local_tx_count(&self) -> usize;

    fn write_load(&self) -> JsonValue;

    fn historical_perminute(&self) -> i64;

    fn sle_hit_rate(&self) -> JsonValue;

    fn ledger_hit_rate(&self) -> JsonValue;

    fn accepted_ledger_cache_size(&self) -> u64;

    fn accepted_ledger_cache_hit_rate(&self) -> JsonValue;

    fn fullbelow_size(&self) -> i64;

    fn treenode_cache_size(&self) -> u64;

    fn treenode_track_size(&self) -> u64;

    fn add_node_store_counts(&self, json: &mut BTreeMap<String, JsonValue>);
}

pub fn read_min_count(params: &JsonValue) -> u32 {
    let JsonValue::Object(object) = params else {
        return DEFAULT_MIN_COUNT;
    };

    let Some(value) = object.get("min_count") else {
        return DEFAULT_MIN_COUNT;
    };

    match value {
        JsonValue::Unsigned(value) => u32::try_from(*value).unwrap_or(DEFAULT_MIN_COUNT),
        JsonValue::Signed(value) if *value >= 0 => {
            u32::try_from(*value as u64).unwrap_or(DEFAULT_MIN_COUNT)
        }
        _ => DEFAULT_MIN_COUNT,
    }
}

fn append_uptime_component(
    text: &mut String,
    remaining: &mut UptimeTimePoint,
    unit_name: &str,
    unit_duration: Duration,
) {
    let count = remaining.time_since_epoch().as_secs() / unit_duration.as_secs();
    if count == 0 {
        return;
    }

    *remaining = *remaining - Duration::from_secs(count * unit_duration.as_secs());
    if !text.is_empty() {
        text.push_str(", ");
    }
    text.push_str(&count.to_string());
    text.push(' ');
    text.push_str(unit_name);
    if count > 1 {
        text.push('s');
    }
}

fn format_uptime(now: UptimeTimePoint) -> String {
    let mut text = String::new();
    let mut remaining = now;

    append_uptime_component(
        &mut text,
        &mut remaining,
        "year",
        Duration::from_secs(365 * 24 * 60 * 60),
    );
    append_uptime_component(
        &mut text,
        &mut remaining,
        "day",
        Duration::from_secs(24 * 60 * 60),
    );
    append_uptime_component(
        &mut text,
        &mut remaining,
        "hour",
        Duration::from_secs(60 * 60),
    );
    append_uptime_component(&mut text, &mut remaining, "minute", Duration::from_secs(60));
    append_uptime_component(&mut text, &mut remaining, "second", Duration::from_secs(1));

    text
}

pub fn get_counts_json<S: GetCountsSource>(source: &S, min_count: u32) -> JsonValue {
    let mut result = BTreeMap::new();

    for (name, count) in CountedObjects::get_instance().get_counts(min_count as i32) {
        result.insert(name, JsonValue::Signed(i64::from(count)));
    }

    if source.use_tx_tables() {
        let db_kb_total = source.db_kb_total();
        if db_kb_total > 0 {
            result.insert("dbKBTotal".to_owned(), JsonValue::Unsigned(db_kb_total));
        }

        let db_kb_ledger = source.db_kb_ledger();
        if db_kb_ledger > 0 {
            result.insert("dbKBLedger".to_owned(), JsonValue::Unsigned(db_kb_ledger));
        }

        let db_kb_transaction = source.db_kb_transaction();
        if db_kb_transaction > 0 {
            result.insert(
                "dbKBTransaction".to_owned(),
                JsonValue::Unsigned(db_kb_transaction),
            );
        }

        let local_txs = source.local_tx_count();
        if local_txs > 0 {
            result.insert(
                "local_txs".to_owned(),
                JsonValue::Unsigned(local_txs as u64),
            );
        }
    }

    result.insert("write_load".to_owned(), source.write_load());
    result.insert(
        "historical_perminute".to_owned(),
        JsonValue::Signed(source.historical_perminute()),
    );
    result.insert("SLE_hit_rate".to_owned(), source.sle_hit_rate());
    result.insert("ledger_hit_rate".to_owned(), source.ledger_hit_rate());
    result.insert(
        "AL_size".to_owned(),
        JsonValue::Unsigned(source.accepted_ledger_cache_size()),
    );
    result.insert(
        "AL_hit_rate".to_owned(),
        source.accepted_ledger_cache_hit_rate(),
    );
    result.insert(
        "fullbelow_size".to_owned(),
        JsonValue::Signed(source.fullbelow_size()),
    );
    result.insert(
        "treenode_cache_size".to_owned(),
        JsonValue::Unsigned(source.treenode_cache_size()),
    );
    result.insert(
        "treenode_track_size".to_owned(),
        JsonValue::Unsigned(source.treenode_track_size()),
    );
    result.insert(
        "uptime".to_owned(),
        JsonValue::String(format_uptime(UptimeClock::now())),
    );

    if let Some(stats) = jemalloc_stats() {
        result.insert(
            "jemalloc_allocated_bytes".to_owned(),
            JsonValue::Unsigned(stats.allocated_bytes as u64),
        );
        result.insert(
            "jemalloc_active_bytes".to_owned(),
            JsonValue::Unsigned(stats.active_bytes as u64),
        );
        result.insert(
            "jemalloc_metadata_bytes".to_owned(),
            JsonValue::Unsigned(stats.metadata_bytes as u64),
        );
        result.insert(
            "jemalloc_mapped_bytes".to_owned(),
            JsonValue::Unsigned(stats.mapped_bytes as u64),
        );
        result.insert(
            "jemalloc_resident_bytes".to_owned(),
            JsonValue::Unsigned(stats.resident_bytes as u64),
        );
        result.insert(
            "jemalloc_retained_bytes".to_owned(),
            JsonValue::Unsigned(stats.retained_bytes as u64),
        );
        result.insert(
            "jemalloc_arenas".to_owned(),
            JsonValue::Unsigned(u64::from(stats.arenas)),
        );
    }

    source.add_node_store_counts(&mut result);

    JsonValue::Object(result)
}

pub fn do_get_counts<S: GetCountsSource>(params: &JsonValue, source: &S) -> JsonValue {
    get_counts_json(source, read_min_count(params))
}
