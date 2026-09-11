//! Tests for the get counts RPC handler.

use std::collections::BTreeMap;

use basics::counted_object::CountedObject;
use protocol::JsonValue;
use rpc::{GetCountsSource, do_get_counts, get_counts_json, read_min_count};

#[derive(Debug)]
struct FakeGetCountsSource {
    use_tx_tables: bool,
    db_kb_total: u64,
    db_kb_ledger: u64,
    db_kb_transaction: u64,
    local_tx_count: usize,
    write_load: JsonValue,
    historical_perminute: i64,
    sle_hit_rate: JsonValue,
    ledger_hit_rate: JsonValue,
    accepted_ledger_cache_size: u64,
    accepted_ledger_cache_hit_rate: JsonValue,
    fullbelow_size: i64,
    treenode_cache_size: u64,
    treenode_cache_capacity_entries: u64,
    treenode_track_size: u64,
    node_store_counts: BTreeMap<String, JsonValue>,
}

impl GetCountsSource for FakeGetCountsSource {
    fn use_tx_tables(&self) -> bool {
        self.use_tx_tables
    }

    fn db_kb_total(&self) -> u64 {
        self.db_kb_total
    }

    fn db_kb_ledger(&self) -> u64 {
        self.db_kb_ledger
    }

    fn db_kb_transaction(&self) -> u64 {
        self.db_kb_transaction
    }

    fn local_tx_count(&self) -> usize {
        self.local_tx_count
    }

    fn write_load(&self) -> JsonValue {
        self.write_load.clone()
    }

    fn historical_perminute(&self) -> i64 {
        self.historical_perminute
    }

    fn sle_hit_rate(&self) -> JsonValue {
        self.sle_hit_rate.clone()
    }

    fn ledger_hit_rate(&self) -> JsonValue {
        self.ledger_hit_rate.clone()
    }

    fn accepted_ledger_cache_size(&self) -> u64 {
        self.accepted_ledger_cache_size
    }

    fn accepted_ledger_cache_hit_rate(&self) -> JsonValue {
        self.accepted_ledger_cache_hit_rate.clone()
    }

    fn fullbelow_size(&self) -> i64 {
        self.fullbelow_size
    }

    fn treenode_cache_size(&self) -> u64 {
        self.treenode_cache_size
    }

    fn treenode_cache_capacity_entries(&self) -> u64 {
        self.treenode_cache_capacity_entries
    }

    fn treenode_track_size(&self) -> u64 {
        self.treenode_track_size
    }

    fn add_node_store_counts(&self, json: &mut BTreeMap<String, JsonValue>) {
        json.extend(self.node_store_counts.clone());
    }
}

impl Default for FakeGetCountsSource {
    fn default() -> Self {
        Self {
            use_tx_tables: true,
            db_kb_total: 12,
            db_kb_ledger: 7,
            db_kb_transaction: 5,
            local_tx_count: 0,
            write_load: JsonValue::Unsigned(9),
            historical_perminute: 3,
            sle_hit_rate: JsonValue::Unsigned(50),
            ledger_hit_rate: JsonValue::Unsigned(75),
            accepted_ledger_cache_size: 4,
            accepted_ledger_cache_hit_rate: JsonValue::Unsigned(60),
            fullbelow_size: 2,
            treenode_cache_size: 11,
            treenode_cache_capacity_entries: 17,
            treenode_track_size: 13,
            node_store_counts: BTreeMap::from([(
                "node_reads_total".to_owned(),
                JsonValue::Unsigned(99),
            )]),
        }
    }
}

fn object(entries: impl IntoIterator<Item = (&'static str, JsonValue)>) -> JsonValue {
    JsonValue::Object(
        entries
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect::<BTreeMap<_, _>>(),
    )
}

#[test]
fn get_counts_defaults_min_count_to_ten() {
    let params = JsonValue::Object(Default::default());
    assert_eq!(read_min_count(&params), 10);

    let source = FakeGetCountsSource::default();
    let JsonValue::Object(result) = do_get_counts(&params, &source) else {
        panic!("response must be an object");
    };

    assert_eq!(result.get("dbKBTotal"), Some(&JsonValue::Unsigned(12)));
    assert_eq!(result.get("dbKBLedger"), Some(&JsonValue::Unsigned(7)));
    assert_eq!(result.get("dbKBTransaction"), Some(&JsonValue::Unsigned(5)));
    assert_eq!(result.get("write_load"), Some(&JsonValue::Unsigned(9)));
    assert_eq!(
        result.get("historical_perminute"),
        Some(&JsonValue::Signed(3))
    );
    assert_eq!(result.get("SLE_hit_rate"), Some(&JsonValue::Unsigned(50)));
    assert_eq!(
        result.get("ledger_hit_rate"),
        Some(&JsonValue::Unsigned(75))
    );
    assert_eq!(result.get("AL_size"), Some(&JsonValue::Unsigned(4)));
    assert_eq!(result.get("AL_hit_rate"), Some(&JsonValue::Unsigned(60)));
    assert_eq!(result.get("fullbelow_size"), Some(&JsonValue::Signed(2)));
    assert_eq!(
        result.get("treenode_cache_size"),
        Some(&JsonValue::Unsigned(11))
    );
    assert_eq!(
        result.get("treenode_cache_capacity_entries"),
        Some(&JsonValue::Unsigned(17))
    );
    assert_eq!(
        result.get("treenode_track_size"),
        Some(&JsonValue::Unsigned(13))
    );
    assert_eq!(
        result.get("node_reads_total"),
        Some(&JsonValue::Unsigned(99))
    );
    assert!(matches!(result.get("uptime"), Some(JsonValue::String(_))));
    assert!(!result.contains_key("local_txs"));
}

#[test]
fn get_counts_uses_explicit_min_count() {
    let params = object([("min_count", JsonValue::Unsigned(27))]);
    assert_eq!(read_min_count(&params), 27);

    let source = FakeGetCountsSource::default();
    let JsonValue::Object(result) = do_get_counts(&params, &source) else {
        panic!("response must be an object");
    };

    assert_eq!(result.get("write_load"), Some(&JsonValue::Unsigned(9)));
}

#[test]
fn get_counts_ignores_non_object_params_handler_boundary() {
    let params = JsonValue::Array(vec![JsonValue::Unsigned(99)]);
    assert_eq!(read_min_count(&params), 10);
}

#[test]
fn get_counts_includes_counted_objects_above_threshold() {
    #[derive(Debug)]
    struct CountedMarker;

    let _guards = [
        CountedObject::<CountedMarker>::new_named("CppParityCountedA"),
        CountedObject::<CountedMarker>::new_named("CppParityCountedA"),
    ];

    let source = FakeGetCountsSource::default();
    let JsonValue::Object(result) = get_counts_json(&source, 2) else {
        panic!("response must be an object");
    };

    assert_eq!(result.get("CppParityCountedA"), Some(&JsonValue::Signed(2)));
}

#[test]
fn get_counts_omits_tx_table_fields_when_disabled() {
    let source = FakeGetCountsSource {
        use_tx_tables: false,
        local_tx_count: 5,
        ..Default::default()
    };

    let JsonValue::Object(result) = get_counts_json(&source, 10) else {
        panic!("response must be an object");
    };

    assert!(!result.contains_key("dbKBTotal"));
    assert!(!result.contains_key("dbKBLedger"));
    assert!(!result.contains_key("dbKBTransaction"));
    assert!(!result.contains_key("local_txs"));
}

#[test]
fn get_counts_response_includes_all_fields() {
    let source = FakeGetCountsSource::default();
    let params = object([("min_count", JsonValue::Unsigned(1))]);

    let result = do_get_counts(&params, &source);
    let JsonValue::Object(result) = result else {
        panic!("result must be an object");
    };

    // Should have db sizes
    assert_eq!(result.get("dbKBTotal"), Some(&JsonValue::Unsigned(12)));
    assert_eq!(result.get("dbKBLedger"), Some(&JsonValue::Unsigned(7)));
    assert_eq!(result.get("dbKBTransaction"), Some(&JsonValue::Unsigned(5)));

    // Should have write_load
    assert_eq!(result.get("write_load"), Some(&JsonValue::Unsigned(9)));

    // Should have historical_perminute
    assert_eq!(
        result.get("historical_perminute"),
        Some(&JsonValue::Signed(3))
    );

    // Should have cache info
    assert_eq!(result.get("SLE_hit_rate"), Some(&JsonValue::Unsigned(50)));
    assert_eq!(
        result.get("ledger_hit_rate"),
        Some(&JsonValue::Unsigned(75))
    );
    assert_eq!(result.get("AL_size"), Some(&JsonValue::Unsigned(4)));
    assert_eq!(result.get("AL_hit_rate"), Some(&JsonValue::Unsigned(60)));
    assert_eq!(result.get("fullbelow_size"), Some(&JsonValue::Signed(2)));
    assert_eq!(
        result.get("treenode_cache_size"),
        Some(&JsonValue::Unsigned(11))
    );
    assert_eq!(
        result.get("treenode_cache_capacity_entries"),
        Some(&JsonValue::Unsigned(17))
    );
    assert_eq!(
        result.get("treenode_track_size"),
        Some(&JsonValue::Unsigned(13))
    );

    // Should have node store counts
    assert_eq!(
        result.get("node_reads_total"),
        Some(&JsonValue::Unsigned(99))
    );
}

#[test]
fn get_counts_omits_tx_fields_when_disabled() {
    let source = FakeGetCountsSource {
        use_tx_tables: false,
        ..Default::default()
    };
    let params = object([]);

    let result = do_get_counts(&params, &source);
    let JsonValue::Object(result) = result else {
        panic!("result must be an object");
    };

    assert!(!result.contains_key("dbKBTransaction"));
}

#[test]
fn get_counts_includes_local_txs_when_nonzero() {
    let source = FakeGetCountsSource {
        local_tx_count: 7,
        ..Default::default()
    };
    let params = object([]);

    let result = do_get_counts(&params, &source);
    let JsonValue::Object(result) = result else {
        panic!("result must be an object");
    };

    assert_eq!(result.get("local_txs"), Some(&JsonValue::Unsigned(7)));
}

#[test]
fn read_min_count_parses_various_inputs() {
    assert_eq!(read_min_count(&object([])), 10);
    assert_eq!(
        read_min_count(&object([("min_count", JsonValue::Unsigned(5))])),
        5
    );
    assert_eq!(
        read_min_count(&object([("min_count", JsonValue::Unsigned(100))])),
        100
    );
    // Non-numeric should default to 10
    assert_eq!(
        read_min_count(&object([(
            "min_count",
            JsonValue::String("abc".to_owned())
        )])),
        10
    );
}
