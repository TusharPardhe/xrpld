use basics::{base_uint::Uint256, basic_config::Section};
use nodestore::{DummyScheduler, Manager, ManagerImp, NodeObject, NodeObjectType, NullJournal};
use protocol::JsonValue;
use std::sync::Arc;

fn memory_section(path: &str) -> Section {
    let mut section = Section::new("node_db");
    section.set("type", "Memory");
    section.set("path", path);
    section
}

fn sample_object(fill: u8) -> NodeObject {
    NodeObject::new(
        NodeObjectType::Ledger,
        vec![fill, fill + 1],
        Uint256::from_array([fill; 32]),
    )
}

#[test]
fn database_counts_json_reports_expected_node_store_fields() {
    let manager = ManagerImp::new();
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal: Arc<dyn nodestore::NodeStoreJournal> = Arc::new(NullJournal);
    let config = memory_section("counts");
    let database = manager
        .make_database(0, Arc::clone(&scheduler), 1, &config, Arc::clone(&journal))
        .expect("database");

    let object = sample_object(0x11);
    database.store(
        object.object_type(),
        object.data().clone(),
        *object.hash(),
        1,
    );
    let fetched = database
        .fetch_node_object(object.hash(), 1, nodestore::FetchType::Synchronous, false)
        .expect("stored object");
    assert_eq!(fetched.data(), object.data());

    let JsonValue::Object(counts) = database.get_counts_json() else {
        panic!("counts json should be an object");
    };
    let expected_keys = [
        "node_object_cache_capacity_bytes",
        "node_object_cache_capacity_bytes_is_estimate",
        "node_object_cache_capacity_entries",
        "node_object_cache_durable_loads",
        "node_object_cache_entries",
        "node_object_cache_eviction_policy",
        "node_object_cache_hits",
        "node_object_cache_idle_seconds",
        "node_object_cache_invalidations",
        "node_object_cache_misses",
        "node_object_cache_oversized",
        "node_object_cache_promotions",
        "node_object_cache_rejected",
        "node_object_cache_ttl_seconds",
        "node_object_cache_weighted_capacity_bytes",
        "node_object_cache_weighted_size_bytes",
        "node_read_bytes",
        "node_reads_duration_us",
        "node_reads_hit",
        "node_reads_total",
        "node_writes",
        "node_written_bytes",
        "read_queue",
        "read_request_bundle",
        "read_threads_running",
        "read_threads_total",
    ];
    assert_eq!(
        counts.keys().map(String::as_str).collect::<Vec<_>>(),
        expected_keys
    );
    assert_eq!(
        counts.get("read_request_bundle"),
        Some(&JsonValue::Signed(4))
    );
    assert!(matches!(
        counts.get("read_threads_total"),
        Some(JsonValue::Signed(value)) if *value >= 1
    ));
    assert!(matches!(
        counts.get("read_threads_running"),
        Some(JsonValue::Signed(value)) if *value >= 0
    ));
    assert!(matches!(counts.get("node_writes"), Some(JsonValue::String(value)) if value == "1"));
    assert!(matches!(
        counts.get("node_reads_total"),
        Some(JsonValue::String(value)) if value.parse::<u64>().expect("integer string") >= 1
    ));
}

#[test]
fn rotating_database_counts_json_reports_the_same_public_fields() {
    let manager = ManagerImp::new();
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal: Arc<dyn nodestore::NodeStoreJournal> = Arc::new(NullJournal);
    let writable = memory_section("rotating-writable");
    let archive = memory_section("rotating-archive");
    let database = manager
        .make_rotating_database(
            0,
            Arc::clone(&scheduler),
            1,
            &writable,
            &archive,
            &writable,
            journal,
        )
        .expect("rotating database");

    let object = sample_object(0x22);
    database.store(
        object.object_type(),
        object.data().clone(),
        *object.hash(),
        1,
    );

    let JsonValue::Object(counts) = database.get_counts_json() else {
        panic!("counts json should be an object");
    };
    assert_eq!(counts.len(), 26);
    assert_eq!(
        counts.get("node_object_cache_eviction_policy"),
        Some(&JsonValue::String("disabled".to_owned()))
    );
    for key in [
        "node_object_cache_capacity_entries",
        "node_object_cache_capacity_bytes",
        "node_object_cache_weighted_capacity_bytes",
        "node_object_cache_weighted_size_bytes",
        "node_object_cache_entries",
        "node_object_cache_hits",
        "node_object_cache_promotions",
    ] {
        assert_eq!(
            counts.get(key),
            Some(&JsonValue::String("0".to_owned())),
            "{key}"
        );
    }
    assert_eq!(
        counts.get("node_object_cache_capacity_bytes_is_estimate"),
        Some(&JsonValue::Bool(false))
    );
    assert!(matches!(
        counts.get("read_request_bundle"),
        Some(JsonValue::Signed(4))
    ));
    assert!(matches!(
        counts.get("read_threads_total"),
        Some(JsonValue::Signed(value)) if *value >= 1
    ));
    assert!(matches!(
        counts.get("node_writes"),
        Some(JsonValue::String(value)) if value == "1"
    ));
    assert_eq!(database.fd_required(), 0);

    database.stop();
}
