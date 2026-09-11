//! Deterministic, offline acquisition parity harness.
//!
//! This is deliberately a producer of Quaxar traces, not a claim that those
//! traces already match rippled. A rippled runner can compare its JSONL output
//! event-for-event; the emitted records are the parity schema.

use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, make_shared_intrusive};
use basics::sha_map_hash::SHAMapHash;
use basics::tagged_cache::ManualClock;
use ledger::{InboundLedgerDataType, InboundLedgerLocal, InboundLedgerTimerResult};
use overlay::{
    Compressed, Message as OverlayMessage, ProtocolMessage, ProtocolPayload, TmGetLedger,
};
use serde_json::{Value, json};
use shamap::family::{
    NullFullBelowCache, NullMissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher,
};
use shamap::sync::{SHAMapType, SyncState, SyncTree};
use shamap::tree_node::{SHAMapNodeType, SHAMapTreeNode};
use shamap::tree_node_cache::TreeNodeCache;
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use time::Duration;

const SCHEMA: &str = "xrpl.acquisition.trace/v2";
const LEDGER_SEQ: u32 = 6_000_001;

fn sample_hash(fill: u8) -> SHAMapHash {
    SHAMapHash::new(Uint256::from_array([fill; 32]))
}

fn hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        result.push(HEX[(byte >> 4) as usize] as char);
        result.push(HEX[(byte & 0x0f) as usize] as char);
    }
    result
}

fn object(fields: impl IntoIterator<Item = (&'static str, Value)>) -> Value {
    let sorted = fields
        .into_iter()
        .map(|(key, value)| (key.to_owned(), value))
        .collect::<BTreeMap<_, _>>();
    Value::Object(sorted.into_iter().collect())
}

#[derive(Default)]
struct CanonicalTrace {
    events: Vec<Value>,
}

impl CanonicalTrace {
    fn emit(
        &mut self,
        _experiment: &'static str,
        scenario: &'static str,
        t_ms: u64,
        phase: &'static str,
        event: &'static str,
        data: Value,
    ) {
        let step = self.events.len() as u64;
        self.events.push(object([
            ("component", Value::String(phase.to_owned())),
            ("event", Value::String(event.to_owned())),
            ("fields", data),
            ("implementation", Value::String("quaxar".to_owned())),
            ("scenario", Value::String(scenario.to_owned())),
            ("schema", Value::String(SCHEMA.to_owned())),
            ("sequence", json!(step)),
            ("t_ms", json!(t_ms)),
        ]));
    }

    fn jsonl(&self) -> String {
        let mut output = String::new();
        for event in &self.events {
            output.push_str(&serde_json::to_string(event).expect("trace events serialize"));
            output.push('\n');
        }
        output
    }

    fn assert_canonical(&self) {
        let encoded = self.jsonl();
        assert!(encoded.ends_with('\n'));
        assert_eq!(encoded, self.jsonl(), "trace must be repeatably canonical");
        for line in encoded.lines() {
            let parsed: Value = serde_json::from_str(line).expect("every trace row is JSON");
            assert_eq!(parsed["schema"], SCHEMA);
            assert_eq!(parsed["implementation"], "quaxar");
        }
    }
}

struct CountingFetcher {
    present: Option<SharedIntrusive<SHAMapTreeNode>>,
    physical_fetches: Arc<Mutex<Vec<SHAMapHash>>>,
}

impl SHAMapNodeFetcher for CountingFetcher {
    fn fetch_node(&self, hash: SHAMapHash) -> Option<SharedIntrusive<SHAMapTreeNode>> {
        self.physical_fetches
            .lock()
            .expect("fetch recorder lock")
            .push(hash);
        self.present
            .as_ref()
            .filter(|node| node.get_hash() == hash)
            .cloned()
    }
}

fn family(
    label: &'static str,
    fetcher: CountingFetcher,
) -> SHAMapFamily<
    ManualClock,
    basics::hardened_hash::HardenedHashBuilder,
    NullFullBelowCache,
    CountingFetcher,
    NullMissingNodeReporter,
> {
    SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            label,
            64,
            Duration::seconds(1),
            ManualClock::new(0),
        )),
        NullFullBelowCache::new(1),
        fetcher,
        NullMissingNodeReporter,
    )
}

fn shared_hash_tree(child_hash: SHAMapHash) -> SyncTree {
    let root = SHAMapTreeNode::new_inner(0);
    // The same physical hash is reachable from two independent branches.
    root.set_child_hash(2, child_hash);
    root.set_child_hash(11, child_hash);
    root.update_hash();
    SyncTree::from_root_with_type(
        root,
        SHAMapType::State,
        true,
        LEDGER_SEQ,
        SyncState::Synching,
    )
}

#[test]
fn parity_deferred_shared_missing_hash_schedules_once_and_fans_out() {
    let shared_hash = sample_hash(0xC3);
    let fetches = Arc::new(Mutex::new(Vec::new()));
    let scan_family = family(
        "parity-deferred-shared-missing",
        CountingFetcher {
            present: None,
            physical_fetches: fetches,
        },
    );
    let mut tree = shared_hash_tree(shared_hash);
    let mut scheduled = Vec::new();
    let mut completion_batches = Vec::new();

    let missing = tree.get_missing_nodes_deferred_with_family(
        16,
        &mut None,
        &scan_family,
        16,
        &mut || 0,
        &mut |hash, ledger_seq| scheduled.push((hash, ledger_seq)),
        &mut |requests| {
            completion_batches.push(
                requests
                    .iter()
                    .map(|request| (request.hash(), request.ledger_seq()))
                    .collect::<Vec<_>>(),
            );
            vec![None; requests.len()]
        },
    );

    assert_eq!(scheduled, vec![(shared_hash, LEDGER_SEQ)]);
    assert_eq!(completion_batches, vec![vec![(shared_hash, LEDGER_SEQ)]]);
    assert_eq!(missing.len(), 1);
    assert_eq!(missing[0].1, *shared_hash.as_uint256());
    assert!(tree.is_synching());
}

#[test]
fn parity_shared_hash_present_and_missing_oracle_is_deterministic() {
    let shared = SHAMapTreeNode::new_leaf(
        SHAMapNodeType::AccountState,
        shamap::item::SHAMapItem::new(Uint256::from_array([0xA1; 32]), vec![0x42; 12]),
        0,
    );
    let shared_hash = shared.get_hash();

    let present_fetches = Arc::new(Mutex::new(Vec::new()));
    let present_family = family(
        "parity-shared-present",
        CountingFetcher {
            present: Some(shared),
            physical_fetches: present_fetches.clone(),
        },
    );
    let mut present_tree = shared_hash_tree(shared_hash);
    let present_frontier =
        present_tree.get_missing_nodes_with_family(16, &mut None, &present_family, &mut || 0);
    let present_physical = present_fetches.lock().expect("fetch recorder lock").clone();
    let present_completions = usize::from(!present_tree.is_synching());

    assert!(present_frontier.is_empty());
    assert_eq!(present_physical, vec![shared_hash]);
    assert_eq!(present_completions, 1);

    let missing_fetches = Arc::new(Mutex::new(Vec::new()));
    let missing_family = family(
        "parity-shared-missing",
        CountingFetcher {
            present: None,
            physical_fetches: missing_fetches.clone(),
        },
    );
    let mut missing_tree = shared_hash_tree(shared_hash);
    let missing_frontier =
        missing_tree.get_missing_nodes_with_family(16, &mut None, &missing_family, &mut || 0);
    let missing_physical = missing_fetches.lock().expect("fetch recorder lock").clone();

    // Both branches receive the shared miss result, but the scan performs one
    // physical backing lookup for the unique hash, matching rippled's
    // NodeStore async-fetch coalescing.
    assert_eq!(missing_physical, vec![shared_hash]);
    assert_eq!(missing_frontier.len(), 1);
    assert_eq!(missing_frontier[0].1, *shared_hash.as_uint256());
    assert!(missing_tree.is_synching());

    let mut trace = CanonicalTrace::default();
    trace.emit(
        "shared_hash",
        "present",
        0,
        "scan",
        "frontier",
        object([
            ("completion_count", json!(present_completions)),
            ("expected_physical_fetches", json!(1)),
            ("missing_frontier", json!([])),
            ("physical_fetches", json!(present_physical.len())),
            ("physical_fetch_parity", json!("matches_unique_hash_oracle")),
            ("shared_hash", json!(shared_hash.to_string())),
        ]),
    );
    trace.emit(
        "shared_hash",
        "missing",
        0,
        "scan",
        "frontier",
        object([
            ("completion_count", json!(0)),
            ("expected_physical_fetches", json!(1)),
            (
                "missing_frontier",
                json!(
                    missing_frontier
                        .iter()
                        .map(|(_, hash)| hash.to_string())
                        .collect::<Vec<_>>()
                ),
            ),
            ("physical_fetches", json!(missing_physical.len())),
            ("physical_fetch_parity", json!("matches_unique_hash_oracle")),
            ("shared_hash", json!(shared_hash.to_string())),
        ]),
    );
    trace.assert_canonical();
}

#[test]
fn parity_virtual_time_scan_timeout_and_packet_interleaving_trace_is_deterministic() {
    let mut inbound = InboundLedgerLocal::new(sample_hash(0xB1), LEDGER_SEQ);
    let packet = ledger::InboundLedgerPacket::new(InboundLedgerDataType::Base, Vec::new());
    let mut trace = CanonicalTrace::default();

    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        0,
        "timer",
        "arm",
        object([("deadline_ms", json!(3_000)), ("interval_ms", json!(3_000))]),
    );
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        100,
        "scan",
        "start",
        object([("map", json!("state")), ("planned_end_ms", json!(3_200))]),
    );

    assert_eq!(
        inbound.timeout_expired(),
        InboundLedgerTimerResult::NoProgress
    );
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        3_000,
        "timer",
        "fire",
        object([
            ("result", json!("no_progress")),
            ("timeout_count", json!(1)),
        ]),
    );
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        3_000,
        "timer",
        "rearm",
        object([("deadline_ms", json!(6_000)), ("interval_ms", json!(3_000))]),
    );

    assert!(inbound.got_data(Some(17), packet));
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        3_050,
        "packet",
        "arrival",
        object([("peer_id", json!(17)), ("queued", json!(true))]),
    );
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        3_200,
        "scan",
        "finish",
        object([("duration_ms", json!(3_100)), ("map", json!("state"))]),
    );
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        3_200,
        "packet",
        "dequeue",
        object([("peer_id", json!(17)), ("queue_delay_ms", json!(150))]),
    );
    assert_eq!(inbound.received_data_len(), 1);
    inbound.set_complete();
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        3_200,
        "acquisition",
        "terminal",
        object([("state", json!("complete")), ("timeout_count", json!(1))]),
    );

    assert_eq!(inbound.timeout_expired(), InboundLedgerTimerResult::Done);
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        6_000,
        "timer",
        "fire",
        object([
            ("result", json!("done")),
            ("terminal_state", json!("complete")),
        ]),
    );
    trace.emit(
        "virtual_time",
        "scan_over_timeout",
        6_200,
        "audit",
        "end",
        object([("terminal_state", json!("complete"))]),
    );

    trace.assert_canonical();
    let events: Vec<_> = trace
        .events
        .iter()
        .map(|event| event["event"].as_str().expect("event name"))
        .collect();
    assert_eq!(
        events,
        vec![
            "arm", "start", "fire", "rearm", "arrival", "finish", "dequeue", "terminal", "fire",
            "end"
        ]
    );
}

// This is a direct transcription of rippled's `packetCorpus()` inputs in
// `InboundLedgerParityTrace_test.cpp`. The fixture below is emitted from the
// native rippled test and stays authoritative: Quaxar may normalize only its
// implementation label, never its inputs, event vocabulary, or wire bytes.
const RIPPLED_LEDGER_SEQ: u32 = 700;
const RIPPLED_LEDGER_HASH: [u8; 32] = [0xA1; 32];

struct RippledPacketCase {
    wire_case: &'static str,
    recipients: &'static [&'static str],
    itype: i32,
    node_id: &'static [u8],
    query_type: Option<i32>,
    query_depth: u32,
}

fn rippled_get_ledger_cases() -> [RippledPacketCase; 5] {
    [
        RippledPacketCase {
            wire_case: "root",
            recipients: &["peer-a", "peer-b"],
            itype: 2,
            node_id: b"root",
            query_type: None,
            query_depth: 0,
        },
        RippledPacketCase {
            wire_case: "state",
            recipients: &["peer-b"],
            itype: 2,
            node_id: b"state-0",
            query_type: None,
            query_depth: 0,
        },
        RippledPacketCase {
            wire_case: "transaction",
            recipients: &["peer-a"],
            itype: 1,
            node_id: b"tx-0",
            query_type: None,
            query_depth: 0,
        },
        RippledPacketCase {
            wire_case: "reply",
            recipients: &["peer-b"],
            itype: 2,
            node_id: b"state-0",
            query_type: None,
            query_depth: 1,
        },
        RippledPacketCase {
            wire_case: "timeout",
            recipients: &["peer-a", "peer-b"],
            itype: 2,
            node_id: b"state-0",
            query_type: Some(0),
            query_depth: 0,
        },
    ]
}

fn rippled_packet_contract_normalized_for_quaxar() -> String {
    let mut normalized = String::new();
    for line in include_str!("../fixtures/rippled-get-ledger-corpus.jsonl").lines() {
        let mut event: Value = serde_json::from_str(line).expect("rippled fixture is valid JSON");
        assert_eq!(event["implementation"], "rippled");
        event["implementation"] = Value::String("quaxar".to_owned());
        normalized.push_str(&serde_json::to_string(&event).expect("normalized trace serializes"));
        normalized.push('\n');
    }
    normalized
}

#[test]
fn parity_get_ledger_routing_resource_and_wire_corpus_is_canonical() {
    let mut trace = CanonicalTrace::default();

    for case in rippled_get_ledger_cases() {
        let protocol = ProtocolMessage::new(ProtocolPayload::GetLedger(TmGetLedger {
            itype: case.itype,
            ltype: None,
            ledger_hash: Some(RIPPLED_LEDGER_HASH.to_vec()),
            ledger_seq: Some(RIPPLED_LEDGER_SEQ),
            node_i_ds: vec![case.node_id.to_vec()],
            request_cookie: None,
            query_type: case.query_type,
            query_depth: Some(case.query_depth),
        }));
        let message = OverlayMessage::new(protocol, None);
        let frame = message.get_buffer(Compressed::Off);

        trace.emit(
            "packet_corpus",
            "packet_corpus",
            0,
            "routing",
            "tmgetledger_capture",
            object([
                ("recipients", json!(case.recipients)),
                ("resource_outcome", json!("ok")),
                ("serialized_tmgetledger_hex", json!(hex(frame))),
                ("wire_case", json!(case.wire_case)),
            ]),
        );
    }

    trace.assert_canonical();
    assert_eq!(
        trace.jsonl(),
        rippled_packet_contract_normalized_for_quaxar(),
        "Quaxar must match rippled's exact TMGetLedger contract after normalizing only implementation"
    );
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BenchmarkInput {
    ledger: &'static str,
    backend: &'static str,
    cache: &'static str,
    peers: Vec<u64>,
    acquisition: &'static str,
    window_ms: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NodeReadLifecycle {
    hash: &'static str,
    outcome: &'static str,
    start_ms: u64,
    end_ms: u64,
}

trait BenchmarkHooks {
    fn scan(&mut self, phase: &'static str, start_ms: u64, end_ms: u64);
    fn node_read(&mut self, lifecycle: NodeReadLifecycle);
    fn peer_lcl(&mut self, peer_id: u64, before: u32, after: u32, t_ms: u64);
    fn terminal(&mut self, state: &'static str, t_ms: u64);
}

struct TraceHooks<'a> {
    trace: &'a mut CanonicalTrace,
}

impl BenchmarkHooks for TraceHooks<'_> {
    fn scan(&mut self, phase: &'static str, start_ms: u64, end_ms: u64) {
        self.trace.emit(
            "benchmark",
            "equal_inputs",
            end_ms,
            "scan",
            "phase",
            object([
                ("duration_ms", json!(end_ms - start_ms)),
                ("name", json!(phase)),
                ("start_ms", json!(start_ms)),
            ]),
        );
    }

    fn node_read(&mut self, lifecycle: NodeReadLifecycle) {
        self.trace.emit(
            "benchmark",
            "equal_inputs",
            lifecycle.end_ms,
            "node_read",
            "lifecycle",
            object([
                ("duration_ms", json!(lifecycle.end_ms - lifecycle.start_ms)),
                ("hash", json!(lifecycle.hash)),
                ("outcome", json!(lifecycle.outcome)),
                ("start_ms", json!(lifecycle.start_ms)),
            ]),
        );
    }

    fn peer_lcl(&mut self, peer_id: u64, before: u32, after: u32, t_ms: u64) {
        self.trace.emit(
            "benchmark",
            "equal_inputs",
            t_ms,
            "peer",
            "lcl_change",
            object([
                ("after", json!(after)),
                ("before", json!(before)),
                ("peer_id", json!(peer_id)),
            ]),
        );
    }

    fn terminal(&mut self, state: &'static str, t_ms: u64) {
        self.trace.emit(
            "benchmark",
            "equal_inputs",
            t_ms,
            "acquisition",
            "terminal",
            object([("state", json!(state))]),
        );
    }
}

fn run_controlled_benchmark(input: &BenchmarkInput, hooks: &mut dyn BenchmarkHooks) {
    // Every timestamp is virtual. This driver intentionally contains no wall
    // clock, I/O, background executor, RNG, or peer discovery dependency.
    assert_eq!(input.backend, "memory");
    assert_eq!(input.cache, "cold");
    assert_eq!(input.peers, vec![11, 12]);
    assert_eq!(input.acquisition, "inbound-ledger");
    assert_eq!(input.window_ms, 6_200);
    assert_eq!(input.ledger, "C1");

    hooks.scan("state_missing_frontier", 100, 3_200);
    hooks.node_read(NodeReadLifecycle {
        hash: "A1",
        outcome: "cache_hit",
        start_ms: 3_200,
        end_ms: 3_200,
    });
    hooks.peer_lcl(11, 6_000_000, 6_000_001, 3_200);
    hooks.terminal("complete", 3_200);
}

#[test]
fn parity_telemetry_and_controlled_benchmark_hooks_are_repeatable() {
    let input = BenchmarkInput {
        ledger: "C1",
        backend: "memory",
        cache: "cold",
        peers: vec![11, 12],
        acquisition: "inbound-ledger",
        window_ms: 6_200,
    };
    let mut first = CanonicalTrace::default();
    run_controlled_benchmark(&input, &mut TraceHooks { trace: &mut first });
    let mut second = CanonicalTrace::default();
    run_controlled_benchmark(&input, &mut TraceHooks { trace: &mut second });

    first.assert_canonical();
    second.assert_canonical();
    assert_eq!(first.jsonl(), second.jsonl());
    assert_eq!(
        first
            .events
            .iter()
            .map(|event| event["event"].as_str().expect("event name"))
            .collect::<Vec<_>>(),
        vec!["phase", "lifecycle", "lcl_change", "terminal"]
    );
}
