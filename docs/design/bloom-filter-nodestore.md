# Implementation Report: Node-Store Bloom Filters for Acquisition, Backfill, and Rotation

Status: Design / pre-implementation review
Scope: `xrpld/nodestore`, `xrpld/app/.../inbound_ledgers`, `xrpld/ledger/history_runtime`
Author context: grounded in a direct read of the current codebase (build 0.8.0).

---

## 1. Executive summary

A bloom filter is a small, in-RAM, probabilistic membership gate that answers
"is key K definitely absent?" with certainty, and "maybe present?" otherwise.
It never yields a false negative, so a "definitely absent" verdict is always
safe to act on.

In this node it is worth adding in exactly the places where the store is
probed with keys that are *expected to miss*, and where a miss is otherwise
paid for with real I/O or a redundant store probe:

1. Initial acquisition local-scan (miss-heavy by design).
2. History backfill (same local-scan pattern, older ledgers).
3. Rotating-store fetch fall-through during `online_delete` (writable then archive).

It is NOT worth adding to steady-state `account_info`/`tx` lookups: measured
miss rate on the live node is ~0.067% (`node_reads_total` 274,354,987 vs
`node_reads_hit` 274,171,772), and the NodeObject cache already absorbs most
reads. Bloom filters only accelerate misses.

This is a sync/catch-up latency and I/O optimization, not a steady-state query
speedup and not an RSS reduction.

---

## 2. How the relevant code works today (verified)

### 2.1 NuDB single-store lookup — `nudb_backend.rs`

`fetch(hash)` → `find_bucket_entry(key)`:
- `key_hash_prefix(key)` takes a prefix of the 256-bit key.
- `bucket_index(prefix, key_header)` is O(1): one bucket.
- `read_key_bucket(bucket_index)` (served from `bucket_cache` on hit).
- Walk sorted entries from `lower_bound(prefix)`; follow a short spill chain.
- On match: `read_data_record_value` from the data file.

A miss therefore costs ~1 bucket read (often cached) + in-memory compares.
There is no scan. A bloom filter saves that one bucket read on the miss path.

### 2.2 Store path — `nudb_backend.rs::store` / `store_batch_result`

`store()` already:
- computes `hash_prefix = key_hash_prefix(encoded.get_key())`,
- takes `store_mutex`,
- calls `find_bucket_entry(...)` and returns early if present.

This is the natural, race-free place to also record the key into the bloom
(under the same `store_mutex`), and `store_batch_result` for batches.

### 2.3 Rotating store fall-through — `database_rotating.rs::fetch_node_object`

```
let (mut writable, archive) = self.backends();
let mut node_object = fetch(&writable);      // probe #1
if node_object.is_none() {
    node_object = fetch(&archive);           // probe #2 (the extra cost)
    // archive-served reads are copied forward into writable during rotation
}
```

A miss that is absent from both stores costs two backend probes. A per-backend
bloom lets the writable and/or archive probe be skipped on a guaranteed miss.

### 2.4 Acquisition read path — `inbound_ledgers`

The acquisition coordinator issues `ReadRequest`s (`acquisition/src/io.rs`)
through the `NodeReadBroker` (`coordinator_ports.rs` → `read_broker.rs`), which
ultimately calls `Database::fetch_node_object` → `Backend::fetch`. The outcome
is `ReadOutcome::Settled { node: Option<Bytes> }`; `None` means "not present in
this store generation" and drives a peer request (batches of 12/128, per the
rippled `InboundLedger::filterNodes`/`kReqNodes` constants in `plan.rs`).

During initial acquisition and catch-up, the tree walk probes many *new* nodes
that are legitimately absent — the miss-heavy phase the bloom targets.

### 2.5 Backfill — `ledger/history_runtime/history_fill.rs` + `history_sync.rs`

History fill walks older ledgers; `LedgerHistoryFillStopReason` includes
`AlreadyHaveLedger` and `NodeStoreMismatch`, i.e. it probes the store for
nodes/ledgers it may or may not already have. Same local-scan miss pattern as
initial acquisition, just for the historical range. It fetches through the same
`Database`/`Backend` surface, so it benefits from the same per-backend bloom.

---

## 3. Design

### 3.1 Filter type

Blocked bloom filter (cache-line-friendly), fixed bits-per-key.
- Target false-positive rate: ~1% at 10 bits/key, k=7 hashes.
- Never false-negative → "absent" is authoritative; "maybe" falls through to the
  existing real lookup (which is exactly what happens today, so a false positive
  costs nothing beyond the status quo).
- Hashing: reuse the existing key hash prefix material; derive k probes via
  double-hashing (h1, h2) to avoid extra hashing cost.

### 3.2 Ownership and placement

The filter belongs to the **backend** (per NuDB store instance), because:
- membership is per store generation (writable vs archive are distinct),
- the store already owns the authoritative key set and the `store_mutex`,
- rotation creates/destroys backends, so per-backend filters rotate correctly.

Add to `NuDbBackend`:
- `bloom: Option<Arc<BloomFilter>>` (feature/config gated),
- consult in `fetch`/`fetch_batch` before the bucket read,
- insert in `store`/`store_batch_result` under `store_mutex`.

Expose an optional `Backend::may_contain(hash) -> bool` trait method
(default `true` = "no filter, must check") so callers (rotation, broker) can
skip a backend without knowing its internals.

### 3.3 Lifecycle (the hard part)

- **Build at open:** iterate existing keys via the store's `for_each`
  key-iteration to populate the filter, OR rebuild lazily. With `fast_load=1`
  the node already walks the tree at startup, so a build pass is affordable but
  must be measured (29M keys @ 10 bits ≈ 36 MiB, build is O(n) key reads).
- **Update on write:** every `store`/`store_batch_result` sets bits under
  `store_mutex` *before* releasing, so a subsequent local scan sees them.
- **Rotation:** the new writable backend starts with an empty (or freshly built)
  filter; the archive keeps its filter until dropped. The existing
  "copy archive-served reads forward into writable" path must also set the
  writable filter bit for the copied key.
- **Backfill writes:** history fill writes go through the same `store` path, so
  the filter stays consistent automatically.
- **Saturation:** bloom FPR degrades as it fills beyond its designed capacity.
  Size to expected node count for the configured `node_size`/history; if a store
  exceeds capacity, either grow (rebuild larger) or accept degraded FPR (still
  correct, just less skipping).

### 3.4 Safety argument

- No false negatives → never skip a node that is actually present. In
  acquisition this means we never wrongly decide "already have it"; a
  "definitely absent" only ever routes to the (correct) peer-request path.
- Concurrency: writes set bits under `store_mutex`; reads are lock-free bit
  tests. A concurrent insert that a reader misses only causes a fall-through to
  the real lookup (safe), never a wrong "absent".
- Ledger hash is unaffected: the filter changes *which reads happen*, never the
  data returned.

---

## 4. Files to change

| File | Change |
| --- | --- |
| `xrpld/nodestore/src/backends/backend.rs` | Add `fn may_contain(&self, _hash: &Uint256) -> bool { true }` to the `Backend` trait (default = must check). |
| `xrpl/basics/src/memory/` (new `bloom.rs`) | Blocked bloom filter type + double-hash probes + tests. |
| `xrpld/nodestore/src/backends/nudb_backend.rs` | Add `bloom` field; consult in `fetch`/`fetch_batch`; set bits in `store`/`store_batch_result`; build-at-open pass; config plumb. |
| `xrpld/nodestore/src/database_runtime/database_rotating.rs` | In `fetch_node_object`, call `writable.may_contain`/`archive.may_contain` to skip a guaranteed-miss probe; set writable bloom on copy-forward. |
| `xrpld/app/src/ledger/inbound_ledgers/read_broker.rs` (+ ports) | Optional: short-circuit a brokered read to a synthetic `Settled { node: None }` when `may_contain` is false, avoiding broker admission for guaranteed misses. |
| config (`node_db` section parsing) | `bloom_filter = 0|1`, `bloom_bits_per_key` (default 10). |
| `get_counts`/`fetch_info` counters | bloom hits/skips, FPR estimate, build time. |

---

## 5. Pros / Cons

Pros:
- Cuts store reads on the acquisition/backfill miss path (~15 µs measured avg
  read replaced by ~100 ns RAM probe → ~100–300x cheaper per avoided miss).
- Removes redundant archive probes during rotation on guaranteed misses.
- Lets the peer-request path start sooner (fewer doomed reads clogging the
  bounded read-admission budget).
- Safe by construction (no false negatives); correctness of ledger unaffected.
- Small memory: ~36 MiB for 29M keys @ 10 bits/key.

Cons / costs:
- Near-zero steady-state benefit (0.067% miss rate; cache absorbs reads).
- Lifecycle complexity: build-at-open, update-under-lock, rotation handoff,
  copy-forward bit set, saturation handling.
- Build-at-open adds startup cost proportional to key count (must be measured
  against the existing `fast_load` walk).
- Adds a small amount of `unsafe`-free but subtle concurrent state to the hot
  store path (bit sets under the existing mutex).
- Benefit is realized mainly during initial sync / deep catch-up / backfill —
  not in a node that is already Full and idle.

---

## 6. Expected impact (order-of-magnitude)

During a full initial sync of ~29M state nodes, if ~50% are probed-then-missed
before a peer fetch: ~14.5M misses × ~15 µs ≈ ~217s of store-read time removed,
spread across 6 read threads ≈ tens of seconds of wall-clock off the read path,
plus earlier network pipelining. Rotation: saves one archive probe per
guaranteed-miss during the `online_delete` window. Steady state: negligible.

---

## 7. Rollout plan

1. Land `bloom.rs` (pure, unit-tested) in `basics`.
2. Add `Backend::may_contain` default + NuDB filter (build-at-open + write
   hooks), behind `bloom_filter=0` default-off config. No behavior change when
   off.
3. Wire rotation `may_contain` skip + copy-forward bit set.
4. Wire acquisition/broker short-circuit.
5. Add counters; measure on testnet during a forced resync and a rotation
   window; compare read counts, sync wall-clock, and RSS delta.
6. Flip default only after measured benefit and parity tests pass.

---

## 8. Verification strategy

- Unit: bloom never false-negative (property test over random key sets); FPR
  within tolerance at target fill.
- Integration: NuDB fetch/store round-trip with filter on == filter off
  (identical results); rotation copy-forward keeps filter consistent.
- Parity: full nodestore parity suite (`nodestore_parity.rs`) unchanged with
  bloom on.
- Live: forced resync on testnet host; compare `node_reads_total`/misses, sync
  duration, and bloom skip counters vs a filter-off baseline.
