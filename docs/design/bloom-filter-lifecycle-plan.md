# Node-Store Bloom Filter — Lifecycle Plan, Edge Cases, and Benefit Analysis

Status: IMPLEMENTED (position A: persisted, store-bound, gated build).
Grounded in the actual quaxar code (build 0.8.1).

Implementation summary (what the code now does):
- Persisted image format `BLOOMFL2` carries `store_uid` + `durable_watermark`
  (`BloomFilter::to_bytes(uid, watermark)` / `from_bytes -> PersistedBloom`).
- At open, NuDB loads the image ONLY if `store_uid` matches the key-file uid
  (stable across restarts) and `durable_watermark <= data_file_size`; else it
  rebuilds. This handles fresh (new uid), foreign (different uid), behind
  (watermark) and corrupt/old (magic/version/size) images (E1/E2/E9/E3/E4).
- The one-time build is NO LONGER started at open. It is triggered only when
  the node reaches Full (`ApplicationRoot::trigger_node_store_membership_build`
  -> `SHAMapStoreNodeStore` -> `Database::trigger_membership_filter_build` ->
  `Backend::start_membership_filter_build`), so its scan never competes with
  startup load / replay / catch-up I/O (E5). A throttle remains as defense.
- Reads consult the filter only when `bloom_ready` (complete coverage) (E6).
- Writes populate the live filter always (atomic); build persists (uid+
  watermark, atomic temp+rename) then flips ready; `Arc::ptr_eq` guards a
  mid-build evict (E7).
- `evict_bloom` now persists-then-drops-RAM but KEEPS the disk image, so a
  later behind-restart reloads instantly.
- Known gap: a rotating store's `export_backend` returns a snapshot wrapper, so
  `trigger_membership_filter_build` does not currently reach the underlying
  rotating backends. Single-store (the deployed config) is fully wired.

---

## 1. Code facts this plan is built on (verified)

| Fact | Location / evidence |
| --- | --- |
| Store open distinguishes fresh vs existing | `NuDbOpenAction::CreateNew` vs `OpenExisting` (build_open_plan) |
| Store identity `uid`/`salt`/`appnum` live in the key-file header | `NuDbKeyFileHeader { uid, appnum, salt, ... }` |
| On `OpenExisting`, `uid`/`salt` are read FROM the on-disk header (stable across restarts) | `read_existing_header` reads `read_nudb_key_file_header` |
| On `CreateNew`, `uid`/`salt` come from `NuDbOpenArgs` (random via `quaxar_default` unless deterministic) | `build_random_open_args`, `NuDbOpenArgs::quaxar_default` |
| Acquisition, consensus, and RPC all read through the SAME `Backend::fetch` | broker `complete_from_node_store(Option)` -> `Found`/`Miss` |
| A `fetch` returning `None` becomes `ReadOutcome::Miss` = "ask a peer" | `read_broker.rs` |
| Writes populate the filter inline | `store` / `store_batch_result` bloom hooks |
| Node operating mode Connected->Tracking->Full is known at app layer | `NetworkOpsOperatingMode`, `SyncPhase::Full` |
| Startup load and startup replay both fully read the state tree from NuDB | `fast_load`/`StartUpType::{Load,Replay}` -> loadOldLedger/walk |
| Measured steady-state miss rate ~0.067% | live `get_counts`: reads_total 274,354,987 vs hit 274,171,772 |
| One full build measured: 60.6M keys, 60 MB filter, ~18.5 min, persisted | live log `bloom filter built ... elapsed_ms=1108521` |

---

## 2. The one safety invariant (everything derives from this)

The filter is consulted on the SHARED `fetch` path (acquisition + consensus +
RPC). Therefore:

> The filter's "definitely absent" verdict may only be TRUSTED (acted on to
> return NotFound / skip a read) when the filter has COMPLETE, CURRENT coverage
> of THIS store. Otherwise a pre-existing on-disk key could be reported absent
> to a consensus/RPC reader = data-loss bug.

Enforced by a `bloom_ready` gate: reads consult the filter only when ready;
ready is set only when coverage is proven complete for the current store.

---

## 3. Where the Bloom filter helps (benefit analysis)

| Phase | Store lookups are... | Bloom benefit | Why |
| --- | --- | --- | --- |
| Fresh initial sync (empty NuDB, fetch all from peers) | mostly MISS (new nodes) | **High** | "absent -> ask peer, skip local probe"; filter fills from writes as it syncs |
| Deep catch-up / backfill from peers (behind restart, existing NuDB) | mixed; new nodes MISS | **High** | skip local probe for genuinely-new nodes while re-acquiring the gap |
| Startup load / replay (fill state FROM NuDB) | all HIT (keys exist) | **None** | no misses to skip; building here also STARVES disk I/O (observed) |
| Steady-state (Full, serving RPC/consensus) | ~99.93% HIT | **~None (0.067%)** | negligible miss rate; filter is dead weight |

Conclusion: the Bloom filter is a **peer-acquisition accelerator**. Its value is
concentrated in fresh sync and deep catch-up. It provides ~no value once the
node is caught up, and no value during reading-existing-data-from-NuDB.

---

## 4. Lifecycle state machine (the plan)

| Trigger / state | Action on the filter | Reads trust filter? | Notes |
| --- | --- | --- | --- |
| Open, `CreateNew` (fresh store) | ignore + delete any stale `nudb.bloom`; create empty filter | no (not ready) | fresh store must never trust an old file (edge case E1) |
| Open, `OpenExisting`, valid file whose stored `uid` == store `uid` | load it; mark READY | **yes** | fast path: ms load, no scan, no contention |
| Open, `OpenExisting`, file missing / bad magic-version / `uid` mismatch / size inconsistent | empty filter, NOT ready; schedule deferred build | no | rebuild path; never misinterpret a stale/foreign file |
| During fast_load / replay / catch-up (not yet settled) | build stays OFF; writes still populate | no | prevents disk-I/O starvation (root cause of the failed deploys) |
| Node becomes settled (Full and stable for a grace period) AND filter not ready | run ONE throttled background scan -> persist -> mark READY | becomes yes on completion | the only scan; gated so it never competes with heavy phases |
| Every successful `store` / `store_batch_result` | insert key into live filter (atomic) | n/a | keeps coverage complete for keys written after the snapshot |
| Node has been Full/caught-up for a while (bloom benefit exhausted) | EVICT FROM RAM, but KEEP the disk file | no (until reloaded) | reclaims ~60 MB; next behind-restart reloads instantly (your idea, corrected) |
| Clean shutdown (`close`) | persist current READY filter to disk (uid-tagged) | n/a | next start takes fast load path |
| Rotation (`online_delete`) | each generation loads/persists its own uid-tagged file; rotating store keeps filters | yes when ready | archive dropped on rotate frees its filter |
| Explicit backfill-complete eviction (single store) | drop RAM (+ optionally keep file) | no | distinct from rotation which must keep filters |

---

## 5. Edge cases (enumerated + handling)

| ID | Edge case | Risk if unhandled | Handling |
| --- | --- | --- | --- |
| E1 | `nudb.bloom` exists but NuDB is fresh/empty (store wiped, file left) | filter claims coverage of keys the new store lacks -> false "absent" -> data loss | On `CreateNew`, delete/ignore the file. Also bind filter to store `uid`; empty/new store has a different uid -> reject. |
| E2 | `nudb.bloom` belongs to a DIFFERENT store (copied dir, swapped DB) | same false-absent data loss | Tag persisted image with store `uid`+`appnum`; reject on mismatch, rebuild. |
| E3 | Torn/partial `nudb.bloom` (crash mid-write) | garbage filter trusted | Atomic temp+rename on write; magic+version+size validation on read; reject -> rebuild. |
| E4 | Format/version change across releases | old layout misread | `FORMAT_VERSION` in header; bump rejects old images -> rebuild. |
| E5 | Build runs during fast_load/replay/catch-up | disk starvation, node can't sync (observed twice) | Gate build to start only when node settled (out of heavy phases). |
| E6 | Filter partially built, read consults it | false "absent" for a not-yet-inserted existing key | `bloom_ready` gate: never consult until fully built/loaded. |
| E7 | Filter evicted mid-build, then build completes | ready flipped on a dead filter | `Arc::ptr_eq` guard before persist/ready (already implemented). |
| E8 | Keys written AFTER the persisted snapshot (between persist and next load) | those keys absent from loaded filter -> false "absent" | Writes always insert into the live (loaded) filter; on shutdown re-persist. Residual: unclean crash may drop last writes -> see E9. |
| E9 | Unclean crash: filter persisted stale, some later writes lost from file | reloaded filter missing recently-written keys -> false "absent" for real data | CRITICAL. Options: (a) only persist on clean shutdown AND invalidate file if the store was not cleanly closed (NuDB has a recovery-log/dirty marker — tie bloom validity to clean-close); (b) store a "covers up to durable write generation N" watermark and require store's generation == filter's on load, else rebuild. Must resolve before trusting persisted reads across crashes. |
| E10 | Store grows far beyond `bloom_expected_keys` (48M default) | FPR rises (never false negative) | Safe; only perf. Optionally rebuild larger when count exceeds threshold. |
| E11 | Rotation vs single-store eviction confusion | rotating store loses a filter it needs | Rotating `evict_membership_filter` is a no-op (already implemented); only single-store evicts. |
| E12 | `bloom_ready` visibility across build thread and readers | stale read of ready flag | Release/Acquire ordering on `bloom_ready` and atomic bit ops (already implemented). |

---

## 6. The critical open risk: E9 (crash consistency)

Persisting for fast restart introduces a correctness dependency the in-memory
build never had: a reloaded filter is TRUSTED for reads, so it MUST be at least
as complete as the store it is loaded against. A crash that persists a stale
filter (missing recently durable-written keys) would, on reload, report real
on-disk keys as absent.

Mitigation options (pick one before trusting persisted reads across crashes):
1. Bind the filter to a durable store WATERMARK (e.g. NuDB write generation /
   data-file size at persist time). On load, require the store's current
   watermark to match; otherwise reject and rebuild. This makes a stale/behind
   filter self-invalidating.
2. Only load-and-trust when the store shows a CLEAN close (no pending recovery
   log). If the store recovered from its log (unclean), ignore the bloom file
   and rebuild.

Recommendation: implement (1) — a monotonic durable watermark in the bloom
header compared on load — because it precisely captures "does this filter cover
everything currently durable?" and composes with E1/E2 (uid) cleanly.

---

## 7. Strategic recommendation

Given Section 3 (benefit is peer-acquisition only; ~0% steady-state) and the
crash-consistency cost of persisted trust (E9), there are two coherent product
positions:

- **A. Full option-1 (persisted, uid+watermark-tagged, gated build, evict-keeps-file):**
  worth it ONLY if fast restart of a BEHIND node with existing NuDB, accelerating
  re-acquisition, is a real priority. Highest complexity; requires E9 resolved.

- **B. Acquisition-only, no persisted read trust:** keep the filter purely as an
  acquisition accelerator that fills from writes and is NEVER trusted for the
  shared `fetch` NotFound short-circuit (only used, if at all, in an
  acquisition-scoped path). No scan, no persistence trust, no E9. Lower value on
  a caught-up node, but zero risk and zero contention.

Decision needed: is fast-restart-of-a-behind-node acceleration worth the E9
crash-consistency machinery (position A), or do we keep it simple and
acquisition-only (position B)? The measured 0.067% steady-state miss rate argues
the bloom should be treated strictly as a sync/catch-up tool, not a general read
accelerator.
