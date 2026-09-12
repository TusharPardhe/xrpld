# Lean ↔ Quaxar divergence resolution

## Scope, authority, and confidence

This record began as a source-only classification of the supplied divergences. The inspected authority is the local rippled checkout at `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification`, specifically the C++ implementation and its formal-verification parity tests. The Lean model and FFI in that same checkout are compared with the Quaxar Rust implementation at `/Users/tusharpardhe/Documents/xrpl/quaxar` and the existing interoperability harness at `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke`.

The R1 resolution changed only the Lean model/properties and bridge; the focused O1 repair changes only Quaxar’s direct fixed-width Rust operators, protocol tests, and the bridge reporting. Requested Lean and bridge Rust validation was run, but no C++ rippled build was run. An item remains **Unresolved** only when the local source deliberately relies on language- or implementation-defined behavior rather than defining an XRPL result.

**Status vocabulary.** **Proven semantic bug** means a publicly reachable value/error result conflicts with the local rippled behavior. **Proven representation-only** means all implementations reject the operation/value, but the boundary leaks incompatible internal error detail. **Proven missing API** means the behavior exists in rippled and Lean but is not available as a Quaxar public projection. **Unresolved** means no portable, source-provable expected result exists.

### Source hierarchy

1. C++ rippled implementation/declarations: authoritative behavioral intent.
2. C++ formal-verification tests: corroboration and named regression locations.
3. Lean model and exported FFI: formal boundary contract.
4. Quaxar Rust sources and the Lean↔Quaxar smoke harness: current port/binding behavior.

Paths below are absolute. Citations use `path — symbol` unless a precise line is available from the local language server; this avoids inventing line numbers for files whose local server did not supply them.

## Decision table

| ID | Divergence | Classification | Owner | Required disposition |
|---|---|---|---|---|
| N1 | `Number::max() / Number::min()` error category | **Proven representation-only** | Bridge/API error contract | Collapse internal normalisation failures to stable public overflow, or export a documented richer error ADT consistently. |
| I1 | IOU zero exponent through direct `fromNumber` | **Proven semantic bug** | Lean FFI/bridge API | Do not expose the private/raw conversion as public canonical IOU construction; route it through bounded canonical construction. |
| I2 | IOU upper/lower exponent bounds through direct `fromNumber` | **Proven semantic bug** | Lean FFI/bridge API | Same repair as I1: enforce `[-96,80]`, overflow above and canonical zero below. |
| A1 | `IntAmount(INT64_MIN) → Number` | **Proven semantic bug** | Quaxar Number normalization | Normalize magnitude `2^63` through the C++/Lean cusp path, not the exact-normalization shortcut. |
| R1 | Negative `mul_ratio` below `INT64_MIN` | **Resolved: deterministic Lean contract** | Lean model/FFI contract | Return `Error.overflow` for any mathematical result below `INT64_MIN`, symmetric with above-max overflow and Quaxar checked conversion. |
| O1 | Debug-vs-release overflowing integral operators | **Resolved: deterministic wrapping contract** | Quaxar direct integral operators | Use explicit `i64` wrapping arithmetic for the direct fixed-width add, subtract, multiply, and negation operators, matching Lean `Int64` and the rippled formal parity tests' wrapped reference. |
| S1 | `can_add`, `can_subtract`, `round_to_exponent` absent from Quaxar public surface | **Proven missing API** | Quaxar public API (temporary bridge adapter possible) | Export fallible projections matching rippled/Lean semantics and retain bridge checks. |

## Detailed classifications

### N1 — Number maximum/minimum division error category

**Status: Proven representation-only.**

The authoritative C++ operation rejects division by zero separately and otherwise normalizes the quotient; a normalization exponent overflow is thrown as `std::overflow_error`:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/src/libxrpl/basics/Number.cpp — Number::operator/=`.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/include/xrpl/basics/Number.h — Number::max`, `Number::min`, and `Number::RoundingMode`.

Quaxar intentionally exposes only two arithmetic categories:

- `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/basics/src/math/number.rs:195-198 — NumberArithmeticError` contains only `Overflow` and `DivideByZero`.
- The same file’s `NumberParts::try_div_assign` maps its normalization failures to `NumberArithmeticError::Overflow`.

Lean instead exposes internal normalization stages in its public error type:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Protocol/Errors.lean — Error` includes `overflow`, `divByZero`, `normalize1`, `normalize1_5`, and `normalize2`.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Protocol/Number.lean — Number.operator_div`, `doNormalize128`, and `doNormalize_scaleDown128`.
- The bridge deliberately observes the disagreement: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/number.rs — run` asserts that `abi::binary(3, max, min, tag)` yields raw Lean error tag `3`, while Quaxar yields `NumberArithmeticError::Overflow`.

Both sides reject the unrepresentable quotient. The mismatch is therefore not a numeric-result defect; it is an unstable FFI representation of the same failure. Keep Lean’s detailed errors internally if useful for proofs, but expose a stable boundary error (`overflow` / `divide_by_zero`) through either (a) a new Lean public wrapper used by the bridge, or (b) bridge-side mapping of every normalization tag to `Overflow`. Do **not** modify Quaxar arithmetic solely to invent Lean’s internal tags.

**Targeted regressions.** Add an ABI-level table for `max/min`, `min/max`, and zero divisor across all four rounding modes. Assert only `{overflow, divide_by_zero}` at the public boundary; unit-test the detailed Lean errors separately at model level.

### I1 and I2 — IOU zero canonicalization and exponent bounds

**Status: Proven semantic bug in the exported Lean conversion path.**

rippled distinguishes an internal pair conversion from public IOU construction:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/src/libxrpl/protocol/IOUAmount.cpp — IOUAmount::fromNumber` converts to the `[10^15, 10^16-1]` range.
- The same file’s `IOUAmount::normalize` canonicalizes any zero with `beast::kZero`; `IOUAmount::IOUAmount(Number const&)` rejects an exponent above `kMaxOffset` and converts an exponent below `kMinOffset` to `beast::kZero`.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/include/xrpl/protocol/IOUAmount.h — IOUAmount::operator=(beast::Zero)` fixes canonical zero at exponent `-100`; its class documentation fixes the nonzero range at exponent `[-96,80]`.

The Lean model has both pieces but its exported direct conversion is the raw one:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Protocol/IOUAmount.lean — IOUAmount.zero` is `{ mantissa_ := 0, exponent_ := -100 }`.
- `IOUAmount.fromNumber` only calls `Number.normalizeToRange` and returns the pair. It neither applies offset bounds nor replaces zero with `IOUAmount.zero`.
- `IOUAmount.ofNumber` and `IOUAmount.normalize` do apply `result.exponent_ > cMaxOffset`, `result.exponent_ < cMinOffset`, and canonical zero.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/FFI/Protocol/IOUAmountFFI.lean — lean_iou_from_number` exports the raw `fromNumber`; `lean_iou_of_number` exports the bounded public construction.

Quaxar follows public-construction semantics:

- `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/protocol/src/amounts/iou_amount.rs — IOUAmount::new` sets zero exponent `IOU_ZERO_EXPONENT = -100`.
- `IOUAmount::from_number` maps exponent `> MAX_IOU_EXPONENT` to `Overflow` and exponent `< MIN_IOU_EXPONENT` to `Self::new()`.
- `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/protocol/tests/amounts/amount_floor_parity.rs — iou_amount_zero_and_signum_match_cpp` asserts canonical zero’s `IOU_ZERO_EXPONENT`.

The local smoke harness demonstrates all three observable divergences without treating them as normal parity:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/iou.rs — run` sends a high Number (exponent `81`) to `iou_abi::from_number`, expects Lean success, and expects Quaxar `IOUAmount::from_number` overflow.
- The same function sends a low Number (exponent `-200`), expects Lean to retain an exponent below `-96`, and expects Quaxar canonical zero.
- Its `same_iou` helper explicitly treats Lean zero with `i32::MIN` as a divergence from Quaxar zero rather than equivalent canonical IOU output.

**Required change.** The public bridge must choose one meaning and name it accordingly:

1. Preferred: change/export the public “from Number to IOUAmount” operation to call `IOUAmount.ofNumber` (or an equivalent wrapper), so it is a canonical IOU constructor. This resolves I1 and I2 together.
2. If raw normalized-range conversion is required for proofs, retain it under an explicitly internal/raw API returning `(mantissa, exponent)` or a distinct `RawIOUAmount`, and do not compare it directly to Quaxar `IOUAmount`.

This is not a Quaxar change: Quaxar’s public result matches the local rippled constructor behavior.

**Targeted regressions.** At FFI and bridge levels, test each mode for (a) `Number(0)` and underflow-to-zero ⇒ `(0,-100)`, (b) normalized `10^18e81` ⇒ overflow, (c) normalized `10^18e-200` ⇒ `(0,-100)`, and (d) the exact nonzero boundaries `10^15e-96` and `10^16-1e80`.

### A1 — `IntAmount(INT64_MIN)` conversion to Number

**Status: Proven semantic bug in Quaxar normalization.**

rippled explicitly supports safely taking the magnitude of `INT64_MIN` before normalization:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/include/xrpl/basics/Number.h — Number::externalToInternal` documents the special `int64_t::min()` case.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/src/libxrpl/basics/Number.cpp — Number::externalToInternal` converts through `int128_t`, obtaining unsigned magnitude `2^63` without signed-negation UB, then Number normalization/rounding decides the representable result.
- Lean mirrors that route: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Protocol/Number.lean — Number.from_rep` uses `mantissa.toInt.natAbs.toUInt64`; `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Protocol/IntAmount.lean — IntAmount.toNumber` calls it.

Quaxar does compute the magnitude safely but then takes the wrong normalization route:

- `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/basics/src/math/number.rs — external_to_internal_mantissa` correctly returns `9_223_372_036_854_775_808` for `i64::MIN`.
- `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/protocol/src/amounts/mpt_amount.rs — impl From<MPTAmount> for NumberParts` uses `NumberParts::try_from_external_parts`.
- In `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/basics/src/math/number.rs — NumberParts::normalize_to_range`, the exact-normalization path does not perform the C++ `kMaxRep`/`kMaxRepUp` cusp reduction. Thus it can preserve an externally unrepresentable magnitude between `kMaxRep` and `kMaxRepUp` instead of taking the guarded arithmetic normalization route.
- The local Quaxar test documents the intended magnitude computation but does not close this path: `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/basics/src/math/number.rs — tests::external_to_internal_mantissa_edge_cases` checks the raw magnitude only.

The smoke harness gives direct evidence that the result diverges, including the rounding-mode-sensitive form:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/int_amount.rs — run` checks `i64::MIN` in every mode, asserts Lean differs from `NumberParts::from(MPTAmount::from(i64::MIN))`, and records five divergence observations total.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/src/test/formal_verification/numbers/LeanIntAmount_test.cpp — LeanIntAmount_test::test_extreme_values` specifically includes `INT64_MIN` in its `toNumber` boundary set.

**Required change.** Quaxar should change `impl From<MPTAmount> for NumberParts` (and the corresponding XRP conversion if it can receive `INT64_MIN`) to use a shared constructor that has exact C++ `Number(rep, exponent)` semantics, including cusp handling for magnitude `2^63`; do not simply reject `INT64_MIN`. Preserve current behavior for ordinary values.

**Targeted regressions.** Add a four-rounding-mode table for `MPTAmount::from(i64::MIN) → NumberParts`, comparing full internal fields and external `(mantissa, exponent)` where representable. Include `i64::MIN + 1`, `-i64::MAX`, and `i64::MAX`, and run it through the existing bridge’s `int_abi::to_number` comparison.

### R1 — negative `mul_ratio` underflow

**Status: Resolved: deterministic Lean contract.**

The local C++ source does not define a portable result for a quotient less than `INT64_MIN`:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/include/xrpl/protocol/XRPAmount.h — mulRatio` calculates with `boost::multiprecision::int128_t`, checks only `r > INT64_MAX`, then returns `r.convert_to<int64_t>()`.
- There is no corresponding `r < INT64_MIN` check, so the negative out-of-range conversion is implementation-defined rather than an exact C++ behavior this model can claim.

The Lean public contract now makes both directions explicit: `IntAmount.mulRatio` returns `Error.overflow` when its mathematical rounded result is greater than `INT64_MAX` **or** less than `INT64_MIN`. This is a safe deterministic boundary contract, symmetric with the existing upper-bound check and with Quaxar’s checked `i128 → i64` conversion; it does not claim an exact rippled C++ result for the implementation-defined conversion.

Focused Lean examples cover exact `INT64_MIN` success, below-min overflow, above-max overflow, ordinary negative rounding, and division by zero in `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Properties/Protocol/IntAmount/MulRatio/CheckedOverflow.lean`. The bridge now treats `INT64_MIN * 2 / 1` as strict `Error.overflow`/`NumberArithmeticError::Overflow` parity, leaving zero Int semantic divergence classes and zero observations. The nine direct-operator overflow probes are exact wrapping parity under O1.

**Targeted regression.** Retain `INT64_MIN * 1 / 1` success; `INT64_MIN * 2 / 1` and `INT64_MAX * 2 / 1` overflow; ordinary negative rounding; and denominator zero at both Lean property and bridge levels.

### O1 — deterministic direct fixed-width integral operators

**Status: Resolved: explicit deterministic wrapping contract.**

Quaxar now specifies all direct fixed-width MPTAmount and XRPAmount add, subtract, scalar multiply, and negation operators (including their corresponding assignment forms) as `i64` wrapping operations. This makes the result identical in debug and release and exactly matches Lean `Int64` arithmetic and the wrapping reference used by the local rippled formal parity tests:

- `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/protocol/src/amounts/mpt_amount.rs — AddAssign`, `SubAssign`, `Mul`, `MulAssign`, and `Neg` use `wrapping_add`, `wrapping_sub`, `wrapping_mul`, and `wrapping_neg`.
- `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/protocol/src/amounts/xrp_amount.rs — AddAssign`, `SubAssign`, scalar `AddAssign`, `SubAssign`, `Mul`, `MulAssign`, and `Neg` use the same explicit wrapping primitives.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/int_arithmetic.rs` now directly asserts every existing bridge operation against both Lean and Quaxar; the nine former profile observations are exact parity checks with no panic hook, `catch_unwind`, or profile-sensitive accounting.

C++ rippled direct signed overflow remains undefined behavior, so this contract does not claim to define a C++ overflow result. Its formal parity tests deliberately avoid evaluating those C++ expressions and instead compare Lean against a wrapped reference. Quaxar’s direct-operator behavior is now stable against that explicit Lean/reference contract. Checked/fallible `mul_ratio` remains separate and continues to report overflow rather than wrap.

**Targeted regressions.** Quaxar protocol tests cover `MAX + 1`, `MIN - 1`, overflowing multiplication, `-MIN`, and representative add/subtract/multiply assignment forms for both MPTAmount and XRPAmount; the same tests run without unwind handling in debug and release. The scratch bridge asserts the nine former profile observations as exact Lean↔Quaxar parity in both profiles.

### S1 — missing Quaxar public STAmount projections

**Status: Proven missing API.**

The authoritative C++ API exposes the required operations as free functions:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/include/xrpl/protocol/STAmount.h — canAdd`, `canSubtract`, and `roundToScale` declarations.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/src/libxrpl/protocol/STAmount.cpp — canAdd`, `canSubtract`, and `roundToScale` implementations; the local language server locates `roundToScale` at lines 1737–1741.

Lean models and exports each projection:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Protocol/STAmount.lean — STAmount.canAdd`, `STAmount.canSubtract`, and `STAmount.roundToExponent`.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/FFI/Protocol/STAmountFFI.lean — lean_stamount_can_add`, `lean_stamount_can_subtract`, and `lean_stamount_round_to_exponent`.

The bridge can invoke them, proving this is not a missing Lean operation:

- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/stamount_bridge.c — lean_st_can` dispatches to both Lean feasibility projections and `lean_st_round` dispatches to `lean_stamount_round_to_exponent`.
- `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/stamount_abi.rs — can` and `round` expose those bridge entry points.

Quaxar’s public `STAmount` instead exposes a different `round(&self, digits: usize)` helper, not C++ `roundToScale(value, scale, rounding)`, and has no public `can_add` or `can_subtract` equivalent:

- `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpl/protocol/src/amounts/st_amount.rs — impl STAmount::round` is digit-count based.
- The same implementation contains construction/arithmetic methods but no public `can_add`, `can_subtract`, or exponent-scale rounding projection.
- The harness names the gap directly: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/stamount.rs — run` adds exactly three divergences because no fallible Quaxar public counterpart exists.

**Required change.** Add the following Quaxar public functions (prefer free functions to mirror rippled):

```rust
pub fn can_add(a: &STAmount, b: &STAmount) -> Result<bool, AmountError>;
pub fn can_subtract(a: &STAmount, b: &STAmount) -> Result<bool, AmountError>;
pub fn round_to_exponent(
    value: &STAmount,
    scale: i32,
    rounding: RoundingMode,
) -> Result<STAmount, AmountError>;
```

They must preserve rippled semantics: comparability returns false for the `can_*` checks; integral and zero values are no-ops for scale rounding; an IOU at/above the scale is unchanged; otherwise use the reference-value add/subtract construction under the requested rounding mode. A temporary bridge adapter is acceptable only for verification; it is not a replacement for a Quaxar public API.

**Targeted regressions.** Port the local C++ parity cases from `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/src/test/formal_verification/numbers/LeanSTAmount_test.cpp — LeanSTAmount_test::test_known_predicates` and `test_known_round_to_exponent`: native/MPT overflow boundaries, IOU precision-loss feasibility, noncomparable values, integral/zero no-op rounding, scale-equal no-op, and positive/negative IOU rounded in all four modes.

## Implementation order

1. **Repair canonical boundary semantics (I1/I2).** Change the public Lean/bridge conversion to canonical `ofNumber` semantics; add the four IOU boundary regressions. This eliminates a wire-visible invalid IOU representation.
2. **Repair `INT64_MIN → Number` (A1).** Reuse a single Quaxar constructor/normalizer that implements the C++ `externalToInternal` plus cusp logic; add field-level all-mode tests.
3. **Expose STAmount projections (S1).** Implement public Quaxar `can_add`, `can_subtract`, and `round_to_exponent`; retain the bridge equivalence test as a second layer.
4. **Stabilize Number public errors (N1).** Add a Lean boundary wrapper or bridge mapping from normalization-stage tags to public overflow; test the error contract rather than raw tags.
5. **Stabilize direct fixed-width operators (O1).** Use explicit Quaxar `i64` wrapping operations for direct add, subtract, multiply, negation, and assignment forms; verify the protocol regressions and all nine Lean bridge probes in debug and release. Checked `mul_ratio` remains fallible and unchanged.

## Regression matrix and acceptance criteria

| Change | Primary regression location | Required assertion |
|---|---|---|
| I1/I2 | `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/iou.rs` plus Lean IOU parity test | Canonical `(0,-100)` and exact upper/lower bound outcomes agree across four modes. |
| A1 | `.../quaxar-lean-number-smoke/src/int_amount.rs` and Quaxar Number tests | `INT64_MIN` has identical Lean/Quaxar Number fields for every rounding mode. |
| S1 | Quaxar protocol amount tests plus `.../LeanSTAmount_test.cpp` port | New public functions agree with Lean/rippled cases, including false rather than panic for noncomparable feasibility checks. |
| N1 | `.../quaxar-lean-number-smoke/src/number.rs` | `max/min` is public `Overflow`; zero divisor remains `DivideByZero`; no raw normalization tag crosses the ABI. |
| R1 | `.../IntAmount/MulRatio/CheckedOverflow.lean` and `.../quaxar-lean-number-smoke/src/int_amount.rs` | Exact `INT64_MIN` success; below-min and above-max return overflow; negative rounding and zero denominator retain their expected results. |
| O1 | Quaxar protocol amount tests plus `.../quaxar-lean-number-smoke/src/int_arithmetic.rs` | `MAX+1`, `MIN-1`, overflowing multiplication, `-MIN`, and representative assignment forms wrap exactly like Lean `Int64` in debug and release; all nine bridge cases are exact parity. |

## Final count

There are **five proven classifications** across the seven requested subjects: one representation/API mismatch (N1), three semantic defects (I1, I2, A1), and one missing public API group (S1). R1 remains resolved by the deterministic checked-overflow Lean/FFI contract. O1 is now resolved by Quaxar’s explicit deterministic wrapping contract for direct fixed-width operators; C++ signed overflow remains undefined and is not used as the asserted result.


## Number nearest-addition monotonicity: executable cusp counterexample (2026-09-12)

The requested unrestricted replacement for
`Number.operator_add_left_toRat_mono` is **false in the current executable
Protocol Number model**, so no no-premise public monotonicity theorem was added
and the existing cusp-gap theorem was preserved.

Using the pinned Lean 4.28.0 environment, the model-only program below
constructed three normalized Numbers:

```lean
private def x  : Number := Number.unchecked false 9223372036854775807 0
private def y₁ : Number := Number.unchecked false 5000000000000000000 (-19)
private def y₂ : Number := Number.unchecked false 6000000000000000000 (-19)

#eval x.isNormalized
#eval y₁.isNormalized
#eval y₂.isNormalized
#eval x.toRat
#eval y₁.toRat
#eval y₂.toRat
#eval Number.operator_add x y₁ .to_nearest
#eval Number.operator_add x y₂ .to_nearest
#eval (x.toRat + y₁.toRat < x.toRat + y₂.toRat)
```

Exact output was:

```text
true
true
true
9223372036854775807
1 / 2
3 / 5
Except.ok { negative_ := false, mantissa_ := 9223372036854775810, exponent_ := 0 }
Except.ok { negative_ := false, mantissa_ := 9223372036854775807, exponent_ := 0 }
true
```

Thus all requested ordinary hypotheses hold for this common-left successful
nearest-addition pair: `y₁` and `y₂` are normalized and ordered;
`x + y₁ = maxRep + 1/2 < maxRep + 3/5 = x + y₂`; both exact sums and both
outputs are positive.  Nevertheless the smaller exact sum returns
`maxRepUp = 9223372036854775810`, while the larger exact sum returns
`maxRep = 9223372036854775807`.  Hence
`r₁.toRat ≤ r₂.toRat` is false.  This is the executable `doRoundUp` cusp
behavior, not a model/proof gap; it is precisely why the old total-relative
cusp-gap condition excluded the case.

The evaluation was run from `formal_verification` as:

```text
PATH=/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/lean-env/elan-home/bin:$PATH \
ELAN_HOME=/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/lean-env/elan-home \
lake env lean /tmp/number_cusp_counterexample.lean
# exit 0
```

For comparison only (not a universal proof), the negative-debit analogue
`y₁ = -3/5 ≤ y₂ = -1/2` at the same left operand executed successfully and
returned the same output `maxRep - 1` for both calls.  It supports the intended
withdrawal absorption intuition, but it cannot justify the requested theorem
whose stated hypotheses permit the positive-right counterexample above.

No Protocol model or rounding semantics was changed.  A sound future public
corollary must add a real restriction excluding the upper-then-lower cusp
transition (for example a proved debit-sign/executable absorption theorem), not
rename or omit the false total-relative premise.
