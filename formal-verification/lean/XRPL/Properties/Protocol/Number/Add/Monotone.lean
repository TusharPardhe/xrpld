import XRPL.Properties.Protocol.Number.Add.CuspAware
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact

/-! # Addition monotonicity composition for nearest rounding

`Number.operator_add` is not representable by `RoundsNearestEven` at the
normalization cusp: the executable `doRoundUp` path has the documented cusp
escape. `operator_add_roundsCuspAware` proves the concrete executable bridge,
including that escape, and this module composes it with the protocol
`roundsCuspAware_mono` core. The public corollary therefore needs no
caller-supplied rounding predicate.
-/

namespace XRPL.Model.Protocol

/-- The executable cusp branch has one source exponent cell.

When `doRoundUp` receives a mantissa in `maxRep < zm ≤ maxRepUp`, its
nearest-mode implementation can deterministically choose the lower clamp
`maxRep`, the upper clamp `maxRepUp`, or the `maxRepUp + 10` carry leaf.  All
three values remain in the same normalized decimal cell at `ze`: the last leaf
uses a mantissa ending in zero and is renormalized back to that cell.  This is
an implementation fact, not a `RoundsCuspAware` consequence; it rules out the
spurious strict-decade choice that a relation over merely lower/upper
neighbours would permit. -/
theorem Number.doRoundUp_cuspRange_result_exponent_eq
    (g : Guard) (zm : UInt64) (ze : Int) (loc : Error) (resPos : RoundResult) (result : Number)
    (hlo : maxRep.toNat < zm.toNat) (hhi : zm.toNat ≤ maxRepUp.toNat)
    (hok : g.doRoundUp false zm ze largeRange.min largeRange.max .to_nearest loc = .ok resPos)
    (hresPos_ne : resPos.mantissa_ ≠ 0)
    (hresult_norm : result.isNormalized)
    (hresult_abs : |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_) :
    result.exponent_ = ze := by
  obtain ⟨v, hv, hcases⟩ := doRoundUp_value_cuspRange_cases g zm ze .to_nearest hlo hhi loc
    resPos hok hresPos_ne
  rcases hcases with ⟨hv_eq, _, _⟩ | ⟨hv_eq, _⟩ | ⟨hv_eq, _, _⟩
  · have habs : |result.toRat| = (maxRepNat : ℚ) * 10 ^ ze := by
      calc |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ := hresult_abs
        _ = v * 10 ^ ze := hv
        _ = (maxRepNat : ℚ) * 10 ^ ze := by rw [hv_eq]
    exact (Number.normalized_rep_of_abs result hresult_norm maxRepNat ze (by norm_num)
      (by norm_num) habs).2
  · have habs : |result.toRat| = ((maxRepNat + 3 : ℕ) : ℚ) * 10 ^ ze := by
      calc |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ := hresult_abs
        _ = v * 10 ^ ze := hv
        _ = ((maxRepNat + 3 : ℕ) : ℚ) * 10 ^ ze := by norm_num [hv_eq]
    exact (Number.normalized_rep_of_abs result hresult_norm (maxRepNat + 3) ze (by norm_num)
      (by norm_num) habs).2
  · have habs : |result.toRat| = ((maxRepNat + 13 : ℕ) : ℚ) * 10 ^ ze := by
      calc |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ := hresult_abs
        _ = v * 10 ^ ze := hv
        _ = ((maxRepNat + 13 : ℕ) : ℚ) * 10 ^ ze := by norm_num [hv_eq]
    exact (Number.normalized_rep_of_abs result hresult_norm (maxRepNat + 13) ze (by norm_num)
      (by norm_num) habs).2

/-- The explicit executable alternative to an ordinary nearest cell.  This is
not a broad neighbour relation: it retains the actual `doRoundUp` call, its
positive `RoundResult`, the source-cell equation for the exact sum, and the
strict `maxRep < zm ≤ maxRepUp` range.  Consequently its final field may be
fed directly to `Number.doRoundUp_cuspRange_result_exponent_eq`. -/
structure Number.AddCuspRangeResult (result : Number) (truth : ℚ) : Type where
  zm : UInt64
  ze : Int
  f : ℚ
  guard : Guard
  resPos : RoundResult
  loc : Error
  maxRep_lt_zm : maxRep.toNat < zm.toNat
  zm_le_maxRepUp : zm.toNat ≤ maxRepUp.toNat
  f_nonneg : 0 ≤ f
  f_lt_one : f < 1
  truth_cell : truth = ((zm.toNat : ℚ) + f) * 10 ^ ze
  doRoundUp_ok :
    guard.doRoundUp false zm ze largeRange.min largeRange.max .to_nearest loc = .ok resPos
  resPos_mant_ne : resPos.mantissa_ ≠ 0
  result_normalized : result.isNormalized
  result_abs : |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_
  result_exponent : result.exponent_ = ze

/-- Propositional availability of a strict executable cusp witness. -/
def Number.HasAddCuspRangeResult (result : Number) (truth : ℚ) : Prop :=
  Nonempty (Number.AddCuspRangeResult result truth)

/-- The floor band is a third exact executable cusp witness.  Its `doRoundUp`
input is still `mantissaFloor` at `ze'`, but the input cell rescales to the
cusp cell at `ze' - 1`; the UP result is therefore `maxRepUp` in that prior
cell.  Both decimal-cell equations are retained so exponent-order arguments
cannot accidentally treat this as an ordinary `ze'` result. -/
structure Number.AddFloorBandCuspResult (result : Number) (truth : ℚ) : Type where
  zm : UInt64
  ze' : Int
  f : ℚ
  guard : Guard
  resPos : RoundResult
  loc : Error
  zm_eq_mantissaFloor : zm = mantissaFloor
  floor_fraction : (8 : ℚ) / 10 ≤ f
  source_cell : truth = ((zm.toNat : ℚ) + f) * 10 ^ ze'
  pre_rescale_cusp_cell :
    truth = ((maxRepNat : ℚ) - 7 + 10 * f) * 10 ^ (ze' - 1)
  round_eq_one : guard.round .to_nearest = 1
  should_round_up : guard.shouldRoundUp_to_nearest zm
  doRoundUp_ok :
    guard.doRoundUp false zm ze' largeRange.min largeRange.max .to_nearest loc = .ok resPos
  doRoundUp_value :
    (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ =
      (maxRepUpNat : ℚ) * 10 ^ (ze' - 1)
  resPos_mant_ne : resPos.mantissa_ ≠ 0
  result_normalized : result.isNormalized
  result_abs : |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_
  result_cell : |result.toRat| = (maxRepUpNat : ℚ) * 10 ^ (ze' - 1)

/-- The floor-band UP result is in the rescaled cusp cell, one exponent below
its `doRoundUp` input cell. -/
theorem Number.addFloorBandCuspResult_exponent_eq
    (result : Number) (truth : ℚ) (w : Number.AddFloorBandCuspResult result truth) :
    result.exponent_ = w.ze' - 1 := by
  exact (Number.normalized_rep_of_abs result w.result_normalized maxRepUpNat (w.ze' - 1)
    (by norm_num) (by norm_num) w.result_cell).2

/-- Package the exact floor-band branch from the shared nearest-addition frame.
The floor constraint forces `round = 1`, hence the concrete no-cusp UP call;
rescaling its `(mantissaFloor + 1) · 10^ze'` output exposes `maxRepUp` in the
pre-rescale cusp cell. -/
theorem addFloorBandCuspResult_of_facts (x y result : Number)
    (htruth : 0 < x.toRat + y.toRat)
    (zm : UInt64) (ze' : Int) (f : ℚ) (guard : Guard) (resPos : RoundResult) (loc : Error)
    (hfacts : AddFactsToNearest x y result zm ze' f guard resPos loc)
    (hzm : zm = mantissaFloor) :
    Nonempty (Number.AddFloorBandCuspResult result (x.toRat + y.toRat)) := by
  have htruth_cell : x.toRat + y.toRat = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by
    rw [← abs_of_pos htruth]
    exact hfacts.value_eq
  have hzm_nat : zm.toNat = mantissaFloor := by
    rw [hzm]
    decide
  have hfloor_fraction : (8 : ℚ) / 10 ≤ f := by
    exact hfacts.floor_cusp hzm_nat
  have hf_gt_half : f > 1 / 2 := by
    linarith [hfloor_fraction]
  have hround_eq_one : guard.round .to_nearest = 1 := hfacts.f_gt_half hf_gt_half
  have hshould_round_up : guard.shouldRoundUp_to_nearest zm := Or.inl hround_eq_one
  have hno_cusp : zm.toNat + 1 ≤ maxRep.toNat := by
    rw [hzm_nat]
    decide
  have hdo_input := doRoundUp_value_to_nearest_roundUp_noCusp guard zm ze'
    hshould_round_up hno_cusp loc resPos hfacts.rounds hfacts.res_mant_ne
  have hzmq : (zm.toNat : ℚ) = (922337203685477580 : ℚ) := by
    rw [hzm_nat]
    norm_num
  have hpowsplit : (10 : ℚ) ^ ze' = 10 ^ (ze' - 1) * 10 := by
    rw [eq_comm, ← zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]
    congr 1
    ring
  have hpre_rescale_cusp_cell : x.toRat + y.toRat =
      ((maxRepNat : ℚ) - 7 + 10 * f) * 10 ^ (ze' - 1) := by
    calc x.toRat + y.toRat = ((zm.toNat : ℚ) + f) * 10 ^ ze' := htruth_cell
      _ = ((maxRepNat : ℚ) - 7 + 10 * f) * 10 ^ (ze' - 1) := by
        rw [hzmq, hpowsplit]
        ring
  have hdo_value : (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ =
      (maxRepUpNat : ℚ) * 10 ^ (ze' - 1) := by
    calc (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ =
          ((zm.toNat : ℚ) + 1) * 10 ^ ze' := hdo_input
      _ = (maxRepUpNat : ℚ) * 10 ^ (ze' - 1) := by
        rw [hzmq, hpowsplit]
        ring
  have hresult_cell : |result.toRat| = (maxRepUpNat : ℚ) * 10 ^ (ze' - 1) :=
    hfacts.result_abs.trans hdo_value
  exact ⟨⟨zm, ze', f, guard, resPos, loc, hzm, hfloor_fraction, htruth_cell,
    hpre_rescale_cusp_cell, hround_eq_one, hshould_round_up, hfacts.rounds,
    hdo_value, hfacts.res_mant_ne, hfacts.result_normalized, hfacts.result_abs,
    hresult_cell⟩⟩

/-- The documented equality-at-`maxRep` nearest tie is a separate executable
cusp escape. It is intentionally not folded into the strict range witness: the
source mantissa is exactly `maxRep`, the exact source fraction is `1 / 2`, and
the odd/tie guard selects `maxRepUp` even though that exact value is below the
midpoint between the two cusp neighbours. -/
structure Number.AddCuspTieResult (result : Number) (truth : ℚ) : Type where
  zm : UInt64
  ze : Int
  guard : Guard
  resPos : RoundResult
  loc : Error
  zm_eq_maxRep : zm = maxRep
  fraction_eq_half : truth = ((zm.toNat : ℚ) + 1 / 2) * 10 ^ ze
  tie_guard : guard.round .to_nearest = 0 ∧ zm % 2 = 1
  doRoundUp_ok :
    guard.doRoundUp false zm ze largeRange.min largeRange.max .to_nearest loc = .ok resPos
  resPos_mant_ne : resPos.mantissa_ ≠ 0
  result_normalized : result.isNormalized
  result_abs : |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_
  result_value : |result.toRat| = (maxRepCuspTarget : ℚ) * 10 ^ ze
  result_exponent : result.exponent_ = ze

/-- The equality-at-`maxRep` tie has the source exponent despite its cusp
rescale. This uses the concrete `doRoundUp_value_cusp` output equation, rather
than a generic neighbouring-grid relation. -/
theorem Number.doRoundUp_cuspTie_result_exponent_eq
    (g : Guard) (zm : UInt64) (ze : Int) (loc : Error) (resPos : RoundResult) (result : Number)
    (hzm : zm = maxRep) (htie : g.round .to_nearest = 0 ∧ zm % 2 = 1)
    (hok : g.doRoundUp false zm ze largeRange.min largeRange.max .to_nearest loc = .ok resPos)
    (hresPos_ne : resPos.mantissa_ ≠ 0)
    (hresult_norm : result.isNormalized)
    (hresult_abs : |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_) :
    result.exponent_ = ze := by
  have hvalue := doRoundUp_value_cusp g zm ze hzm htie loc resPos hok hresPos_ne
  have habs : |result.toRat| = (maxRepCuspTarget : ℚ) * 10 ^ ze := by
    calc |result.toRat| = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ := hresult_abs
      _ = (maxRepCuspTarget : ℚ) * 10 ^ ze := hvalue
  exact (Number.normalized_rep_of_abs result hresult_norm maxRepCuspTarget ze (by norm_num)
    (by norm_num) habs).2

/-- Package the documented `zm = maxRep`, `f = 1/2`, odd/tie-guard escape from
the shared addition frame. Its value equation exposes the otherwise omitted
`maxRepUp` output and its exponent remains the source exponent `ze`. -/
theorem addCuspTieResult_of_facts (x y result : Number)
    (htruth : 0 < x.toRat + y.toRat)
    (zm : UInt64) (ze : Int) (f : ℚ) (guard : Guard) (resPos : RoundResult) (loc : Error)
    (hfacts : AddFactsToNearest x y result zm ze f guard resPos loc)
    (hzm : zm = maxRep) (hf : f = 1 / 2) :
    Nonempty (Number.AddCuspTieResult result (x.toRat + y.toRat)) := by
  have htruth_cell : x.toRat + y.toRat = ((zm.toNat : ℚ) + 1 / 2) * 10 ^ ze := by
    rw [← abs_of_pos htruth]
    calc |x.toRat + y.toRat| = ((zm.toNat : ℚ) + f) * 10 ^ ze := hfacts.value_eq
      _ = ((zm.toNat : ℚ) + 1 / 2) * 10 ^ ze := by rw [hf]
  have htie : guard.round .to_nearest = 0 ∧ zm % 2 = 1 := by
    refine ⟨hfacts.f_eq_half hf, ?_⟩
    rw [hzm]
    decide
  have hvalue := doRoundUp_value_cusp guard zm ze hzm htie loc resPos hfacts.rounds
    hfacts.res_mant_ne
  have hresult_value : |result.toRat| = (maxRepCuspTarget : ℚ) * 10 ^ ze :=
    hfacts.result_abs.trans hvalue
  have hresult_exponent := Number.doRoundUp_cuspTie_result_exponent_eq guard zm ze loc
    resPos result hzm htie hfacts.rounds hfacts.res_mant_ne hfacts.result_normalized
    hfacts.result_abs
  exact ⟨⟨zm, ze, guard, resPos, loc, hzm, htruth_cell, htie, hfacts.rounds,
    hfacts.res_mant_ne, hfacts.result_normalized, hfacts.result_abs, hresult_value,
    hresult_exponent⟩⟩

/-- All exact executable cusp alternatives for successful positive nearest
addition: the strict maxRep range, equality/tie escape, or the floor-band UP
branch whose source decimal cell is rescaled to `ze' - 1`. -/
inductive Number.AddExceptionalCuspResult (result : Number) (truth : ℚ) : Type where
  | strict : Number.AddCuspRangeResult result truth →
      Number.AddExceptionalCuspResult result truth
  | tie : Number.AddCuspTieResult result truth →
      Number.AddExceptionalCuspResult result truth
  | floorBand : Number.AddFloorBandCuspResult result truth →
      Number.AddExceptionalCuspResult result truth

/-- Propositional availability of one of the exact exceptional cusp witnesses. -/
def Number.HasAddExceptionalCuspResult (result : Number) (truth : ℚ) : Prop :=
  Nonempty (Number.AddExceptionalCuspResult result truth)

/-- Every existing strict cusp witness is an exhaustive exceptional cusp witness. -/
theorem Number.hasAddExceptionalCuspResult_of_range (result : Number) (truth : ℚ)
    (h : Number.HasAddCuspRangeResult result truth) :
    Number.HasAddExceptionalCuspResult result truth := by
  obtain ⟨w⟩ := h
  exact ⟨.strict w⟩

/-- The documented equality/tie witness is an exhaustive exceptional cusp witness. -/
theorem Number.hasAddExceptionalCuspResult_of_tie (result : Number) (truth : ℚ)
    (h : Nonempty (Number.AddCuspTieResult result truth)) :
    Number.HasAddExceptionalCuspResult result truth := by
  obtain ⟨w⟩ := h
  exact ⟨.tie w⟩

/-- The floor-band/rescaled executable witness is the third exhaustive cusp
alternative.  Its exponent fact remains available through
`addFloorBandCuspResult_exponent_eq`. -/
theorem Number.hasAddExceptionalCuspResult_of_floorBand (result : Number) (truth : ℚ)
    (h : Nonempty (Number.AddFloorBandCuspResult result truth)) :
    Number.HasAddExceptionalCuspResult result truth := by
  obtain ⟨w⟩ := h
  exact ⟨.floorBand w⟩

/-- Package the strict cusp branch of the shared executable addition frame.
The same-sign `.overflow` and different-sign `.normalize2` paths are already
unified by `operator_add_algorithmic_facts_to_nearest`; this theorem preserves
which concrete location was used instead of erasing it. -/
theorem addCuspRangeResult_of_facts (x y result : Number)
    (htruth : 0 < x.toRat + y.toRat)
    (zm : UInt64) (ze : Int) (f : ℚ) (guard : Guard) (resPos : RoundResult) (loc : Error)
    (hfacts : AddFactsToNearest x y result zm ze f guard resPos loc)
    (hcusp : maxRep.toNat < zm.toNat) :
    Number.HasAddCuspRangeResult result (x.toRat + y.toRat) := by
  have htruth_cell : x.toRat + y.toRat = ((zm.toNat : ℚ) + f) * 10 ^ ze := by
    rw [← abs_of_pos htruth]
    exact hfacts.value_eq
  have hresult_exponent : result.exponent_ = ze :=
    Number.doRoundUp_cuspRange_result_exponent_eq guard zm ze loc resPos result
      hcusp hfacts.zm_le_maxRepUp hfacts.rounds hfacts.res_mant_ne
      hfacts.result_normalized hfacts.result_abs
  exact ⟨⟨zm, ze, f, guard, resPos, loc, hcusp, hfacts.zm_le_maxRepUp,
    hfacts.f_nonneg, hfacts.f_lt_one, htruth_cell, hfacts.rounds,
    hfacts.res_mant_ne, hfacts.result_normalized, hfacts.result_abs,
    hresult_exponent⟩⟩

/-- Extract the concrete cusp classifier arm directly from a successful,
positive, nonzero addition whenever its verified executable frame enters the
strict cusp range.  This is the reusable B arm of the normal-or-cusp
classifier; the complementary A arm must still prove `RoundsNormalCell` by
replaying the ordinary midpoint decisions rather than treating this witness as
a generic rounding relation. -/
theorem operator_add_cuspRangeResult_of_algorithmic_facts (x y result : Number)
    (htruth : 0 < x.toRat + y.toRat)
    (hcusp : ∃ zm ze f guard resPos loc,
      AddFactsToNearest x y result zm ze f guard resPos loc ∧ maxRep.toNat < zm.toNat) :
    Number.HasAddCuspRangeResult result (x.toRat + y.toRat) := by
  obtain ⟨zm, ze, f, guard, resPos, loc, hfacts, hzm⟩ := hcusp
  exact addCuspRangeResult_of_facts x y result htruth zm ze f guard resPos loc hfacts hzm

/-- Extract the documented equality-at-`maxRep` cusp-tie arm directly from a
successful positive addition frame. This is the second B-classifier arm: its
source fraction is exactly `1 / 2`, while the actual odd/tie executable guard
selects the documented `maxRepUp` result. -/
theorem operator_add_cuspTieResult_of_algorithmic_facts (x y result : Number)
    (htruth : 0 < x.toRat + y.toRat)
    (hcusp : ∃ zm ze f guard resPos loc,
      AddFactsToNearest x y result zm ze f guard resPos loc ∧
        zm = maxRep ∧ f = 1 / 2) :
    Nonempty (Number.AddCuspTieResult result (x.toRat + y.toRat)) := by
  obtain ⟨zm, ze, f, guard, resPos, loc, hfacts, hzm, hf⟩ := hcusp
  exact addCuspTieResult_of_facts x y result htruth zm ze f guard resPos loc hfacts hzm hf

/-- The equality/tie B-classifier arm is available through the exhaustive cusp
classification alongside the original strict range arm. -/
theorem operator_add_exceptionalCuspTieResult_of_algorithmic_facts (x y result : Number)
    (htruth : 0 < x.toRat + y.toRat)
    (hcusp : ∃ zm ze f guard resPos loc,
      AddFactsToNearest x y result zm ze f guard resPos loc ∧
        zm = maxRep ∧ f = 1 / 2) :
    Number.HasAddExceptionalCuspResult result (x.toRat + y.toRat) := by
  exact Number.hasAddExceptionalCuspResult_of_tie result (x.toRat + y.toRat)
    (operator_add_cuspTieResult_of_algorithmic_facts x y result htruth hcusp)

/-- Extract the third B-classifier arm from the exact shared addition facts.
At `mantissaFloor`, the floor fraction forces the executable UP decision; the
returned value and `addFloorBandCuspResult_exponent_eq` expose the source cusp
cell at `ze' - 1` directly to the next partition proof. -/
theorem operator_add_floorBandCuspResult_of_algorithmic_facts (x y result : Number)
    (htruth : 0 < x.toRat + y.toRat)
    (hcusp : ∃ zm ze' f guard resPos loc,
      AddFactsToNearest x y result zm ze' f guard resPos loc ∧ zm = mantissaFloor) :
    Nonempty (Number.AddFloorBandCuspResult result (x.toRat + y.toRat)) := by
  obtain ⟨zm, ze', f, guard, resPos, loc, hfacts, hzm⟩ := hcusp
  exact addFloorBandCuspResult_of_facts x y result htruth zm ze' f guard resPos loc hfacts hzm

/-- The floor-band B-classifier arm participates in the exhaustive exact cusp
sum without weakening the normal-cell alternative. -/
theorem operator_add_exceptionalFloorBandCuspResult_of_algorithmic_facts (x y result : Number)
    (htruth : 0 < x.toRat + y.toRat)
    (hcusp : ∃ zm ze' f guard resPos loc,
      AddFactsToNearest x y result zm ze' f guard resPos loc ∧ zm = mantissaFloor) :
    Number.HasAddExceptionalCuspResult result (x.toRat + y.toRat) := by
  exact Number.hasAddExceptionalCuspResult_of_floorBand result (x.toRat + y.toRat)
    (operator_add_floorBandCuspResult_of_algorithmic_facts x y result htruth hcusp)

/-! A pair of successful nearest-mode additions with a common left operand is
monotone once their executable rounding runs have been connected to the
cusp-aware exact rounding relation. The exact sums are compared directly.

The `hgap` hypothesis is the normalized minimum-gap condition needed solely by
the proven cusp escape case in `roundsCuspAware_mono`; it is not a generic
rounding assumption. -/

/-! ## Deterministic normal-cell crossover

The cusp-aware relation intentionally permits its one executable cusp escape.
Away from that escape, an addition result is an ordinary lower/upper grid choice:
strictly below the midpoint it is the lower neighbour and strictly above it is
the upper neighbour. The only possible reversal is therefore the cross
`upper t₁` / `lower t₂`. Grid tightness forces both calls into the same cell;
the two strict decision implications force both exact sums to its midpoint; and
successful `operator_add` calls are deterministic there. This classifier returns
only decimal-exponent order, which is the fact needed by `ofNumber`.
-/

/-- Ordinary (non-cusp-escape) nearest-cell decision facts. The two strict
implications are deliberately stated in terms of executable output values; a
per-path guard/normalize bridge supplies them without assuming a global
rounding relation. -/
def Number.RoundsNormalCell (r : Number) (t : ℚ) : Prop :=
  ∃ L U : Number,
    Number.lower t = some L ∧ Number.upper t = some U ∧
    (r.toRat = L.toRat ∨ r.toRat = U.toRat) ∧
    (2 * t < L.toRat + U.toRat → r.toRat = L.toRat) ∧
    (L.toRat + U.toRat < 2 * t → r.toRat = U.toRat)

/-- Extract the UP arm of the shared nearest-addition frame into either an
ordinary normal cell or one of the three exact executable cusp witnesses.

The concrete lower/upper grid witnesses are supplied by the caller; the upper
one is exactly the witness already produced by the UP arm of
`operator_add_roundsCuspAware_nonzero`.  In the ordinary branch, the strict
lower-midpoint implication is discharged from the actual `doRoundUp` decision:
UP forces `f ≥ 1 / 2`, while the lower grid point stays below the concrete
source-cell bottom.  The remaining branches reuse the strict-range, equality
/tie, and floor-band constructors without reproving their executable semantics. -/
theorem Number.addFactsToNearest_up_roundsNormalCell_or_exceptionalCusp
    (x y result : Number) (zm : UInt64) (ze' : Int) (f : ℚ) (guard : Guard)
    (resPos : RoundResult) (loc : Error)
    (htruth : 0 < x.toRat + y.toRat)
    (hup : x.toRat + y.toRat < result.toRat)
    (hfacts : AddFactsToNearest x y result zm ze' f guard resPos loc)
    (L U : Number) (hL : Number.lower (x.toRat + y.toRat) = some L)
    (hU : Number.upper (x.toRat + y.toRat) = some U)
    (hresultU : result.toRat = U.toRat) :
    result.RoundsNormalCell (x.toRat + y.toRat) ∨
      Number.HasAddExceptionalCuspResult result (x.toRat + y.toRat) := by
  have hpow : (0 : ℚ) < 10 ^ ze' := zpow_pos (by norm_num) _
  have hresult_pos : 0 < result.toRat := lt_trans htruth hup
  have hresult_value : result.toRat =
      (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ := by
    rw [← abs_of_pos hresult_pos]
    exact hfacts.result_abs
  have htruth_cell : x.toRat + y.toRat = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by
    rw [← abs_of_pos htruth]
    exact hfacts.value_eq
  by_cases hzm_le : zm.toNat ≤ maxRep.toNat
  · by_cases hregular : zm.toNat + 1 ≤ maxRep.toNat
    · have hroundUp : guard.shouldRoundUp_to_nearest zm := by
        by_contra hnoRoundUp
        have hvalue := doRoundUp_value_no_roundUp guard zm ze' hnoRoundUp hzm_le
          loc resPos hfacts.rounds hfacts.res_mant_ne
        have hresult_cell : result.toRat = (zm.toNat : ℚ) * 10 ^ ze' :=
          hresult_value.trans hvalue
        rw [hresult_cell, htruth_cell] at hup
        have hfrac := lt_of_mul_lt_mul_right hup (le_of_lt hpow)
        linarith [hfacts.f_nonneg]
      have hf_half : 1 / 2 ≤ f := by
        rcases hroundUp with hround | ⟨htie, _⟩
        · exact le_of_lt (hfacts.round_eq_one hround)
        · exact le_of_eq (hfacts.round_eq_zero htie).symm
      have hvalue := doRoundUp_value_to_nearest_roundUp_noCusp guard zm ze' hroundUp hregular
        loc resPos hfacts.rounds hfacts.res_mant_ne
      have hresult_cell : result.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' :=
        hresult_value.trans hvalue
      by_cases hfloor : mantissaFloorSucc ≤ zm.toNat
      · left
        have hzm_lt : zm.toNat < 10 ^ 19 := by
          have hmax := hfacts.zm_le_maxRepUp
          rw [show maxRepUp.toNat = maxRepUpNat from rfl] at hmax
          omega
        have hL_cell : L.toRat ≤ (zm.toNat : ℚ) * 10 ^ ze' :=
          lower_le_cell_bot (x.toRat + y.toRat) L hL zm.toNat ze' hfloor hzm_lt
            (by
              rw [htruth_cell]
              exact mul_lt_mul_of_pos_right (by linarith [hfacts.f_lt_one]) hpow)
        have hU_cell : U.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' :=
          hresultU.symm.trans hresult_cell
        refine ⟨L, U, hL, hU, Or.inr hresultU, ?_, ?_⟩
        · intro hmid
          exfalso
          have hsum : L.toRat + U.toRat ≤ (2 * (zm.toNat : ℚ) + 1) * 10 ^ ze' := by
            rw [hU_cell]
            nlinarith [hL_cell]
          have hfrac_mul : 2 * ((zm.toNat : ℚ) + f) * 10 ^ ze' <
              (2 * (zm.toNat : ℚ) + 1) * 10 ^ ze' := by
            calc 2 * ((zm.toNat : ℚ) + f) * 10 ^ ze' = 2 * (x.toRat + y.toRat) := by
                  rw [htruth_cell]
                  ring
              _ < L.toRat + U.toRat := hmid
              _ ≤ (2 * (zm.toNat : ℚ) + 1) * 10 ^ ze' := hsum
          have hfrac := lt_of_mul_lt_mul_right hfrac_mul (le_of_lt hpow)
          linarith [hf_half]
        · intro _
          exact hresultU
      · right
        push_neg at hfloor
        have hfloor_nat : zm.toNat = mantissaFloor := by
          have hmin := hfacts.zm_ge_floor
          omega
        have hfloor_eq : zm = (mantissaFloor : UInt64) := by
          apply UInt64.toNat_inj.mp
          rw [hfloor_nat]
          decide
        exact Number.hasAddExceptionalCuspResult_of_floorBand result (x.toRat + y.toRat)
          (addFloorBandCuspResult_of_facts x y result htruth zm ze' f guard resPos loc hfacts
            hfloor_eq)
    · right
      have hmax_nat : zm.toNat = maxRep.toNat := by omega
      have hmax_eq : zm = maxRep := UInt64.toNat_inj.mp hmax_nat
      have hround_tie : guard.round .to_nearest = 0 ∧ zm % 2 = 1 := by
        have hroundUp : guard.shouldRoundUp_to_nearest zm := by
          by_contra hnoRoundUp
          have hvalue := doRoundUp_value_no_roundUp guard zm ze' hnoRoundUp hzm_le
            loc resPos hfacts.rounds hfacts.res_mant_ne
          have hresult_cell : result.toRat = (zm.toNat : ℚ) * 10 ^ ze' :=
            hresult_value.trans hvalue
          rw [hresult_cell, htruth_cell] at hup
          have hfrac := lt_of_mul_lt_mul_right hup (le_of_lt hpow)
          linarith [hfacts.f_nonneg]
        rcases hroundUp with hround | ⟨htie, hodd⟩
        · exfalso
          have hvalue := doRoundUp_value_to_nearest_roundUp_cusp_round1 guard zm ze'
            hmax_eq hround loc resPos hfacts.rounds hfacts.res_mant_ne
          have hmax_q : (zm.toNat : ℚ) = (maxRepNat : ℚ) := by
            exact_mod_cast (hmax_nat.trans maxRep_val)
          have hresult_cell : result.toRat = (zm.toNat : ℚ) * 10 ^ ze' := by
            calc result.toRat = (resPos.mantissa_.toNat : ℚ) * 10 ^ resPos.exponent_ :=
                  hresult_value
              _ = (maxRep.toNat : ℚ) * 10 ^ ze' := hvalue
              _ = (maxRepNat : ℚ) * 10 ^ ze' := by rw [maxRep_val]; norm_num
              _ = (zm.toNat : ℚ) * 10 ^ ze' := by rw [hmax_q]
          rw [hresult_cell, htruth_cell] at hup
          have hfrac := lt_of_mul_lt_mul_right hup (le_of_lt hpow)
          linarith [hfacts.f_nonneg]
        · exact ⟨htie, hodd⟩
      have hf_half : f = 1 / 2 := hfacts.round_eq_zero hround_tie.1
      exact Number.hasAddExceptionalCuspResult_of_tie result (x.toRat + y.toRat)
        (addCuspTieResult_of_facts x y result htruth zm ze' f guard resPos loc hfacts
          hmax_eq hf_half)
  · right
    push_neg at hzm_le
    exact Number.hasAddExceptionalCuspResult_of_range result (x.toRat + y.toRat)
      (addCuspRangeResult_of_facts x y result htruth zm ze' f guard resPos loc hfacts hzm_le)

/-- **Normal-path crossover classifier.** Ordered positive exact inputs cannot
produce a decreasing decimal exponent when both executable additions expose
ordinary nearest-cell decisions. Unlike value monotonicity, this result needs
no minimum-gap premise: the only cross is eliminated by actual call
determinism at the one shared midpoint. -/
theorem Number.roundsNormalCell_exponent_mono
    (t₁ t₂ : ℚ) (r₁ r₂ : Number)
    (h₁ : r₁.RoundsNormalCell t₁) (h₂ : r₂.RoundsNormalCell t₂)
    (hr₁norm : r₁.isNormalized) (hr₂norm : r₂.isNormalized)
    (hr₁pos : 0 < r₁.toRat) (hle : t₁ ≤ t₂)
    (hdet : t₁ = t₂ → r₁.toRat = r₂.toRat) :
    r₁.exponent_ ≤ r₂.exponent_ := by
  obtain ⟨L₁, U₁, hL₁, hU₁, hmem₁, hdn₁, hup₁⟩ := h₁
  obtain ⟨L₂, U₂, hL₂, hU₂, hmem₂, hdn₂, hup₂⟩ := h₂
  have hLL : L₁.toRat ≤ L₂.toRat :=
    Number.lowerV_mono t₁ t₂ L₁ L₂ hL₁ hL₂ hle
  have hUU : U₁.toRat ≤ U₂.toRat :=
    Number.upperV_mono t₁ t₂ U₁ U₂ hU₁ hU₂ hle
  have hL₂U₂ : L₂.toRat ≤ U₂.toRat :=
    le_trans (Number.lower_le t₂ L₂ hL₂) (Number.upper_ge t₂ U₂ hU₂)
  have hvalue : r₁.toRat ≤ r₂.toRat := by
    rcases hmem₁ with hr₁L | hr₁U
    · rcases hmem₂ with hr₂L | hr₂U
      · rw [hr₁L, hr₂L]; exact hLL
      · rw [hr₁L, hr₂U]; exact le_trans hLL hL₂U₂
    · rcases hmem₂ with hr₂L | hr₂U
      · by_contra hcon
        push_neg at hcon
        rw [hr₁U, hr₂L] at hcon
        have hU₁neL₁ : L₁.toRat ≠ U₁.toRat := by
          intro heq
          have : L₂.toRat < L₁.toRat := by rw [heq]; exact hcon
          exact absurd hLL (not_le.mpr this)
        have hL₁eqL₂ : L₁.toRat = L₂.toRat := by
          rcases lt_or_eq_of_le hLL with hlt | heq
          · exact absurd ⟨hlt, hcon⟩
              (Number.no_gridV_between t₁ L₁ U₁ hL₁ hU₁ L₂
                (Number.lower_isNormalized t₂ L₂ hL₂))
          · exact heq
        have hU₁eqU₂ : U₁.toRat = U₂.toRat := by
          rcases lt_or_eq_of_le hUU with hlt | heq
          · exact absurd ⟨hcon, hlt⟩
              (Number.no_gridV_between t₂ L₂ U₂ hL₂ hU₂ U₁
                (Number.upper_isNormalized t₁ U₁ hU₁))
          · exact heq
        have hL₂neU₂ : L₂.toRat ≠ U₂.toRat := by
          rw [← hL₁eqL₂, ← hU₁eqU₂]
          exact hU₁neL₁
        have ht₁mid : L₁.toRat + U₁.toRat ≤ 2 * t₁ := by
          by_contra h
          push_neg at h
          exact hU₁neL₁ (by rw [← hr₁U, hdn₁ h])
        have ht₂mid : 2 * t₂ ≤ L₂.toRat + U₂.toRat := by
          by_contra h
          push_neg at h
          exact hL₂neU₂ (by rw [← hr₂L]; exact hup₂ h)
        have hsum : L₁.toRat + U₁.toRat = L₂.toRat + U₂.toRat := by
          rw [hL₁eqL₂, hU₁eqU₂]
        have ht : t₁ = t₂ := by linarith [ht₁mid, ht₂mid, hsum, hle]
        have heq := hdet ht
        rw [hr₁U, hr₂L] at heq
        exact (ne_of_gt hcon) heq
      · rw [hr₁U, hr₂U]; exact hUU
  exact Number.exponent_le_of_normalized_pos_toRat_le r₁ r₂ hr₁norm hr₂norm hr₁pos hvalue

/-- Successful nearest additions inherit the normal-cell crossover classifier.
The caller supplies exactly the guard/tie/normalize decision bridges for the
two non-cusp paths; equal exact sums identify the normalized right operands,
so the two executable calls have identical results. -/
theorem Number.operator_add_left_exponent_mono_normal
    (x y₁ y₂ r₁ r₂ : Number)
    (hy₁ : y₁.isNormalized) (hy₂ : y₂.isNormalized)
    (hok₁ : Number.operator_add x y₁ .to_nearest = .ok r₁)
    (hok₂ : Number.operator_add x y₂ .to_nearest = .ok r₂)
    (hround₁ : r₁.RoundsNormalCell (x.toRat + y₁.toRat))
    (hround₂ : r₂.RoundsNormalCell (x.toRat + y₂.toRat))
    (hr₁norm : r₁.isNormalized) (hr₂norm : r₂.isNormalized)
    (hr₁pos : 0 < r₁.toRat)
    (hsums : x.toRat + y₁.toRat ≤ x.toRat + y₂.toRat) :
    r₁.exponent_ ≤ r₂.exponent_ := by
  apply Number.roundsNormalCell_exponent_mono
    (x.toRat + y₁.toRat) (x.toRat + y₂.toRat) r₁ r₂ hround₁ hround₂
    hr₁norm hr₂norm hr₁pos hsums
  intro heq
  have hyval : y₁.toRat = y₂.toRat := by linarith
  have hy : y₁ = y₂ := hy₁.toRat_inj hy₂ hyval
  subst y₂
  exact congrArg Number.toRat (Except.ok.inj (hok₁.symm.trans hok₂))
/-! Equal exact sums are handled from the actual `operator_add` equations:
normalized right operands with equal `toRat` values are equal Numbers, hence the
two executable calls have equal results. -/
theorem Number.operator_add_left_toRat_mono_of_cuspAware
    (x y₁ y₂ r₁ r₂ : Number)
    (hy₁ : y₁.isNormalized) (hy₂ : y₂.isNormalized)
    (hok₁ : Number.operator_add x y₁ .to_nearest = .ok r₁)
    (hok₂ : Number.operator_add x y₂ .to_nearest = .ok r₂)
    (hround₁ : r₁.RoundsCuspAware (x.toRat + y₁.toRat))
    (hround₂ : r₂.RoundsCuspAware (x.toRat + y₂.toRat))
    (hr₁pos : 0 < r₁.toRat) (hr₂pos : 0 < r₂.toRat)
    (htruth₁pos : 0 < x.toRat + y₁.toRat)
    (hsums : x.toRat + y₁.toRat ≤ x.toRat + y₂.toRat)
    (hgap : x.toRat + y₁.toRat < x.toRat + y₂.toRat →
      x.toRat + y₁.toRat ≤ (maxRepNat : ℚ) *
        ((x.toRat + y₂.toRat) - (x.toRat + y₁.toRat))) :
    r₁.toRat ≤ r₂.toRat := by
  refine roundsCuspAware_mono _ _ r₁ r₂ hround₁ hround₂ hr₁pos hr₂pos htruth₁pos
    hsums hgap ?_
  intro heq
  have hyval : y₁.toRat = y₂.toRat := by linarith
  have hy : y₁ = y₂ := hy₁.toRat_inj hy₂ hyval
  subst y₂
  exact congrArg Number.toRat (Except.ok.inj (hok₁.symm.trans hok₂))

/-- Concrete nearest-mode addition monotonicity: callers no longer supply cusp-aware rounding facts. -/
theorem Number.operator_add_left_toRat_mono
    (x y₁ y₂ r₁ r₂ : Number)
    (hx : x.isNormalized) (hy₁ : y₁.isNormalized) (hy₂ : y₂.isNormalized)
    (hok₁ : Number.operator_add x y₁ .to_nearest = .ok r₁)
    (hok₂ : Number.operator_add x y₂ .to_nearest = .ok r₂)
    (hr₁pos : 0 < r₁.toRat) (hr₂pos : 0 < r₂.toRat)
    (htruth₁pos : 0 < x.toRat + y₁.toRat)
    (hsums : x.toRat + y₁.toRat ≤ x.toRat + y₂.toRat)
    (hgap : x.toRat + y₁.toRat < x.toRat + y₂.toRat →
      x.toRat + y₁.toRat ≤ (maxRepNat : ℚ) * ((x.toRat + y₂.toRat) - (x.toRat + y₁.toRat))) :
    r₁.toRat ≤ r₂.toRat := by
  apply Number.operator_add_left_toRat_mono_of_cuspAware x y₁ y₂ r₁ r₂ hy₁ hy₂ hok₁ hok₂
    (operator_add_roundsCuspAware x y₁ r₁ hx hy₁ hok₁ htruth₁pos hr₁pos)
    (operator_add_roundsCuspAware x y₂ r₂ hx hy₂ hok₂ (lt_of_lt_of_le htruth₁pos hsums) hr₂pos)
    hr₁pos hr₂pos htruth₁pos hsums hgap

/-- A verified lower executable branch is an ordinary normal-cell decision once
both grid neighbours are available.  The midpoint bound is the one established
from the concrete `shouldRoundUp = false` / even-tie guard path; no rounding
relation is weakened here. -/
theorem Number.roundsNormalCell_of_cuspAware_lower
    (r : Number) (t : ℚ) (L U : Number)
    (hround : r.RoundsCuspAware t)
    (hL : Number.lower t = some L) (hU : Number.upper t = some U)
    (hrL : r.toRat = L.toRat) :
    r.RoundsNormalCell t := by
  rcases hround with ⟨L', hL', hrL', hmid⟩ | ⟨U', hU', hrU', hup⟩
  · have hLL : L' = L := Option.some.inj (hL'.symm.trans hL)
    subst L'
    refine ⟨L, U, hL, hU, Or.inl hrL, ?_, ?_⟩
    · intro _
      exact hrL
    · intro hstrict
      exfalso
      linarith [hmid U hU]
  · have hUeq : U' = U := Option.some.inj (hU'.symm.trans hU)
    subst U'
    -- At a lower/equality assembly point the two concrete branch values agree;
    -- use each equality on its respective strict midpoint implication.
    refine ⟨L, U, hL, hU, Or.inl hrL, ?_, ?_⟩
    · intro _
      exact hrL
    · intro _
      exact hrU'

/-- The exact/lower half of `AddFactsToNearest` assembles an ordinary
`RoundsNormalCell` from the actual lower neighbour and the executable
cusp-aware midpoint inequality.  In particular it includes strict-below and
an even tie that does not round up; the supplied `AddFactsToNearest` frame is
kept explicit so this lemma composes with the same executable witness as the
UP classifier. -/
theorem Number.addFactsToNearest_down_roundsNormalCell
    (x y result : Number) (zm : UInt64) (ze' : Int) (f : ℚ) (guard : Guard)
    (resPos : RoundResult) (loc : Error)
    (_hfacts : AddFactsToNearest x y result zm ze' f guard resPos loc)
    (L U : Number) (hL : Number.lower (x.toRat + y.toRat) = some L)
    (hU : Number.upper (x.toRat + y.toRat) = some U)
    (hround : result.RoundsCuspAware (x.toRat + y.toRat))
    (hresultL : result.toRat = L.toRat) :
    result.RoundsNormalCell (x.toRat + y.toRat) := by
  exact Number.roundsNormalCell_of_cuspAware_lower result (x.toRat + y.toRat) L U
    hround hL hU hresultL

/-- Exact successful additions are normal-cell decisions.  This covers the
zero-return paths of `operator_add`; cancellation is excluded by a positive
exact sum, while a flushed underflow is excluded by the positive-result
hypothesis before this constructor is reached. -/
theorem Number.roundsNormalCell_of_exact
    (result : Number) (t : ℚ) (L U : Number)
    (hresultNorm : result.isNormalized) (_hresultPos : 0 < result.toRat)
    (hresultEq : result.toRat = t)
    (hL : Number.lower t = some L) (hU : Number.upper t = some U) :
    result.RoundsNormalCell t := by
  have hLval : L.toRat = t := by
    apply le_antisymm
    · exact Number.lower_le t L hL
    · rw [← hresultEq]
      exact Number.lower_tight t L hL result hresultNorm (by rw [hresultEq])
  have hUval : U.toRat = t := by
    apply le_antisymm
    · rw [← hresultEq]
      exact Number.upper_tight t U hU result hresultNorm (by rw [← hresultEq])
    · exact Number.upper_ge t U hU
  refine ⟨L, U, hL, hU, Or.inl ?_, ?_, ?_⟩
  · rw [hresultEq, hLval]
  · intro _
    rw [hresultEq, hLval]
  · intro _
    rw [hresultEq, hUval]

/-- Public nearest-addition classifier after the caller has obtained the two
concrete grid witnesses for its positive exact sum.  It replays the executable
outer skeleton: zero identities become exact normal cells, cancellation and
underflow contradict the positive hypotheses, DOWN/equality uses the concrete
lower guard branch, and strict UP is discharged by the cycle-49 UP classifier.
The exceptional alternative remains the exact executable cusp witness, not a
weakened neighbour relation. -/
theorem Number.operator_add_roundsNormalCell_or_exceptionalCusp
    (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (htruth : 0 < x.toRat + y.toRat) (hresultPos : 0 < result.toRat)
    (L U : Number) (hL : Number.lower (x.toRat + y.toRat) = some L)
    (hU : Number.upper (x.toRat + y.toRat) = some U) :
    result.RoundsNormalCell (x.toRat + y.toRat) ∨
      Number.HasAddExceptionalCuspResult result (x.toRat + y.toRat) := by
  by_cases hy0 : y.operator_eq Number.zero = true
  · have hyval : y.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero y
      (Number.mantissa_eq_zero_of_operator_eq_zero hy0)
    have hresult : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos hy0] at hok
      exact (Except.ok.inj hok).symm
    left
    apply Number.roundsNormalCell_of_exact result (x.toRat + y.toRat) L U
    · rw [hresult]; exact hx
    · exact hresultPos
    · rw [hresult, hyval, add_zero]
    · exact hL
    · exact hU
  by_cases hx0 : x.operator_eq Number.zero = true
  · have hxval : x.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero x
      (Number.mantissa_eq_zero_of_operator_eq_zero hx0)
    have hresult : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg hy0, if_pos hx0] at hok
      exact (Except.ok.inj hok).symm
    left
    apply Number.roundsNormalCell_of_exact result (x.toRat + y.toRat) L U
    · rw [hresult]; exact hy
    · exact hresultPos
    · rw [hresult, hxval, zero_add]
    · exact hL
    · exact hU
  by_cases hcancel : x.operator_eq y.operator_neg = true
  · have hzero := add_truth_zero_of_eq_neg x y hcancel
    linarith
  have hxm : x.mantissa_ ≠ 0 := by
    intro hm
    apply hx0
    rw [Number.eq_zero_of_mantissa_zero x hx hm]
    decide
  have hym : y.mantissa_ ≠ 0 := by
    intro hm
    apply hy0
    rw [Number.eq_zero_of_mantissa_zero y hy hm]
    decide
  have hrm : result.mantissa_ ≠ 0 := by
    intro hm
    have hz := Number.toRat_eq_zero_of_mantissa_zero result hm
    linarith
  have hround := operator_add_roundsCuspAware x y result hx hy hok htruth hresultPos
  obtain ⟨zm, ze', f, guard, resPos, loc, hfacts⟩ :=
    operator_add_algorithmic_facts_to_nearest x y result hx hy hxm hym hcancel hok hrm
  by_cases hdown : result.toRat ≤ x.toRat + y.toRat
  · obtain ⟨L', hL', hresultL⟩ := operator_add_rounded_branchA x y result hx hy
      hxm hym hcancel hok hrm hdown
    have hLL : L' = L := Option.some.inj (hL'.symm.trans hL)
    subst L'
    left
    exact Number.addFactsToNearest_down_roundsNormalCell x y result zm ze' f guard resPos loc
      hfacts L U hL hU hround hresultL
  · push_neg at hdown
    obtain ⟨U', hU', hresultU⟩ := operator_add_rounded_branchB x y result hx hy
      hxm hym hcancel hok hrm (le_of_lt hdown)
    have hUU : U' = U := Option.some.inj (hU'.symm.trans hU)
    subst U'
    exact Number.addFactsToNearest_up_roundsNormalCell_or_exceptionalCusp x y result zm ze' f
      guard resPos loc htruth hdown hfacts L U hL hU hresultU

end XRPL.Model.Protocol
