import XRPL.Properties.Protocol.Number.Mul.Common.ToNearest.RoundedHelpers
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.RoundedHelpers
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Div.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact
import XRPL.Properties.Protocol.Number.Common.Closest.Gap
import XRPL.Properties.Protocol.Number.Common.Rounding.DoRoundUp.ValueChar

/-! # Monotonicity core for the `Number` round-to-nearest layer

Operation-agnostic building blocks for the vault `deposit_shares_monotone` /
`withdraw_raw_payout_monotone` claims, via the no-inbetween route (not the
`RoundsNearestEven` cusp-band route). Final debit monotonicity is separately
transported through the source-faithful post-sum clamp.

`Number.NearestTo r t` states that `r` is a nearest representable to the exact
value `t`. Round-to-nearest monotonicity follows from `NearestTo` for both results
plus determinism at an exact tie (`round_mono_core`, `operator_mul_left_mono_of_nearest`,
`operator_div_num_mono_of_nearest`).

Contents:

* `round_mono_core`: the order-theoretic reduction. Two results that are each a
  nearest representable to their ordered exact truths, with deterministic rounding
  at an exact tie, are ordered.

* `Number.nearestTo_of_gap` and `doRoundUp_clean_down_up`: establish `NearestTo`
  for a positive truth whose scaled mantissa lies in the regular grid range
  (`mantissaFloorSucc ≤ zm < 10^19`), from the round direction (`f ⋛ 1/2` via
  `round_correct`), the `doRoundUp` value, and the unit-cell grid gap
  (`no_normalized_in_open_ulp_gap_pos_zm`).

* `operator_mul_to_nearest_le/_ge`, `operator_div_to_nearest_le/_ge`: a rounded
  result respects a representable comparison point (mirrors
  `Number.operator_sub_to_nearest_le/_ge`).

* `operator_mul_toRat_eq_of_truth_eq`, `operator_div_toRat_eq_of_truth_eq`:
  determinism at a tie, via `Number.isNormalized.toRat_inj`.

* `operator_mul_left_mono_of_nearest`, `operator_div_num_mono_of_nearest`: the
  packaged one-operand monotonicity of the rounded operation, taking `NearestTo`
  for both results.

`nearestTo_of_gap` covers the regular grid range, where the model rounds to the
nearer of the two grid neighbours. At the scaled-mantissa floor (`zm = mantissaFloor`,
where the invariant forces `f ≥ 8/10`) and the cusp band (`maxRep < zm ≤ maxRepUp`)
the model can round to the farther neighbour, so `NearestTo` is not the operative
property there and those bands are not covered by `nearestTo_of_gap`. -/

namespace XRPL.Model.Protocol

/-! ## Layer 1: the order-theoretic reduction -/

/-- `r` is a nearest representable to the exact value `t`: no normalized `Number`
is strictly closer to `t` than `r` is. This is what round-to-nearest delivers. -/
def Number.NearestTo (r : Number) (t : ℚ) : Prop :=
  ∀ m : Number, m.isNormalized → |r.toRat - t| ≤ |m.toRat - t|

/-- **Round-to-nearest is monotone.** If `t₁ ≤ t₂`, each `rᵢ` is a nearest
representable to `tᵢ`, and the rounding is deterministic at a tie (`t₁ = t₂ ⟹
r₁ = r₂` as values), then `r₁.toRat ≤ r₂.toRat`.

The only way a strict inversion `r₂ < r₁` can hold is at an exact tie: the two
"nearest" inequalities force `t₁` above and `t₂` below the shared midpoint
`(r₁+r₂)/2`, which with `t₁ ≤ t₂` collapses to `t₁ = t₂`, and determinism then
equates the results. -/
theorem round_mono_core (t₁ t₂ : ℚ) (r₁ r₂ : Number)
    (h₁ : r₁.NearestTo t₁) (h₂ : r₂.NearestTo t₂)
    (hr₁ : r₁.isNormalized) (hr₂ : r₂.isNormalized)
    (hle : t₁ ≤ t₂) (hdet : t₁ = t₂ → r₁.toRat = r₂.toRat) :
    r₁.toRat ≤ r₂.toRat := by
  by_contra hcon
  push_neg at hcon
  -- distances, squared: `r₁` is at least as close to `t₁` as `r₂`, and vice versa
  have e1 : |r₁.toRat - t₁| ≤ |r₂.toRat - t₁| := h₁ r₂ hr₂
  have e2 : |r₂.toRat - t₂| ≤ |r₁.toRat - t₂| := h₂ r₁ hr₁
  have hsq1 : (r₁.toRat - t₁) * (r₁.toRat - t₁) ≤ (r₂.toRat - t₁) * (r₂.toRat - t₁) := by
    have h := mul_self_le_mul_self (abs_nonneg (r₁.toRat - t₁)) e1
    rwa [abs_mul_abs_self, abs_mul_abs_self] at h
  have hsq2 : (r₂.toRat - t₂) * (r₂.toRat - t₂) ≤ (r₁.toRat - t₂) * (r₁.toRat - t₂) := by
    have h := mul_self_le_mul_self (abs_nonneg (r₂.toRat - t₂)) e2
    rwa [abs_mul_abs_self, abs_mul_abs_self] at h
  -- midpoint pinning: with `r₂ < r₁`, `hsq1 ⟹ r₁+r₂ ≤ 2t₁`, `hsq2 ⟹ 2t₂ ≤ r₁+r₂`
  have hmid1 : r₁.toRat + r₂.toRat ≤ 2 * t₁ := by nlinarith [hsq1, hcon]
  have hmid2 : 2 * t₂ ≤ r₁.toRat + r₂.toRat := by nlinarith [hsq2, hcon]
  have hteq : t₁ = t₂ := le_antisymm hle (by linarith [hmid1, hmid2])
  linarith [hdet hteq, hcon]

/-! ## Layer 1b: `NearestTo` from a clean grid cell

For a positive truth `t = (zm + f)·10^ze'` in the regular grid range
(`mantissaFloorSucc ≤ zm < 10^19`), a result equal to `zm·10^ze'` with `f ≤ 1/2`,
or `(zm+1)·10^ze'` with `f ≥ 1/2`, is a nearest representable. The far side is
closed by the grid-gap lemma `no_normalized_in_open_ulp_gap_pos_zm` (no normalized
value sits strictly inside a unit grid cell, cusp invariant included). -/

/-- A rounded-down (`r = zm·10^ze'`, `f ≤ 1/2`) or rounded-up
(`r = (zm+1)·10^ze'`, `f ≥ 1/2`) result on a regular grid cell is a nearest
representable to the positive truth `t = (zm+f)·10^ze'`. -/
theorem Number.nearestTo_of_gap (t f : ℚ) (zm : UInt64) (ze' : Int) (r : Number)
    (hpos : 0 < t)
    (hval : t = ((zm.toNat : ℚ) + f) * 10 ^ ze')
    (hf_nn : 0 ≤ f) (hf_lt : f < 1)
    (hzm_lo : mantissaFloorSucc ≤ zm.toNat)
    (hzm_hi : zm.toNat < 10 ^ 19)
    (hcase : (r.toRat = (zm.toNat : ℚ) * 10 ^ ze' ∧ f ≤ 1 / 2)
           ∨ (r.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' ∧ 1 / 2 ≤ f)) :
    r.NearestTo t := by
  intro m hm
  have hpow : (0 : ℚ) < (10 : ℚ) ^ ze' := zpow_pos (by norm_num) _
  have hzm_pos : (0 : ℚ) < (zm.toNat : ℚ) := by
    have : (0 : ℕ) < zm.toNat := by
      have : (0 : ℕ) < mantissaFloorSucc := by norm_num
      omega
    exact_mod_cast this
  rcases hcase with ⟨hr, hf_le⟩ | ⟨hr, hf_ge⟩
  · -- rounded down: r = zm·10^ze', within `f·10^ze'` below `t`
    rw [hr, hval]
    by_cases hmL : m.toRat ≤ (zm.toNat : ℚ) * 10 ^ ze'
    · rw [abs_of_nonpos (by nlinarith [hpow, hf_nn]),
          abs_of_nonpos (by nlinarith [hpow, hmL, hf_nn])]
      nlinarith [hpow, hmL]
    · push_neg at hmL
      have hmpos : 0 < m.toRat := lt_trans (by positivity) hmL
      have hmge : ((zm.toNat : ℚ) + 1) * 10 ^ ze' ≤ m.toRat := by
        by_contra hlt
        push_neg at hlt
        exact no_normalized_in_open_ulp_gap_pos_zm ze' zm.toNat hzm_lo hzm_hi m hm hmpos hmL hlt
      rw [abs_of_nonpos (by nlinarith [hpow, hf_nn]),
          abs_of_nonneg (by nlinarith [hpow, hmge])]
      nlinarith [hpow, hmge, hf_le]
  · -- rounded up: r = (zm+1)·10^ze', within `(1-f)·10^ze'` above `t`
    rw [hr, hval]
    by_cases hmU : ((zm.toNat : ℚ) + 1) * 10 ^ ze' ≤ m.toRat
    · rw [abs_of_nonneg (by nlinarith [hpow, hf_lt]),
          abs_of_nonneg (by nlinarith [hpow, hmU, hf_lt])]
      nlinarith [hpow, hmU]
    · push_neg at hmU
      have hmle : m.toRat ≤ (zm.toNat : ℚ) * 10 ^ ze' := by
        by_cases hmpos : 0 < m.toRat
        · by_contra hgt
          push_neg at hgt
          exact no_normalized_in_open_ulp_gap_pos_zm ze' zm.toNat hzm_lo hzm_hi m hm hmpos hgt hmU
        · push_neg at hmpos
          nlinarith [hpow, hzm_pos, hmpos]
      rw [abs_of_nonneg (by nlinarith [hpow, hf_lt]),
          abs_of_nonpos (by nlinarith [hpow, hmle, hf_lt])]
      nlinarith [hpow, hmle, hf_ge]

/-- **Direction + value at a clean `doRoundUp` cell.** For a positive result on the
regular range (`zm ≤ maxRep - 1`), the round-to-nearest `doRoundUp` output is either
`zm·10^ze'` with fractional position `f ≤ 1/2` (round down), or `(zm+1)·10^ze'` with
`f ≥ 1/2` (round up). Shared by `operator_mul` and `operator_div` (both funnel the
same `g, zm, ze', f`). -/
theorem doRoundUp_clean_down_up (g : Guard) (zm : UInt64) (ze' : Int) (f : ℚ)
    (res_pos : RoundResult) (result : Number) (loc : Error)
    (hf_rep : represents g f)
    (hrounds : g.doRoundUp false zm ze' largeRange.min largeRange.max .to_nearest loc
      = .ok res_pos)
    (habs : result.toRat = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_)
    (hres_ne : res_pos.mantissa_ ≠ 0)
    (hzm_hi : zm.toNat + 1 ≤ maxRep.toNat) :
    (result.toRat = (zm.toNat : ℚ) * 10 ^ ze' ∧ f ≤ 1 / 2)
  ∨ (result.toRat = ((zm.toNat : ℚ) + 1) * 10 ^ ze' ∧ 1 / 2 ≤ f) := by
  by_cases hru : g.shouldRoundUp_to_nearest zm
  · right
    have hval := doRoundUp_value_to_nearest_roundUp_noCusp g zm ze' hru hzm_hi loc res_pos
      hrounds hres_ne
    refine ⟨by rw [habs, hval], ?_⟩
    rcases hru with h1 | ⟨h0, _⟩
    · exact le_of_lt (represents_round_eq_one hf_rep h1)
    · exact le_of_eq (represents_round_eq_zero hf_rep h0).symm
  · left
    have hzm_le : zm.toNat ≤ maxRep.toNat := by omega
    have hval := doRoundUp_value_no_roundUp g zm ze' hru hzm_le loc res_pos hrounds hres_ne
    refine ⟨by rw [habs, hval], ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hru (Or.inl (represents_f_gt_half hf_rep hlt))

/-- **`NearestTo` for an `operator_mul` result on the regular grid range.** From the
`operator_mul` algorithmic decomposition (`MulFactsToNearest`) with a positive product
and a scaled mantissa in `[mantissaFloorSucc, maxRep - 1]`, the result is a nearest
representable to the exact product. Composes `doRoundUp_clean_down_up` (round direction
and value) with `Number.nearestTo_of_gap` (the grid gap). -/
theorem mul_nearestTo_of_facts (x y r : Number) (zm : UInt64) (ze' : Int) (f : ℚ)
    (g : Guard) (res_pos : RoundResult)
    (hfacts : MulFactsToNearest x y r .to_nearest zm ze' f g res_pos)
    (hpos : 0 < x.toRat * y.toRat)
    (hzm_lo : mantissaFloorSucc ≤ zm.toNat)
    (hzm_hi : zm.toNat + 1 ≤ maxRep.toNat) :
    r.NearestTo (x.toRat * y.toRat) := by
  have htruth : x.toRat * y.toRat = ((zm.toNat : ℚ) + f) * 10 ^ ze' := by
    rw [← abs_of_pos hpos]; exact hfacts.value_eq
  have hrnn : 0 ≤ r.toRat := mul_result_nonneg_of_truth_pos x y r hfacts.result_neg hpos
  have habs : r.toRat = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_ := by
    rw [← abs_of_nonneg hrnn]; exact hfacts.result_abs
  have hcase := doRoundUp_clean_down_up g zm ze' f res_pos r _ hfacts.represents_f
    hfacts.rounds habs hfacts.res_mant_ne hzm_hi
  have hzm_lt : zm.toNat < 10 ^ 19 := by
    have hm : maxRep.toNat = 9223372036854775807 := maxRep_val
    omega
  exact Number.nearestTo_of_gap (x.toRat * y.toRat) f zm ze' r hpos htruth
    hfacts.f_nonneg hfacts.f_lt_one hzm_lo hzm_lt hcase

/-! ## Layer 2: a rounded result respects representable comparison points -/

/-- A `to_nearest` product is at most any representable `z` bounding the exact
product from above. No representable lies strictly between the truth and a value
above `z` (`operator_mul_no_inbetween_above`). -/
lemma Number.operator_mul_to_nearest_le (x y z r : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hok : Number.operator_mul x y .to_nearest = .ok r) (hres : r.mantissa_ ≠ 0)
    (hz_ge : x.toRat * y.toRat ≤ z.toRat) : r.toRat ≤ z.toRat := by
  by_contra hlt
  push_neg at hlt
  have h_ge : x.toRat * y.toRat ≤ r.toRat := le_trans hz_ge (le_of_lt hlt)
  exact operator_mul_no_inbetween_above x y r hx hy hxm hym hok hres h_ge z hz hlt hz_ge

/-- A `to_nearest` product is at least any representable `z` bounding the exact
product from below (`operator_mul_no_inbetween_below_to_nearest`). -/
lemma Number.operator_mul_to_nearest_ge (x y z r : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hok : Number.operator_mul x y .to_nearest = .ok r) (hres : r.mantissa_ ≠ 0)
    (hz_le : z.toRat ≤ x.toRat * y.toRat) : z.toRat ≤ r.toRat := by
  by_contra hlt
  push_neg at hlt
  have h_le : r.toRat ≤ x.toRat * y.toRat := le_trans (le_of_lt hlt) hz_le
  exact operator_mul_no_inbetween_below_to_nearest x y r hx hy hxm hym hok hres h_le z hz hlt hz_le

/-- A `to_nearest` quotient is at most any representable `z` bounding the exact
quotient from above (`operator_div_no_inbetween_above`). -/
lemma Number.operator_div_to_nearest_le (x y z r : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hok : Number.operator_div x y .to_nearest = .ok r) (hres : r.mantissa_ ≠ 0)
    (hz_ge : x.toRat / y.toRat ≤ z.toRat) : r.toRat ≤ z.toRat := by
  by_contra hlt
  push_neg at hlt
  have h_ge : x.toRat / y.toRat ≤ r.toRat := le_trans hz_ge (le_of_lt hlt)
  exact operator_div_no_inbetween_above x y r hx hy hxm hym hok hres h_ge z hz hlt hz_ge

/-- A `to_nearest` quotient is at least any representable `z` bounding the exact
quotient from below (`operator_div_no_inbetween_below_to_nearest`). -/
lemma Number.operator_div_to_nearest_ge (x y z r : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hz : z.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (hym : y.mantissa_ ≠ 0)
    (hok : Number.operator_div x y .to_nearest = .ok r) (hres : r.mantissa_ ≠ 0)
    (hz_le : z.toRat ≤ x.toRat / y.toRat) : z.toRat ≤ r.toRat := by
  by_contra hlt
  push_neg at hlt
  have h_le : r.toRat ≤ x.toRat / y.toRat := le_trans (le_of_lt hlt) hz_le
  exact operator_div_no_inbetween_below_to_nearest x y r hx hy hxm hym hok hres h_le z hz hlt hz_le

/-! ## Layer 3: determinism at a tie -/

/-- Determinism of `operator_mul` at a tie: equal exact products (with a fixed
nonzero left factor) give equal results. Normalized inputs with equal value are
equal (`toRat_inj`), so the calls coincide. -/
theorem operator_mul_toRat_eq_of_truth_eq (x y₁ y₂ r₁ r₂ : Number)
    (hy₁ : y₁.isNormalized) (hy₂ : y₂.isNormalized)
    (hok₁ : Number.operator_mul x y₁ .to_nearest = .ok r₁)
    (hok₂ : Number.operator_mul x y₂ .to_nearest = .ok r₂)
    (hx : x.toRat ≠ 0)
    (heq : x.toRat * y₁.toRat = x.toRat * y₂.toRat) :
    r₁.toRat = r₂.toRat := by
  have hy : y₁.toRat = y₂.toRat := mul_left_cancel₀ hx heq
  have hyy : y₁ = y₂ := hy₁.toRat_inj hy₂ hy
  subst hyy
  rw [Except.ok.inj (hok₁.symm.trans hok₂)]

/-- Determinism of `operator_div` at a tie: equal exact quotients (with a fixed
nonzero divisor) give equal results. -/
theorem operator_div_toRat_eq_of_truth_eq (a₁ a₂ b r₁ r₂ : Number)
    (ha₁ : a₁.isNormalized) (ha₂ : a₂.isNormalized)
    (hok₁ : Number.operator_div a₁ b .to_nearest = .ok r₁)
    (hok₂ : Number.operator_div a₂ b .to_nearest = .ok r₂)
    (hb : b.toRat ≠ 0)
    (heq : a₁.toRat / b.toRat = a₂.toRat / b.toRat) :
    r₁.toRat = r₂.toRat := by
  have ha : a₁.toRat = a₂.toRat := by
    have h := heq
    rw [div_eq_div_iff hb hb] at h
    exact mul_right_cancel₀ hb h
  have haa : a₁ = a₂ := ha₁.toRat_inj ha₂ ha
  subst haa
  rw [Except.ok.inj (hok₁.symm.trans hok₂)]

/-! ## Layer 4: the packaged monotonicity reductions

Given that each result is a nearest representable to its exact truth (`NearestTo`,
established by `nearestTo_of_gap` on the clean grid range), `round_mono_core`
plus the tie-determinism lemma delivers monotonicity of the rounded operation in
one operand. These are the composable statements the vault pipeline consumes. -/

/-- **`operator_mul` is monotone in one factor at `.to_nearest`.** For a fixed
positive left factor `x`, given both results are nearest representables to their
exact products, a larger second factor never rounds to a smaller product. -/
theorem operator_mul_left_mono_of_nearest (x y₁ y₂ r₁ r₂ : Number)
    (hy₁ : y₁.isNormalized) (hy₂ : y₂.isNormalized)
    (hr₁ : r₁.isNormalized) (hr₂ : r₂.isNormalized)
    (hok₁ : Number.operator_mul x y₁ .to_nearest = .ok r₁)
    (hok₂ : Number.operator_mul x y₂ .to_nearest = .ok r₂)
    (hn₁ : r₁.NearestTo (x.toRat * y₁.toRat))
    (hn₂ : r₂.NearestTo (x.toRat * y₂.toRat))
    (hx : 0 < x.toRat) (hle : y₁.toRat ≤ y₂.toRat) :
    r₁.toRat ≤ r₂.toRat :=
  round_mono_core _ _ r₁ r₂ hn₁ hn₂ hr₁ hr₂
    (mul_le_mul_of_nonneg_left hle (le_of_lt hx))
    (fun heq => operator_mul_toRat_eq_of_truth_eq x y₁ y₂ r₁ r₂ hy₁ hy₂ hok₁ hok₂
      (ne_of_gt hx) heq)

/-- **`operator_div` is monotone in the numerator at `.to_nearest`.** For a fixed
positive divisor `b`, given both results are nearest representables to their exact
quotients, a larger numerator never rounds to a smaller quotient. -/
theorem operator_div_num_mono_of_nearest (a₁ a₂ b r₁ r₂ : Number)
    (ha₁ : a₁.isNormalized) (ha₂ : a₂.isNormalized)
    (hr₁ : r₁.isNormalized) (hr₂ : r₂.isNormalized)
    (hok₁ : Number.operator_div a₁ b .to_nearest = .ok r₁)
    (hok₂ : Number.operator_div a₂ b .to_nearest = .ok r₂)
    (hn₁ : r₁.NearestTo (a₁.toRat / b.toRat))
    (hn₂ : r₂.NearestTo (a₂.toRat / b.toRat))
    (hb : 0 < b.toRat) (hle : a₁.toRat ≤ a₂.toRat) :
    r₁.toRat ≤ r₂.toRat :=
  round_mono_core _ _ r₁ r₂ hn₁ hn₂ hr₁ hr₂
    (by gcongr)
    (fun heq => operator_div_toRat_eq_of_truth_eq a₁ a₂ b r₁ r₂ ha₁ ha₂ hok₁ hok₂
      (ne_of_gt hb) heq)

end XRPL.Model.Protocol
