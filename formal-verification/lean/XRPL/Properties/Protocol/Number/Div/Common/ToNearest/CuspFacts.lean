import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Div.Common.ToNearest.RoundedHelpers
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize128.RoundFacts

namespace XRPL.Model.Protocol

/-! # `operator_div` cusp-aware algorithmic facts (`.to_nearest`)

Div analog of `MulFactsToNearest` / `operator_mul_algorithmic_facts_to_nearest`, but
carrying the *tight* round-decision facts (`round ⋛ 1 ↔ f ⋛ 1/2`) instead of
`represents g f` (which is false for the div path, whose guard tracks only the top
dropped digits with a residual tail). -/

/-- The div-side facts bundle consumed by `operator_div_roundsCuspAware`. -/
structure DivFactsToNearest (x y result : Number) (mode : rounding_mode)
    (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult) : Prop where
  zm_ge_floor : mantissaFloor ≤ zm.toNat
  zm_le_maxRepUp : zm.toNat ≤ maxRepUp.toNat
  f_nonneg : 0 ≤ f
  f_lt_one : f < 1
  floor_cusp : zm.toNat = mantissaFloor → (8 : ℚ) / 10 ≤ f
  value_eq : |x.toRat / y.toRat| = ((zm.toNat : ℚ) + f) * 10 ^ ze'
  rounds : g.doRoundUp false zm ze' largeRange.min largeRange.max mode
    .normalize2 = .ok res_pos
  result_abs : |result.toRat| = (res_pos.mantissa_.toNat : ℚ) * 10 ^ res_pos.exponent_
  res_mant_ne : res_pos.mantissa_ ≠ 0
  result_nonneg : 0 < x.toRat / y.toRat → 0 ≤ result.toRat
  round_eq_one : g.round .to_nearest = 1 → f > 1 / 2
  round_eq_zero : g.round .to_nearest = 0 → f = 1 / 2
  f_gt_half : f > 1 / 2 → g.round .to_nearest = 1
  f_eq_half : f = 1 / 2 → g.round .to_nearest = 0

theorem operator_div_algorithmic_facts_to_nearest (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (hok : Number.operator_div x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0) :
    ∃ (zm : UInt64) (ze' : Int) (f : ℚ) (g : Guard) (res_pos : RoundResult),
      DivFactsToNearest x y result .to_nearest zm ze' f g res_pos := by
  obtain ⟨M, ze0, δ, zn, sticky, hδ_low, _hδ_le, hsticky_zero, hM_pos, hM_lt, hδM,
      htruth, hok128, hsign, hδ_lt, hsticky_pos⟩ :=
    operator_div_algorithmic_facts_represents x y result .to_nearest hx hy
      hx_mant_ne hy_mant_ne hok
  obtain ⟨zm, ze', f, g, res_pos, hzm_ge, hzm_le, hf_nn, hf_lt, hfloor, h_value,
      h_rup, h_abs, hres_mant, h_neg, _hzm_succ, hround1, hround0, hfgt, hfeq⟩ :=
    doNormalize128_algorithmic_facts_round zn M ze0 δ sticky .to_nearest hδ_low hδ_lt
      hsticky_zero hsticky_pos hM_pos hM_lt hδM result hok128 hresult
  have value_eq : |x.toRat / y.toRat| = ((zm.toNat : ℚ) + f) * 10 ^ ze' :=
    htruth.trans h_value
  have result_nonneg : 0 < x.toRat / y.toRat → 0 ≤ result.toRat := fun hpos => by
    have hzn := zn_eq_false_of_pos hsign.1 hpos
    exact Number.toRat_nonneg_of_nonnegative result (h_neg.trans hzn)
  exact ⟨zm, ze', f, g, res_pos,
    ⟨hzm_ge, hzm_le, hf_nn, hf_lt, hfloor, value_eq, h_rup, h_abs, hres_mant,
     result_nonneg, hround1, hround0, hfgt, hfeq⟩⟩

/-! ## Branch identification (div analogs of `operator_mul_rounded_branchA/B`) -/

/-- Round-down cell: `result = lower(x/y)`. -/
theorem operator_div_rounded_branchA (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (hok : Number.operator_div x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0)
    (h_round_down : result.toRat ≤ x.toRat / y.toRat)
    (h_no_inbetween : ∀ m : Number, m.isNormalized →
                       result.toRat < m.toRat → ¬ (m.toRat ≤ x.toRat / y.toRat)) :
    ∃ n_lo : Number, Number.lower (x.toRat / y.toRat) = some n_lo ∧
                     result.toRat = n_lo.toRat := by
  have h5 := operator_div_rounding_bound_to_nearest x y result hx hy hx_mant_ne hy_mant_ne hok hresult
  have h_result_norm : result.isNormalized :=
    operator_div_result_isNormalized x y result .to_nearest hx hy hx_mant_ne hy_mant_ne hok hresult
  have h_truth_ne : x.toRat / y.toRat ≠ 0 := operator_div_truth_ne x y hx_mant_ne hy_mant_ne
  have h_bound : |result.toRat - x.toRat / y.toRat|
      ≤ |x.toRat / y.toRat| * (11 / (2 ^ 63 - 18 : ℚ)) :=
    le_trans h5 (mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _))
  have h_truth_top : result.exponent_ ≥ maxExponent →
      |x.toRat / y.toRat| < 10 ^ 19 * (10 : ℚ) ^ (maxExponent : ℤ) := fun h =>
    truth_top_of_result_cap result (x.toRat / y.toRat) h_result_norm hresult h_bound
      (operator_div_no_overflow_mantissa x y result .to_nearest hx hy hx_mant_ne hy_mant_ne hok hresult h) h
  exact closest_lower_of_no_inbetween result (x.toRat / y.toRat) h_result_norm hresult
    h_truth_ne h_bound h_truth_top h_round_down h_no_inbetween

/-- Round-up cell: `result = upper(x/y)`. -/
theorem operator_div_rounded_branchB (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hx_mant_ne : x.mantissa_ ≠ 0) (hy_mant_ne : y.mantissa_ ≠ 0)
    (hok : Number.operator_div x y .to_nearest = .ok result)
    (hresult : result.mantissa_ ≠ 0)
    (h_round_up : x.toRat / y.toRat ≤ result.toRat)
    (h_no_inbetween : ∀ m : Number, m.isNormalized →
                       m.toRat < result.toRat → ¬ (x.toRat / y.toRat ≤ m.toRat)) :
    ∃ n_up : Number, Number.upper (x.toRat / y.toRat) = some n_up ∧
                     result.toRat = n_up.toRat := by
  have h5 := operator_div_rounding_bound_to_nearest x y result hx hy hx_mant_ne hy_mant_ne hok hresult
  have h_result_norm : result.isNormalized :=
    operator_div_result_isNormalized x y result .to_nearest hx hy hx_mant_ne hy_mant_ne hok hresult
  have h_truth_ne : x.toRat / y.toRat ≠ 0 := operator_div_truth_ne x y hx_mant_ne hy_mant_ne
  have h_bound : |result.toRat - x.toRat / y.toRat|
      ≤ |x.toRat / y.toRat| * (11 / (2 ^ 63 - 18 : ℚ)) :=
    le_trans h5 (mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _))
  have h_truth_top : result.exponent_ ≥ maxExponent →
      |x.toRat / y.toRat| < 10 ^ 19 * (10 : ℚ) ^ (maxExponent : ℤ) := fun h =>
    truth_top_of_result_cap result (x.toRat / y.toRat) h_result_norm hresult h_bound
      (operator_div_no_overflow_mantissa x y result .to_nearest hx hy hx_mant_ne hy_mant_ne hok hresult h) h
  exact closest_upper_of_no_inbetween result (x.toRat / y.toRat) h_result_norm hresult
    h_truth_ne h_bound h_truth_top h_round_up h_no_inbetween

end XRPL.Model.Protocol
