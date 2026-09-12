import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Add.Common.DirectedTight

/-! # Proof bodies for the IOU addition discrete/ULP (`RoundsToRepresentableWithin`)
headlines. The thin headlines live in `Add.RoundsToRepresentable`. -/

namespace XRPL.Model.Protocol

/-- The `to_nearest` case of `operator_add_repr_iou`, via the half-ULP re-rounding
bound. -/
theorem STAmount.operator_add_repr_iou_to_nearest_proof (v1 v2 result : STAmount)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (hok : STAmount.operator_add v1 v2 .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat + v2.toRat) .to_nearest 1 := by
  obtain ⟨xn, yn, sum, sumI, hrv, hexp_br, hofn, hsumI_ne, h_lo, h_hi, he_lo, he_hi,
      hxn_val, hyn_val, hxn_norm, hyn_norm, hxn_ne, hyn_ne, h_no_cancel, hsum_ne, hadd⟩ :=
    STAmount.operator_add_iou_decompose_anyMode v1 v2 result .to_nearest hc1 hc2
      h_truth_ne hok hresult
  have hexp : sum.exponent_ + 3 ≤ result.exponent := by
    rw [hexp_br]; exact IOUAmount.ofNumber_exp_ge sum .to_nearest sumI h_lo h_hi he_lo he_hi hofn hsumI_ne
  have hsnap : |result.toRat - sum.toRat| ≤ (1 / 2) * (10 : ℚ) ^ result.exponent := by
    rw [hrv]
    refine le_trans (IOUAmount.ofNumber_within_half_ulp sum sumI h_lo h_hi he_lo he_hi hofn hsumI_ne) ?_
    exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hexp) (by norm_num)
  have hr_ulp : |sum.toRat| ≤ 10 ^ 16 * (10 : ℚ) ^ result.exponent := by
    rw [abs_toRat_eq sum]
    have hkey : (sum.mantissa_.toNat : ℚ) * (10 : ℚ) ^ sum.exponent_
        ≤ 10 ^ 16 * (10 : ℚ) ^ (sum.exponent_ + 3) := by
      rw [show (10 : ℚ) ^ (sum.exponent_ + 3) = (10 : ℚ) ^ sum.exponent_ * (10 : ℚ) ^ (3 : ℤ) by
            rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)],
          show (10 : ℚ) ^ 16 * ((10 : ℚ) ^ sum.exponent_ * (10 : ℚ) ^ (3 : ℤ))
            = ((10 : ℚ) ^ 16 * (10 : ℚ) ^ (3 : ℤ)) * (10 : ℚ) ^ sum.exponent_ by ring,
          show (10 : ℚ) ^ 16 * (10 : ℚ) ^ (3 : ℤ) = (10 : ℚ) ^ 19 by norm_num]
      gcongr
      exact_mod_cast le_of_lt h_hi
    exact le_trans hkey (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hexp)
      (by positivity))
  have hop : |sum.toRat - (v1.toRat + v2.toRat)|
      ≤ |v1.toRat + v2.toRat| * (11 / (2 ^ 63 - 18 : ℚ)) := by
    have hb := operator_add_RoundsWithin_anyMode xn yn sum .to_nearest hxn_norm hyn_norm
      hxn_ne hyn_ne h_no_cancel hsum_ne hadd
    simp only [RoundsWithin] at hb
    rw [hxn_val, hyn_val, show RatValued.toRat sum = sum.toRat from rfl] at hb
    exact hb
  exact STAmount.RoundsToRepresentableWithin_of_double_round result sum (v1.toRat + v2.toRat)
    .to_nearest 1 (1 / 2) (11 / (2 ^ 63 - 18 : ℚ)) trivial hsnap hr_ulp hop (by positivity)
    (by norm_num) (by norm_num)

/-- Proof of `operator_add_repr_iou`: half-ULP re-rounding bound for `to_nearest`;
sign-split minimality argument for the directed modes. -/
theorem STAmount.operator_add_repr_iou_proof (v1 v2 result : STAmount)
    (mode : rounding_mode)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (h_truth_ne : v1.toRat + v2.toRat ≠ 0)
    (hok : STAmount.operator_add v1 v2 mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat + v2.toRat) mode 1 := by
  cases mode with
  | to_nearest =>
    exact STAmount.operator_add_repr_iou_to_nearest_proof v1 v2 result hc1 hc2 h_truth_ne
      hok hresult
  | upward =>
    rcases lt_or_gt_of_ne h_truth_ne with hneg | hpos
    · exact STAmount.operator_add_repr_iou_directed_core_neg v1 v2 result .upward
        (Or.inl rfl) hc1 hc2 h_truth_ne (le_of_lt hneg) hok hresult
    · exact STAmount.operator_add_repr_iou_directed_core v1 v2 result .upward
        (Or.inl rfl) hc1 hc2 h_truth_ne (le_of_lt hpos) hok hresult
  | downward =>
    rcases lt_or_gt_of_ne h_truth_ne with hneg | hpos
    · exact STAmount.operator_add_repr_iou_directed_core_neg v1 v2 result .downward
        (Or.inr (Or.inl rfl)) hc1 hc2 h_truth_ne (le_of_lt hneg) hok hresult
    · exact STAmount.operator_add_repr_iou_directed_core v1 v2 result .downward
        (Or.inr (Or.inl rfl)) hc1 hc2 h_truth_ne (le_of_lt hpos) hok hresult
  | towards_zero =>
    rcases lt_or_gt_of_ne h_truth_ne with hneg | hpos
    · exact STAmount.operator_add_repr_iou_directed_core_neg v1 v2 result .towards_zero
        (Or.inr (Or.inr rfl)) hc1 hc2 h_truth_ne (le_of_lt hneg) hok hresult
    · exact STAmount.operator_add_repr_iou_directed_core v1 v2 result .towards_zero
        (Or.inr (Or.inr rfl)) hc1 hc2 h_truth_ne (le_of_lt hpos) hok hresult

end XRPL.Model.Protocol
