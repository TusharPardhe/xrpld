import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight

/-! # Proof bodies for the IOU multiplication discrete/ULP (`RoundsToRepresentableWithin`)
headlines. The thin headlines live in `Mul.RoundsToRepresentable`. -/

namespace XRPL.Model.Protocol

/-- Proof of `operator_mul_repr_iou` (IOU multiply within 1 ULP, `to_nearest`). -/
theorem STAmount.operator_mul_repr_iou_proof (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .to_nearest = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ 10 ^ result.exponent := by
  obtain ⟨r, hofn, hr_lo, hr_hi, hr_exp_lo, hr_exp_hi, hop⟩ :=
    STAmount.operator_mul_iou_decompose v1 v2 result nt hnt
      hc1 hc2 hok hresult
  obtain ⟨hsnap_r, hexp⟩ := STAmount.ofNumber_iou_within_half_ulp nt r result hnt
    hr_lo hr_hi hr_exp_lo hr_exp_hi hofn hresult
  have hsnap : |result.toRat - r.toRat| ≤ (1 / 2) * (10 : ℚ) ^ result.exponent := by
    refine le_trans hsnap_r ?_
    exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hexp) (by norm_num)
  have hr_ulp : |r.toRat| ≤ 10 ^ 16 * (10 : ℚ) ^ result.exponent := by
    rw [abs_toRat_eq r]
    have hkey : (r.mantissa_.toNat : ℚ) * (10 : ℚ) ^ r.exponent_
        ≤ 10 ^ 16 * (10 : ℚ) ^ (r.exponent_ + 3) := by
      rw [show (10 : ℚ) ^ (r.exponent_ + 3) = (10 : ℚ) ^ r.exponent_ * (10 : ℚ) ^ (3 : ℤ) by
            rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)],
          show (10 : ℚ) ^ 16 * ((10 : ℚ) ^ r.exponent_ * (10 : ℚ) ^ (3 : ℤ))
            = ((10 : ℚ) ^ 16 * (10 : ℚ) ^ (3 : ℤ)) * (10 : ℚ) ^ r.exponent_ by ring,
          show (10 : ℚ) ^ 16 * (10 : ℚ) ^ (3 : ℤ) = (10 : ℚ) ^ 19 by norm_num]
      gcongr
      exact_mod_cast le_of_lt hr_hi
    exact le_trans hkey (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) hexp)
      (by positivity))
  have h := STAmount.double_round_abs_le result r (v1.toRat * v2.toRat) 1 (1 / 2)
    (5 / (2 ^ 63 + 7 : ℚ)) hsnap hr_ulp hop (by positivity) (by norm_num) (by norm_num)
  simpa using h

/-- Proof of `operator_mul_repr_iou_directed` (IOU multiply within **1** ULP, directed
modes, non-negative operands). The directed double rounding does not compound: because the
16-digit grid embeds in the 19-digit `Number` grid, the composed rounding equals a single
directed rounding of the exact product, hence lands within one ULP. The `to_nearest` case
reuses the dedicated half-ULP snap (`operator_mul_repr_iou_proof`); the three directed modes
use the `Number.upper`/`lower` minimality collapse (`operator_mul_repr_iou_directed_core`). -/
theorem STAmount.operator_mul_repr_iou_directed_proof (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    (mode = .downward → result.toRat ≤ v1.toRat * v2.toRat) ∧
     (mode = .upward   → v1.toRat * v2.toRat ≤ result.toRat) ∧
    |result.toRat - v1.toRat * v2.toRat| ≤ (10 : ℚ) ^ result.exponent := by
  have h : STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) mode 1 := by
    cases mode with
    | to_nearest =>
      exact ⟨trivial, by
        rw [Nat.cast_one, one_mul]
        exact STAmount.operator_mul_repr_iou_proof v1 v2 result nt hnt hc1 hc2 hok hresult⟩
    | upward =>
      exact STAmount.operator_mul_repr_iou_directed_core v1 v2 result nt .upward
        (Or.inl rfl) hnt hc1 hc2 hn1 hn2 hok hresult
    | downward =>
      exact STAmount.operator_mul_repr_iou_directed_core v1 v2 result nt .downward
        (Or.inr (Or.inl rfl)) hnt hc1 hc2 hn1 hn2 hok hresult
    | towards_zero =>
      exact STAmount.operator_mul_repr_iou_directed_core v1 v2 result nt .towards_zero
        (Or.inr (Or.inr rfl)) hnt hc1 hc2 hn1 hn2 hok hresult
  have hbound := h.2
  rw [Nat.cast_one, one_mul] at hbound
  have hdir := h.1
  refine ⟨?_, ?_, hbound⟩
  · intro hm; subst hm; exact hdir
  · intro hm; subst hm; exact hdir

/-- Proof of `operator_mul_iou_within_1ulp` (IOU multiply accuracy **1** ULP, any sign/mode).
Dispatches to the half-ULP `to_nearest` snap, the magnitude `towards_zero` collapse, and the
`upward`/`downward` mixed-direction magnitude bound; each lands within one ULP. -/
theorem STAmount.operator_mul_iou_within_1ulp_proof (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ (10 : ℚ) ^ result.exponent := by
  cases mode with
  | to_nearest =>
    exact STAmount.operator_mul_repr_iou_proof v1 v2 result nt hnt hc1 hc2 hok hresult
  | upward =>
    exact STAmount.operator_mul_iou_directed_mag_one v1 v2 result nt .upward (Or.inl rfl)
      hnt hc1 hc2 hok hresult
  | downward =>
    exact STAmount.operator_mul_iou_directed_mag_one v1 v2 result nt .downward (Or.inr rfl)
      hnt hc1 hc2 hok hresult
  | towards_zero =>
    exact STAmount.operator_mul_iou_towards_zero_one v1 v2 result nt hnt
      hc1 hc2 hok hresult

/-- Proof of `operator_mul_iou_abs_le_towards_zero` (magnitude never increases). -/
theorem STAmount.operator_mul_iou_abs_le_towards_zero_proof (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat| ≤ |v1.toRat * v2.toRat| := by
  obtain ⟨r, hofn, hr_lo, hr_hi, hr_exp_lo, hr_exp_hi, _, hmb⟩ :=
    STAmount.operator_mul_iou_decompose_mag v1 v2 result nt .towards_zero hnt
      hc1 hc2 hok hresult
  exact le_trans
    (STAmount.ofNumber_iou_abs_le_towards_zero nt r result hnt hr_lo hr_hi
      hr_exp_lo hr_exp_hi hofn hresult)
    hmb.1

end XRPL.Model.Protocol
