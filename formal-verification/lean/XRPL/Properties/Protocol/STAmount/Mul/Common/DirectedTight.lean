import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedSupport
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangePos
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.GridNeighbors

/-! # IOU multiplication is within **1 ULP** for directed modes (non-negative operands).

The double rounding of the IOU `multiply` pipeline (19-digit `Number` product, then the
16-digit `ofNumber` snap) does **not** compound for the directed modes: because the
16-digit grid is a subgrid of the 19-digit grid, the composed rounding equals a single
directed rounding of the exact product, hence lands within one ULP.

The engine is a minimality argument: the `Number` product `r` is the *least* representable
`Number ≥ truth` (`upward`) / *greatest* `≤ truth` (`downward`), and the 16-digit snap is
an exact fixed-scale ceiling/floor. The adjacent 16-digit grid point on the far side of
`result` is itself a representable `Number`, so minimality pins `result` to within one ULP
of `truth`. -/

namespace XRPL.Model.Protocol

/-- **Raw `ofNumber` snap facts for a non-negative 19-digit `Number` `r`.** Exposes the
`normalizeToRange` output `(mant, exp)`, the grid form of `result`, and the exponent
range. The engine for the exact ceiling/floor characterization of the 16-digit snap. -/
lemma STAmount.ofNumber_iou_snap_pos (nt : NumericType) (r : Number) (mode : rounding_mode)
    (result : STAmount)
    (hnt : nt = .fractional)
    (hr_neg : r.negative_ = false)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r mode = .ok result) (hresult : result.mValue ≠ 0) :
    ∃ (mant : Int64) (exp : ℤ),
      r.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) ∧
      result.toRat = (mant.toInt : ℚ) * 10 ^ exp ∧
      result.exponent = exp ∧
      (mant.toInt : ℚ) = ((mant.toUInt64.toNat : ℕ) : ℚ) ∧
      10 ^ 15 ≤ mant.toUInt64.toNat ∧ mant.toUInt64.toNat < 10 ^ 16 ∧
      (-96 : ℤ) ≤ exp ∧ exp ≤ 80 := by
  subst hnt
  have hr_ne : r.mantissa_ ≠ 0 := by intro h; rw [h] at hr_lo; simp at hr_lo
  have hmne : (r.mantissa_ != 0) = true := by simp [hr_ne]
  have hneg_eq : decide (r.signum < 0) = r.negative_ := by
    unfold Number.signum
    rcases hrn : r.negative_ with _ | _ <;> simp only [hmne, if_true, if_false,
      Bool.false_eq_true] <;> decide
  set neg : Bool := decide (r.signum < 0) with hneg_def
  have hneg_false : neg = false := by rw [hneg_eq]; exact hr_neg
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_eq : working = r := by rw [hw_def, hneg_false]; simp
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_eq]; exact hr_lo
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_eq]; exact hr_hi
  have hwe_lo : minExponent ≤ working.exponent_ + 3 := by rw [hw_eq]; omega
  have hwe_hi : working.exponent_ + 4 ≤ maxExponent := by rw [hw_eq]; exact hre_hi
  have hw_neg : working.negative_ = false := by rw [hw_eq]; exact hr_neg
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide), ← hneg_def, ← hw_def] at hok
  cases hnorm : working.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : working.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hbound := normalizeToRange_16_within_ulp working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hmrange := normalizeToRange_16_mantissa_range working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have herange := normalizeToRange_16_exp_range working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
    have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
    have hwlarge : (10 : ℚ) ^ (working.exponent_ + 18) ≤ working.toRat := by
      rw [Number.toRat_of_nonneg working hw_neg]
      have h1018 : (10 : ℚ) ^ (18 : ℤ) ≤ (working.mantissa_.toNat : ℚ) := by
        have : ((10 ^ 18 : ℕ) : ℚ) ≤ (working.mantissa_.toNat : ℚ) := by exact_mod_cast hw_lo
        rwa [show ((10 ^ 18 : ℕ) : ℚ) = (10 : ℚ) ^ (18 : ℤ) by push_cast; norm_num] at this
      calc (10 : ℚ) ^ (working.exponent_ + 18)
          = (10 : ℚ) ^ (18 : ℤ) * (10 : ℚ) ^ working.exponent_ := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring_nf
        _ ≤ (working.mantissa_.toNat : ℚ) * (10 : ℚ) ^ working.exponent_ := by gcongr
    have hmant_pos : 0 ≤ mant.toInt := by
      by_contra hc
      push_neg at hc
      have hmant_neg_q : (mant.toInt : ℚ) < 0 := by exact_mod_cast hc
      have hval_neg : (mant.toInt : ℚ) * 10 ^ exp < 0 :=
        mul_neg_of_neg_of_pos hmant_neg_q (zpow_pos (by norm_num) _)
      have hb := abs_le.mp hbound
      have hule : (10 : ℚ) ^ (working.exponent_ + 3) ≤ (10 : ℚ) ^ (working.exponent_ + 18) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : working.toRat ≤ (mant.toInt : ℚ) * 10 ^ exp + 10 ^ (working.exponent_ + 3) := by
        linarith [hb.1]
      nlinarith [hwlarge, hule, hval_neg]
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      have := hmrange.1; rw [hcMin] at this; omega
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      have := hmrange.2; rw [hcMax] at this; omega
    have hwe : working.exponent_ = r.exponent_ := by rw [hw_eq]
    rw [hwe] at herange
    have hcc := STAmount.checked_iou_cases .fractional mant.toUInt64 exp neg mode rfl
      hmtu_lo hmtu_hi (by omega) (by omega) result hok hresult
    obtain ⟨hexp_lo, hexp_hi, hres_eq⟩ := hcc
    have hres_toRat : result.toRat = (mant.toInt : ℚ) * 10 ^ exp := by
      rw [hres_eq, STAmount.toRat_signed]
      show (if neg then (-1 : ℚ) else 1) * (mant.toUInt64.toNat : ℚ) * 10 ^ exp = _
      have : (mant.toUInt64.toNat : ℚ) = (mant.toInt : ℚ) := by
        exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos
      rw [this, hneg_false]; simp
    refine ⟨mant, exp, by rw [← hw_eq]; exact hnorm', hres_toRat, ?_,
      by symm; exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos, hmtu_lo, hmtu_hi, hexp_lo, hexp_hi⟩
    rw [hres_eq]; rfl

/-- **Magnitude version of the `ofNumber` snap facts, any sign.** `ofNumber` rounds the
*magnitude* `|r|` (`working = if r.negative_ then -r else r`) onto the 16-digit grid and
reattaches the sign, so this exposes the `normalizeToRange` output on `working = |r|`, the
grid form of `|result|`, and the exponent range — the engine for the sign-agnostic
magnitude 1-ULP bound. -/
lemma STAmount.ofNumber_iou_snap_mag (nt : NumericType) (r : Number) (mode : rounding_mode)
    (result : STAmount)
    (hnt : nt = .fractional)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_) (hre_hi : r.exponent_ + 4 ≤ maxExponent)
    (hok : STAmount.ofNumber nt r mode = .ok result) (hresult : result.mValue ≠ 0) :
    ∃ (mant : Int64) (exp : ℤ),
      (if r.negative_ then r.operator_neg else r).normalizeToRange cMinValue cMaxValue mode
        = .ok (mant, exp) ∧
      |result.toRat| = (mant.toInt : ℚ) * 10 ^ exp ∧
      result.exponent = exp ∧
      result.mIsNegative = r.negative_ ∧
      (mant.toInt : ℚ) = ((mant.toUInt64.toNat : ℕ) : ℚ) ∧
      10 ^ 15 ≤ mant.toUInt64.toNat ∧ mant.toUInt64.toNat < 10 ^ 16 ∧
      (-96 : ℤ) ≤ exp ∧ exp ≤ 80 := by
  subst hnt
  have hr_ne : r.mantissa_ ≠ 0 := by intro h; rw [h] at hr_lo; simp at hr_lo
  have hmne : (r.mantissa_ != 0) = true := by simp [hr_ne]
  have hneg_eq : decide (r.signum < 0) = r.negative_ := by
    unfold Number.signum
    rcases hrn : r.negative_ with _ | _ <;> simp only [hmne, if_true, if_false,
      Bool.false_eq_true] <;> decide
  set neg : Bool := decide (r.signum < 0) with hneg_def
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_mant : working.mantissa_ = r.mantissa_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp [Number.operator_neg_mantissa_of_ne r hr_ne]
  have hw_exp : working.exponent_ = r.exponent_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp only [if_true]; unfold Number.operator_neg
      rw [if_neg (by simpa using hr_ne)]
  have hw_neg : working.negative_ = false := by
    rw [hw_def, hneg_eq]
    by_cases hrn : r.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne r hr_ne]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_mant]; exact hr_lo
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hr_hi
  have hwe_lo : minExponent ≤ working.exponent_ + 3 := by rw [hw_exp]; omega
  have hwe_hi : working.exponent_ + 4 ≤ maxExponent := by rw [hw_exp]; exact hre_hi
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide), ← hneg_def, ← hw_def] at hok
  cases hnorm : working.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : working.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hbound := normalizeToRange_16_within_ulp working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hmrange := normalizeToRange_16_mantissa_range working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have herange := normalizeToRange_16_exp_range working mode mant exp hw_lo hw_hi hwe_lo hwe_hi hnorm'
    have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
    have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
    have hwlarge : (10 : ℚ) ^ (working.exponent_ + 18) ≤ working.toRat := by
      rw [Number.toRat_of_nonneg working hw_neg]
      have h1018 : (10 : ℚ) ^ (18 : ℤ) ≤ (working.mantissa_.toNat : ℚ) := by
        have : ((10 ^ 18 : ℕ) : ℚ) ≤ (working.mantissa_.toNat : ℚ) := by exact_mod_cast hw_lo
        rwa [show ((10 ^ 18 : ℕ) : ℚ) = (10 : ℚ) ^ (18 : ℤ) by push_cast; norm_num] at this
      calc (10 : ℚ) ^ (working.exponent_ + 18)
          = (10 : ℚ) ^ (18 : ℤ) * (10 : ℚ) ^ working.exponent_ := by
            rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring_nf
        _ ≤ (working.mantissa_.toNat : ℚ) * (10 : ℚ) ^ working.exponent_ := by gcongr
    have hmant_pos : 0 ≤ mant.toInt := by
      by_contra hc
      push_neg at hc
      have hmant_neg_q : (mant.toInt : ℚ) < 0 := by exact_mod_cast hc
      have hval_neg : (mant.toInt : ℚ) * 10 ^ exp < 0 :=
        mul_neg_of_neg_of_pos hmant_neg_q (zpow_pos (by norm_num) _)
      have hb := abs_le.mp hbound
      have hule : (10 : ℚ) ^ (working.exponent_ + 3) ≤ (10 : ℚ) ^ (working.exponent_ + 18) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : working.toRat ≤ (mant.toInt : ℚ) * 10 ^ exp + 10 ^ (working.exponent_ + 3) := by
        linarith [hb.1]
      nlinarith [hwlarge, hule, hval_neg]
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      have := hmrange.1; rw [hcMin] at this; omega
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      have := hmrange.2; rw [hcMax] at this; omega
    have hwe : working.exponent_ = r.exponent_ := by rw [hw_exp]
    rw [hwe] at herange
    have hcc := STAmount.checked_iou_cases .fractional mant.toUInt64 exp neg mode rfl
      hmtu_lo hmtu_hi (by omega) (by omega) result hok hresult
    obtain ⟨hexp_lo, hexp_hi, hres_eq⟩ := hcc
    have hcast : (mant.toInt : ℚ) = ((mant.toUInt64.toNat : ℕ) : ℚ) := by
      symm; exact_mod_cast toUInt64_toNat_of_nonneg mant hmant_pos
    have hres_abs : |result.toRat| = (mant.toInt : ℚ) * 10 ^ exp := by
      rw [hres_eq, STAmount.toRat_signed]
      show |(if neg then (-1 : ℚ) else 1) * (mant.toUInt64.toNat : ℚ) * 10 ^ exp| = _
      rw [hcast, abs_mul, abs_mul,
          show |if neg then (-1 : ℚ) else 1| = 1 by rcases neg <;> norm_num, one_mul,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    refine ⟨mant, exp,
      by rw [show (if r.negative_ then r.operator_neg else r) = working from by
              rw [hw_def, hneg_eq]]; exact hnorm',
      hres_abs, ?_, by rw [hres_eq]; exact hneg_eq, hcast, hmtu_lo, hmtu_hi, hexp_lo, hexp_hi⟩
    rw [hres_eq]; rfl

/-- **Stage-1 exact rounding of the IOU multiply pipeline (directed modes, non-negative
operands).** Like `operator_mul_iou_decompose_anyMode` but additionally exposes that the
19-digit `Number` product `r` is the *exact* directed rounding of the true product onto
the `Number` grid (`Number.RoundsToRepresentable`), the key minimality fact. -/
lemma STAmount.operator_mul_iou_decompose_tight (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    ∃ r : Number, STAmount.ofNumber nt r mode = .ok result ∧
      10 ^ 18 ≤ r.mantissa_.toNat ∧ r.mantissa_.toNat < 10 ^ 19 ∧
      minExponent ≤ r.exponent_ ∧ r.exponent_ + 4 ≤ maxExponent ∧ r.negative_ = false ∧
      Number.RoundsToRepresentable r (v1.toRat * v2.toRat) mode := by
  subst hnt
  have hv1ne : v1.mValue ≠ 0 := by intro h; have := hc1.mant_lo; rw [h] at this; simp at this
  have hv2ne : v2.mValue ≠ 0 := by intro h; have := hc2.mant_lo; rw [h] at this; simp at this
  have hint1 : v1.integral = false := by unfold STAmount.integral; rw [hc1.is_fractional]; rfl
  unfold STAmount.multiply at hok
  rw [if_neg (show ¬ (v1.isZero || v2.isZero) = true from by simp [STAmount.isZero, hv1ne, hv2ne]),
      if_neg (show ¬ (v1.integral && v2.integral && NumericType.fractional.isIntegral) = true from by
        rw [hint1]; simp),
      STAmount.toNumber_iou_canonical v1 mode hc1,
      STAmount.toNumber_iou_canonical v2 mode hc2] at hok
  simp only at hok
  set n1 : Number := ⟨v1.mIsNegative, v1.mValue * 10 * 10 * 10, v1.mOffset - 3⟩ with hn1_def
  set n2 : Number := ⟨v2.mIsNegative, v2.mValue * 10 * 10 * 10, v2.mOffset - 3⟩ with hn2_def
  cases hmul : Number.operator_mul n1 n2 mode with
  | error e => rw [hmul] at hok; simp at hok
  | ok r =>
    rw [hmul] at hok; simp only at hok
    have hofn : STAmount.ofNumber .fractional r mode = .ok result := hok
    have hn1_norm := STAmount.toNumber_iou_canonical_isNormalized v1 hc1
    have hn2_norm := STAmount.toNumber_iou_canonical_isNormalized v2 hc2
    have hn1_ne := STAmount.toNumber_iou_canonical_mantissa_ne v1 hc1
    have hn2_ne := STAmount.toNumber_iou_canonical_mantissa_ne v2 hc2
    have hn1_val := STAmount.toNumber_iou_canonical_toRat v1 hc1
    have hn2_val := STAmount.toNumber_iou_canonical_toRat v2 hc2
    have hr_ne := STAmount.ofNumber_iou_mantissa_ne_zero .fractional r mode result rfl
      hofn hresult
    have hr_norm := operator_mul_result_isNormalized n1 n2 r mode hn1_norm hn2_norm hn1_ne hn2_ne
      hmul hr_ne
    have hr_mant := hr_norm.mantissaBounds_nat hr_ne
    have hr_exp_lo : minExponent ≤ r.exponent_ := by
      rcases hr_norm with hz | ⟨_, _, _, hlo, _⟩
      · exact absurd (show r.mantissa_ = 0 by rw [hz]; rfl) hr_ne
      · exact hlo
    have hr_exp_hi := operator_mul_exponent_hi_anyMode n1 n2 r 77 mode hn1_norm hn2_norm hn1_ne
      hn2_ne hr_ne (by show v1.mOffset - 3 ≤ 77; have := hc1.exp_hi; omega)
      (by show v2.mOffset - 3 ≤ 77; have := hc2.exp_hi; omega) (by unfold maxExponent; omega) hmul
    have hr_neg : r.negative_ = false := by
      rw [operator_mul_negative_eq n1 n2 r mode hn1_norm hn2_norm hn1_ne hn2_ne hmul hr_ne]
      show (v1.mIsNegative != v2.mIsNegative) = false
      rw [hn1, hn2]; rfl
    have hrepr : Number.RoundsToRepresentable r (n1.toRat * n2.toRat) mode := by
      cases mode with
      | to_nearest => exact operator_mul_rounded_to_nearest n1 n2 r hn1_norm hn2_norm hmul
      | downward => exact operator_mul_rounded_downward n1 n2 r hn1_norm hn2_norm hmul hr_ne
      | upward => exact operator_mul_rounded_upward n1 n2 r hn1_norm hn2_norm hmul hr_ne
      | towards_zero => exact operator_mul_rounded_towards_zero n1 n2 r hn1_norm hn2_norm hmul
    rw [hn1_val, hn2_val] at hrepr
    exact ⟨r, hofn, hr_mant.1, hr_mant.2, hr_exp_lo, hr_exp_hi, hr_neg, hrepr⟩

/-- **Sign-agnostic stage-1 exact rounding decomposition.** Like
`operator_mul_iou_decompose_tight` but with no non-negativity hypothesis: exposes the
19-digit `Number` product `r`, its range, its sign (XOR of the operand signs), and that it
is the exact directed rounding of the true product (`Number.RoundsToRepresentable`). -/
lemma STAmount.operator_mul_iou_decompose_mag_tight (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    ∃ r : Number, STAmount.ofNumber nt r mode = .ok result ∧
      10 ^ 18 ≤ r.mantissa_.toNat ∧ r.mantissa_.toNat < 10 ^ 19 ∧
      minExponent ≤ r.exponent_ ∧ r.exponent_ + 4 ≤ maxExponent ∧
      r.negative_ = (v1.mIsNegative != v2.mIsNegative) ∧
      Number.RoundsToRepresentable r (v1.toRat * v2.toRat) mode := by
  subst hnt
  have hv1ne : v1.mValue ≠ 0 := by intro h; have := hc1.mant_lo; rw [h] at this; simp at this
  have hv2ne : v2.mValue ≠ 0 := by intro h; have := hc2.mant_lo; rw [h] at this; simp at this
  have hint1 : v1.integral = false := by unfold STAmount.integral; rw [hc1.is_fractional]; rfl
  unfold STAmount.multiply at hok
  rw [if_neg (show ¬ (v1.isZero || v2.isZero) = true from by simp [STAmount.isZero, hv1ne, hv2ne]),
      if_neg (show ¬ (v1.integral && v2.integral && NumericType.fractional.isIntegral) = true from by
        rw [hint1]; simp),
      STAmount.toNumber_iou_canonical v1 mode hc1,
      STAmount.toNumber_iou_canonical v2 mode hc2] at hok
  simp only at hok
  set n1 : Number := ⟨v1.mIsNegative, v1.mValue * 10 * 10 * 10, v1.mOffset - 3⟩ with hn1_def
  set n2 : Number := ⟨v2.mIsNegative, v2.mValue * 10 * 10 * 10, v2.mOffset - 3⟩ with hn2_def
  cases hmul : Number.operator_mul n1 n2 mode with
  | error e => rw [hmul] at hok; simp at hok
  | ok r =>
    rw [hmul] at hok; simp only at hok
    have hofn : STAmount.ofNumber .fractional r mode = .ok result := hok
    have hn1_norm := STAmount.toNumber_iou_canonical_isNormalized v1 hc1
    have hn2_norm := STAmount.toNumber_iou_canonical_isNormalized v2 hc2
    have hn1_ne := STAmount.toNumber_iou_canonical_mantissa_ne v1 hc1
    have hn2_ne := STAmount.toNumber_iou_canonical_mantissa_ne v2 hc2
    have hn1_val := STAmount.toNumber_iou_canonical_toRat v1 hc1
    have hn2_val := STAmount.toNumber_iou_canonical_toRat v2 hc2
    have hr_ne := STAmount.ofNumber_iou_mantissa_ne_zero .fractional r mode result rfl
      hofn hresult
    have hr_norm := operator_mul_result_isNormalized n1 n2 r mode hn1_norm hn2_norm hn1_ne hn2_ne
      hmul hr_ne
    have hr_mant := hr_norm.mantissaBounds_nat hr_ne
    have hr_exp_lo : minExponent ≤ r.exponent_ := by
      rcases hr_norm with hz | ⟨_, _, _, hlo, _⟩
      · exact absurd (show r.mantissa_ = 0 by rw [hz]; rfl) hr_ne
      · exact hlo
    have hr_exp_hi := operator_mul_exponent_hi_anyMode n1 n2 r 77 mode hn1_norm hn2_norm hn1_ne
      hn2_ne hr_ne (by show v1.mOffset - 3 ≤ 77; have := hc1.exp_hi; omega)
      (by show v2.mOffset - 3 ≤ 77; have := hc2.exp_hi; omega) (by unfold maxExponent; omega) hmul
    have hr_neg : r.negative_ = (v1.mIsNegative != v2.mIsNegative) :=
      operator_mul_negative_eq n1 n2 r mode hn1_norm hn2_norm hn1_ne hn2_ne hmul hr_ne
    have hrepr : Number.RoundsToRepresentable r (n1.toRat * n2.toRat) mode := by
      cases mode with
      | to_nearest => exact operator_mul_rounded_to_nearest n1 n2 r hn1_norm hn2_norm hmul
      | downward => exact operator_mul_rounded_downward n1 n2 r hn1_norm hn2_norm hmul hr_ne
      | upward => exact operator_mul_rounded_upward n1 n2 r hn1_norm hn2_norm hmul hr_ne
      | towards_zero => exact operator_mul_rounded_towards_zero n1 n2 r hn1_norm hn2_norm hmul
    rw [hn1_val, hn2_val] at hrepr
    exact ⟨r, hofn, hr_mant.1, hr_mant.2, hr_exp_lo, hr_exp_hi, hr_neg, hrepr⟩

set_option maxHeartbeats 1200000 in
-- three directed-mode branches, each composing the exact ceiling/floor snap with the
-- `Number.upper`/`lower` minimality argument and zpow/nlinarith algebra; exceeds default
/-- **IOU multiplication is within 1 ULP for the directed modes (non-negative operands).**
The double rounding collapses: `result` is the single directed rounding of the exact
product onto the 16-digit grid, so it lands within one ULP. -/
lemma STAmount.operator_mul_repr_iou_directed_core (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode)
    (hmode : mode = .upward ∨ mode = .downward ∨ mode = .towards_zero)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hn1 : v1.mIsNegative = false) (hn2 : v2.mIsNegative = false)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    STAmount.RoundsToRepresentableWithin result (v1.toRat * v2.toRat) mode 1 := by
  obtain ⟨r, hofn, hr_lo, hr_hi, hr_exp_lo, hr_exp_hi, hr_neg, hrepr⟩ :=
    STAmount.operator_mul_iou_decompose_tight v1 v2 result nt mode hnt
      hc1 hc2 hn1 hn2 hok hresult
  have htruth_nn : 0 ≤ v1.toRat * v2.toRat := by
    have h1 : 0 ≤ v1.toRat := by rw [STAmount.toRat_of_nonneg v1 hn1]; positivity
    have h2 : 0 ≤ v2.toRat := by rw [STAmount.toRat_of_nonneg v2 hn2]; positivity
    positivity
  obtain ⟨mant, exp, hnorm_r, hres_toRat, hres_exp, hcast, hmtu_lo, hmtu_hi, hexp_lo, hexp_hi⟩ :=
    STAmount.ofNumber_iou_snap_pos nt r mode result hnt hr_neg hr_lo hr_hi
      hr_exp_lo hr_exp_hi hofn hresult
  set truth := v1.toRat * v2.toRat with htruth_def
  have hr_val : r.toRat = (r.mantissa_.toNat : ℚ) * (10:ℚ) ^ r.exponent_ :=
    Number.toRat_of_nonneg r hr_neg
  set M : ℕ := r.mantissa_.toNat with hM_def
  set Mr : ℕ := mant.toUInt64.toNat with hMr_def
  have hres_grid : result.toRat = (Mr : ℚ) * (10:ℚ) ^ exp := by rw [hres_toRat, hcast]
  have hp : (0:ℚ) < (10:ℚ) ^ r.exponent_ := zpow_pos (by norm_num) _
  have hpec : (0:ℚ) < (10:ℚ) ^ exp := zpow_pos (by norm_num) _
  have h1000 : (10:ℚ) ^ (r.exponent_ + 3) = (10:ℚ) ^ r.exponent_ * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ)≠0)]; norm_num
  have hgb_lo : minExponent + 4 ≤ exp := by unfold minExponent; omega
  have hgb_hi : exp + 3 ≤ maxExponent := by unfold maxExponent; omega
  have hid : ((Mr:ℚ) - 1) * (10:ℚ)^exp = (Mr:ℚ)*(10:ℚ)^exp - (10:ℚ)^exp := by ring
  have hida : ((Mr:ℚ) + 1) * (10:ℚ)^exp = (Mr:ℚ)*(10:ℚ)^exp + (10:ℚ)^exp := by ring
  rcases hmode with hm | hm | hm
  · -- upward: exact ceiling; `r` is the least representable `Number ≥ truth`.
    subst hm
    obtain ⟨hval, hEle⟩ := normalizeToRange_16_ceil_pos r mant exp hr_neg hr_lo hr_hi (by omega)
      hr_exp_hi hnorm_r
    set c : ℕ := M / 1000 + (if M % 1000 ≠ 0 then 1 else 0) with hc_def
    have hres_M : result.toRat = (c:ℚ) * 1000 * (10:ℚ)^r.exponent_ := by
      rw [hres_toRat, hval, h1000]; ring
    have hc_ge : M ≤ c * 1000 := by
      rw [hc_def]; rcases Nat.eq_zero_or_pos (M % 1000) with h | h
      · rw [if_neg (by omega)]; omega
      · rw [if_pos (by omega)]; omega
    have hc_lt : c * 1000 < M + 1000 := by
      rw [hc_def]; rcases Nat.eq_zero_or_pos (M % 1000) with h | h
      · rw [if_neg (by omega)]; omega
      · rw [if_pos (by omega)]; omega
    have hcgeq : (M:ℚ) ≤ (c:ℚ)*1000 := by exact_mod_cast hc_ge
    have hcltq : (c:ℚ)*1000 < (M:ℚ) + 1000 := by exact_mod_cast hc_lt
    have hr_le_res : r.toRat ≤ result.toRat := by rw [hres_M, hr_val]; nlinarith [hcgeq, hp]
    have hos : result.toRat - r.toRat < (10:ℚ)^exp := by
      have h1 : result.toRat - r.toRat < (10:ℚ)^(r.exponent_+3) := by
        rw [hres_M, hr_val, h1000]; nlinarith [hcltq, hp]
      have h2 : (10:ℚ)^(r.exponent_+3) ≤ (10:ℚ)^exp := zpow_le_zpow_right₀ (by norm_num) hEle
      linarith
    obtain ⟨nUp, hup_eq, hr_eq⟩ := hrepr
    have htruth_le_r : truth ≤ r.toRat := by rw [hr_eq]; exact Number.le_upper truth nUp hup_eq
    have htruth_le_res : truth ≤ result.toRat := le_trans htruth_le_r hr_le_res
    obtain ⟨m0, hm0_norm, hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_below Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have hbelow : ((Mr:ℚ) - 1) * (10:ℚ)^exp ≤ truth := by
      by_contra hcon
      push_neg at hcon
      have hge : truth ≤ m0.toRat := by rw [hm0_val]; linarith
      have hmin := Number.upper_tight truth nUp hup_eq m0 hm0_norm hge
      rw [← hr_eq, hm0_val] at hmin
      have hcontra : (10:ℚ)^exp ≤ result.toRat - r.toRat := by rw [hres_grid]; linarith [hmin, hid]
      linarith [hos, hcontra]
    refine ⟨htruth_le_res, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonneg (by linarith [htruth_le_res])]
    rw [hres_grid]; linarith [hbelow, hid]
  · -- downward: exact floor; `r` is the greatest representable `Number ≤ truth`.
    subst hm
    obtain ⟨hval, hEeq⟩ := normalizeToRange_16_floor_pos r mant exp .downward (Or.inl rfl) hr_neg
      hr_lo hr_hi (by omega) hr_exp_hi hnorm_r
    have hres_M : result.toRat = ((M/1000 : ℕ):ℚ) * 1000 * (10:ℚ)^r.exponent_ := by
      rw [hres_toRat, hval, h1000]; ring
    have hf_le : (M/1000) * 1000 ≤ M := by omega
    have hf_lt : M < (M/1000) * 1000 + 1000 := by omega
    have hfleq : ((M/1000 : ℕ):ℚ)*1000 ≤ (M:ℚ) := by exact_mod_cast hf_le
    have hfltq : (M:ℚ) < ((M/1000 : ℕ):ℚ)*1000 + 1000 := by exact_mod_cast hf_lt
    have hexpeq : (10:ℚ)^exp = (10:ℚ)^r.exponent_ * 1000 := by rw [hEeq, h1000]
    have hres_le_r : result.toRat ≤ r.toRat := by rw [hres_M, hr_val]; nlinarith [hfleq, hp]
    have hos : r.toRat - result.toRat < (10:ℚ)^exp := by
      rw [hres_M, hr_val, hexpeq]; nlinarith [hfltq, hp]
    obtain ⟨nLo, hlo_eq, hr_eq⟩ := hrepr
    have hr_le_truth : r.toRat ≤ truth := by rw [hr_eq]; exact Number.lower_le truth nLo hlo_eq
    have hres_le_truth : result.toRat ≤ truth := le_trans hres_le_r hr_le_truth
    obtain ⟨m0, hm0_norm, hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_above Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have habove : truth ≤ ((Mr:ℚ) + 1) * (10:ℚ)^exp := by
      by_contra hcon
      push_neg at hcon
      have hle : m0.toRat ≤ truth := by rw [hm0_val]; linarith
      have hmax := Number.lower_tight truth nLo hlo_eq m0 hm0_norm hle
      rw [← hr_eq, hm0_val] at hmax
      have hcontra : (10:ℚ)^exp ≤ r.toRat - result.toRat := by rw [hres_grid]; linarith [hmax, hida]
      linarith [hos, hcontra]
    refine ⟨hres_le_truth, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonpos (by linarith [hres_le_truth]), neg_sub]
    rw [hres_grid]; linarith [habove, hida]
  · -- towards_zero (nonneg ⟹ truncation = floor): identical to downward, no directional clause.
    subst hm
    obtain ⟨hval, hEeq⟩ := normalizeToRange_16_floor_pos r mant exp .towards_zero (Or.inr rfl) hr_neg
      hr_lo hr_hi (by omega) hr_exp_hi hnorm_r
    have hres_M : result.toRat = ((M/1000 : ℕ):ℚ) * 1000 * (10:ℚ)^r.exponent_ := by
      rw [hres_toRat, hval, h1000]; ring
    have hf_le : (M/1000) * 1000 ≤ M := by omega
    have hf_lt : M < (M/1000) * 1000 + 1000 := by omega
    have hfleq : ((M/1000 : ℕ):ℚ)*1000 ≤ (M:ℚ) := by exact_mod_cast hf_le
    have hfltq : (M:ℚ) < ((M/1000 : ℕ):ℚ)*1000 + 1000 := by exact_mod_cast hf_lt
    have hexpeq : (10:ℚ)^exp = (10:ℚ)^r.exponent_ * 1000 := by rw [hEeq, h1000]
    have hres_le_r : result.toRat ≤ r.toRat := by rw [hres_M, hr_val]; nlinarith [hfleq, hp]
    have hos : r.toRat - result.toRat < (10:ℚ)^exp := by
      rw [hres_M, hr_val, hexpeq]; nlinarith [hfltq, hp]
    obtain ⟨nLo, hlo_eq, hr_eq⟩ := hrepr
    rw [if_pos htruth_nn] at hlo_eq
    have hr_le_truth : r.toRat ≤ truth := by rw [hr_eq]; exact Number.lower_le truth nLo hlo_eq
    have hres_le_truth : result.toRat ≤ truth := le_trans hres_le_r hr_le_truth
    obtain ⟨m0, hm0_norm, hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_above Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
    have habove : truth ≤ ((Mr:ℚ) + 1) * (10:ℚ)^exp := by
      by_contra hcon
      push_neg at hcon
      have hle : m0.toRat ≤ truth := by rw [hm0_val]; linarith
      have hmax := Number.lower_tight truth nLo hlo_eq m0 hm0_norm hle
      rw [← hr_eq, hm0_val] at hmax
      have hcontra : (10:ℚ)^exp ≤ r.toRat - result.toRat := by rw [hres_grid]; linarith [hmax, hida]
      linarith [hos, hcontra]
    refine ⟨trivial, ?_⟩
    rw [hres_exp, Nat.cast_one, one_mul, abs_of_nonpos (by linarith [hres_le_truth]), neg_sub]
    rw [hres_grid]; linarith [habove, hida]

set_option maxHeartbeats 1200000 in
-- sign-factoring reduces the any-sign product to a magnitude floor∘floor collapse;
-- `lower`/`upper` maximality plus zpow/nlinarith algebra exceeds the default budget
/-- **IOU multiplication is within 1 ULP under `towards_zero`, for operands of *any* sign.**
`towards_zero` truncates the *magnitude* at both stages regardless of sign, so `|result|`
is the single 16-digit floor of `|v1·v2|`, hence within one ULP. -/
lemma STAmount.operator_mul_iou_towards_zero_one (v1 v2 result : STAmount) (nt : NumericType)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt .towards_zero = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ (10 : ℚ) ^ result.exponent := by
  obtain ⟨r, hofn, hr_lo, hr_hi, hr_exp_lo, hr_exp_hi, hr_neg, hrepr⟩ :=
    STAmount.operator_mul_iou_decompose_mag_tight v1 v2 result nt .towards_zero hnt
      hc1 hc2 hok hresult
  obtain ⟨mant, exp, hnorm_w, habs, hres_exp, hres_sign, hcast, hmtu_lo, hmtu_hi, hexp_lo, hexp_hi⟩ :=
    STAmount.ofNumber_iou_snap_mag nt r .towards_zero result hnt hr_lo hr_hi
      hr_exp_lo hr_exp_hi hofn hresult
  have hr_ne : r.mantissa_ ≠ 0 := by intro h; rw [h] at hr_lo; simp at hr_lo
  -- magnitude/sign factoring helpers.
  have vabs : ∀ v : STAmount, |v.toRat| = (v.mValue.toNat : ℚ) * 10 ^ v.mOffset := by
    intro v
    rw [STAmount.toRat_signed, abs_mul, abs_mul,
        show |if v.mIsNegative then (-1:ℚ) else 1| = 1 by split_ifs <;> norm_num,
        one_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hsv : ∀ v : STAmount, v.toRat = (if v.mIsNegative then (-1:ℚ) else 1) * |v.toRat| := by
    intro v; rw [vabs v, STAmount.toRat_signed]; ring
  have hv1pos : 0 < |v1.toRat| := by
    rw [vabs v1]; have h : 0 < v1.mValue.toNat := by have := hc1.mant_lo; omega
    exact mul_pos (by exact_mod_cast h) (by positivity)
  have hv2pos : 0 < |v2.toRat| := by
    rw [vabs v2]; have h : 0 < v2.mValue.toNat := by have := hc2.mant_lo; omega
    exact mul_pos (by exact_mod_cast h) (by positivity)
  set truth := v1.toRat * v2.toRat with htruth_def
  have htruth_abs : |truth| = |v1.toRat| * |v2.toRat| := by rw [htruth_def, abs_mul]
  have hA_pos : 0 < |truth| := by rw [htruth_abs]; positivity
  have sfac : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1)
      = (if v1.mIsNegative then (-1:ℚ) else 1) * (if v2.mIsNegative then (-1:ℚ) else 1) := by
    rcases v1.mIsNegative <;> rcases v2.mIsNegative <;> simp
  -- `r`, `result`, `truth` all factor as (shared sign)·magnitude.
  have hr_form : r.toRat
      = (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) * |r.toRat| := by
    have hrf : r.toRat = (if r.negative_ then (-1:ℚ) else 1) * |r.toRat| := by
      rcases hrn : r.negative_ with _ | _
      · have h0 : (0:ℚ) ≤ r.toRat := by rw [Number.toRat_of_nonneg r hrn]; positivity
        rw [if_neg (by decide), one_mul, abs_of_nonneg h0]
      · have h0 : r.toRat < 0 := by
          rw [Number.toRat_of_neg r hrn]
          have : (0:ℚ) < (r.mantissa_.toNat : ℚ) * 10 ^ r.exponent_ := by positivity
          linarith
        rw [if_pos rfl, neg_one_mul, abs_of_neg h0, neg_neg]
    rw [hr_neg] at hrf; exact hrf
  have htruth_form : truth
      = (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) * |truth| := by
    rw [htruth_abs, sfac]; nth_rewrite 1 [htruth_def]
    nth_rewrite 1 [hsv v1]; nth_rewrite 1 [hsv v2]; ring
  have hres_form : result.toRat
      = (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) * |result.toRat| := by
    nth_rewrite 1 [hsv result]; rw [hres_sign, hr_neg]
  -- working = |r|; |result| = floor₁₆(|r|); |r| = M·10^E.
  set w : Number := if r.negative_ then r.operator_neg else r with hw_def
  have hw_mant : w.mantissa_ = r.mantissa_ := by
    rw [hw_def]; rcases r.negative_
    · simp
    · simp [Number.operator_neg_mantissa_of_ne r hr_ne]
  have hw_exp : w.exponent_ = r.exponent_ := by
    rw [hw_def]; rcases r.negative_
    · simp
    · simp only [if_true]; unfold Number.operator_neg; rw [if_neg (by simpa using hr_ne)]
  have hw_neg : w.negative_ = false := by
    rw [hw_def]
    by_cases hrn : r.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne r hr_ne]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ w.mantissa_.toNat := by rw [hw_mant]; exact hr_lo
  have hw_hi : w.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hr_hi
  obtain ⟨hfloorval, hexpeq⟩ :=
    normalizeToRange_16_floor_pos w mant exp .towards_zero (Or.inr rfl) hw_neg hw_lo hw_hi
      (by rw [hw_exp]; omega) (by rw [hw_exp]; exact hr_exp_hi) hnorm_w
  set M : ℕ := r.mantissa_.toNat with hM_def
  set E : ℤ := r.exponent_ with hE_def
  set Mr : ℕ := mant.toUInt64.toNat with hMr_def
  have hp : (0:ℚ) < (10:ℚ) ^ E := zpow_pos (by norm_num) _
  have hres_mag : |result.toRat| = ((M / 1000 : ℕ) : ℚ) * (10:ℚ) ^ (E + 3) := by
    rw [habs, hfloorval, hw_mant, hw_exp]
  have hexpE : exp = E + 3 := by rw [hexpeq, hw_exp]
  have hr_mag : |r.toRat| = (M : ℚ) * (10:ℚ) ^ E := abs_toRat_eq r
  have hMr_eq : (Mr : ℚ) = ((M / 1000 : ℕ) : ℚ) := by
    have h1 : (Mr : ℚ) * (10:ℚ) ^ exp = ((M / 1000 : ℕ) : ℚ) * (10:ℚ) ^ (E + 3) := by
      rw [← hres_mag, habs, hcast]
    rw [hexpE] at h1; exact mul_right_cancel₀ (by positivity) h1
  have h103 : (10:ℚ) ^ (E + 3) = (10:ℚ) ^ E * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ)≠0)]; norm_num
  -- |result| ≤ |r| (floor never increases the magnitude).
  have hres_le_r : |result.toRat| ≤ |r.toRat| := by
    rw [hres_mag, hr_mag, h103]
    have hn : ((M / 1000 : ℕ) : ℚ) * 1000 ≤ (M : ℚ) := by
      have hnat : (M / 1000) * 1000 ≤ M := by omega
      have := (Nat.cast_le (α := ℚ)).mpr hnat; push_cast at this ⊢; linarith
    nlinarith [hp, hn]
  obtain ⟨n, hn_eq, hr_eq⟩ := hrepr
  -- |r| ≤ |truth| (Number-multiply toward zero never increases the magnitude).
  have hr_le_truth : |r.toRat| ≤ |truth| := by
    rcases hxor : (v1.mIsNegative != v2.mIsNegative) with _ | _
    · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = 1 := by rw [hxor]; simp
      have htf := htruth_form; rw [hif, one_mul] at htf
      have hrf := hr_form; rw [hif, one_mul] at hrf
      rw [if_pos (by rw [htf]; exact abs_nonneg truth)] at hn_eq
      have hle' := Number.lower_le truth n hn_eq
      rw [← hr_eq] at hle'; linarith [hle', hrf, htf]
    · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = -1 := by rw [hxor]; simp
      have htf := htruth_form; rw [hif, neg_one_mul] at htf
      have hrf := hr_form; rw [hif, neg_one_mul] at hrf
      have htneg : truth < 0 := by rw [htf]; simpa using hA_pos
      rw [if_neg (not_le.mpr htneg)] at hn_eq
      have hge' := Number.le_upper truth n hn_eq
      rw [← hr_eq] at hge'; linarith [hge', hrf, htf]
  have hle : |result.toRat| ≤ |truth| := le_trans hres_le_r hr_le_truth
  -- maximality: any representable magnitude ≤ |truth| is ≤ |r|.
  have hkey_le : ∀ (m0 : Number), m0.isNormalized → m0.negative_ = false → m0.toRat ≤ |truth| →
      m0.toRat ≤ |r.toRat| := by
    intro m0 hm0n hm0neg hm0le
    rcases eq_or_lt_of_le (Number.toRat_nonneg_of_nonnegative m0 hm0neg) with hm0z | hm0pos
    · rw [← hm0z]; exact abs_nonneg _
    · have hm0_ne : m0.mantissa_ ≠ 0 := by
        intro h; apply ne_of_gt hm0pos
        rw [Number.toRat_of_nonneg m0 hm0neg, h]; simp
      rcases hxor : (v1.mIsNegative != v2.mIsNegative) with _ | _
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = 1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, one_mul] at htf
        have hrf := hr_form; rw [hif, one_mul] at hrf
        have hle_t : m0.toRat ≤ truth := le_trans hm0le (le_of_eq htf.symm)
        rw [if_pos (by rw [htf]; exact abs_nonneg truth)] at hn_eq
        have := Number.lower_tight truth n hn_eq m0 hm0n hle_t
        rw [← hr_eq] at this; linarith [this, hrf]
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = -1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, neg_one_mul] at htf
        have hrf := hr_form; rw [hif, neg_one_mul] at hrf
        have htneg : truth < 0 := by rw [htf]; simpa using hA_pos
        set m0' : Number := { m0 with negative_ := true } with hm0'_def
        have hm0'_toRat : m0'.toRat = -m0.toRat := Number.toRat_set_neg_true_of_nn m0 hm0neg
        have hm0'_norm : m0'.isNormalized := by
          rcases hm0n with hz | ⟨h1, h2, h3, h4, h5⟩
          · exact absurd (show m0.mantissa_ = 0 by rw [hz]; rfl) hm0_ne
          · right; exact ⟨h1, h2, h3, h4, h5⟩
        have hm0'_ge : truth ≤ m0'.toRat := by
          rw [hm0'_toRat]; have : m0.toRat ≤ -truth := by rw [htf]; simpa using hm0le
          linarith
        rw [if_neg (not_le.mpr htneg)] at hn_eq
        have hut := Number.upper_tight truth n hn_eq m0' hm0'_norm hm0'_ge
        rw [← hr_eq, hm0'_toRat] at hut; linarith [hut, hrf]
  -- |truth| ≤ (Mr+1)·10^exp via maximality against the grid point above.
  have habove : |truth| ≤ ((Mr : ℚ) + 1) * (10:ℚ) ^ exp := by
    by_contra hcon; push_neg at hcon
    obtain ⟨m0, hm0_norm, hm0_neg, hm0_val⟩ :=
      exists_normalized_grid_above Mr exp hmtu_lo hmtu_hi (by unfold minExponent; omega)
        (by unfold maxExponent; omega)
    have hm0le : m0.toRat ≤ |truth| := by rw [hm0_val]; linarith
    have hmx := hkey_le m0 hm0_norm hm0_neg hm0le
    rw [hm0_val, hr_mag] at hmx
    have hlt : (M : ℚ) * (10:ℚ) ^ E < ((Mr : ℚ) + 1) * (10:ℚ) ^ exp := by
      rw [hMr_eq, hexpE, h103]
      have hnat : M < (M / 1000 + 1) * 1000 := by omega
      have hc : (M : ℚ) < ((M / 1000 : ℕ) : ℚ) * 1000 + 1000 := by
        have := (Nat.cast_lt (α := ℚ)).mpr hnat; push_cast at this; linarith
      nlinarith [hp, hc]
    linarith
  have hkey : |truth| - |result.toRat| ≤ (10:ℚ) ^ exp := by
    have heq : ((Mr : ℚ) + 1) * (10:ℚ) ^ exp = |result.toRat| + (10:ℚ) ^ exp := by
      rw [show |result.toRat| = (Mr : ℚ) * (10:ℚ)^exp by rw [hres_mag, hexpE, hMr_eq]]; ring
    linarith [habove, heq]
  -- combine via the shared sign factor.
  have hsub : result.toRat - truth
      = (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) * (|result.toRat| - |truth|) := by
    rw [mul_sub, ← hres_form, ← htruth_form]
  have hsign : |result.toRat - truth| = |truth| - |result.toRat| := by
    rw [hsub, abs_mul,
        show |if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1| = 1 by split_ifs <;> norm_num,
        one_mul, abs_of_nonpos (by linarith [hle])]; ring
  rw [hsign, hres_exp]; exact hkey



set_option maxHeartbeats 1600000 in
-- `upward`/`downward`, any sign: the mixed-direction double rounding (fine one way, coarse
-- the other, for negative products) still lands within one ULP, via the fine `upper`/`lower`
-- minimality against a coarse neighbour, cased over sign × mode. Exceeds the default budget.
/-- **IOU multiplication is within 1 ULP under `upward`/`downward`, for operands of *any*
sign** (magnitude/accuracy form, no directional claim). Even the mixed `ceil∘floor` /
`floor∘ceil` double rounding for negative products lands within one ULP. -/
lemma STAmount.operator_mul_iou_directed_mag_one (v1 v2 result : STAmount) (nt : NumericType)
    (mode : rounding_mode) (hmode : mode = .upward ∨ mode = .downward)
    (hnt : nt = .fractional)
    (hc1 : v1.IOUCanonical) (hc2 : v2.IOUCanonical)
    (hok : STAmount.multiply v1 v2 nt mode = .ok result) (hresult : result.mValue ≠ 0) :
    |result.toRat - v1.toRat * v2.toRat| ≤ (10 : ℚ) ^ result.exponent := by
  obtain ⟨r, hofn, hr_lo, hr_hi, hr_exp_lo, hr_exp_hi, hr_neg, hrepr⟩ :=
    STAmount.operator_mul_iou_decompose_mag_tight v1 v2 result nt mode hnt
      hc1 hc2 hok hresult
  obtain ⟨mant, exp, hnorm_w, habs, hres_exp, hres_sign, hcast, hmtu_lo, hmtu_hi, hexp_lo, hexp_hi⟩ :=
    STAmount.ofNumber_iou_snap_mag nt r mode result hnt hr_lo hr_hi
      hr_exp_lo hr_exp_hi hofn hresult
  have hr_ne : r.mantissa_ ≠ 0 := by intro h; rw [h] at hr_lo; simp at hr_lo
  have vabs : ∀ v : STAmount, |v.toRat| = (v.mValue.toNat : ℚ) * 10 ^ v.mOffset := by
    intro v
    rw [STAmount.toRat_signed, abs_mul, abs_mul,
        show |if v.mIsNegative then (-1:ℚ) else 1| = 1 by split_ifs <;> norm_num,
        one_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hsv : ∀ v : STAmount, v.toRat = (if v.mIsNegative then (-1:ℚ) else 1) * |v.toRat| := by
    intro v; rw [vabs v, STAmount.toRat_signed]; ring
  have hv1pos : 0 < |v1.toRat| := by
    rw [vabs v1]; have h : 0 < v1.mValue.toNat := by have := hc1.mant_lo; omega
    exact mul_pos (by exact_mod_cast h) (by positivity)
  have hv2pos : 0 < |v2.toRat| := by
    rw [vabs v2]; have h : 0 < v2.mValue.toNat := by have := hc2.mant_lo; omega
    exact mul_pos (by exact_mod_cast h) (by positivity)
  set truth := v1.toRat * v2.toRat with htruth_def
  have htruth_abs : |truth| = |v1.toRat| * |v2.toRat| := by rw [htruth_def, abs_mul]
  have hA_pos : 0 < |truth| := by rw [htruth_abs]; positivity
  have sfac : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1)
      = (if v1.mIsNegative then (-1:ℚ) else 1) * (if v2.mIsNegative then (-1:ℚ) else 1) := by
    rcases v1.mIsNegative <;> rcases v2.mIsNegative <;> simp
  have hr_form : r.toRat
      = (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) * |r.toRat| := by
    have hrf : r.toRat = (if r.negative_ then (-1:ℚ) else 1) * |r.toRat| := by
      rcases hrn : r.negative_ with _ | _
      · have h0 : (0:ℚ) ≤ r.toRat := by rw [Number.toRat_of_nonneg r hrn]; positivity
        rw [if_neg (by decide), one_mul, abs_of_nonneg h0]
      · have h0 : r.toRat < 0 := by
          rw [Number.toRat_of_neg r hrn]
          have : (0:ℚ) < (r.mantissa_.toNat : ℚ) * 10 ^ r.exponent_ := by positivity
          linarith
        rw [if_pos rfl, neg_one_mul, abs_of_neg h0, neg_neg]
    rw [hr_neg] at hrf; exact hrf
  have htruth_form : truth
      = (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) * |truth| := by
    rw [htruth_abs, sfac]; nth_rewrite 1 [htruth_def]
    nth_rewrite 1 [hsv v1]; nth_rewrite 1 [hsv v2]; ring
  have hres_form : result.toRat
      = (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) * |result.toRat| := by
    nth_rewrite 1 [hsv result]; rw [hres_sign, hr_neg]
  set w : Number := if r.negative_ then r.operator_neg else r with hw_def
  have hw_mant : w.mantissa_ = r.mantissa_ := by
    rw [hw_def]; rcases r.negative_
    · simp
    · simp [Number.operator_neg_mantissa_of_ne r hr_ne]
  have hw_exp : w.exponent_ = r.exponent_ := by
    rw [hw_def]; rcases r.negative_
    · simp
    · simp only [if_true]; unfold Number.operator_neg; rw [if_neg (by simpa using hr_ne)]
  have hw_neg : w.negative_ = false := by
    rw [hw_def]
    by_cases hrn : r.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne r hr_ne]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ w.mantissa_.toNat := by rw [hw_mant]; exact hr_lo
  have hw_hi : w.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hr_hi
  set M : ℕ := r.mantissa_.toNat with hM_def
  set E : ℤ := r.exponent_ with hE_def
  set Mr : ℕ := mant.toUInt64.toNat with hMr_def
  have hp : (0:ℚ) < (10:ℚ) ^ E := zpow_pos (by norm_num) _
  have hpec : (0:ℚ) < (10:ℚ) ^ exp := zpow_pos (by norm_num) _
  have hr_mag : |r.toRat| = (M : ℚ) * (10:ℚ) ^ E := abs_toRat_eq r
  have hres_mag_Mr : |result.toRat| = (Mr : ℚ) * (10:ℚ) ^ exp := by rw [habs, hcast]
  have h103 : (10:ℚ) ^ (E + 3) = (10:ℚ) ^ E * 1000 := by
    rw [zpow_add₀ (by norm_num : (10:ℚ)≠0)]; norm_num
  have hgb_lo : minExponent + 4 ≤ exp := by unfold minExponent; omega
  have hgb_hi : exp + 3 ≤ maxExponent := by unfold maxExponent; omega
  -- Reduce to the two-sided coarse bracket.
  suffices hP : ((Mr : ℚ) - 1) * (10:ℚ) ^ exp ≤ |truth| ∧
      |truth| ≤ ((Mr : ℚ) + 1) * (10:ℚ) ^ exp by
    have hsub : result.toRat - truth
        = (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) * (|result.toRat| - |truth|) := by
      rw [mul_sub, ← hres_form, ← htruth_form]
    have hbound : |result.toRat - truth| ≤ (10:ℚ) ^ exp := by
      rw [hsub, abs_mul,
          show |if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1| = 1 by split_ifs <;> norm_num,
          one_mul, hres_mag_Mr, abs_le]
      refine ⟨?_, ?_⟩ <;> [linarith [hP.2]; linarith [hP.1]]
    rw [hres_exp]; exact hbound
  rcases hmode with hup | hdn
  · -- upward: coarse ceiling, |r| ∈ ((Mr-1)·10^exp, Mr·10^exp].
    rw [hup] at hnorm_w hrepr
    obtain ⟨hceilval, hEle⟩ := normalizeToRange_16_ceil_pos w mant exp hw_neg hw_lo hw_hi
      (by rw [hw_exp]; omega) (by rw [hw_exp]; exact hr_exp_hi) hnorm_w
    rw [hw_exp] at hEle
    obtain ⟨n, hn_eq, hr_eq⟩ := hrepr
    set c : ℕ := M / 1000 + (if M % 1000 ≠ 0 then 1 else 0) with hc_def
    have hc_ge : M ≤ c * 1000 := by
      rw [hc_def]; rcases Nat.eq_zero_or_pos (M % 1000) with h | h
      · rw [if_neg (by omega)]; omega
      · rw [if_pos (by omega)]; omega
    have hc_lt : c * 1000 < M + 1000 := by
      rw [hc_def]; rcases Nat.eq_zero_or_pos (M % 1000) with h | h
      · rw [if_neg (by omega)]; omega
      · rw [if_pos (by omega)]; omega
    have hMr_val : (Mr : ℚ) * (10:ℚ) ^ exp = (c : ℚ) * 1000 * (10:ℚ) ^ E := by
      rw [← hres_mag_Mr, habs, hceilval, hw_mant, hw_exp, h103]; ring
    have hMle : (M:ℚ) ≤ (c:ℚ) * 1000 := by exact_mod_cast hc_ge
    have hMgt : (c:ℚ) * 1000 - 1000 < (M:ℚ) := by
      have : (c:ℚ) * 1000 < (M:ℚ) + 1000 := by exact_mod_cast hc_lt
      linarith
    have hexp_ge : (10:ℚ) ^ E * 1000 ≤ (10:ℚ) ^ exp := by
      rw [← h103]; exact zpow_le_zpow_right₀ (by norm_num) hEle
    have hup_le : |r.toRat| ≤ (Mr : ℚ) * (10:ℚ) ^ exp := by
      rw [hr_mag, hMr_val]; nlinarith [hMle, hp]
    have hup_gt : ((Mr : ℚ) - 1) * (10:ℚ) ^ exp < |r.toRat| := by
      rw [hr_mag, show ((Mr:ℚ)-1)*(10:ℚ)^exp = (Mr:ℚ)*(10:ℚ)^exp - (10:ℚ)^exp from by ring, hMr_val]
      nlinarith [hMgt, hexp_ge, hp]
    refine ⟨?_, ?_⟩
    · by_contra hcon; push_neg at hcon
      obtain ⟨m0, hm0_norm, hm0_neg, hm0_val⟩ :=
        exists_normalized_grid_below Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
      rcases hxor : (v1.mIsNegative != v2.mIsNegative) with _ | _
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = 1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, one_mul] at htf
        have hrf := hr_form; rw [hif, one_mul] at hrf
        have hge : truth ≤ m0.toRat := by rw [hm0_val]; linarith [hcon, htf]
        have hut := Number.upper_tight truth n hn_eq m0 hm0_norm hge
        rw [← hr_eq, hm0_val] at hut; linarith [hut, hup_gt, hrf]
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = -1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, neg_one_mul] at htf
        have hrf := hr_form; rw [hif, neg_one_mul] at hrf
        have htneg : truth < 0 := by rw [htf]; simpa using hA_pos
        have hle_up := Number.le_upper truth n hn_eq
        rw [← hr_eq] at hle_up
        -- |r| ≤ |truth| here (fine floor), and |truth| < (Mr-1)·10^exp, so |r| < (Mr-1)·10^exp; contra hup_gt.
        linarith [hle_up, htf, hrf, hcon, hup_gt]
    · by_contra hcon; push_neg at hcon
      have hlt : |r.toRat| < ((Mr : ℚ) + 1) * (10:ℚ) ^ exp := by
        rw [show ((Mr:ℚ)+1)*(10:ℚ)^exp = (Mr:ℚ)*(10:ℚ)^exp + (10:ℚ)^exp from by ring]
        linarith [hup_le, hpec]
      rcases hxor : (v1.mIsNegative != v2.mIsNegative) with _ | _
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = 1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, one_mul] at htf
        have hrf := hr_form; rw [hif, one_mul] at hrf
        have hle_up := Number.le_upper truth n hn_eq
        rw [← hr_eq] at hle_up
        -- |truth| = truth ≤ r.toRat = |r.toRat| < (Mr+1)·10^exp, contradicting hcon.
        linarith [hle_up, htf, hrf, hlt, hcon]
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = -1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, neg_one_mul] at htf
        have hrf := hr_form; rw [hif, neg_one_mul] at hrf
        have htneg : truth < 0 := by rw [htf]; simpa using hA_pos
        obtain ⟨m0, hm0_norm, hm0_neg, hm0_val⟩ :=
          exists_normalized_grid_above Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
        set m0' : Number := { m0 with negative_ := true } with hm0'_def
        have hm0'_toRat : m0'.toRat = -m0.toRat := Number.toRat_set_neg_true_of_nn m0 hm0_neg
        have hm0_ne : m0.mantissa_ ≠ 0 := by
          intro h
          have hpos : (0:ℚ) < m0.toRat := by
            rw [hm0_val]; apply mul_pos
            · have hb : (10:ℚ) ^ 15 ≤ (Mr:ℚ) := by exact_mod_cast hmtu_lo
              nlinarith [hb]
            · positivity
          rw [Number.toRat_of_nonneg m0 hm0_neg, h] at hpos; simp at hpos
        have hm0'_norm : m0'.isNormalized := by
          rcases hm0_norm with hz | ⟨h1, h2, h3, h4, h5⟩
          · exact absurd (show m0.mantissa_ = 0 by rw [hz]; rfl) hm0_ne
          · right; exact ⟨h1, h2, h3, h4, h5⟩
        have hm0'_ge : truth ≤ m0'.toRat := by
          rw [hm0'_toRat, hm0_val]; linarith [hcon, htf]
        have hut := Number.upper_tight truth n hn_eq m0' hm0'_norm hm0'_ge
        rw [← hr_eq, hm0'_toRat, hm0_val] at hut
        linarith [hut, hlt, hrf]
  · -- downward: coarse floor, |r| ∈ [Mr·10^exp, (Mr+1)·10^exp).
    obtain ⟨hfloorval, hexpeq⟩ :=
      normalizeToRange_16_floor_pos w mant exp mode (Or.inl hdn) hw_neg hw_lo hw_hi
        (by rw [hw_exp]; omega) (by rw [hw_exp]; exact hr_exp_hi) hnorm_w
    rw [hdn] at hrepr
    obtain ⟨n, hn_eq, hr_eq⟩ := hrepr
    have hexpE : exp = E + 3 := by rw [hexpeq, hw_exp]
    have hMr_val : (Mr : ℚ) * (10:ℚ) ^ exp = ((M / 1000 : ℕ):ℚ) * 1000 * (10:ℚ) ^ E := by
      rw [← hres_mag_Mr, habs, hfloorval, hw_mant, hw_exp, h103]; ring
    have hMge : ((M / 1000 : ℕ):ℚ) * 1000 ≤ (M:ℚ) := by
      have : (M/1000)*1000 ≤ M := by omega
      have := (Nat.cast_le (α:=ℚ)).mpr this; push_cast at this ⊢; linarith
    have hMlt : (M:ℚ) < ((M / 1000 : ℕ):ℚ) * 1000 + 1000 := by
      have hnat : M < (M/1000 + 1)*1000 := by omega
      have := (Nat.cast_lt (α:=ℚ)).mpr hnat; push_cast at this; linarith
    have hexp10 : (10:ℚ) ^ exp = (10:ℚ) ^ E * 1000 := by rw [hexpE, h103]
    have hdn_ge : (Mr : ℚ) * (10:ℚ) ^ exp ≤ |r.toRat| := by
      rw [hr_mag, hMr_val]; nlinarith [hMge, hp]
    have hdn_lt : |r.toRat| < ((Mr : ℚ) + 1) * (10:ℚ) ^ exp := by
      rw [hr_mag, show ((Mr:ℚ)+1)*(10:ℚ)^exp = (Mr:ℚ)*(10:ℚ)^exp + (10:ℚ)^exp from by ring,
          hMr_val, hexp10]
      nlinarith [hMlt, hp]
    refine ⟨?_, ?_⟩
    · by_contra hcon; push_neg at hcon
      rcases hxor : (v1.mIsNegative != v2.mIsNegative) with _ | _
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = 1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, one_mul] at htf
        have hrf := hr_form; rw [hif, one_mul] at hrf
        have hle_lo := Number.lower_le truth n hn_eq
        rw [← hr_eq] at hle_lo
        -- Mr·10^exp ≤ |r| = r.toRat ≤ truth = |truth| < (Mr-1)·10^exp; contra.
        linarith [hdn_ge, hle_lo, htf, hrf, hcon]
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = -1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, neg_one_mul] at htf
        have hrf := hr_form; rw [hif, neg_one_mul] at hrf
        have htneg : truth < 0 := by rw [htf]; simpa using hA_pos
        obtain ⟨m0, hm0_norm, hm0_neg, hm0_val⟩ :=
          exists_normalized_grid_below Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
        set m0' : Number := { m0 with negative_ := true } with hm0'_def
        have hm0'_toRat : m0'.toRat = -m0.toRat := Number.toRat_set_neg_true_of_nn m0 hm0_neg
        have hm0_ne : m0.mantissa_ ≠ 0 := by
          intro h
          have hpos : (0:ℚ) < m0.toRat := by
            rw [hm0_val]; apply mul_pos
            · have hb : (10:ℚ) ^ 15 ≤ (Mr:ℚ) := by exact_mod_cast hmtu_lo
              nlinarith [hb]
            · positivity
          rw [Number.toRat_of_nonneg m0 hm0_neg, h] at hpos; simp at hpos
        have hm0'_norm : m0'.isNormalized := by
          rcases hm0_norm with hz | ⟨h1, h2, h3, h4, h5⟩
          · exact absurd (show m0.mantissa_ = 0 by rw [hz]; rfl) hm0_ne
          · right; exact ⟨h1, h2, h3, h4, h5⟩
        have hm0'_le : m0'.toRat ≤ truth := by
          rw [hm0'_toRat, hm0_val]; linarith [hcon, htf]
        have hlt := Number.lower_tight truth n hn_eq m0' hm0'_norm hm0'_le
        rw [← hr_eq, hm0'_toRat, hm0_val] at hlt
        linarith [hlt, hdn_ge, hrf]
    · by_contra hcon; push_neg at hcon
      rcases hxor : (v1.mIsNegative != v2.mIsNegative) with _ | _
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = 1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, one_mul] at htf
        have hrf := hr_form; rw [hif, one_mul] at hrf
        obtain ⟨m0, hm0_norm, hm0_neg, hm0_val⟩ :=
          exists_normalized_grid_above Mr exp hmtu_lo hmtu_hi hgb_lo hgb_hi
        have hm0le : m0.toRat ≤ truth := by rw [hm0_val]; linarith [hcon, htf]
        have hlt_lo := Number.lower_tight truth n hn_eq m0 hm0_norm hm0le
        rw [← hr_eq, hm0_val] at hlt_lo
        linarith [hlt_lo, hdn_lt, hrf]
      · have hif : (if (v1.mIsNegative != v2.mIsNegative) then (-1:ℚ) else 1) = -1 := by rw [hxor]; simp
        have htf := htruth_form; rw [hif, neg_one_mul] at htf
        have hrf := hr_form; rw [hif, neg_one_mul] at hrf
        have hle_lo := Number.lower_le truth n hn_eq
        rw [← hr_eq] at hle_lo
        linarith [hle_lo, htf, hrf, hdn_lt, hcon]

end XRPL.Model.Protocol
