import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Vault.Common.SubZeroShape

/-! # Shared `ofNumber` / exchange-pipeline / grid-spacing lemmas

General value-exactness, exchange-pipeline, and grid-spacing lemmas shared by the
withdraw (`WithdrawBounds`) and clawback (`ClawbackAccuracy`) accuracy suites. None
carries a clawback- or withdraw-specific dependency, so they live upstream of both
to keep the two suites off a mutual import cycle. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-! ## Shared two-stage `mul`/`div` exchange pipeline

Both clawback exchange helpers (`assetsToSharesWithdraw`,
`sharesToAssetsWithdraw`) compute the same shape: a `to_nearest` product `S · A`,
then a `to_nearest` quotient by an *exact* divisor `nav`. Under `WithdrawNavExact`
the divisor is used at its exact value, so only the two interior roundings
contribute and the composed result stays within `depositε` of the exact ratio. -/

/-- **Core relative-error bound of the two-stage `mul`/`div` exchange pipeline.**
For normalized positive `S`, `A` and a normalized positive divisor `nav`, the
`to_nearest` product `P = S·A` followed by the `to_nearest` quotient `Q = P/nav`
lands within `depositε` of the exact ratio `S·A/nav`. `hPm` (nonzero product) is
discharged by the caller from a magnitude floor. -/
lemma RawVault.exchange_pipeline_within (S A nav P Q : Number)
    (hS : S.isNormalized) (hA : A.isNormalized) (hnav : nav.isNormalized)
    (hSpos : 0 < S.toRat) (hApos : 0 < A.toRat) (hnavpos : 0 < nav.toRat)
    (hP : S.operator_mul A .to_nearest = .ok P)
    (hQ : P.operator_div nav .to_nearest = .ok Q)
    (hPm : P.mantissa_ ≠ 0) (hQm : Q.mantissa_ ≠ 0) :
    Q.isNormalized ∧ 0 < Q.toRat ∧
    |Q.toRat - S.toRat * A.toRat / nav.toRat|
      ≤ S.toRat * A.toRat / nav.toRat * depositε := by
  have hSm : S.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hSpos.ne'
  have hAm : A.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hApos.ne'
  have hnavm : nav.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hnavpos.ne'
  set T0 : ℚ := S.toRat * A.toRat with hT0_def
  have hT0_pos : 0 < T0 := mul_pos hSpos hApos
  -- product stage
  have hPnorm : P.isNormalized :=
    operator_mul_result_isNormalized S A P .to_nearest hS hA hSm hAm hP hPm
  have hPbound := operator_mul_rounds_to_nearest S A P hS hA hP hPm
  have hPb : |P.toRat - T0| ≤ T0 * (5 / (2 ^ 63 + 7)) := by
    have h1 : |P.toRat - S.toRat * A.toRat| ≤ |S.toRat * A.toRat| * (5 / (2 ^ 63 + 7)) := hPbound
    rw [← hT0_def, abs_of_pos hT0_pos] at h1
    exact h1
  have hPpos : 0 < P.toRat := by
    have := abs_le.mp hPb
    have hε₂lt : (5 : ℚ) / (2 ^ 63 + 7) < 1 := by norm_num
    nlinarith
  -- division stage
  have hQnorm : Q.isNormalized :=
    operator_div_result_isNormalized P nav Q .to_nearest hPnorm hnav hPm hnavm hQ hQm
  have hQbound := operator_div_rounds_to_nearest P nav Q hPnorm hnav hQ hQm
  have hPN_pos : 0 < P.toRat / nav.toRat := div_pos hPpos hnavpos
  have hQpos : 0 < Q.toRat := by
    have h1 : |Q.toRat - P.toRat / nav.toRat| ≤ |P.toRat / nav.toRat| * (6 / (2 ^ 63 - 3)) := hQbound
    rw [abs_of_pos hPN_pos] at h1
    have := abs_le.mp h1
    nlinarith
  have h3 : |Q.toRat * nav.toRat - P.toRat| ≤ P.toRat * (6 / (2 ^ 63 - 3)) := by
    have h1 : |Q.toRat - P.toRat / nav.toRat| ≤ P.toRat / nav.toRat * (6 / (2 ^ 63 - 3)) := by
      have h0' : |Q.toRat - P.toRat / nav.toRat|
          ≤ |P.toRat / nav.toRat| * (6 / (2 ^ 63 - 3)) := hQbound
      rw [abs_of_pos hPN_pos] at h0'
      exact h0'
    have h2 : |Q.toRat - P.toRat / nav.toRat| * nav.toRat = |Q.toRat * nav.toRat - P.toRat| := by
      rw [show Q.toRat * nav.toRat - P.toRat
        = (Q.toRat - P.toRat / nav.toRat) * nav.toRat from by field_simp]
      rw [abs_mul, abs_of_pos hnavpos]
    calc |Q.toRat * nav.toRat - P.toRat|
        = |Q.toRat - P.toRat / nav.toRat| * nav.toRat := h2.symm
      _ ≤ P.toRat / nav.toRat * (6 / (2 ^ 63 - 3)) * nav.toRat := by nlinarith [hnavpos]
      _ = P.toRat * (6 / (2 ^ 63 - 3)) := by field_simp
  -- compose the two stages against the exact divisor
  have hcomp := div_pipeline_rel_bound nav.toRat nav.toRat T0 P.toRat Q.toRat
    (6 / (2 ^ 63 - 3)) (5 / (2 ^ 63 + 7)) (6 / (2 ^ 63 - 3)) depositε hT0_pos
    (le_of_lt hQpos) (by rw [sub_self, abs_zero]; positivity) hPb h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deposit_pipeline_up deposit_pipeline_lo
  refine ⟨hQnorm, hQpos, ?_⟩
  have heq : Q.toRat - T0 / nav.toRat = (Q.toRat * nav.toRat - T0) / nav.toRat := by
    field_simp
  rw [hT0_def] at heq ⊢
  rw [← hT0_def, heq, abs_div, abs_of_pos hnavpos, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hcomp (le_of_lt hnavpos)

/-- **`ofNumber .int64` with `to_nearest` rounds within half a unit.** On a
normalized sign-cleared `Number`, the int64 conversion lands within `1/2` of the
value, returns a nonnegative integer. The `1/2` comes from the underlying
`to_rep` round-to-nearest. -/
lemma STAmount.ofNumber_int64_to_nearest_within_half (n : Number) (a : STAmount)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber .int64 n .to_nearest = .ok a) :
    |a.toRat - n.toRat| ≤ 1 / 2 ∧ a.toRat.den = 1 ∧ 0 ≤ a.toRat := by
  have hint : (NumericType.int64).isIntegral = true := by decide
  have hneg' : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  unfold STAmount.ofNumber at hok
  rw [if_pos hint] at hok
  have hw_eq : (if decide (n.signum < 0) = true then n.operator_neg else n) = n := by
    rw [hneg']; rfl
  rw [hw_eq] at hok
  cases hrep : n.to_rep .to_nearest with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hrep] at hok
    simp only [] at hok
    rw [STAmount.checked] at hok
    have hwithin := Number.to_rep_to_nearest_within_half n intValue hn hneg hrep
    have hn_nonneg : 0 ≤ n.toRat := by rw [Number.toRat_of_nonneg n hneg]; positivity
    have hiv_nonneg : (0 : ℤ) ≤ intValue.toInt := by
      have hb := abs_le.mp hwithin
      have h2 : (-1 : ℚ) < (intValue.toInt : ℚ) := by linarith [hb.1]
      have : (-1 : ℤ) < intValue.toInt := by exact_mod_cast h2
      omega
    have hiv_le : intValue.toInt ≤ (2 : ℤ) ^ 63 - 1 := by
      have := Int64.toInt_lt intValue; omega
    have htu : (intValue.toUInt64.toNat : ℤ) = intValue.toInt :=
      toUInt64_toNat_of_nonneg intValue hiv_nonneg
    have hfit : intValue.toUInt64.toNat ≤ maxRep.toNat := by rw [maxRep_val]; omega
    have hexact := STAmount.canonicalize_integral_toRat _ a .to_nearest
      (show (STAmount.unchecked .int64 intValue.toUInt64 0 (decide (n.signum < 0))).integral = true
        from hint) rfl hfit hok
    have haval : a.toRat = (intValue.toInt : ℚ) := by
      rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
      show ((if decide (n.signum < 0) = true then -(intValue.toUInt64.toNat : ℤ)
        else (intValue.toUInt64.toNat : ℤ) : ℤ) : ℚ) = (intValue.toInt : ℚ)
      rw [hneg']
      simp only [Bool.false_eq_true, if_false]
      exact_mod_cast htu
    refine ⟨?_, ?_, ?_⟩
    · rw [haval]; exact hwithin
    · rw [haval]; exact Rat.den_intCast _
    · rw [haval]; exact_mod_cast hiv_nonneg

/-- A nonzero canonical amount (fractional or integral) is at least `10 ^ (-81)`
in magnitude. -/
lemma STAmount.canonical_disj_abs_toRat_ge (s : STAmount)
    (hc : s.IOUCanonical ∨ s.IntegralCanonical) (hnz : s.mValue ≠ 0) :
    (10 : ℚ) ^ (-81 : ℤ) ≤ |s.toRat| := by
  rw [STAmount.abs_toRat]
  rcases hc with hio | hint
  · have hoff : (10 : ℚ) ^ (-96 : ℤ) ≤ (10 : ℚ) ^ s.mOffset :=
      zpow_le_zpow_right₀ (by norm_num) hio.exp_lo
    have hsplit : (10 : ℚ) ^ (-81 : ℤ) = (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ (-96 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 15, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
    rw [hsplit]
    have h10 : (0 : ℚ) < (10 : ℚ) ^ s.mOffset := zpow_pos (by norm_num) _
    calc (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ (-96 : ℤ)
        ≤ (10 : ℚ) ^ (15 : ℕ) * (10 : ℚ) ^ s.mOffset :=
          mul_le_mul_of_nonneg_left hoff (by positivity)
      _ ≤ (s.mValue.toNat : ℚ) * 10 ^ s.mOffset :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hio.mant_lo) (le_of_lt h10)
  · rw [hint.offset_zero]
    have h1 : 1 ≤ s.mValue.toNat := by
      have hne : s.mValue.toNat ≠ 0 := fun h0 => hnz (by rw [← UInt64.toNat_inj]; simpa using h0)
      omega
    have h1q : (1 : ℚ) ≤ (s.mValue.toNat : ℚ) := by exact_mod_cast h1
    have hp : ((10 : ℚ) ^ (-81 : ℤ)) ≤ 1 := by
      rw [show ((-81) : ℤ) = -(81 : ℕ) from rfl, zpow_neg, zpow_natCast, inv_le_one_iff₀]
      right; norm_num
    calc (10 : ℚ) ^ (-81 : ℤ) ≤ 1 := hp
      _ ≤ (s.mValue.toNat : ℚ) * 10 ^ (0 : ℤ) := by simpa using h1q

/-- **A sign-cleared source rounds up to a non-negative `ofNumber` output** (any
mode, any numeric type). Integral outputs floor a non-negative `to_rep`; fractional
outputs snap a non-negative 16-digit mantissa. -/
lemma STAmount.ofNumber_nonneg (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) : 0 ≤ result.toRat := by
  by_cases hint : nt.isIntegral = true
  · unfold STAmount.ofNumber at hok
    simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hint] at hok
    cases hr : n.to_rep mode with
    | error e => rw [hr] at hok; exact absurd hok (by simp)
    | ok intValue =>
      rw [hr] at hok
      simp only [] at hok
      obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n mode intValue hneg hr
      have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
        toUInt64_toNat_le_maxRep intValue hnn hle
      have hres_val : result.toRat = (intValue.toInt : ℚ) := by
        have hexact := STAmount.canonicalize_integral_toRat
          (STAmount.unchecked nt intValue.toUInt64 0 false) result mode
          (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint) rfl
          hval hok
        rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
        show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
        rw [toUInt64_toNat_of_nonneg intValue hnn]
      rw [hres_val]; exact_mod_cast hnn
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    by_cases hz : result.mValue = 0
    · rw [STAmount.toRat_signed, hz]; simp
    · have hn_ne : n.mantissa_ ≠ 0 :=
        STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result hnt_frac hok hz
      obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
      have hexp_lo : minExponent ≤ n.exponent_ := by
        rcases hn with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
        · exact hlo
      have hok' : STAmount.ofNumber .fractional n mode = .ok result := by rw [← hnt_frac]; exact hok
      have hexp_hi : n.exponent_ + 4 ≤ maxExponent :=
        STAmount.ofNumber_iou_success_exp_range n mode result hlo19 hhi19 hexp_lo hok' hz
      obtain ⟨mant, exp, -, hval, -, hcast, -, -, -, -⟩ :=
        STAmount.ofNumber_iou_snap_pos nt n mode result hnt_frac hneg
          hlo19 hhi19 hexp_lo hexp_hi hok hz
      rw [hval, hcast]; positivity

/-- **`toNumber` of a zero-mantissa fractional amount is the exact zero.** The IOU
lift short-circuits: `signedDrops = 0`, `ofMantissaExp` returns `IOUAmount.zero`,
whose `from_rep` normalizes a zero mantissa to `Number.zero`. -/
lemma STAmount.toNumber_zero_fractional (s : STAmount) (mode : rounding_mode)
    (hfr : s.integral = false) (hz : s.mValue = 0) :
    s.toNumber mode = .ok Number.zero := by
  unfold STAmount.toNumber
  rw [if_neg (by rw [hfr]; decide)]
  have hsd : s.signedDrops.toInt64 = 0 := by
    have h0 : s.signedDrops = 0 := by unfold STAmount.signedDrops; rw [hz]; simp
    rw [h0]; rfl
  have hiou : s.iou mode = .ok IOUAmount.zero := by
    unfold STAmount.iou IOUAmount.ofMantissaExp
    rw [if_neg (by rw [hfr]; decide), hsd]
    show IOUAmount.normalize ⟨0, s.mOffset⟩ mode = .ok IOUAmount.zero
    unfold IOUAmount.normalize
    rw [if_pos (show (((⟨0, s.mOffset⟩ : IOUAmount)).mantissa_ == 0) = true from rfl)]
  rw [hiou]
  show IOUAmount.toNumber IOUAmount.zero mode = .ok Number.zero
  unfold IOUAmount.toNumber IOUAmount.zero Number.from_rep Number.normalized Number.normalize
  rw [show doNormalize (Number.unchecked ((0 : Int64) < 0) (0 : Int64).toInt.natAbs.toUInt64 (-100)).negative_
        (Number.unchecked ((0 : Int64) < 0) (0 : Int64).toInt.natAbs.toUInt64 (-100)).mantissa_
        (Number.unchecked ((0 : Int64) < 0) (0 : Int64).toInt.natAbs.toUInt64 (-100)).exponent_
        largeRange.min largeRange.max mode
      = doNormalize false 0 (-100) largeRange.min largeRange.max mode from rfl]
  unfold doNormalize
  rw [if_pos (by decide)]

/-- `canonicalize` never changes the numeric type. -/
lemma STAmount.canonicalize_mNumericType (s result : STAmount) (mode : rounding_mode)
    (hok : s.canonicalize mode = .ok result) : result.mNumericType = s.mNumericType := by
  unfold STAmount.canonicalize at hok
  by_cases hint : s.integral = true
  · rw [if_pos hint] at hok
    by_cases hz : (s.mValue == 0 || decide (s.mOffset ≤ -20)) = true
    · rw [if_pos hz] at hok
      rw [← Except.ok.inj hok]
    · rw [if_neg hz] at hok
      by_cases hmo : s.mOffset > s.mNumericType.maxOffset
      · rw [if_pos hmo] at hok; exact absurd hok (by simp)
      · rw [if_neg hmo] at hok
        simp only [] at hok
        cases hio : IntAmount.ofNumber (Number.unchecked s.mIsNegative s.mValue s.mOffset) mode with
        | error e => rw [hio] at hok; exact absurd hok (by simp)
        | ok i =>
          rw [hio] at hok
          simp only [] at hok
          split at hok
          · exact absurd hok (by simp)
          · rw [← Except.ok.inj hok]
  · rw [if_neg hint] at hok
    cases hiou : s.iou mode with
    | error e => rw [hiou] at hok; exact absurd hok (by simp)
    | ok i =>
      rw [hiou] at hok
      simp only [] at hok
      rw [← Except.ok.inj hok]

/-- `ofNumber` outputs an amount of the requested numeric type. -/
lemma STAmount.ofNumber_mNumericType (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hok : STAmount.ofNumber nt n mode = .ok result) :
    result.mNumericType = nt := by
  unfold STAmount.ofNumber at hok
  by_cases hint : nt.isIntegral = true
  · rw [if_pos hint] at hok
    cases hrep : (if decide (n.signum < 0) = true then n.operator_neg else n).to_rep mode with
    | error e => rw [hrep] at hok; exact absurd hok (by simp)
    | ok iv =>
      rw [hrep] at hok; simp only [] at hok
      rw [STAmount.checked] at hok
      exact STAmount.canonicalize_mNumericType _ result mode hok
  · rw [if_neg hint] at hok
    cases hnorm : (if decide (n.signum < 0) = true then n.operator_neg else n).normalizeToRange
        kMinValue kMaxValue mode with
    | error e => rw [hnorm] at hok; exact absurd hok (by simp)
    | ok me =>
      obtain ⟨mant, exp⟩ := me
      rw [hnorm] at hok; simp only [] at hok
      rw [STAmount.checked] at hok
      exact STAmount.canonicalize_mNumericType _ result mode hok

/-- **`toNumber` is value-exact on any `ofNumber` output.** Integral outputs route
through the offset-`0` integral exactness (keyed on the stored magnitude, no carried
bound needed); fractional outputs are `IOUCanonical` (exact 19-digit lift) or zero
(exact zero). -/
lemma STAmount.ofNumber_toNumber_exact (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized) (_hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    ∃ an : Number, result.toNumber .to_nearest = .ok an ∧ an.toRat = result.toRat ∧
      an.isNormalized := by
  by_cases hint : nt.isIntegral = true
  · obtain ⟨hnt', hoff, hval⟩ := STAmount.ofNumber_integral_facts nt n mode result hint hok
    obtain ⟨sn, h1, h2, h3, -⟩ :=
      STAmount.toNumber_integral_exact' result .to_nearest (by rw [hnt']; exact hint) hoff hval
    exact ⟨sn, h1, h2, h3⟩
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    have hty : result.integral = false := by
      show result.mNumericType.isIntegral = false
      rw [STAmount.ofNumber_mNumericType nt n mode result hok, hnt_frac]; decide
    by_cases hz : result.mValue = 0
    · refine ⟨Number.zero, STAmount.toNumber_zero_fractional result .to_nearest hty hz, ?_, ?_⟩
      · rw [Number.toRat_zero, STAmount.toRat_signed, hz]; simp
      · exact Or.inl rfl
    · have hn_ne : n.mantissa_ ≠ 0 :=
        STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result hnt_frac hok hz
      obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
      have hexp_lo : minExponent ≤ n.exponent_ := by
        rcases hn with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
        · exact hlo
      have hok' : STAmount.ofNumber .fractional n mode = .ok result := by rw [← hnt_frac]; exact hok
      have hcanon := (STAmount.ofNumber_iou_ok_facts n mode result hlo19 hhi19 hexp_lo hok' hz).1
      exact STAmount.toNumber_iou_exact result .to_nearest hcanon

/-- **`toNumber` is value-exact on any `ofNumber` output**, needing only source
normalization (the sign bit is not read: `ofNumber` clears it before rounding). -/
lemma STAmount.ofNumber_toNumber_exact_of_norm (nt : NumericType) (n : Number)
    (mode : rounding_mode) (result : STAmount) (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    ∃ an : Number, result.toNumber .to_nearest = .ok an ∧ an.toRat = result.toRat ∧
      an.isNormalized := by
  by_cases hint : nt.isIntegral = true
  · obtain ⟨hnt', hoff, hval⟩ := STAmount.ofNumber_integral_facts nt n mode result hint hok
    obtain ⟨sn, h1, h2, h3, -⟩ :=
      STAmount.toNumber_integral_exact' result .to_nearest (by rw [hnt']; exact hint) hoff hval
    exact ⟨sn, h1, h2, h3⟩
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    have hty : result.integral = false := by
      show result.mNumericType.isIntegral = false
      rw [STAmount.ofNumber_mNumericType nt n mode result hok, hnt_frac]; decide
    by_cases hz : result.mValue = 0
    · refine ⟨Number.zero, STAmount.toNumber_zero_fractional result .to_nearest hty hz, ?_, ?_⟩
      · rw [Number.toRat_zero, STAmount.toRat_signed, hz]; simp
      · exact Or.inl rfl
    · have hn_ne : n.mantissa_ ≠ 0 :=
        STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result hnt_frac hok hz
      obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
      have hexp_lo : minExponent ≤ n.exponent_ := by
        rcases hn with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
        · exact hlo
      have hok' : STAmount.ofNumber .fractional n mode = .ok result := by rw [← hnt_frac]; exact hok
      have hcanon := (STAmount.ofNumber_iou_ok_facts n mode result hlo19 hhi19 hexp_lo hok' hz).1
      exact STAmount.toNumber_iou_exact result .to_nearest hcanon

/-- **A nonzero `ofNumber` output is canonical for its kind.** Integral outputs are
`IntegralCanonical`; fractional outputs are `IOUCanonical`. Feeds the magnitude
floor `canonical_disj_abs_toRat_ge`. -/
lemma STAmount.ofNumber_disj_canonical (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized)
    (hok : STAmount.ofNumber nt n mode = .ok result) (hnz : result.mValue ≠ 0) :
    result.IOUCanonical ∨ result.IntegralCanonical := by
  by_cases hint : nt.isIntegral = true
  · exact Or.inr (STAmount.ofNumber_integral_canonical nt n mode result hint hok).1
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    have hn_ne : n.mantissa_ ≠ 0 :=
      STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result hnt_frac hok hnz
    obtain ⟨hlo19, hhi19⟩ := hn.mantissaBounds_nat hn_ne
    have hexp_lo : minExponent ≤ n.exponent_ := by
      rcases hn with h0 | ⟨_, _, _, hlo, _⟩
      · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hn_ne
      · exact hlo
    have hok' : STAmount.ofNumber .fractional n mode = .ok result := by rw [← hnt_frac]; exact hok
    exact Or.inl (STAmount.ofNumber_iou_ok_facts n mode result hlo19 hhi19 hexp_lo hok' hnz).1

/-- **Full input spec of an `ofNumber` output** for feeding `assetsToSharesWithdraw_spec`:
non-negative (sign-cleared source), exact `toNumber`, and the `10^(-81)` magnitude
floor. -/
lemma STAmount.ofNumber_input_spec (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n mode = .ok result) :
    0 ≤ result.toRat ∧
    (∃ an : Number, result.toNumber .to_nearest = .ok an ∧ an.toRat = result.toRat ∧
      an.isNormalized) ∧
    (result.mValue ≠ 0 → (10 : ℚ) ^ (-81 : ℤ) ≤ |result.toRat|) :=
  ⟨STAmount.ofNumber_nonneg nt n mode result hn hneg hok,
   STAmount.ofNumber_toNumber_exact nt n mode result hn hneg hok,
   fun hnz => STAmount.canonical_disj_abs_toRat_ge result
     (STAmount.ofNumber_disj_canonical nt n mode result hn hok hnz) hnz⟩

/-- A successful `ofNumber` on any numeric type forces a nonzero source mantissa
from a nonzero result: integral via `to_rep`, fractional via the 16-digit snap. -/
lemma STAmount.ofNumber_source_ne_zero (nt : NumericType) (n : Number) (mode : rounding_mode)
    (result : STAmount)
    (hok : STAmount.ofNumber nt n mode = .ok result) (hres : result.mValue ≠ 0) :
    n.mantissa_ ≠ 0 := by
  by_cases hint : nt.isIntegral = true
  · exact STAmount.ofNumber_integral_source_ne_zero nt n mode result hint hok hres
  · have hnt_frac : nt = .fractional := by
      cases nt with
      | fractional => rfl
      | integral mv mo ms msh => simp [NumericType.isIntegral] at hint
    exact STAmount.ofNumber_iou_mantissa_ne_zero nt n mode result hnt_frac hok hres

/-- **`assetsToSharesWithdraw` packs the shares through `ofNumber .int64`,** so a
nonzero result is a canonical `int64` record. -/
lemma assetsToSharesWithdraw_int64_canonical (v : Vault) (assets shares : STAmount)
    (truncateShares waiveUnrealizedLoss : Bool)
    (hok : assetsToSharesWithdraw v assets truncateShares waiveUnrealizedLoss = .ok shares)
    (hnz : shares.isZero = false) :
    shares.IntegralCanonical ∧ shares.mNumericType = .int64 := by
  obtain ⟨nav, -, hcase⟩ :=
    assetsToSharesWithdraw_ok_reduces v assets shares truncateShares waiveUnrealizedLoss hok
  rcases hcase with ⟨-, hzero⟩ | ⟨-, an, sa, sn, sn', -, -, -, -, hofn⟩
  · rw [hzero, STAmount.zero_isZero] at hnz; exact absurd hnz (by decide)
  · exact STAmount.ofNumber_integral_canonical .int64 sn' .to_nearest shares (by decide) hofn

/-- A nonzero `assetsToSharesWithdraw` result is `Canonical` (feeds
`sharesToAssetsWithdraw_bounds_proof`). -/
lemma assetsToSharesWithdraw_shares_canonical (v : Vault) (assets shares : STAmount)
    (truncateShares waiveUnrealizedLoss : Bool)
    (hok : assetsToSharesWithdraw v assets truncateShares waiveUnrealizedLoss = .ok shares)
    (hnz : shares.isZero = false) :
    shares.Canonical := by
  obtain ⟨hic, hnt⟩ :=
    assetsToSharesWithdraw_int64_canonical v assets shares truncateShares waiveUnrealizedLoss hok hnz
  have hint : shares.integral = true := by show shares.mNumericType.isIntegral = true; rw [hnt]; decide
  refine ⟨fun _ => ⟨hic, by rw [hnt]; decide⟩, fun hfr => ?_⟩
  rw [hint] at hfr; exact absurd hfr (by decide)

/-- **`toNumber` is value-exact on a nonzero `sharesToAssetsWithdraw` payout.** The
payout packs through `ofNumber v.numericType (NAVShares/sharesTotal) .downward`; its
division source is normalized (both operands normalized and nonzero once the payout
is nonzero), so `ofNumber_toNumber_exact_of_norm` applies. -/
lemma Vault.sharesToAssetsWithdraw_toNumber_exact_of_ne (v : Vault)
    (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (hc : shares.Canonical)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets)
    (hne : assets.mValue ≠ 0) :
    ∃ an : Number, assets.toNumber .to_nearest = .ok an ∧
      an.toRat = assets.toRat ∧ an.isNormalized := by
  obtain ⟨nav, hsub, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets waiveUnrealizedLoss hok
  rcases hcase with ⟨hnav2m, hzero⟩ |
      ⟨hnav2m, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · exfalso; rw [hzero, STAmount.zero_mValue] at hne; exact hne rfl
  · have hnav2norm : nav.isNormalized := by
      cases waiveUnrealizedLoss with
      | false =>
        exact operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm v.wf.lossUnrealized_norm hsub
      | true => exact operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm (Or.inl rfl) hsub
    obtain ⟨sn0, hsn0ok, -, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
    have hsnnorm : sharesNumber.isNormalized := by
      rw [show sharesNumber = sn0 from (Except.ok.inj (hsn0ok.symm.trans hsn)).symm]; exact hsn0norm
    have hanm : assetsNumber.mantissa_ ≠ 0 :=
      STAmount.ofNumber_source_ne_zero v.numericType assetsNumber .downward assets hof hne
    have hST_ne : ¬ v.sharesTotal.operator_eq Number.zero = true := by
      intro h0
      unfold Number.operator_div at hdiv
      rw [if_pos h0] at hdiv
      exact absurd hdiv (by simp)
    have hSTm : v.sharesTotal.mantissa_ ≠ 0 := by
      intro h0
      exact hST_ne (by
        rw [Number.eq_zero_of_mantissa_zero v.sharesTotal v.wf.sharesTotal_norm h0]; decide)
    have hNAVm : NAVShares.mantissa_ ≠ 0 :=
      operator_div_numerator_ne_zero_sz NAVShares v.sharesTotal assetsNumber .to_nearest hST_ne hdiv hanm
    obtain ⟨hnav2_m', hsn_m⟩ := operator_mul_operands_ne_zero hnav2norm hsnnorm hmul hNAVm
    have hNAVnorm : NAVShares.isNormalized :=
      operator_mul_result_isNormalized nav sharesNumber NAVShares .to_nearest
        hnav2norm hsnnorm hnav2_m' hsn_m hmul hNAVm
    have hANnorm : assetsNumber.isNormalized :=
      operator_div_result_isNormalized NAVShares v.sharesTotal assetsNumber .to_nearest
        hNAVnorm v.wf.sharesTotal_norm hNAVm hSTm hdiv hanm
    exact STAmount.ofNumber_toNumber_exact_of_norm v.numericType assetsNumber .downward assets hANnorm hof

/-- Every `sharesToAssetsWithdraw` payout carries the vault's numeric type. -/
lemma Vault.sharesToAssetsWithdraw_mNumericType (v : Vault) (shares assets : STAmount)
    (waiveUnrealizedLoss : Bool)
    (hok : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets) :
    assets.mNumericType = v.numericType := by
  obtain ⟨_, _, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets waiveUnrealizedLoss hok
  rcases hcase with ⟨_, hzero⟩ | ⟨_, _, _, an, _, _, _, hof⟩
  · rw [hzero]; cases v.numericType <;> rfl
  · exact STAmount.ofNumber_mNumericType v.numericType an .downward assets hof

/-- **`toNumber` is value-exact and normalized on any `sharesToAssetsWithdraw`
payout,** the zero payout included. -/
lemma Vault.sharesToAssetsWithdraw_toNumber_facts (v : Vault)
    (shares assets : STAmount) (waiveUnrealizedLoss : Bool) (arn : Number) (hc : shares.Canonical)
    (hprice : v.sharesToAssetsWithdraw shares waiveUnrealizedLoss = .ok assets)
    (hnum : assets.toNumber .to_nearest = .ok arn) :
    arn.toRat = assets.toRat ∧ arn.isNormalized := by
  by_cases hz : assets.mValue = 0
  · have hnt : assets.mNumericType = v.numericType :=
      Vault.sharesToAssetsWithdraw_mNumericType v shares assets waiveUnrealizedLoss hprice
    by_cases hint : v.numericType.isIntegral = true
    · obtain ⟨hshape_nt, hshape_off, hshape_val⟩ :=
        Vault.sharesToAssetsWithdraw_integral_shape v shares assets waiveUnrealizedLoss hint hprice
      obtain ⟨sn, hsn_ok, hsn_val, hsn_norm, -⟩ :=
        STAmount.toNumber_integral_exact' assets .to_nearest (by rw [hshape_nt]; exact hint)
          hshape_off hshape_val
      rw [show arn = sn from Except.ok.inj (hnum.symm.trans hsn_ok)]
      exact ⟨hsn_val, hsn_norm⟩
    · have hvfr : v.numericType.isIntegral = false := by
        cases hh : v.numericType.isIntegral with
        | true => exact absurd hh hint
        | false => rfl
      have hfr : assets.integral = false := by
        show assets.mNumericType.isIntegral = false; rw [hnt]; exact hvfr
      rw [show arn = Number.zero from
        Except.ok.inj (hnum.symm.trans (STAmount.toNumber_zero_fractional assets .to_nearest hfr hz))]
      refine ⟨?_, Or.inl rfl⟩
      rw [Number.toRat_zero, STAmount.toRat_signed, hz]; simp
  · obtain ⟨an, hnum', hval, hnorm⟩ :=
      Vault.sharesToAssetsWithdraw_toNumber_exact_of_ne v shares assets waiveUnrealizedLoss hc hprice hz
    rw [show arn = an from Except.ok.inj (hnum.symm.trans hnum')]
    exact ⟨hval, hnorm⟩

/-! ## Grid-spacing support for the fractional `clawback_vault_updates` subtractions

A `to_nearest` `Number` subtraction can spuriously flush to a zero mantissa only
when the true difference is below `10 ^ 18 · 10 ^ minExponent = 10 ^ (-32750)`. The
grid-spacing lemma pins a nonzero difference of two numbers on the `10 ^ E` grid at
`≥ 10 ^ E`; for the clawback operands (both `≥ 10⁻⁸¹`, so exponents `≥ -99`) that
floor `10⁻⁹⁹` clears the threshold, so the difference never underflows and the
`operator_sub` rounding bound applies. -/

/-- A number's value is an integer multiple of `10 ^ E` whenever `E ≤ its exponent`. -/
lemma Number.toRat_int_mul_zpow (x : Number) (E : Int) (hE : E ≤ x.exponent_) :
    ∃ k : ℤ, x.toRat = (k : ℚ) * (10:ℚ)^E := by
  refine ⟨(if x.negative_ then -(x.mantissa_.toNat:ℤ) else (x.mantissa_.toNat:ℤ))
            * (10:ℤ)^((x.exponent_ - E).toNat), ?_⟩
  have hexp : (10:ℚ)^x.exponent_ = (10:ℚ)^((x.exponent_ - E).toNat) * (10:ℚ)^E := by
    rw [← zpow_natCast (10:ℚ) ((x.exponent_ - E).toNat), Int.toNat_of_nonneg (by omega),
        ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]
    congr 1; omega
  by_cases hneg : x.negative_
  · rw [Number.toRat_of_neg x hneg, if_pos hneg]; push_cast; rw [hexp]; ring
  · rw [Number.toRat_of_nonneg x (by simpa using hneg), if_neg hneg]; push_cast; rw [hexp]; ring

/-- **Grid-spacing.** A nonzero difference of two numbers whose exponents are both
`≥ E` is at least the grid step `10 ^ E`: both values are integer multiples of
`10 ^ E`, so a nonzero difference is a nonzero integer multiple of it. -/
lemma Number.sub_toRat_lower_of_ne (x y : Number) (E : Int)
    (hEx : E ≤ x.exponent_) (hEy : E ≤ y.exponent_)
    (hne : x.toRat ≠ y.toRat) :
    (10:ℚ)^E ≤ |x.toRat - y.toRat| := by
  obtain ⟨kx, hkx⟩ := Number.toRat_int_mul_zpow x E hEx
  obtain ⟨ky, hky⟩ := Number.toRat_int_mul_zpow y E hEy
  have hkxy : kx ≠ ky := by intro h; apply hne; rw [hkx, hky, h]
  have h10 : (0:ℚ) < (10:ℚ)^E := zpow_pos (by norm_num) _
  have hdiff : x.toRat - y.toRat = ((kx - ky : ℤ) : ℚ) * (10:ℚ)^E := by rw [hkx, hky]; push_cast; ring
  have habs : |x.toRat - y.toRat| = |((kx - ky : ℤ) : ℚ)| * (10:ℚ)^E := by
    rw [hdiff, abs_mul, abs_of_pos h10]
  rw [habs]
  have hge1 : (1:ℚ) ≤ |((kx - ky : ℤ) : ℚ)| := by
    have hne' : (kx - ky) ≠ 0 := sub_ne_zero.mpr hkxy
    have h1 : (1:ℤ) ≤ |kx - ky| := Int.one_le_abs hne'
    calc (1:ℚ) = ((1:ℤ):ℚ) := by norm_num
      _ ≤ ((|kx - ky| : ℤ):ℚ) := by exact_mod_cast h1
      _ = |((kx - ky : ℤ) : ℚ)| := by rw [Int.cast_abs]
  nlinarith [hge1, h10]

/-- Subtracting a zero-mantissa `arn` is the identity (`operator_add x 0 = x`). -/
lemma Number.operator_sub_zero_right (x arn result : Number) (harn : arn.mantissa_ = 0)
    (hok : x.operator_sub arn .to_nearest = .ok result) : result = x := by
  unfold Number.operator_sub at hok
  have hneg0 : arn.operator_neg = Number.zero := by
    unfold Number.operator_neg; rw [if_pos (by rw [harn]; rfl)]
  rw [hneg0] at hok
  unfold Number.operator_add at hok
  rw [if_pos (by decide : Number.zero.operator_eq Number.zero = true)] at hok
  simp only [pure, Except.pure] at hok
  exact (Except.ok.inj hok).symm

/-- Subtracting an equal (nonzero) `arn` yields `Number.zero` (`x - x = 0`). -/
lemma Number.operator_sub_eq_zero_of_operator_eq (x arn result : Number)
    (hxm : x.mantissa_ ≠ 0) (harnm : arn.mantissa_ ≠ 0)
    (heq : x.operator_eq arn = true)
    (hok : x.operator_sub arn .to_nearest = .ok result) : result = Number.zero := by
  unfold Number.operator_sub at hok
  unfold Number.operator_add at hok
  have hnegm : (arn.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne arn harnm]; exact harnm
  rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hnegm)] at hok
  rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hxm)] at hok
  have h3 : x.operator_eq ((arn.operator_neg).operator_neg) = true := by
    rw [neg_neg_of_mant_ne harnm]; exact heq
  rw [if_pos h3] at hok
  simp only [pure, Except.pure] at hok
  exact (Except.ok.inj hok).symm

/-- **Underflow exclusion.** A nonzero-difference `to_nearest` subtraction of two
normalized nonnegative operands whose exponents clear `minExponent + 18` cannot round
to a zero mantissa: the grid-spacing floor `10 ^ E` exceeds the underflow threshold
`10 ^ (minExponent + 18)`. -/
lemma Number.operator_sub_result_ne_zero_of_grid (x arn result : Number) (E : Int)
    (hx : x.isNormalized) (harn : arn.isNormalized)
    (hxm : x.mantissa_ ≠ 0) (harnm : arn.mantissa_ ≠ 0)
    (hxsign : x.negative_ = false) (harnsign : arn.negative_ = false)
    (hEx : E ≤ x.exponent_) (hEarn : E ≤ arn.exponent_) (hE : minExponent + 18 ≤ E)
    (hne : ¬ x.operator_eq arn = true)
    (hok : x.operator_sub arn .to_nearest = .ok result) :
    result.mantissa_ ≠ 0 := by
  intro hres0
  have hxtr_ne : x.toRat ≠ arn.toRat := fun heq => hne ((operator_eq_iff x arn hx harn).mpr heq)
  have hgrid : (10:ℚ)^E ≤ |x.toRat - arn.toRat| :=
    Number.sub_toRat_lower_of_ne x arn E hEx hEarn hxtr_ne
  have hok_add : Number.operator_add x arn.operator_neg .to_nearest = .ok result := hok
  have hnegnorm : (arn.operator_neg).isNormalized := Number.operator_neg_isNormalized arn harn
  have hnegm : (arn.operator_neg).mantissa_ ≠ 0 := by
    rw [Number.operator_neg_mantissa_of_ne arn harnm]; exact harnm
  have hnegsign : (arn.operator_neg).negative_ = true := by
    rw [Number.operator_neg_negative_of_ne arn harnm, harnsign]; decide
  have hdiffsign : x.negative_ ≠ (arn.operator_neg).negative_ := by rw [hxsign, hnegsign]; decide
  have hnotzero : ¬ x.operator_eq (arn.operator_neg).operator_neg = true := by
    rw [neg_neg_of_mant_ne harnm]; exact hne
  have hsmall := operator_add_underflow_truth_small x arn.operator_neg result .to_nearest
    hx hnegnorm hxm hnegm hdiffsign hnotzero hok_add hres0
  rw [Number.toRat_neg] at hsmall
  have hthresh : (10:ℚ)^(18:ℕ) * (10:ℚ)^(minExponent:ℤ) = (10:ℚ)^((minExponent:ℤ)+18) := by
    rw [← zpow_natCast (10:ℚ) 18, ← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; congr 1
  rw [hthresh] at hsmall
  have hEge : (10:ℚ)^((minExponent:ℤ)+18) ≤ (10:ℚ)^E := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have habs_eq : x.toRat + -arn.toRat = x.toRat - arn.toRat := by ring
  rw [habs_eq] at hsmall
  linarith [hgrid, hsmall, hEge]

/-- **A `to_nearest` subtraction of a (possibly-zero) recovery from a normalized
nonnegative operand rounds within `depositε`.** The zero recovery is exact
(`operator_sub_zero_right`), equal operands cancel to zero, and a genuine nonzero
difference clears the underflow threshold so `operator_sub_rounds_to_nearest` applies
(its `6 / (2⁶³ - 3)` bound is under `depositε`). -/
lemma Number.sub_recovery_rounds_within (x arn result : Number) (E : Int)
    (hx : x.isNormalized) (hxsign : x.negative_ = false)
    (hxm : arn.mantissa_ ≠ 0 → x.mantissa_ ≠ 0)
    (harn : arn.isNormalized) (harnsign : arn.negative_ = false)
    (hEx : arn.mantissa_ ≠ 0 → E ≤ x.exponent_) (hEarn : arn.mantissa_ ≠ 0 → E ≤ arn.exponent_)
    (hE : minExponent + 18 ≤ E)
    (hok : x.operator_sub arn .to_nearest = .ok result) :
    RoundsWithin result (x.toRat - arn.toRat) .to_nearest depositε := by
  have hεnn : (0:ℚ) ≤ depositε := by rw [depositε_eq]; norm_num
  by_cases harnm : arn.mantissa_ = 0
  · have hres : result = x := Number.operator_sub_zero_right x arn result harnm hok
    have harn0 : arn.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero arn harnm
    show |result.toRat - (x.toRat - arn.toRat)| ≤ |x.toRat - arn.toRat| * depositε
    rw [hres, harn0]
    have h0 : x.toRat - (x.toRat - 0) = 0 := by ring
    rw [h0, abs_zero]
    exact mul_nonneg (abs_nonneg _) hεnn
  · by_cases heq : x.operator_eq arn = true
    · have hres : result = Number.zero :=
        Number.operator_sub_eq_zero_of_operator_eq x arn result (hxm harnm) harnm heq hok
      have hval : x.toRat = arn.toRat := (operator_eq_iff x arn hx harn).mp heq
      show |result.toRat - (x.toRat - arn.toRat)| ≤ |x.toRat - arn.toRat| * depositε
      rw [hres, hval, Number.toRat_zero]
      have h0 : (0:ℚ) - (arn.toRat - arn.toRat) = 0 := by ring
      rw [h0, abs_zero]
      exact mul_nonneg (abs_nonneg _) hεnn
    · have hresm : result.mantissa_ ≠ 0 :=
        Number.operator_sub_result_ne_zero_of_grid x arn result E hx harn (hxm harnm) harnm hxsign harnsign
          (hEx harnm) (hEarn harnm) hE heq hok
      have hround := operator_sub_rounds_to_nearest x arn result hx harn (hxm harnm) harnm heq hok hresm
      show |result.toRat - (x.toRat - arn.toRat)| ≤ |x.toRat - arn.toRat| * depositε
      have hround' : |result.toRat - (x.toRat - arn.toRat)|
          ≤ |x.toRat - arn.toRat| * (6 / (2^63 - 3 : ℚ)) := hround
      have hεle : (6 / (2^63 - 3 : ℚ)) ≤ depositε := by rw [depositε_eq]; norm_num
      calc |result.toRat - (x.toRat - arn.toRat)|
          ≤ |x.toRat - arn.toRat| * (6 / (2^63 - 3 : ℚ)) := hround'
        _ ≤ |x.toRat - arn.toRat| * depositε :=
            mul_le_mul_of_nonneg_left hεle (abs_nonneg _)

/-- **The recovery's pre-round `Number` `aN` and its two-sided pipeline bound.** The
payout is `ofNumber v.numericType aN .downward`, and the exact recovery ideal sits
within `depositε` of `aN` when `aN` is nonzero, or is `Number`-underflow tiny when
`aN` is zero. Feeds the zero-payout corner of the accuracy headlines. -/
lemma Vault.recovery_pipeline_bound (v : Vault) (shares assets : STAmount)
    (hnav : v.WithdrawNavExact false) (hc : shares.Canonical)
    (hnav_pos : 0 < v.withdrawNav) (hshpos : 0 < shares.toRat)
    (hprice : v.sharesToAssetsWithdraw shares false = .ok assets) :
    ∃ aN : Number,
      STAmount.ofNumber v.numericType aN .downward = .ok assets ∧
      (aN.mantissa_ ≠ 0 → aN.isNormalized ∧ aN.negative_ = false ∧
        v.idealAssetsWithdraw false shares.toRat ≤
          aN.toRat + v.idealAssetsWithdraw false shares.toRat * depositε) ∧
      (aN.mantissa_ = 0 →
        v.idealAssetsWithdraw false shares.toRat ≤ (10 : ℚ) ^ (-32700 : ℤ)) := by
  obtain ⟨nav2, hsub, hcase⟩ :=
    Vault.sharesToAssetsWithdraw_ok_reduces v shares assets false hprice
  have hnav2norm : nav2.isNormalized :=
    operator_sub_isNormalized_to_nearest_sz _ _ _ v.wf.assetsTotal_norm v.wf.lossUnrealized_norm hsub
  obtain ⟨nvv, hs, hnavval⟩ := hnav
  have hnav2eq : nav2 = nvv := Except.ok.inj (hsub.symm.trans hs)
  have hnav2val : nav2.toRat = v.withdrawNav := by rw [hnav2eq]; exact hnavval
  have hnav2_pos : 0 < nav2.toRat := by rw [hnav2val]; exact hnav_pos
  -- shares total positive integer
  have hST_pos : 0 < v.sharesTotal.toRat := by
    rcases lt_or_eq_of_le v.wf.sharesTotal_nonneg with h | h
    · exact h
    · exfalso
      have hz : v.toExact.sharesTotal = 0 := by
        show v.sharesTotal.toRat.num.toNat = 0; rw [← h]; rfl
      have hAT := (v.exact.empty_shares hz).1
      have hnav0 : v.withdrawNav = 0 := by
        have hl := v.exact.lossUnrealized_nonneg
        have hle := v.exact.withdraw_nav_nonneg
        rw [hAT] at hle
        unfold RawVault.withdrawNav; rw [hAT]; linarith
      linarith [hnav_pos]
  have hST_one : 1 ≤ v.sharesTotal.toRat := by
    have hnum_pos : 0 < v.sharesTotal.toRat.num := Rat.num_pos.mpr hST_pos
    have hcast : v.sharesTotal.toRat = (v.sharesTotal.toRat.num : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den v.sharesTotal.toRat]
      rw [v.wf.sharesTotal_int]; simp
    rw [hcast]; exact_mod_cast hnum_pos
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero hST_pos.ne'
  set ideal : ℚ := v.idealAssetsWithdraw false shares.toRat with hideal_def
  have hideal_eq : ideal = nav2.toRat * shares.toRat / v.sharesTotal.toRat := by
    rw [hideal_def]
    unfold RawVault.idealAssetsWithdraw
    rw [if_neg (by decide : ¬ ((false : Bool) = true)), ← hnav2val,
      RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
  rcases hcase with ⟨hnav2m0, hzero⟩ |
      ⟨hnav2m, sharesNumber, NAVShares, assetsNumber, hsn, hmul, hdiv, hof⟩
  · exfalso
    have : nav2.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero nav2 hnav2m0
    linarith [hnav2_pos]
  · -- shares lift
    obtain ⟨sn0, hsn0ok, hsn0val, hsn0norm⟩ := STAmount.toNumber_canonical_exact shares .to_nearest hc
    have hsn_eq : sharesNumber = sn0 := Except.ok.inj (hsn.symm.trans hsn0ok)
    have hsnnorm : sharesNumber.isNormalized := by rw [hsn_eq]; exact hsn0norm
    have hsnval : sharesNumber.toRat = shares.toRat := by rw [hsn_eq]; exact hsn0val
    have hsn_pos : 0 < sharesNumber.toRat := by rw [hsnval]; exact hshpos
    have hideal_eq' : ideal = nav2.toRat * sharesNumber.toRat / v.sharesTotal.toRat := by
      rw [hideal_eq, hsnval]
    refine ⟨assetsNumber, hof, ?_, ?_⟩
    · intro hQm
      have hNAVm : NAVShares.mantissa_ ≠ 0 :=
        operator_div_numerator_ne_zero_sz NAVShares v.sharesTotal assetsNumber .to_nearest
          (Number.not_operator_eq_zero_of_mantissa_ne hSTm) hdiv hQm
      obtain ⟨hnav2_m', hsn_m⟩ := operator_mul_operands_ne_zero hnav2norm hsnnorm hmul hNAVm
      have hPm : NAVShares.mantissa_ ≠ 0 := hNAVm
      obtain ⟨hQnorm, hQpos, hQbound⟩ :=
        RawVault.exchange_pipeline_within nav2 sharesNumber v.sharesTotal NAVShares assetsNumber
          hnav2norm hsnnorm v.wf.sharesTotal_norm hnav2_pos hsn_pos hST_pos hmul hdiv hPm hQm
      rw [← hideal_eq'] at hQbound
      have hANneg : assetsNumber.negative_ = false := Number.negative_false_of_pos assetsNumber hQpos
      obtain ⟨_, hhi⟩ := abs_le.mp hQbound
      exact ⟨hQnorm, hANneg, by linarith [hhi]⟩
    · intro hQm0
      -- Number-underflow: the div (or its numerator's mul) collapsed. Either way
      -- `ideal < 2·10^18·10^minExponent ≤ 10^(-32700)`.
      have hunit : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) = (10 : ℚ) ^ (-32750 : ℤ) := by
        rw [← zpow_natCast (10 : ℚ) 18, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
        norm_num [minExponent]
      have hu_pos : (0 : ℚ) < (10 : ℚ) ^ (-32750 : ℤ) := zpow_pos (by norm_num) _
      have h2u_le : 2 * (10 : ℚ) ^ (-32750 : ℤ) ≤ (10 : ℚ) ^ (-32700 : ℤ) := by
        rw [show (10 : ℚ) ^ (-32700 : ℤ) = (10 : ℚ) ^ (50 : ℤ) * (10 : ℚ) ^ (-32750 : ℤ) from by
          rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num]
        have h50 : (2 : ℚ) ≤ (10 : ℚ) ^ (50 : ℤ) := by norm_num
        nlinarith [hu_pos, h50]
      have hbound : ideal < 2 * (10 : ℚ) ^ (-32750 : ℤ) := by
        by_cases hPm0 : NAVShares.mantissa_ = 0
        · -- multiplication underflowed
          have hsmall := operator_mul_underflow_truth_small nav2 sharesNumber NAVShares .to_nearest
            hnav2norm hsnnorm (Number.mantissa_ne_zero_of_toRat_ne_zero hnav2_pos.ne')
            (Number.mantissa_ne_zero_of_toRat_ne_zero hsn_pos.ne') hmul hPm0
          have hprod_pos : 0 < nav2.toRat * sharesNumber.toRat := mul_pos hnav2_pos hsn_pos
          rw [abs_of_pos hprod_pos, hunit] at hsmall
          have hle : ideal ≤ nav2.toRat * sharesNumber.toRat := by
            rw [hideal_eq']
            calc nav2.toRat * sharesNumber.toRat / v.sharesTotal.toRat
                ≤ nav2.toRat * sharesNumber.toRat / 1 :=
                  div_le_div_of_nonneg_left (le_of_lt hprod_pos) (by norm_num) hST_one
              _ = nav2.toRat * sharesNumber.toRat := by ring
          nlinarith [hsmall, hle, hu_pos]
        · -- division underflowed
          have hNAVnorm : NAVShares.isNormalized :=
            operator_mul_result_isNormalized nav2 sharesNumber NAVShares .to_nearest
              hnav2norm hsnnorm (Number.mantissa_ne_zero_of_toRat_ne_zero hnav2_pos.ne')
              (Number.mantissa_ne_zero_of_toRat_ne_zero hsn_pos.ne') hmul hPm0
          have hsmall := operator_div_underflow_truth_small NAVShares v.sharesTotal assetsNumber
            .to_nearest hNAVnorm v.wf.sharesTotal_norm hPm0 hSTm hdiv hQm0
          have hmulbound : |NAVShares.toRat - nav2.toRat * sharesNumber.toRat|
              ≤ |nav2.toRat * sharesNumber.toRat| * (5 / (2 ^ 63 + 7)) :=
            operator_mul_rounds_to_nearest nav2 sharesNumber NAVShares hnav2norm hsnnorm hmul hPm0
          have hprodpos : 0 < nav2.toRat * sharesNumber.toRat := mul_pos hnav2_pos hsn_pos
          rw [abs_of_pos hprodpos] at hmulbound
          have hNAVpos : 0 < NAVShares.toRat := by
            have := abs_le.mp hmulbound; nlinarith [hprodpos]
          have hNAV_close : nav2.toRat * sharesNumber.toRat ≤ NAVShares.toRat * 2 := by
            have := abs_le.mp hmulbound; nlinarith [hprodpos]
          rw [abs_of_nonneg (le_of_lt (div_pos hNAVpos hST_pos)), hunit] at hsmall
          have hle : ideal ≤ NAVShares.toRat / v.sharesTotal.toRat * 2 := by
            rw [hideal_eq', div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right hNAV_close (le_of_lt hST_pos)
          nlinarith [hsmall, hle, div_pos hNAVpos hST_pos]
      linarith [hbound, h2u_le]

/-- **A `.downward` integral `ofNumber` that lands on zero came from a source below
one.** The floor of the source is `0`, so the source sits in `[0, 1)`. -/
lemma STAmount.ofNumber_integral_zero_floor (nt : NumericType) (n : Number) (result : STAmount)
    (hint : nt.isIntegral = true) (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : STAmount.ofNumber nt n .downward = .ok result) (hz : result.mValue = 0) :
    n.toRat < 1 := by
  unfold STAmount.ofNumber at hok
  simp only [Number.signum_neg_decide, hneg, Bool.false_eq_true, if_false, if_pos hint] at hok
  cases hrep : n.to_rep .downward with
  | error e => rw [hrep] at hok; exact absurd hok (by simp)
  | ok intValue =>
    rw [hrep] at hok
    simp only [] at hok
    obtain ⟨hnn, hle⟩ := Number.to_rep_nonneg_range n .downward intValue hneg hrep
    have hval : intValue.toUInt64.toNat ≤ maxRep.toNat :=
      toUInt64_toNat_le_maxRep intValue hnn hle
    have hres_val : result.toRat = (intValue.toInt : ℚ) := by
      have hexact := STAmount.canonicalize_integral_toRat
        (STAmount.unchecked nt intValue.toUInt64 0 false) result .downward
        (show (STAmount.unchecked nt intValue.toUInt64 0 false).integral = true from hint) rfl
        hval hok
      rw [hexact, STAmount.toRat_of_offset_zero _ rfl]
      show ((intValue.toUInt64.toNat : ℤ) : ℚ) = (intValue.toInt : ℚ)
      rw [toUInt64_toNat_of_nonneg intValue hnn]
    have hr0 : result.toRat = 0 := by rw [STAmount.toRat_signed, hz]; simp
    have hiv0 : intValue.toInt = 0 := by
      have : (intValue.toInt : ℚ) = 0 := by rw [← hres_val]; exact hr0
      exact_mod_cast this
    obtain ⟨_, hlt⟩ := Number.to_rep_downward_floor n intValue hn hneg hrep
    rw [hiv0] at hlt; simpa using hlt

/-- **A `.fractional` `checked` landing on a zero mantissa forces the exponent below
`cMinOffset`.** On a canonical 16-digit mantissa the fractional `checked` reproduces
the record when the exponent sits in `[cMinOffset, cMaxOffset]` and errors above it,
so an `.ok` zero result can only come from `exp < cMinOffset`. -/
lemma STAmount.checked_iou_zero_exp (mant : UInt64) (exp : Int) (neg : Bool) (mode : rounding_mode)
    (h_lo : 10 ^ 15 ≤ mant.toNat) (h_hi : mant.toNat < 10 ^ 16)
    (he_lo : minExponent + 3 ≤ exp) (he_hi : exp ≤ maxExponent)
    (result : STAmount)
    (hok : STAmount.checked .fractional mant exp neg mode = .ok result)
    (hz : result.mValue = 0) :
    exp < cMinOffset := by
  by_contra hnlt
  push_neg at hnlt
  have h_fit : mant.toNat < 2 ^ 63 := by omega
  have hint : ¬ (STAmount.unchecked .fractional mant exp neg).integral = true := by
    simp [STAmount.integral, STAmount.unchecked, NumericType.isIntegral]
  have h_sd : (STAmount.unchecked .fractional mant exp neg).signedDrops.toInt64
      = if neg then -mant.toInt64 else mant.toInt64 := by
    apply Int64.toInt_inj.mp
    rw [STAmount.signedDrops_toInt64_toInt _
          (show (STAmount.unchecked .fractional mant exp neg).mValue.toNat < 10 ^ 16 from h_hi),
        signed_mantissa_toInt neg mant h_fit]
    show (STAmount.unchecked .fractional mant exp neg).signedDrops = _
    unfold STAmount.signedDrops STAmount.unchecked
    rcases neg <;> simp
  have hiou : (STAmount.unchecked .fractional mant exp neg).iou mode
      = (if exp > cMaxOffset then .error .overflow
         else if exp < cMinOffset then .ok IOUAmount.zero
         else .ok ⟨if neg then -mant.toInt64 else mant.toInt64, exp⟩) := by
    unfold STAmount.iou
    rw [if_neg hint]
    unfold IOUAmount.ofMantissaExp
    rw [h_sd]
    exact IOUAmount.normalize_canonical16 mant exp neg mode h_lo h_hi he_lo he_hi
  by_cases hhi : exp > cMaxOffset
  · have hb : STAmount.checked .fractional mant exp neg mode = .error .overflow := by
      rw [STAmount.checked]; unfold STAmount.canonicalize
      rw [if_neg hint, hiou, if_pos hhi]
    rw [hb] at hok; simp at hok
  · have hexp_lo : (-96 : ℤ) ≤ exp := by unfold cMinOffset at hnlt; exact hnlt
    have hexp_hi : exp ≤ 80 := by unfold cMaxOffset at hhi; omega
    have hc : (⟨.fractional, mant, exp, neg⟩ : STAmount).IOUCanonical :=
      ⟨rfl, h_lo, h_hi, hexp_lo, hexp_hi⟩
    have hcid := STAmount.canonicalize_canonical_id ⟨.fractional, mant, exp, neg⟩ mode hc
    rw [STAmount.checked,
        show STAmount.unchecked .fractional mant exp neg = (⟨.fractional, mant, exp, neg⟩ : STAmount) from rfl,
        hcid] at hok
    have hres : result = ⟨.fractional, mant, exp, neg⟩ := (Except.ok.inj hok).symm
    rw [hres] at hz
    simp only [] at hz
    rw [hz] at h_lo
    simp at h_lo

/-- **A `.downward` fractional `ofNumber` that lands on zero came from a source below
the smallest positive IOU value `10⁻⁸¹`.** The `.downward` snap of a normalized
sign-cleared nonzero `Number` floors to zero exactly when its value is below the grid
minimum `cMinValue · 10^cMinOffset = 10⁻⁸¹`: the 16-digit `normalizeToRange` exponent
runs below `cMinOffset`, so the source exponent is `≤ -100` and its 19-digit mantissa
keeps the value under `10¹⁹ · 10⁻¹⁰⁰ = 10⁻⁸¹`. Fractional companion of
`ofNumber_integral_zero_floor`. -/
lemma STAmount.ofNumber_fractional_zero_below_min (nt : NumericType) (n : Number)
    (result : STAmount) (hnt : nt.isIntegral = false)
    (hn : n.isNormalized) (hneg : n.negative_ = false) (hnz : n.mantissa_ ≠ 0)
    (hok : STAmount.ofNumber nt n .downward = .ok result) (hz : result.mValue = 0) :
    n.toRat < (10 : ℚ) ^ (-81 : ℤ) := by
  have hnt_frac : nt = .fractional := by
    cases nt with
    | fractional => rfl
    | integral mv mo ms msh => simp [NumericType.isIntegral] at hnt
  subst hnt_frac
  obtain ⟨hr_lo, hr_hi⟩ := hn.mantissaBounds_nat hnz
  have hre_lo : minExponent ≤ n.exponent_ := by
    rcases hn with h0 | ⟨_, _, _, hlo, _⟩
    · exact absurd (show n.mantissa_ = 0 by rw [h0]; rfl) hnz
    · exact hlo
  have hneg_dec : decide (n.signum < 0) = false := by rw [Number.signum_neg_decide]; exact hneg
  have hwork : (if decide (n.signum < 0) then n.operator_neg else n) = n := by
    rw [hneg_dec]; simp
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide : ¬ (NumericType.fractional.isIntegral = true))] at hok
  rw [hwork] at hok
  rw [hneg_dec] at hok
  cases hnorm : n.normalizeToRange kMinValue kMaxValue .downward with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : n.normalizeToRange cMinValue cMaxValue .downward = .ok (mant, exp) := hnorm
    have hexp_hi3 : n.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi n .downward mant exp hr_lo hr_hi hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts n .downward mant exp hr_lo hr_hi (by omega) hexp_hi3 hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn hneg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
      exact this
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
      omega
    have hexp_zero : exp < cMinOffset :=
      STAmount.checked_iou_zero_exp mant.toUInt64 exp false .downward hmtu_lo hmtu_hi
        (by omega) hexp_le result hok hz
    have hexp_n : n.exponent_ ≤ -100 := by unfold cMinOffset at hexp_zero; omega
    rw [Number.toRat_of_nonneg n hneg]
    have hm : (n.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hr_hi
    have hpe_pos : (0 : ℚ) < (10 : ℚ) ^ n.exponent_ := zpow_pos (by norm_num) _
    have hstep : (n.mantissa_.toNat : ℚ) * (10 : ℚ) ^ n.exponent_
        < (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ :=
      mul_lt_mul_of_pos_right hm hpe_pos
    have hle2 : (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ n.exponent_ ≤ (10 : ℚ) ^ (-81 : ℤ) := by
      rw [← zpow_natCast (10 : ℚ) 19, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
      apply zpow_le_zpow_right₀ (by norm_num)
      omega
    linarith [hstep, hle2]

end XRPL.Model.SingleAssetVault
