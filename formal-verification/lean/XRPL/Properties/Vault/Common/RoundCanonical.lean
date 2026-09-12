import XRPL.Properties.Vault.Common.OfNumberBoundary
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Protocol.STAmount.Div.Common.IOU
import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Sum
import XRPL.Properties.Protocol.STAmount.Sub.RoundsWithin
import XRPL.Properties.Protocol.STAmount.Common.RoundToScaleHelpers
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing

/-! # Canonicity of the `roundToVaultExponent` output

The `Vault.deposit` accuracy headlines only ever hypothesize that the *raw* input
`amountDeposit` is stored canonically (`amountDeposit.Canonical`). Internally the
deposit rounds it with `roundToVaultExponent`, and the rounded amount must itself
be canonical for the `toNumber`-exactness lemmas the exchange proofs consume.

This file derives that fact rather than hypothesizing it. The fractional pipeline
(`iou`/`canonicalize` → `operator_add`/`operator_sub` → `roundToExponent` →
`roundToVaultExponent`) always canonicalizes its fractional output, so the result
is `IOUCanonical`-or-zero; the integral pass is the identity. -/

namespace XRPL.Model.Protocol

set_option maxRecDepth 4000

/-! ## `IOUAmount.normalize` output range -/

/-- A successful `IOUAmount.normalize` output is either a canonical 16-digit
amount (`InRange16`) or the zero amount. The 19-digit `from_rep` re-lift is
`largeRange`-normalized, so the 16-digit `normalizeToRange` snap lands in
`[cMinValue, cMaxValue]`; the `cMinOffset`/`cMaxOffset` clamps that a `.ok`
passed pin the exponent to `[-96, 80]`. -/
lemma IOUAmount.normalize_InRange16_or_zero (a : IOUAmount) (mode : rounding_mode)
    (i : IOUAmount) (hok : IOUAmount.normalize a mode = .ok i) :
    i.InRange16 ∨ i.mantissa_ = 0 := by
  by_cases hi0 : i.mantissa_ = 0
  · exact Or.inr hi0
  refine Or.inl ?_
  unfold IOUAmount.normalize at hok
  by_cases hma : a.mantissa_ = 0
  · rw [if_pos (beq_iff_eq.mpr hma)] at hok
    rw [← Except.ok.inj hok] at hi0
    exact absurd rfl hi0
  · rw [show (a.mantissa_ == 0) = false from beq_eq_false_iff_ne.mpr hma] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    have ham_toInt : a.mantissa_.toInt ≠ 0 := by
      intro h; exact hma (Int64.toInt_inj.mp (by rw [h]; decide))
    cases hfr : Number.from_rep a.mantissa_ a.exponent_ largeRange.min largeRange.max mode with
    | error err => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      have hofn : IOUAmount.ofNumber v mode = .ok i := hok
      have hv_ne : v.mantissa_ ≠ 0 := IOUAmount.ofNumber_mantissa_ne_zero v mode i hofn hi0
      have hfr' : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
          a.exponent_).normalize largeRange.min largeRange.max mode = .ok v := hfr
      have hun_ne : (Number.unchecked (a.mantissa_ < 0) a.mantissa_.toInt.natAbs.toUInt64
          a.exponent_).mantissa_ ≠ 0 := by
        show a.mantissa_.toInt.natAbs.toUInt64 ≠ 0
        have hb : a.mantissa_.toInt.natAbs < 2 ^ 64 := by
          have h1 := Int64.le_toInt a.mantissa_
          have h2 := Int64.toInt_lt a.mantissa_
          omega
        have heq : a.mantissa_.toInt.natAbs.toUInt64.toNat = a.mantissa_.toInt.natAbs :=
          UInt64.toNat_ofNat_of_lt hb
        intro h; rw [h] at heq; simp at heq; omega
      have hv_norm : v.isNormalized := normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
      obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv_ne
      have hv_exp_lo : minExponent ≤ v.exponent_ := by
        rcases hv_norm with hz | ⟨_, _, _, hlo', _⟩
        · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
        · exact hlo'
      cases hfn : IOUAmount.fromNumber v mode with
      | error err =>
        unfold IOUAmount.ofNumber at hofn; rw [hfn] at hofn; exact absurd hofn (by simp)
      | ok r =>
        unfold IOUAmount.ofNumber at hofn
        rw [hfn] at hofn
        simp only [] at hofn
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hofn; exact absurd hofn (by simp)
        rw [if_neg hhi] at hofn
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hofn
          rw [← Except.ok.inj hofn] at hi0
          exact absurd rfl hi0
        rw [if_neg hlo] at hofn
        have hir : i = r := (Except.ok.inj hofn).symm
        unfold IOUAmount.fromNumber at hfn
        cases hnorm : v.normalizeToRange cMinValue cMaxValue mode with
        | error err => rw [hnorm] at hfn; exact absurd hfn (by simp)
        | ok me' =>
          obtain ⟨mm, ee⟩ := me'
          rw [hnorm] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          rw [hrmm] at hhi hlo
          have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
            normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnorm
          obtain ⟨⟨hmlo, hmhi⟩, _, _⟩ :=
            normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnorm
          rw [hir, hrmm]
          refine ⟨?_, ?_, ?_, ?_⟩
          · show 10 ^ 15 ≤ mm.toInt.natAbs
            rw [show cMinValue.toNat = 10 ^ 15 from by decide] at hmlo; exact hmlo
          · show mm.toInt.natAbs < 10 ^ 16
            rw [show cMaxValue.toNat = 10 ^ 16 - 1 from by decide] at hmhi; omega
          · show (-96 : ℤ) ≤ ee
            have := not_lt.mp hlo; unfold cMinOffset at this; omega
          · show ee ≤ (80 : ℤ)
            have := not_lt.mp hhi; unfold cMaxOffset at this; omega

/-- **Sign preservation of `IOUAmount.normalize`.** A nonnegative signed mantissa
stays nonnegative through the 19-digit re-lift and the 16-digit snap: each stage
carries the cleared sign into its output (`doRoundUp` copies the input sign, and a
flushed-to-zero result is nonnegative trivially). Magnitude-free, unlike the
`RoundsWithin` characterizations, so it applies to sub-`10^16` mantissas. -/
lemma IOUAmount.normalize_mantissa_nonneg (m : Int64) (e : Int) (mode : rounding_mode)
    (i : IOUAmount) (hm : 0 ≤ m.toInt)
    (hok : IOUAmount.normalize ⟨m, e⟩ mode = .ok i) :
    0 ≤ i.mantissa_.toInt := by
  by_cases hi0 : i.mantissa_ = 0
  · rw [hi0]; decide
  have hmlt : decide (m < 0) = false := by
    rw [decide_eq_false_iff_not, Int64.lt_iff_toInt_lt]
    have h0 : (0 : Int64).toInt = 0 := by decide
    omega
  unfold IOUAmount.normalize at hok
  by_cases hma : m = 0
  · rw [if_pos (show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = true from beq_iff_eq.mpr hma)] at hok
    rw [← Except.ok.inj hok] at hi0; exact absurd rfl hi0
  · have hm_toInt : m.toInt ≠ 0 := fun h => hma (Int64.toInt_inj.mp (by rw [h]; decide))
    rw [show ((⟨m, e⟩ : IOUAmount).mantissa_ == 0) = false from beq_eq_false_iff_ne.mpr hma] at hok
    simp only [Bool.false_eq_true, if_false] at hok
    cases hfr : Number.from_rep m e largeRange.min largeRange.max mode with
    | error err => rw [hfr] at hok; exact absurd hok (by simp)
    | ok v =>
      rw [hfr] at hok
      simp only [] at hok
      have hofn : IOUAmount.ofNumber v mode = .ok i := hok
      have hv_ne : v.mantissa_ ≠ 0 := IOUAmount.ofNumber_mantissa_ne_zero v mode i hofn hi0
      have hfr' : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).normalize
          largeRange.min largeRange.max mode = .ok v := hfr
      have hun_ne : (Number.unchecked (m < 0) m.toInt.natAbs.toUInt64 e).mantissa_ ≠ 0 := by
        show m.toInt.natAbs.toUInt64 ≠ 0
        have hb : m.toInt.natAbs < 2 ^ 64 := by
          have h1 := Int64.le_toInt m
          have h2 := Int64.toInt_lt m
          omega
        have heq : m.toInt.natAbs.toUInt64.toNat = m.toInt.natAbs :=
          UInt64.toNat_ofNat_of_lt hb
        intro h; rw [h] at heq; simp at heq; omega
      have hv_norm : v.isNormalized :=
        normalize_result_isNormalized _ v mode hun_ne hfr' hv_ne
      obtain ⟨hvm_lo, hvm_hi⟩ := hv_norm.mantissaBounds_nat hv_ne
      have hv_exp_lo : minExponent ≤ v.exponent_ := by
        rcases hv_norm with hz | ⟨_, _, _, hlo', _⟩
        · exact absurd (show v.mantissa_ = 0 by rw [hz]; rfl) hv_ne
        · exact hlo'
      -- Stage 1: the 19-digit re-lift keeps the cleared sign, so `v.negative_ = false`.
      have hvneg : v.negative_ = false := by
        obtain ⟨m3, e3, g3, res, hrup, hres_eq, -, -, -, -⟩ :=
          normalize_doRoundUp_stage _ v mode hun_ne hfr' hv_ne
        have hres_ne : res.mantissa_ ≠ 0 := by rw [hres_eq] at hv_ne; exact hv_ne
        have hsg := doRoundUp_negative_of_mant_ne g3 _ m3 e3 largeRange.min largeRange.max mode
          .normalize2 res hrup hres_ne
        rw [hres_eq]
        show res.negative_ = false
        rw [hsg]; exact hmlt
      -- Stage 2: the 16-digit snap keeps the cleared sign, giving a nonnegative mantissa.
      unfold IOUAmount.ofNumber at hofn
      cases hfn : IOUAmount.fromNumber v mode with
      | error err => rw [hfn] at hofn; exact absurd hofn (by simp)
      | ok r =>
        rw [hfn] at hofn
        simp only [] at hofn
        by_cases hhi : r.exponent_ > cMaxOffset
        · rw [if_pos hhi] at hofn; exact absurd hofn (by simp)
        rw [if_neg hhi] at hofn
        by_cases hlo : r.exponent_ < cMinOffset
        · rw [if_pos hlo] at hofn
          rw [← Except.ok.inj hofn] at hi0; exact absurd rfl hi0
        rw [if_neg hlo] at hofn
        have hir : i = r := (Except.ok.inj hofn).symm
        unfold IOUAmount.fromNumber at hfn
        cases hnorm : v.normalizeToRange cMinValue cMaxValue mode with
        | error err => rw [hnorm] at hfn; exact absurd hfn (by simp)
        | ok me' =>
          obtain ⟨mm, ee⟩ := me'
          rw [hnorm] at hfn
          simp only [] at hfn
          have hrmm : r = ⟨mm, ee⟩ := (Except.ok.inj hfn).symm
          have hexp3 : v.exponent_ + 3 ≤ maxExponent :=
            normalizeToRange_iou_exp_hi v mode mm ee hvm_lo hvm_hi hnorm
          obtain ⟨-, -, hsign⟩ :=
            normalizeToRange_iou_ok_facts v mode mm ee hvm_lo hvm_hi (by omega) hexp3 hnorm
          rw [hir, hrmm]
          exact hsign hvneg

/-- **`canonicalize` of a sign-cleared fractional source is nonnegative.** The
`iou`/`ofMantissaExp`/`normalize` snap preserves the cleared sign
(`normalize_mantissa_nonneg`), so the packed record is nonnegative. Needs only
that the stored magnitude fits `Int64` (`< 2^63`), not the canonical `10^16`
window, so it covers small first-deposit mantissas. -/
lemma STAmount.canonicalize_signfalse_nonneg (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional) (hneg : s.mIsNegative = false)
    (hfit : s.mValue.toNat < 2 ^ 63)
    (hok : s.canonicalize mode = .ok result) :
    0 ≤ result.toRat := by
  have hint : ¬ s.integral = true := by unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  have hiou : s.iou mode = IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode := by
    unfold STAmount.iou; rw [if_neg hint]
  rw [hiou] at hok
  have hsd_nn : 0 ≤ s.signedDrops.toInt64.toInt := by
    rw [STAmount.signedDrops_toInt64_toInt_of_lt s hfit]
    unfold STAmount.signedDrops; rw [hneg]; simp
  cases hone : IOUAmount.ofMantissaExp s.signedDrops.toInt64 s.mOffset mode with
  | error e => rw [hone] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hone] at hok
    simp only [] at hok
    have hi_nn : 0 ≤ i.mantissa_.toInt :=
      IOUAmount.normalize_mantissa_nonneg s.signedDrops.toInt64 s.mOffset mode i hsd_nn hone
    have hneg_false : decide (i.signum < 0) = false := by
      rw [decide_eq_false_iff_not, IOUAmount.signum_neg_iff, Int64.lt_iff_toInt_lt]
      have h0 : (0 : Int64).toInt = 0 := by decide
      omega
    have heq := Except.ok.inj hok
    have hcneg : result.mIsNegative = false := by rw [← heq]; exact hneg_false
    rw [STAmount.toRat_of_nonneg result hcneg]; positivity

/-! ## Canonical-or-zero for a fractional STAmount -/

/-- A deposit-ready fractional amount: fractional type and stored canonically or
zero. The `roundToVaultExponent` fractional pipeline preserves this. -/
def STAmount.FracCanonZero (s : STAmount) : Prop :=
  s.mNumericType = .fractional ∧ (s.IOUCanonical ∨ s.mValue = 0)

/-- `canonicalize` on a fractional record yields a `FracCanonZero` result: the IOU
branch routes `iou → ofMantissaExp → normalize`, whose output is `InRange16`-or-zero
(`normalize_InRange16_or_zero`), and the packed record keeps the fractional type. -/
lemma STAmount.canonicalize_fczr (s result : STAmount) (mode : rounding_mode)
    (hfr : s.mNumericType = .fractional) (hok : s.canonicalize mode = .ok result) :
    result.FracCanonZero := by
  have hint : ¬ s.integral = true := by unfold STAmount.integral; rw [hfr]; decide
  unfold STAmount.canonicalize at hok
  rw [if_neg hint] at hok
  have hiou : s.iou mode = IOUAmount.normalize ⟨s.signedDrops.toInt64, s.mOffset⟩ mode := by
    unfold STAmount.iou IOUAmount.ofMantissaExp; rw [if_neg hint]
  rw [hiou] at hok
  cases hnorm : IOUAmount.normalize ⟨s.signedDrops.toInt64, s.mOffset⟩ mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok i =>
    rw [hnorm] at hok
    simp only [] at hok
    have hres : result = { s with
        mValue := (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64,
        mOffset := i.exponent_,
        mIsNegative := decide (i.signum < 0) } := (Except.ok.inj hok).symm
    have hnt : result.mNumericType = .fractional := by rw [hres]; exact hfr
    refine ⟨hnt, ?_⟩
    rcases IOUAmount.normalize_InRange16_or_zero _ mode i hnorm with hr | hz
    · left
      have h_fit : i.mantissa_.toInt.natAbs < 2 ^ 63 := by have := hr.mant_hi; omega
      have h_absToNat := IOUAmount.absMant_toNat i h_fit
      refine ⟨hnt, ?_, ?_, ?_, ?_⟩
      · show 10 ^ 15 ≤ result.mValue.toNat
        rw [hres]
        show 10 ^ 15 ≤ (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64.toNat
        rw [h_absToNat]; exact hr.mant_lo
      · show result.mValue.toNat < 10 ^ 16
        rw [hres]
        show (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64.toNat < 10 ^ 16
        rw [h_absToNat]; exact hr.mant_hi
      · show (-96 : ℤ) ≤ result.mOffset
        rw [hres]; exact hr.exp_lo
      · show result.mOffset ≤ 80
        rw [hres]; exact hr.exp_hi
    · right
      show result.mValue = 0
      rw [hres]
      show (if i.signum < 0 then -i.mantissa_ else i.mantissa_).toUInt64 = 0
      rw [hz]; split <;> decide

/-- `ofIOUAmount` canonicalizes a fractional record, so its output is
`FracCanonZero`. -/
lemma STAmount.ofIOUAmount_fczr (a : IOUAmount) (mode : rounding_mode) (result : STAmount)
    (hok : STAmount.ofIOUAmount a mode = .ok result) : result.FracCanonZero := by
  unfold STAmount.ofIOUAmount at hok
  exact STAmount.canonicalize_fczr _ result mode rfl hok

/-- Negation preserves `FracCanonZero`: it flips only the sign flag (or is the
identity on zero), leaving the type, magnitude, and exponent untouched. -/
lemma STAmount.operator_neg_fczr (s : STAmount) (h : s.FracCanonZero) :
    s.operator_neg.FracCanonZero := by
  obtain ⟨hnt, hcz⟩ := h
  unfold STAmount.operator_neg
  by_cases hz : s.mValue = 0
  · rw [if_pos (beq_iff_eq.mpr hz)]; exact ⟨hnt, hcz⟩
  · rw [if_neg (fun hb => hz (beq_iff_eq.mp hb))]
    refine ⟨hnt, ?_⟩
    rcases hcz with hc | hcv
    · exact Or.inl ⟨hnt, hc.mant_lo, hc.mant_hi, hc.exp_lo, hc.exp_hi⟩
    · exact Or.inr hcv

/-- `operator_add` of a `FracCanonZero` first operand is `FracCanonZero`: the
`v2 = 0` branch returns the operand, and both other reachable branches
(`v1 = 0` and the IOU add) canonicalize a fractional record. -/
lemma STAmount.operator_add_fczr (v1 v2 result : STAmount) (mode : rounding_mode)
    (h1 : v1.FracCanonZero) (hok : STAmount.operator_add v1 v2 mode = .ok result) :
    result.FracCanonZero := by
  obtain ⟨h1nt, h1cz⟩ := h1
  have hint1 : ¬ v1.integral = true := by unfold STAmount.integral; rw [h1nt]; decide
  unfold STAmount.operator_add at hok
  cases hcmp : STAmount.areComparable v1 v2 with
  | false => rw [if_pos (by rw [hcmp]; decide)] at hok; exact absurd hok (by simp)
  | true =>
    rw [if_neg (by rw [hcmp]; decide)] at hok
    by_cases hv2 : v2.mValue = 0
    · rw [if_pos (beq_iff_eq.mpr hv2)] at hok
      rw [← Except.ok.inj hok]; exact ⟨h1nt, h1cz⟩
    · rw [show (v2.mValue == 0) = false from beq_eq_false_iff_ne.mpr hv2] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      by_cases hv1 : v1.mValue = 0
      · rw [if_pos (beq_iff_eq.mpr hv1)] at hok
        rw [STAmount.checked] at hok
        exact STAmount.canonicalize_fczr _ result mode
          (show (STAmount.unchecked v1.mNumericType v2.mValue v2.mOffset
            v2.mIsNegative).mNumericType = .fractional from h1nt) hok
      · rw [show (v1.mValue == 0) = false from beq_eq_false_iff_ne.mpr hv1] at hok
        simp only [Bool.false_eq_true, if_false] at hok
        rw [if_neg hint1] at hok
        cases hi1 : v1.iou mode with
        | error e => rw [hi1] at hok; exact absurd hok (by simp)
        | ok i1 =>
          rw [hi1] at hok; simp only [] at hok
          cases hi2 : v2.iou mode with
          | error e => rw [hi2] at hok; exact absurd hok (by simp)
          | ok i2 =>
            rw [hi2] at hok; simp only [] at hok
            cases hadd : IOUAmount.operator_add i1 i2 mode with
            | error e => rw [hadd] at hok; exact absurd hok (by simp)
            | ok sumI =>
              rw [hadd] at hok; simp only [] at hok
              exact STAmount.ofIOUAmount_fczr sumI mode result hok

/-- `operator_sub` of a `FracCanonZero` first operand is `FracCanonZero`
(it is `operator_add` against the negated second operand). -/
lemma STAmount.operator_sub_fczr (v1 v2 result : STAmount) (mode : rounding_mode)
    (h1 : v1.FracCanonZero) (hok : STAmount.operator_sub v1 v2 mode = .ok result) :
    result.FracCanonZero := by
  unfold STAmount.operator_sub at hok
  exact STAmount.operator_add_fczr v1 v2.operator_neg result mode h1 hok

/-- `roundToExponent` of a `FracCanonZero` value is `FracCanonZero`: the three
early exits pass the value through, and the general path is
`operator_sub (operator_add value reference) reference`, each preserving the
predicate (the reference is a fractional `checked`). -/
lemma STAmount.roundToExponent_fczr (value result : STAmount) (scale : Int)
    (rounding : rounding_mode) (h : value.FracCanonZero)
    (hok : STAmount.roundToExponent value scale rounding = .ok result) :
    result.FracCanonZero := by
  obtain ⟨hnt, hcz⟩ := h
  have hint : ¬ value.integral = true := by unfold STAmount.integral; rw [hnt]; decide
  unfold STAmount.roundToExponent at hok
  rw [if_neg hint] at hok
  by_cases hz : value.isZero = true
  · rw [if_pos hz] at hok; rw [← Except.ok.inj hok]; exact ⟨hnt, hcz⟩
  · rw [if_neg hz] at hok
    by_cases hge : value.exponent ≥ scale
    · rw [if_pos hge] at hok; rw [← Except.ok.inj hok]; exact ⟨hnt, hcz⟩
    · rw [if_neg hge] at hok
      cases href : STAmount.checked value.mNumericType kMinValue scale value.negative rounding with
      | error e => rw [href] at hok; exact absurd hok (by simp)
      | ok referenceValue =>
        rw [href] at hok; simp only [] at hok
        cases hsum : STAmount.operator_add value referenceValue rounding with
        | error e => rw [hsum] at hok; exact absurd hok (by simp)
        | ok sum =>
          rw [hsum] at hok; simp only [] at hok
          have hsum_fczr : sum.FracCanonZero :=
            STAmount.operator_add_fczr value referenceValue sum rounding ⟨hnt, hcz⟩ hsum
          exact STAmount.operator_sub_fczr sum referenceValue result rounding hsum_fczr hok

/-- A zero-mantissa `Number` renormalizes to the zero `IOUAmount`. (The version in
`RoundToScale.Common.Proofs` is `private`, so it is reproven here.) -/
private lemma IOUAmount.ofNumber_zero_mant (n : Number) (mode : rounding_mode)
    (h : n.mantissa_ = 0) :
    IOUAmount.ofNumber n mode = .ok IOUAmount.zero := by
  have hd : doNormalize n.negative_ n.mantissa_ n.exponent_ cMinValue cMaxValue mode
      = .ok Number.zero := by
    unfold doNormalize
    rw [show (n.mantissa_ == 0) = true from beq_iff_eq.mpr h, if_pos rfl]
  unfold IOUAmount.ofNumber IOUAmount.fromNumber Number.normalizeToRange
  rw [hd]
  rfl

/-- `ofIOUAmount` of the zero `IOUAmount` is the canonical zero record. (The version
in `RoundToScale.Common.Proofs` is `private`, so it is reproven here.) -/
private lemma STAmount.ofIOU_zero_rec (mode : rounding_mode) :
    STAmount.ofIOUAmount IOUAmount.zero mode = .ok ⟨.fractional, 0, -100, false⟩ := by
  unfold STAmount.ofIOUAmount STAmount.canonicalize STAmount.iou
  simp only [STAmount.unchecked, STAmount.integral, NumericType.isIntegral,
    Bool.false_eq_true, if_false]
  rfl

/-- **The directed subtraction of an `IOUCanonical` amount from itself flushes to the
canonical zero.** The two 19-digit summands the `IOUAmount` add builds are exact
opposites, so the `Number` cancellation guard returns `Number.zero`, which repacks
to the zero record. Holds on the full `[-96, 80]` scale range (unlike the exact-floor
characterization, which needs `-81`). -/
lemma STAmount.operator_sub_self_zero (a result : STAmount) (mode : rounding_mode)
    (hc : a.IOUCanonical)
    (hok : STAmount.operator_sub a a mode = .ok result) :
    result.mValue = 0 := by
  have h_mv : a.mValue ≠ 0 := by
    intro h0
    have h1 : a.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo; omega
  unfold STAmount.operator_sub at hok
  rw [STAmount.operator_neg_of_ne a h_mv] at hok
  set negA : STAmount := { a with mIsNegative := !a.mIsNegative } with hnegA_def
  have hc_negA : negA.IOUCanonical :=
    { is_fractional := hc.is_fractional
      mant_lo := hc.mant_lo
      mant_hi := hc.mant_hi
      exp_lo := hc.exp_lo
      exp_hi := hc.exp_hi }
  rw [STAmount.operator_add_iou_unfold a negA mode hc hc_negA] at hok
  set s1n : Number := ⟨a.mIsNegative, a.mValue * 10 * 10 * 10, a.mOffset - 3⟩ with hs1n_def
  set s2n : Number := ⟨negA.mIsNegative, negA.mValue * 10 * 10 * 10, negA.mOffset - 3⟩
    with hs2n_def
  obtain ⟨n₂, h_add₂, hok₃⟩ : ∃ n₂, Number.operator_add s1n s2n mode = .ok n₂ ∧
      (match IOUAmount.ofNumber n₂ mode with
       | .error e => (Except.error e : Except Error STAmount)
       | .ok sumI => STAmount.ofIOUAmount sumI mode) = .ok result := by
    match h1 : Number.operator_add s1n s2n mode with
    | .error e => rw [h1] at hok; exact absurd hok (by intro h; cases h)
    | .ok n₂ => rw [h1] at hok; exact ⟨n₂, rfl, hok⟩
  obtain ⟨sumI₂, h_of₂, h_pack₂⟩ : ∃ sumI₂, IOUAmount.ofNumber n₂ mode = .ok sumI₂ ∧
      STAmount.ofIOUAmount sumI₂ mode = .ok result := by
    match h1 : IOUAmount.ofNumber n₂ mode with
    | .error e => rw [h1] at hok₃; exact absurd hok₃ (by intro h; cases h)
    | .ok sumI₂ => rw [h1] at hok₃; exact ⟨sumI₂, rfl, hok₃⟩
  have hs1_norm : s1n.isNormalized :=
    lift_isNormalized a.mIsNegative a.mValue a.mOffset hc.mant_lo hc.mant_hi
      (by have := hc.exp_lo; unfold minExponent; omega)
      (by have := hc.exp_hi; unfold maxExponent; omega)
  have hs2_norm : s2n.isNormalized :=
    lift_isNormalized negA.mIsNegative negA.mValue negA.mOffset hc_negA.mant_lo hc_negA.mant_hi
      (by have := hc_negA.exp_lo; unfold minExponent; omega)
      (by have := hc_negA.exp_hi; unfold maxExponent; omega)
  have hs1_val : s1n.toRat = a.toRat := lift_toRat a hc.mant_hi
  have hs2_val : s2n.toRat = negA.toRat := lift_toRat negA hc_negA.mant_hi
  have hs1_mant : s1n.mantissa_ ≠ 0 := by
    intro h0
    have h1 : s1n.mantissa_.toNat = 0 := by rw [h0]; rfl
    have hM : s1n.mantissa_.toNat = a.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hc.mant_hi
    have := hc.mant_lo; omega
  have hs2_mant : s2n.mantissa_ ≠ 0 := by
    intro h0
    have h1 : s2n.mantissa_.toNat = 0 := by rw [h0]; rfl
    have hM : s2n.mantissa_.toNat = negA.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hc_negA.mant_hi
    have := hc_negA.mant_lo; omega
  have h_diff : s1n.negative_ ≠ s2n.negative_ := by
    show a.mIsNegative ≠ !a.mIsNegative
    rcases hb : a.mIsNegative with _ | _ <;> simp
  have h_opp : s1n.toRat + s2n.toRat = 0 := by
    rw [hs1_val, hs2_val, STAmount.toRat_signed a, STAmount.toRat_signed negA]
    show ((if a.mIsNegative then (-1 : ℚ) else 1) * (a.mValue.toNat : ℚ) * (10 : ℚ) ^ a.mOffset)
       + ((if (!a.mIsNegative) then (-1 : ℚ) else 1) * (a.mValue.toNat : ℚ)
          * (10 : ℚ) ^ a.mOffset) = 0
    rcases hb : a.mIsNegative with _ | _ <;>
      simp only [Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] <;>
      ring
  have h_n₂_val : n₂.toRat = 0 := by
    have h := operator_add_exact_diff_sign s1n s2n n₂ mode hs1_norm hs2_norm
      hs1_mant hs2_mant h_diff Number.zero (Or.inl rfl)
      (by rw [Number.toRat_zero, h_opp]) h_add₂
    rw [h, h_opp]
  have h_n₂_mant : n₂.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp h_n₂_val
  rw [IOUAmount.ofNumber_zero_mant n₂ mode h_n₂_mant] at h_of₂
  have h_sumI₂ : sumI₂ = IOUAmount.zero := Except.ok.inj h_of₂.symm
  rw [h_sumI₂, STAmount.ofIOU_zero_rec mode] at h_pack₂
  rw [← Except.ok.inj h_pack₂]

/-- **The downward `roundToExponent` of a nonnegative value is nonnegative.** The
early exits pass the value through (already nonnegative); the truncation path
floors `value` onto the `10 ^ s` grid, and the floor of a nonnegative value is
nonnegative (`0` is a grid point below it), so the stored result never goes
negative. Uses only the `[-96, 80]` scale range (available from `IOUCanonical`),
never the tighter `-81` the exact-floor characterization needs. -/
theorem STAmount.roundToExponent_downward_nonneg (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-96 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hnn : 0 ≤ value.toRat)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    0 ≤ result.toRat := by
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv_ne : value.mValue ≠ 0 := by
    intro h0; have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo; omega
  have hpos : 0 < value.toRat :=
    lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero value h_mv_ne))
  have hneg : value.mIsNegative = false := by
    rcases hb : value.mIsNegative with _ | _
    · rfl
    · exfalso
      have hsigned := STAmount.toRat_signed value
      rw [hb] at hsigned
      have hm : (0 : ℚ) ≤ (value.mValue.toNat : ℚ) * 10 ^ value.mOffset := by positivity
      rw [hsigned] at hpos
      simp only [if_true] at hpos
      nlinarith [hpos, hm]
  have h_notZero : ¬ value.isZero = true := by
    unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg h_notZero] at hok
  by_cases h_exp : value.exponent ≥ s
  · rw [if_pos h_exp] at hok; rw [← Except.ok.inj hok]; exact hnn
  · rw [if_neg h_exp] at hok
    push_neg at h_exp
    have h_ev : value.mOffset < s := h_exp
    have href_eq : STAmount.checked value.mNumericType kMinValue s value.negative .downward
        = .ok ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
      rw [hc.is_fractional]
      exact STAmount.checked_reference s value.mIsNegative .downward hs_lo hs_hi
    cases href : STAmount.checked value.mNumericType kMinValue s value.negative .downward with
    | error e => rw [href_eq] at href; exact absurd href (by simp)
    | ok referenceValue =>
      rw [href] at hok
      simp only [] at hok
      have hrefeq : referenceValue = ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
        rw [href_eq] at href; exact (Except.ok.inj href).symm
      subst hrefeq
      set refA : STAmount := ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ with hrefA_def
      cases hsum : STAmount.operator_add value refA .downward with
      | error e => rw [hsum] at hok; exact absurd hok (by simp)
      | ok sum =>
        rw [hsum] at hok
        simp only [] at hok
        obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, _, _, _, _⟩ :=
          STAmount.roundToExponent_sum_spec value s .downward hc h_ev hs_lo hs_hi sum hsum
        have h_kMin_toNat : kMinValue.toNat = 10 ^ 15 := by decide
        have hc_sum : sum.IOUCanonical :=
          { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
            mant_lo := by rw [h_sum_mv]; omega
            mant_hi := by rw [h_sum_mv]; omega
            exp_lo := by rw [h_sum_off]; omega
            exp_hi := by rw [h_sum_off]; exact hs_hi }
        have hc_refA : refA.IOUCanonical :=
          { is_fractional := by rw [hrefA_def]; exact hc.is_fractional
            mant_lo := by rw [hrefA_def]; show 10 ^ 15 ≤ kMinValue.toNat; omega
            mant_hi := by rw [hrefA_def]; show kMinValue.toNat < 10 ^ 16; rw [h_kMin_toNat]; norm_num
            exp_lo := by rw [hrefA_def]; show (-96 : ℤ) ≤ s; omega
            exp_hi := by rw [hrefA_def]; exact hs_hi }
        have h_pow_s_pos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
        have hsum_val : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
          rw [STAmount.toRat_signed, h_sum_neg, hneg, h_sum_off, h_sum_mv]
          push_cast; ring
        have hrefA_val : refA.toRat = (10 ^ 15 : ℚ) * 10 ^ s := by
          rw [hrefA_def, STAmount.toRat_signed]
          show (if value.mIsNegative then (-1 : ℚ) else 1) * (kMinValue.toNat : ℚ) * 10 ^ s = _
          rw [hneg, h_kMin_toNat]; push_cast; ring
        have htruth : sum.toRat - refA.toRat = (k : ℚ) * 10 ^ s := by
          rw [hsum_val, hrefA_val]; push_cast; ring
        by_cases hrv : result.mValue = 0
        · rw [STAmount.toRat_signed, show result.mValue.toNat = 0 from by rw [hrv]; rfl]; simp
        · by_cases hk0 : k = 0
          · -- exact cancellation: `k = 0` forces `sum = refA`, so `operator_sub sum refA` is a
            -- self-difference and flushes to the canonical zero, contradicting `result.mValue ≠ 0`.
            exfalso
            have hmv_eq : sum.mValue = kMinValue :=
              UInt64.toNat_inj.mp (by rw [h_sum_mv, hk0, h_kMin_toNat, Nat.add_zero])
            have hsum_eq : sum = refA := by
              rw [hrefA_def]
              have hsum_eta : sum
                  = ⟨sum.mNumericType, sum.mValue, sum.mOffset, sum.mIsNegative⟩ := rfl
              rw [hsum_eta, h_sum_asset, hmv_eq, h_sum_off, h_sum_neg]
            rw [hsum_eq] at hok
            exact hrv (STAmount.operator_sub_self_zero refA result .downward hc_refA hok)
          · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have htruth_pos : 0 < sum.toRat - refA.toRat := by
              rw [htruth]
              have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1
              have : (0 : ℚ) < (k : ℚ) := by linarith
              positivity
            have hrw := STAmount.operator_sub_rounds_iou_downward sum refA result hc_sum hc_refA
              (ne_of_gt htruth_pos) hok hrv
            obtain ⟨_, hgap⟩ := hrw
            have hgap2 : (sum.toRat - refA.toRat) - result.toRat
                ≤ |sum.toRat - refA.toRat| * IOUAmount.εDirected := hgap
            rw [abs_of_pos htruth_pos] at hgap2
            have hεlt : IOUAmount.εDirected < 1 := by
              have h1 : (10 : ℚ) ^ (-15 : ℤ) = 1 / 10 ^ 15 := by
                rw [show ((-15) : ℤ) = -(15 : ℕ) from rfl, zpow_neg, zpow_natCast]; norm_num
              show 11 / (2 ^ 63 - 18 : ℚ) + (10 : ℚ) ^ (-15 : ℤ)
                + 11 / (2 ^ 63 - 18 : ℚ) * (10 : ℚ) ^ (-15 : ℤ) < 1
              rw [h1]; norm_num
            have hε1 : (0 : ℚ) < 1 - IOUAmount.εDirected := by linarith [hεlt]
            have hlb : (sum.toRat - refA.toRat) - (sum.toRat - refA.toRat) * IOUAmount.εDirected
                ≤ result.toRat := by linarith [hgap2]
            have hpos_lb : 0 < (sum.toRat - refA.toRat)
                - (sum.toRat - refA.toRat) * IOUAmount.εDirected := by
              nlinarith [mul_pos htruth_pos hε1]
            linarith [hlb, hpos_lb]

/-- **`roundToExponent` downward never raises the value.** The truncating
`.downward` pass keeps a nonnegative amount at or below its input: it rounds
`value.toRat` down onto the `10^s` grid (`⌊value/10^s⌋·10^s ≤ value`), and the
internal `reference + sub` rounds down again, so `result.toRat ≤ value.toRat`.
Works across the full `[-96, 80]` scale range (no `-81` grid-exactness needed). -/
theorem STAmount.roundToExponent_downward_le (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-96 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hnn : 0 ≤ value.toRat)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    result.toRat ≤ value.toRat := by
  have h_int : value.integral = false := by
    unfold STAmount.integral; rw [hc.is_fractional]; rfl
  have h_mv_ne : value.mValue ≠ 0 := by
    intro h0; have h1 : value.mValue.toNat = 0 := by rw [h0]; rfl
    have := hc.mant_lo; omega
  have hpos : 0 < value.toRat :=
    lt_of_le_of_ne hnn (Ne.symm (STAmount.toRat_ne_zero value h_mv_ne))
  have hneg : value.mIsNegative = false := by
    rcases hb : value.mIsNegative with _ | _
    · rfl
    · exfalso
      have hsigned := STAmount.toRat_signed value
      rw [hb] at hsigned
      have hm : (0 : ℚ) ≤ (value.mValue.toNat : ℚ) * 10 ^ value.mOffset := by positivity
      rw [hsigned] at hpos
      simp only [if_true] at hpos
      nlinarith [hpos, hm]
  have h_notZero : ¬ value.isZero = true := by
    unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
  unfold STAmount.roundToExponent at hok
  rw [if_neg (by rw [h_int]; exact Bool.false_ne_true), if_neg h_notZero] at hok
  by_cases h_exp : value.exponent ≥ s
  · rw [if_pos h_exp] at hok; rw [← Except.ok.inj hok]
  · rw [if_neg h_exp] at hok
    push_neg at h_exp
    have h_ev : value.mOffset < s := h_exp
    have href_eq : STAmount.checked value.mNumericType kMinValue s value.negative .downward
        = .ok ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
      rw [hc.is_fractional]
      exact STAmount.checked_reference s value.mIsNegative .downward hs_lo hs_hi
    cases href : STAmount.checked value.mNumericType kMinValue s value.negative .downward with
    | error e => rw [href_eq] at href; exact absurd href (by simp)
    | ok referenceValue =>
      rw [href] at hok
      simp only [] at hok
      have hrefeq : referenceValue = ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ := by
        rw [href_eq] at href; exact (Except.ok.inj href).symm
      subst hrefeq
      set refA : STAmount := ⟨value.mNumericType, kMinValue, s, value.mIsNegative⟩ with hrefA_def
      cases hsum : STAmount.operator_add value refA .downward with
      | error e => rw [hsum] at hok; exact absurd hok (by simp)
      | ok sum =>
        rw [hsum] at hok
        simp only [] at hok
        obtain ⟨k, hk_le, h_sum_asset, h_sum_mv, h_sum_off, h_sum_neg, _, _, h_dw, _⟩ :=
          STAmount.roundToExponent_sum_spec value s .downward hc h_ev hs_lo hs_hi sum hsum
        have h_kMin_toNat : kMinValue.toNat = 10 ^ 15 := by decide
        have hc_sum : sum.IOUCanonical :=
          { is_fractional := by rw [h_sum_asset]; exact hc.is_fractional
            mant_lo := by rw [h_sum_mv]; omega
            mant_hi := by rw [h_sum_mv]; omega
            exp_lo := by rw [h_sum_off]; omega
            exp_hi := by rw [h_sum_off]; exact hs_hi }
        have hc_refA : refA.IOUCanonical :=
          { is_fractional := by rw [hrefA_def]; exact hc.is_fractional
            mant_lo := by rw [hrefA_def]; show 10 ^ 15 ≤ kMinValue.toNat; omega
            mant_hi := by rw [hrefA_def]; show kMinValue.toNat < 10 ^ 16; rw [h_kMin_toNat]; norm_num
            exp_lo := by rw [hrefA_def]; show (-96 : ℤ) ≤ s; omega
            exp_hi := by rw [hrefA_def]; exact hs_hi }
        have h_pow_s_pos : (0 : ℚ) < (10 : ℚ) ^ s := zpow_pos (by norm_num) _
        have hsum_val : sum.toRat = ((10 ^ 15 + k : ℕ) : ℚ) * 10 ^ s := by
          rw [STAmount.toRat_signed, h_sum_neg, hneg, h_sum_off, h_sum_mv]
          push_cast; ring
        have hrefA_val : refA.toRat = (10 ^ 15 : ℚ) * 10 ^ s := by
          rw [hrefA_def, STAmount.toRat_signed]
          show (if value.mIsNegative then (-1 : ℚ) else 1) * (kMinValue.toNat : ℚ) * 10 ^ s = _
          rw [hneg, h_kMin_toNat]; push_cast; ring
        have htruth : sum.toRat - refA.toRat = (k : ℚ) * 10 ^ s := by
          rw [hsum_val, hrefA_val]; push_cast; ring
        -- `k = ⌊value/10^s⌋`, so `sum - refA = ⌊value/10^s⌋·10^s ≤ value`
        have hkval : (k : ℤ) = ⌊value.toRat / 10 ^ s⌋ := by
          have hh := h_dw rfl
          rw [hneg, if_neg (by decide : ¬ (false = true)), abs_of_nonneg hnn] at hh
          exact hh
        have hsr_le : sum.toRat - refA.toRat ≤ value.toRat := by
          rw [htruth]
          have hfl : (k : ℚ) = (⌊value.toRat / 10 ^ s⌋ : ℚ) := by exact_mod_cast hkval
          rw [hfl]
          have hle : (⌊value.toRat / 10 ^ s⌋ : ℚ) ≤ value.toRat / 10 ^ s := Int.floor_le _
          calc (⌊value.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s
              ≤ (value.toRat / 10 ^ s) * 10 ^ s :=
                mul_le_mul_of_nonneg_right hle (le_of_lt h_pow_s_pos)
            _ = value.toRat := by field_simp
        by_cases hrv : result.mValue = 0
        · have hr0 : result.toRat = 0 := by
            rw [STAmount.toRat_signed, show result.mValue.toNat = 0 from by rw [hrv]; rfl]; simp
          rw [hr0]; exact hnn
        · by_cases hk0 : k = 0
          · exfalso
            have hmv_eq : sum.mValue = kMinValue :=
              UInt64.toNat_inj.mp (by rw [h_sum_mv, hk0, h_kMin_toNat, Nat.add_zero])
            have hsum_eq : sum = refA := by
              rw [hrefA_def]
              have hsum_eta : sum
                  = ⟨sum.mNumericType, sum.mValue, sum.mOffset, sum.mIsNegative⟩ := rfl
              rw [hsum_eta, h_sum_asset, hmv_eq, h_sum_off, h_sum_neg]
            rw [hsum_eq] at hok
            exact hrv (STAmount.operator_sub_self_zero refA result .downward hc_refA hok)
          · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have htruth_pos : 0 < sum.toRat - refA.toRat := by
              rw [htruth]
              have hkq : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1
              have : (0 : ℚ) < (k : ℚ) := by linarith
              positivity
            have hrw := STAmount.operator_sub_rounds_iou_downward sum refA result hc_sum hc_refA
              (ne_of_gt htruth_pos) hok hrv
            have hle : result.toRat ≤ sum.toRat - refA.toRat := hrw.1
            linarith [hle, hsr_le]

/-- A nonzero fractional-canonical amount is `Canonical`. -/
lemma STAmount.Canonical.of_iou (s : STAmount) (h : s.IOUCanonical) : s.Canonical := by
  have hintf : s.integral = false := by
    unfold STAmount.integral; rw [h.is_fractional]; decide
  refine ⟨fun hi => ?_, fun _ => h⟩
  rw [hintf] at hi; exact absurd hi Bool.false_ne_true

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- **KEYSTONE.** The rounded deposit amount is stored canonically (or is zero)
whenever the raw `amountDeposit` is. Integral amounts pass through unchanged; a
fractional amount rounds via the `roundToExponent` pipeline, whose output is
`IOUCanonical`-or-zero. -/
theorem roundToVaultExponent_canonical_or_isZero (amountDeposit rounded : STAmount)
    (assetsTotal : Number) (hcanon : amountDeposit.Canonical)
    (hok : roundToVaultExponent amountDeposit assetsTotal = .ok rounded) :
    rounded.Canonical ∨ rounded.isZero = true := by
  by_cases hint : amountDeposit.integral = true
  · rw [roundToVaultExponent_integral amountDeposit assetsTotal hint] at hok
    left; rw [← Except.ok.inj hok]; exact hcanon
  · have hfr : amountDeposit.integral = false := by
      cases hb : amountDeposit.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hcz : amountDeposit.FracCanonZero :=
      ⟨(hcanon.2 hfr).is_fractional, Or.inl (hcanon.2 hfr)⟩
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, _, hok⟩ := bind_ok_peel _ _ _ hok
    have hrx : amountDeposit.roundToExponent postScale .downward = .ok rounded := hok
    have hres := STAmount.roundToExponent_fczr amountDeposit rounded postScale .downward hcz hrx
    rcases hres.2 with hc | hzero
    · left; exact STAmount.Canonical.of_iou rounded hc
    · right; unfold STAmount.isZero; rw [hzero]; decide

/-- **`roundToVaultExponent` of a nonnegative amount is nonnegative.** The integral
pass is the identity; the fractional pass rounds down onto the post-deposit grid,
which never turns a nonnegative amount negative. The scale range `[-96, 80]` (or the
early-exit sentinel `-100`) is read off the packed exponent, and the truncation core
is `STAmount.roundToExponent_downward_nonneg`. -/
theorem RawVault.roundToVaultExponent_nonneg (amountDeposit result : STAmount) (assetsTotal : Number)
    (hc : amountDeposit.Canonical) (hnn : 0 ≤ amountDeposit.toRat)
    (hok : roundToVaultExponent amountDeposit assetsTotal = .ok result) :
    0 ≤ result.toRat := by
  by_cases hint : amountDeposit.integral = true
  · rw [roundToVaultExponent_integral amountDeposit assetsTotal hint] at hok
    rw [← Except.ok.inj hok]; exact hnn
  · have hfr : amountDeposit.integral = false := by
      cases hb : amountDeposit.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hiou : amountDeposit.IOUCanonical := hc.2 hfr
    have h_mv_ne : amountDeposit.mValue ≠ 0 := by
      intro h0; have h1 : amountDeposit.mValue.toNat = 0 := by rw [h0]; rfl
      have := hiou.mant_lo; omega
    have h_notZero : ¬ amountDeposit.isZero = true := by
      unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, hps, hok⟩ := bind_ok_peel _ _ _ hok
    have hrx : amountDeposit.roundToExponent postScale .downward = .ok result := hok
    unfold postSumExponent at hps
    obtain ⟨_, _, hps⟩ := bind_ok_peel _ _ _ hps
    obtain ⟨assetsTotal', _, hps⟩ := bind_ok_peel _ _ _ hps
    have hps_nt : numberExponent assetsTotal' .fractional = .ok postScale := by
      rw [← hiou.is_fractional]; exact hps
    have hps_range : postScale = -100 ∨ ((-96 : ℤ) ≤ postScale ∧ postScale ≤ 80) := by
      unfold numberExponent at hps_nt
      obtain ⟨a, ha, he⟩ := bind_ok_peel _ _ _ hps_nt
      have heq : a.exponent = postScale :=
        Except.ok.inj (show Except.ok a.exponent = .ok postScale from he)
      rw [← heq]
      exact STAmount.ofNumber_fractional_offset .fractional assetsTotal' .to_nearest a rfl ha
    rcases hps_range with h100 | ⟨hlo, hhi⟩
    · -- the sentinel `-100`: the amount's exponent already clears it, so the amount passes through
      subst h100
      have hge : amountDeposit.exponent ≥ (-100 : ℤ) := by
        have := hiou.exp_lo; show (-100 : ℤ) ≤ amountDeposit.mOffset; omega
      unfold STAmount.roundToExponent at hrx
      rw [if_neg (by rw [hfr]; exact Bool.false_ne_true), if_neg h_notZero, if_pos hge] at hrx
      rw [← Except.ok.inj hrx]; exact hnn
    · exact STAmount.roundToExponent_downward_nonneg amountDeposit result postScale hiou hlo hhi hnn hrx

/-- **`roundToVaultExponent` never raises a nonnegative amount.** The integral pass
is the identity; the fractional pass rounds down onto the post-deposit grid, which
never exceeds the input. So `result.toRat ≤ amountDeposit.toRat`, over the full
`Canonical` range (the deposit charge's conjunct-1 chain `charge ≤ rounded ≤ raw`). -/
theorem RawVault.roundToVaultExponent_le (amountDeposit result : STAmount) (assetsTotal : Number)
    (hc : amountDeposit.Canonical) (hnn : 0 ≤ amountDeposit.toRat)
    (hok : roundToVaultExponent amountDeposit assetsTotal = .ok result) :
    result.toRat ≤ amountDeposit.toRat := by
  by_cases hint : amountDeposit.integral = true
  · rw [roundToVaultExponent_integral amountDeposit assetsTotal hint] at hok
    rw [← Except.ok.inj hok]
  · have hfr : amountDeposit.integral = false := by
      cases hb : amountDeposit.integral with
      | false => rfl
      | true => exact absurd hb hint
    have hiou : amountDeposit.IOUCanonical := hc.2 hfr
    have h_mv_ne : amountDeposit.mValue ≠ 0 := by
      intro h0; have h1 : amountDeposit.mValue.toNat = 0 := by rw [h0]; rfl
      have := hiou.mant_lo; omega
    have h_notZero : ¬ amountDeposit.isZero = true := by
      unfold STAmount.isZero; rw [beq_eq_false_iff_ne.mpr h_mv_ne]; exact Bool.false_ne_true
    unfold roundToVaultExponent at hok
    rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)] at hok
    obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
    obtain ⟨postScale, hps, hok⟩ := bind_ok_peel _ _ _ hok
    have hrx : amountDeposit.roundToExponent postScale .downward = .ok result := hok
    unfold postSumExponent at hps
    obtain ⟨_, _, hps⟩ := bind_ok_peel _ _ _ hps
    obtain ⟨assetsTotal', _, hps⟩ := bind_ok_peel _ _ _ hps
    have hps_nt : numberExponent assetsTotal' .fractional = .ok postScale := by
      rw [← hiou.is_fractional]; exact hps
    have hps_range : postScale = -100 ∨ ((-96 : ℤ) ≤ postScale ∧ postScale ≤ 80) := by
      unfold numberExponent at hps_nt
      obtain ⟨a, ha, he⟩ := bind_ok_peel _ _ _ hps_nt
      have heq : a.exponent = postScale :=
        Except.ok.inj (show Except.ok a.exponent = .ok postScale from he)
      rw [← heq]
      exact STAmount.ofNumber_fractional_offset .fractional assetsTotal' .to_nearest a rfl ha
    rcases hps_range with h100 | ⟨hlo, hhi⟩
    · subst h100
      have hge : amountDeposit.exponent ≥ (-100 : ℤ) := by
        have := hiou.exp_lo; show (-100 : ℤ) ≤ amountDeposit.mOffset; omega
      unfold STAmount.roundToExponent at hrx
      rw [if_neg (by rw [hfr]; exact Bool.false_ne_true), if_neg h_notZero, if_pos hge] at hrx
      rw [← Except.ok.inj hrx]
    · exact STAmount.roundToExponent_downward_le amountDeposit result postScale hiou hlo hhi hnn hrx

/-- The rounded deposit amount from `roundedDepositAmount` is stored canonically
whenever the raw `amountDeposit` is: the `.rounded` outcome forbids the zero case. -/
theorem Vault.roundedDepositAmount_canonical (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hcanon : amountDeposit.Canonical)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    roundedAmount.Canonical := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  rcases roundToVaultExponent_canonical_or_isZero amountDeposit roundedAmount v.assetsTotal
    hcanon hround with hc | hz
  · exact hc
  · rw [hz] at hnz; exact absurd hnz (by decide)

end XRPL.Model.SingleAssetVault
