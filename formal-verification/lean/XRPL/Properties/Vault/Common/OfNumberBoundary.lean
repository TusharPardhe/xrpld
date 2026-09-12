import XRPL.Properties.Vault.Common.NumberBridge
import XRPL.Properties.Vault.Common.STAmountToNumber
import XRPL.Properties.Vault.Common.WithdrawAccuracy
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Protocol.STAmount.Mul.Common.DirectedTight
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRangeBound
import XRPL.Properties.Protocol.Number.ToRep.ToRep

/-! # Boundary facts for the fractional `ofNumber` pipeline

The IOU `ofNumber` rounding lemmas (`ofNumber_iou_within_ulp`,
`ofNumber_iou_within_half_ulp`, `ofNumber_iou_rounds_within`,
`ofNumber_iou_snap_pos`) require a 19-digit source mantissa,
`minExponent ≤ r.exponent_`, and `r.exponent_ + 4 ≤ maxExponent`. This file
derives the exponent side conditions from the success of the run itself, so the
vault accuracy proofs can consume the ULP bounds without free-floating exponent
hypotheses:

* **success bounds the source exponent** — a successful fractional `ofNumber`
  with nonzero result forces `r.exponent_ + 4 ≤ maxExponent` (in fact
  `r.exponent_ ≤ 77`): `doNormalize_scaleDown` errors at `maxExponent`, and the
  final `checked` errors above `cMaxOffset = 80`;
* **fractional outputs are `IOUCanonical`-or-zero** — a `.ok` fractional
  `ofNumber` yields a canonical 16-digit record or a zero-mantissa record;
* **directional `to_rep` facts** — `.downward` on a sign-cleared normalized
  `Number` is the integer floor, and `.to_nearest` lands within `1/2`. -/

namespace XRPL.Model.Protocol

/-! ## `doNormalize_scaleDown` errors when the exponent runs into `maxExponent` -/

/-- One erroring step of `doNormalize_scaleDown`: when the mantissa is still above
`maxMant` and the exponent has reached `maxExponent`, the loop aborts. -/
lemma doNormalize_scaleDown_step_error {maxMant M : UInt64} {e : Int} {g : Guard}
    (hgt : maxMant < M) (he : maxExponent ≤ e) :
    doNormalize_scaleDown maxMant M e g = .error .normalize1 := by
  conv_lhs => unfold doNormalize_scaleDown
  rw [dif_pos hgt, if_pos he]

/-- A 19-digit mantissa needs three `scaleDown` steps to reach the 16-digit range;
if the exponent is within two of `maxExponent` at entry, one of those three
`maxExponent` guards fires and the loop errors. -/
lemma doNormalize_scaleDown_errors_of_ge (M : UInt64) (e : Int) (g : Guard)
    (hM_lo : 10 ^ 18 ≤ M.toNat) (hM_hi : M.toNat < 10 ^ 19)
    (he : maxExponent ≤ e + 2) :
    doNormalize_scaleDown cMaxValue M e g = .error .normalize1 := by
  have h10 : (10 : UInt64).toNat = 10 := uint64_ten_toNat
  have hm1 : (M / 10).toNat = M.toNat / 10 := by rw [UInt64.toNat_div, h10]
  have hm2 : (M / 10 / 10).toNat = M.toNat / 100 := by
    rw [UInt64.toNat_div, hm1, h10, Nat.div_div_eq_div_mul]
  by_cases hc0 : maxExponent ≤ e
  · exact doNormalize_scaleDown_step_error
      (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val]; omega) hc0
  · have hc0' : e < maxExponent := by omega
    rw [doNormalize_scaleDown_step
          (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val]; omega) hc0']
    by_cases hc1 : maxExponent ≤ e + 1
    · exact doNormalize_scaleDown_step_error
        (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val, hm1]; omega) hc1
    · have hc1' : e + 1 < maxExponent := by omega
      rw [doNormalize_scaleDown_step
            (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val, hm1]; omega) hc1']
      exact doNormalize_scaleDown_step_error
        (by rw [UInt64.lt_iff_toNat_lt, cMaxValue_val, hm2]; omega) (by omega)

/-- **Success of the 16-digit `doNormalize` bounds the source exponent.** A `.ok`
result of `doNormalize _ M _ cMinValue cMaxValue _` on a 19-digit mantissa forces
`e + 3 ≤ maxExponent` (otherwise the `scaleDown` loop would abort). -/
lemma doNormalize_iou_exp_hi (neg : Bool) (M : UInt64) (e : Int) (mode : rounding_mode)
    (res : Number)
    (hM_lo : 10 ^ 18 ≤ M.toNat) (hM_hi : M.toNat < 10 ^ 19)
    (hok : doNormalize neg M e cMinValue cMaxValue mode = .ok res) :
    e + 3 ≤ maxExponent := by
  by_contra hc
  have hge : maxExponent ≤ e + 2 := by omega
  have hM_ne : ¬ (M == 0) = true := by
    intro h
    have : M = 0 := by exact_mod_cast beq_iff_eq.mp h
    rw [this] at hM_lo; simp at hM_lo
  set g0 : Guard := if neg then Guard.new.set_negative else Guard.new with hg0_def
  have herr := doNormalize_scaleDown_errors_of_ge M e g0 hM_lo hM_hi hge
  rw [doNormalize] at hok
  rw [show (M == 0) = false from Bool.eq_false_iff.mpr (fun h => hM_ne h)] at hok
  simp only [Bool.false_eq_true, if_false] at hok
  rw [doNormalize_scaleUp_id cMinValue M e
        (by rw [UInt64.le_iff_toNat_le, cMinValue_val]; omega)] at hok
  simp only [] at hok
  rw [← hg0_def, herr] at hok
  exact absurd hok (by simp)

/-- The `doRoundUp` overflow guard: whenever the outer
`if r'.exponent_ > maxExponent then .error else .ok r'` returns `.ok res`, the
exponent of `res` is at most `maxExponent`. -/
private lemma doRoundUp_outer_ok_exp_le {r' res : RoundResult} {loc : Error}
    (h : (if r'.exponent_ > maxExponent then (.error loc : Except Error RoundResult)
          else .ok r') = .ok res) :
    res.exponent_ ≤ maxExponent := by
  by_cases h_ovf : r'.exponent_ > maxExponent
  · rw [if_pos h_ovf] at h; exact absurd h (by simp)
  · rw [if_neg h_ovf] at h
    rw [← Except.ok.inj h]
    exact not_lt.mp h_ovf

/-- **A `.ok` `doRoundUp` result never overshoots `maxExponent`.** The final guard
of `doRoundUp` errors exactly when the rounded exponent exceeds `maxExponent`. -/
lemma doRoundUp_ok_exp_le (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp neg m e minM maxM mode loc = .ok res) :
    res.exponent_ ≤ maxExponent := by
  unfold Guard.doRoundUp at hok
  simp only [] at hok
  exact doRoundUp_outer_ok_exp_le hok

/-! ## Success-keyed 16-digit `normalizeToRange` facts

`normalizeToRange_16_mantissa_range` / `_exp_range` characterize the output but
require `n.exponent_ + 4 ≤ maxExponent`. Keyed on **success** we only have
`n.exponent_ + 3 ≤ maxExponent` (from `doNormalize_iou_exp_hi`); the carry-cusp
branch, which would push the exponent to `n.exponent_ + 4`, is then handled by a
combined `doRoundUp` characterization whose overflow guard errors when
`maxExponent < n.exponent_ + 4`. -/

/-- **Combined carry-cusp `doRoundUp` characterization.** Rounding up the top of
the 16-digit range renormalizes to `(cMinValue, e+1)` and then either errors (if
`e+1` overflows `maxExponent`) or returns that record. This unifies
`doRoundUp_small_cusp` (the `.ok` leg) with its erroring leg. -/
lemma doRoundUp_small_cusp_eq (g : Guard) (neg : Bool) (e : Int) (mode : rounding_mode)
    (loc : Error)
    (hb : (g.round mode == 1 || (g.round mode == 0 && cMaxValue % 2 == 1)) = true)
    (hexp_lo : minExponent ≤ e + 1) :
    g.doRoundUp neg cMaxValue e cMinValue cMaxValue mode loc
      = if maxExponent < e + 1 then (.error loc : Except Error RoundResult)
        else .ok { negative_ := neg, mantissa_ := cMinValue, exponent_ := e + 1 } := by
  have h9 : cMaxValue % 10 = 9 := by decide
  have hdiv : cMaxValue / 10 = 999999999999999 := by decide
  have hdivsucc : (999999999999999 : UInt64) + 1 = cMinValue := by decide
  have hdig9 : 9 * 2 ^ 60 ≤ (g.push 9).digits_.toNat := by
    rw [toNat_push_digits, show (9 : UInt64).toNat % 16 = 9 from by decide]; omega
  have hne0 : (g.push 9).digits_ ≠ 0 := by
    intro h
    have : (g.push 9).digits_.toNat = 0 := by rw [h]; rfl
    omega
  have hpush_ne : (g.push 9).empty = false := by unfold Guard.empty Guard.unrecoverable; simp [hne0]
  have hpush_sbit : (g.push 9).sbit_ = g.sbit_ := Guard.push_sbit g 9
  have hroundUp' : ((g.push 9).round mode == 1
      || ((g.push 9).round mode == 0 && (999999999999999 : UInt64) % 2 == 1)) = true := by
    cases mode with
    | to_nearest =>
      have htn : (g.push 9).round .to_nearest = 1 := by
        unfold Guard.round
        rw [if_neg (by rw [hpush_ne]; exact Bool.false_ne_true),
            if_pos (show (g.push 9).digits_ > 0x5000000000000000 from by
              rw [gt_iff_lt, UInt64.lt_iff_toNat_lt,
                  show (0x5000000000000000 : UInt64).toNat = 5764607523034234880 from by decide]
              omega)]
      rw [htn]; rfl
    | towards_zero =>
      exfalso
      have : g.round .towards_zero = -1 ∨ g.round .towards_zero = -2 := by
        unfold Guard.round; by_cases he : g.empty = true
        · rw [if_pos he]; right; rfl
        · rw [if_neg he]; left; rfl
      rcases this with h | h <;> rw [h] at hb <;> simp at hb
    | downward =>
      have hsb : g.sbit_ = true := by
        by_contra hh; rw [Bool.not_eq_true] at hh
        have : g.round .downward = -1 ∨ g.round .downward = -2 := by
          unfold Guard.round; by_cases he : g.empty = true
          · rw [if_pos he]; right; rfl
          · rw [if_neg he, hh]; left; rfl
        rcases this with h | h <;> rw [h] at hb <;> simp at hb
      exact round_bool_downward_neg (g.push 9) 999999999999999 (hpush_sbit.trans hsb) hpush_ne
    | upward =>
      have hsb : g.sbit_ = false := by
        by_contra hh; rw [Bool.not_eq_false] at hh
        have : g.round .upward = -1 ∨ g.round .upward = -2 := by
          unfold Guard.round; by_cases he : g.empty = true
          · rw [if_pos he]; right; rfl
          · rw [if_neg he, hh]; left; rfl
        rcases this with h | h <;> rw [h] at hb <;> simp at hb
      exact round_bool_upward_pos (g.push 9) 999999999999999 (hpush_sbit.trans hsb) hpush_ne
  unfold Guard.doRoundUp
  simp only []
  rw [pushOverflow_noop_of_lt_maxRep (by rw [maxRep_val, cMaxValue_val]; omega) g mode, hb]
  simp only [if_true]
  rw [if_neg (show ¬ (cMaxValue < cMaxValue ∧ cMaxValue < maxRep) from
        fun h => absurd (UInt64.lt_iff_toNat_lt.mp h.1) (by omega)),
      if_neg (show ¬ (maxRep < cMaxValue ∧ cMaxValue < maxRepUp) from fun h =>
        absurd (UInt64.lt_iff_toNat_lt.mp h.1) (by rw [maxRep_val, cMaxValue_val]; omega))]
  unfold Guard.doDropDigit
  rw [h9, hdiv]
  simp only []
  rw [if_pos hroundUp', hdivsucc,
      show Guard.bringIntoRange neg cMinValue (e + 1) cMinValue
          = { negative_ := neg, mantissa_ := cMinValue, exponent_ := e + 1 } from by
        rw [bringIntoRange_noscale_result
              (fun h => absurd (UInt64.lt_iff_toNat_lt.mp h.1) (by omega)),
            if_neg (not_or.mpr ⟨by omega, by decide⟩)]]

/-- **Success-keyed 16-digit `normalizeToRange` facts.** A `.ok` result on a
19-digit input, under the *weaker* `n.exponent_ + 3 ≤ maxExponent`, still has a
canonical 16-digit mantissa, an exponent in `[n.exponent_ + 3, maxExponent]`, and
(for a sign-cleared input) a non-negative signed mantissa. The carry-cusp exponent
`n.exponent_ + 4` is admissible only when it does not overflow `maxExponent`
(otherwise the run would have errored). -/
theorem normalizeToRange_iou_ok_facts (n : Number) (mode : rounding_mode)
    (mant : Int64) (exp : Int)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (he_lo : minExponent ≤ n.exponent_ + 3) (he_hi : n.exponent_ + 3 ≤ maxExponent)
    (hok : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp)) :
    (cMinValue.toNat ≤ mant.toInt.natAbs ∧ mant.toInt.natAbs ≤ cMaxValue.toNat) ∧
    (n.exponent_ + 3 ≤ exp ∧ exp ≤ maxExponent) ∧
    (n.negative_ = false → 0 ≤ mant.toInt) := by
  obtain ⟨g, _hrep, _hsbit, _h_empty_of, h_red⟩ :=
    doNormalize_small_facts n.negative_ n.mantissa_ n.exponent_ mode h_lo h_hi he_lo he_hi
  have hm3 : (n.mantissa_ / 10 / 10 / 10).toNat = n.mantissa_.toNat / 1000 :=
    m_div_thousand_toNat n.mantissa_
  have hcMax : cMaxValue.toNat = 10 ^ 16 - 1 := by decide
  have hcMin : cMinValue.toNat = 10 ^ 15 := by decide
  -- A sign-cleared `if`-mantissa over a sub-`2^63` magnitude is non-negative.
  have hsign : ∀ (X : UInt64), X.toNat < 2 ^ 63 →
      (if n.negative_ then -X.toInt64 else X.toInt64) = mant → n.negative_ = false → 0 ≤ mant.toInt := by
    intro X hX heq hneg
    rw [← heq, hneg]
    simp only [Bool.false_eq_true, if_false]
    rw [UInt64.toInt64_toInt_of_lt _ hX]; positivity
  by_cases hround : (g.round mode == 1
      || (g.round mode == 0 && (n.mantissa_ / 10 / 10 / 10) % 2 == 1)) = true
  · by_cases hcusp : n.mantissa_ / 10 / 10 / 10 = cMaxValue
    · -- carry-cusp: admissible only when `(n.exponent_+3)+1 ≤ maxExponent`.
      have hbr : (g.round mode == 1 || (g.round mode == 0 && cMaxValue % 2 == 1)) = true := by
        rw [hcusp] at hround; exact hround
      have hcusp_eq := doRoundUp_small_cusp_eq g n.negative_ (n.exponent_ + 3) mode
        .normalize2 hbr (by omega)
      by_cases hovf : maxExponent < (n.exponent_ + 3) + 1
      · exfalso
        have h_err : n.normalizeToRange cMinValue cMaxValue mode = .error .normalize2 := by
          unfold Number.normalizeToRange
          rw [h_red, hcusp, hcusp_eq, if_pos hovf]
        rw [h_err] at hok; exact absurd hok (by simp)
      · have hcompute : n.normalizeToRange cMinValue cMaxValue mode
            = .ok (if n.negative_ then -cMinValue.toInt64 else cMinValue.toInt64,
                   (n.exponent_ + 3) + 1) := by
          unfold Number.normalizeToRange
          rw [h_red, hcusp, hcusp_eq, if_neg hovf]
          rfl
        rw [hcompute] at hok
        obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
        refine ⟨⟨?_, ?_⟩, ⟨by omega, by omega⟩, hsign cMinValue (by rw [hcMin]; omega) hmant⟩
        · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hcMin]; omega), hcMin]
        · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hcMin]; omega), hcMin, hcMax]
          omega
    · -- fire: increment in place, exponent unchanged.
      have hlt : (n.mantissa_ / 10 / 10 / 10).toNat < cMaxValue.toNat := by
        have hne : (n.mantissa_ / 10 / 10 / 10).toNat ≠ cMaxValue.toNat :=
          fun h => hcusp (UInt64.toNat_inj.mp h)
        rw [hcMax, hm3] at hne ⊢; omega
      have hadd : (n.mantissa_ / 10 / 10 / 10 + 1).toNat = n.mantissa_.toNat / 1000 + 1 := by
        rw [UInt64.toNat_add, hm3, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      have hcompute : n.normalizeToRange cMinValue cMaxValue mode
          = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10 + 1).toInt64
                 else (n.mantissa_ / 10 / 10 / 10 + 1).toInt64, n.exponent_ + 3) := by
        unfold Number.normalizeToRange
        rw [h_red, doRoundUp_small_fire g n.negative_ _ (n.exponent_ + 3) mode
          .normalize2 hround (by rw [hcMin, hm3]; omega) hlt (by omega) (by omega)]
        rfl
      rw [hcompute] at hok
      obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
      refine ⟨⟨?_, ?_⟩, ⟨by omega, by omega⟩, hsign _ (by rw [hadd]; omega) hmant⟩
      · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hadd]; omega), hadd, hcMin]
        omega
      · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hadd]; omega), hadd, hcMax]
        omega
  · -- truncate: keep the 3-digit truncation, exponent unchanged.
    have hcompute : n.normalizeToRange cMinValue cMaxValue mode
        = .ok (if n.negative_ then -(n.mantissa_ / 10 / 10 / 10).toInt64
               else (n.mantissa_ / 10 / 10 / 10).toInt64, n.exponent_ + 3) := by
      unfold Number.normalizeToRange
      rw [h_red, doRoundUp_small_truncate g n.negative_ _ (n.exponent_ + 3) mode
        .normalize2 (by simpa using hround) (by rw [hcMin, hm3]; omega)
        (by rw [hcMax, hm3]; omega) (by omega) (by omega)]
      rfl
    rw [hcompute] at hok
    obtain ⟨hmant, hexp⟩ := Prod.mk.inj (Except.ok.inj hok)
    refine ⟨⟨?_, ?_⟩, ⟨by omega, by omega⟩, hsign _ (by rw [hm3]; omega) hmant⟩
    · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hm3]; omega), hm3, hcMin]
      omega
    · rw [← hmant, signed_mantissa_natAbs n.negative_ _ (by rw [hm3]; omega), hm3, hcMax]
      omega

/-- A `.ok` `normalizeToRange` implies the underlying `doNormalize` succeeded. -/
lemma normalizeToRange_ok_doNormalize_ok (n : Number) (minM maxM : UInt64) (mode : rounding_mode)
    (mant : Int64) (exp : Int)
    (hok : n.normalizeToRange minM maxM mode = .ok (mant, exp)) :
    ∃ res : Number, doNormalize n.negative_ n.mantissa_ n.exponent_ minM maxM mode = .ok res := by
  unfold Number.normalizeToRange at hok
  split at hok
  · exact absurd hok (by simp)
  · rename_i res hd; exact ⟨res, hd⟩

/-- A `.ok` 16-digit `normalizeToRange` on a 19-digit input bounds the source
exponent below `maxExponent - 2`. -/
lemma normalizeToRange_iou_exp_hi (n : Number) (mode : rounding_mode) (mant : Int64) (exp : Int)
    (h_lo : 10 ^ 18 ≤ n.mantissa_.toNat) (h_hi : n.mantissa_.toNat < 10 ^ 19)
    (hok : n.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp)) :
    n.exponent_ + 3 ≤ maxExponent := by
  obtain ⟨res, hd⟩ := normalizeToRange_ok_doNormalize_ok n cMinValue cMaxValue mode mant exp hok
  exact doNormalize_iou_exp_hi n.negative_ n.mantissa_ n.exponent_ mode res h_lo h_hi hd

/-! ## Lemmas 1 & 2: success shape of a fractional `ofNumber`

The shared reduction below feeds the 19-digit `normalizeToRange` output through
`checked_iou_cases`: a nonzero result is exactly the canonical 16-digit record
`⟨.fractional, m, e, neg⟩` with `e ∈ [-96, 80]`, which is both `IOUCanonical`
(**Lemma 2**) and forces `r.exponent_ ≤ 77` (**Lemma 1**). -/

/-- **Core success shape of a nonzero fractional `ofNumber`.** The result is a
canonical 16-digit IOU record and the source exponent obeys `r.exponent_ + 4 ≤
maxExponent`. -/
lemma STAmount.ofNumber_iou_ok_facts (r : Number) (mode : rounding_mode) (result : STAmount)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_)
    (hok : STAmount.ofNumber .fractional r mode = .ok result) (hresult : result.mValue ≠ 0) :
    result.IOUCanonical ∧ r.exponent_ + 4 ≤ maxExponent := by
  have hr_ne : r.mantissa_ ≠ 0 := by intro h; rw [h] at hr_lo; simp at hr_lo
  have hmne : (r.mantissa_ != 0) = true := by simp [hr_ne]
  have hneg_eq : decide (r.signum < 0) = r.negative_ := by
    unfold Number.signum
    rcases hrn : r.negative_ with _ | _ <;>
      simp only [hmne, if_true, if_false, Bool.false_eq_true] <;> decide
  set neg : Bool := decide (r.signum < 0) with hneg_def
  set working : Number := if neg then r.operator_neg else r with hw_def
  have hw_mant : working.mantissa_ = r.mantissa_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp [Number.operator_neg_mantissa_of_ne r hr_ne]
  have hw_exp : working.exponent_ = r.exponent_ := by
    rw [hw_def]; rcases neg with _ | _
    · simp
    · simp only [if_true]; unfold Number.operator_neg; rw [if_neg (by simpa using hr_ne)]
  have hw_neg : working.negative_ = false := by
    rw [hw_def, hneg_eq]
    by_cases hrn : r.negative_ = true
    · rw [if_pos hrn, Number.operator_neg_negative_of_ne r hr_ne]; simp [hrn]
    · rw [if_neg hrn]; simpa using hrn
  have hw_lo : 10 ^ 18 ≤ working.mantissa_.toNat := by rw [hw_mant]; exact hr_lo
  have hw_hi : working.mantissa_.toNat < 10 ^ 19 := by rw [hw_mant]; exact hr_hi
  have hwe_lo : minExponent ≤ working.exponent_ := by rw [hw_exp]; exact hre_lo
  unfold STAmount.ofNumber at hok
  rw [if_neg (by decide), ← hneg_def, ← hw_def] at hok
  cases hnorm : working.normalizeToRange kMinValue kMaxValue mode with
  | error e => rw [hnorm] at hok; exact absurd hok (by simp)
  | ok me =>
    obtain ⟨mant, exp⟩ := me
    rw [hnorm] at hok
    simp only at hok
    have hnorm' : working.normalizeToRange cMinValue cMaxValue mode = .ok (mant, exp) := hnorm
    have hexp_hi3 : working.exponent_ + 3 ≤ maxExponent :=
      normalizeToRange_iou_exp_hi working mode mant exp hw_lo hw_hi hnorm'
    obtain ⟨⟨hmlo, hmhi⟩, ⟨hexp_lo3, hexp_le⟩, hsgn⟩ :=
      normalizeToRange_iou_ok_facts working mode mant exp hw_lo hw_hi (by omega) hexp_hi3 hnorm'
    have hmant_pos : 0 ≤ mant.toInt := hsgn hw_neg
    have hmant_natAbs : mant.toInt.natAbs = mant.toUInt64.toNat := by
      have := toUInt64_toNat_of_nonneg mant hmant_pos; omega
    have hmtu_lo : 10 ^ 15 ≤ mant.toUInt64.toNat := by
      rw [← hmant_natAbs]; have := hmlo; rw [(by decide : cMinValue.toNat = 10 ^ 15)] at this
      exact this
    have hmtu_hi : mant.toUInt64.toNat < 10 ^ 16 := by
      rw [← hmant_natAbs]; have := hmhi; rw [(by decide : cMaxValue.toNat = 10 ^ 16 - 1)] at this
      omega
    obtain ⟨hexp_lo80, hexp_hi80, hres_eq⟩ :=
      STAmount.checked_iou_cases .fractional mant.toUInt64 exp neg mode rfl
        hmtu_lo hmtu_hi (by omega) hexp_le result hok hresult
    refine ⟨?_, ?_⟩
    · rw [hres_eq]; exact ⟨rfl, hmtu_lo, hmtu_hi, hexp_lo80, hexp_hi80⟩
    · rw [hw_exp] at hexp_lo3
      have hme : maxExponent = 32768 := rfl
      omega

/-- **Lemma 1: success bounds the source exponent away from `maxExponent`.**
Discharges the `hre_hi` (`r.exponent_ + 4 ≤ maxExponent`) side condition of the
delivered IOU `ofNumber` rounding lemmas (`ofNumber_iou_within_ulp`,
`_within_half_ulp`, `_rounds_within`, `_snap_pos`) from success of the run. -/
lemma STAmount.ofNumber_iou_success_exp_range (r : Number) (mode : rounding_mode) (result : STAmount)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_)
    (hok : STAmount.ofNumber .fractional r mode = .ok result) (hresult : result.mValue ≠ 0) :
    r.exponent_ + 4 ≤ maxExponent :=
  (STAmount.ofNumber_iou_ok_facts r mode result hr_lo hr_hi hre_lo hok hresult).2

/-- **Lemma 2: fractional `ofNumber` output is `IOUCanonical`-or-zero.** Every
`.ok` fractional `ofNumber` yields a canonical 16-digit record or a zero-mantissa
record, so `toNumber` is value-faithful on it without a separate 16-digit
hypothesis. -/
lemma STAmount.ofNumber_iou_canonical_or_zero (r : Number) (mode : rounding_mode) (result : STAmount)
    (hr_lo : 10 ^ 18 ≤ r.mantissa_.toNat) (hr_hi : r.mantissa_.toNat < 10 ^ 19)
    (hre_lo : minExponent ≤ r.exponent_)
    (hok : STAmount.ofNumber .fractional r mode = .ok result) :
    result.IOUCanonical ∨ result.mValue = 0 := by
  by_cases hz : result.mValue = 0
  · exact Or.inr hz
  · exact Or.inl (STAmount.ofNumber_iou_ok_facts r mode result hr_lo hr_hi hre_lo hok hz).1

/-! ## Lemma 3: `.downward` `to_rep` on a sign-cleared `Number` is the floor -/

/-- `pushOverflow` never touches the sign bit. -/
lemma Guard.pushOverflow_sbit (g : Guard) (m : UInt64) (mode : rounding_mode) :
    (g.pushOverflow m mode).sbit_ = g.sbit_ := by
  unfold Guard.pushOverflow
  by_cases h : maxRep ≤ m ∧ m < maxRepUp
  · rw [if_pos h]
    simp only []
    rw [apply_ite Guard.sbit_, Guard.push_sbit, ite_self]
  · rw [if_neg h]

/-- `to_rep.shift` never touches the sign bit (it only `push`es digits). -/
lemma Number.to_rep_shift_sbit (D : Int64) (off : Int) (g : Guard) :
    (Number.to_rep.shift D off g).2.sbit_ = g.sbit_ := by
  simp only [shift_eq_spec]
  induction D, off, g using shiftSpec.induct with
  | case1 drops offset gg hneg ih =>
    rw [shiftSpec, if_pos hneg, ih, Guard.push_sbit]
  | case2 drops offset gg hnneg =>
    rw [shiftSpec, if_neg hnneg]

/-- **`.downward` `to_rep` on a sign-cleared `Number` is the integer floor.**
When `sbit_ = false` the `.downward` round decision is `-1`/`-2`, never a bump, so
the shifted magnitude is truncated toward zero: the result brackets the value as
`r ≤ n.toRat < r + 1`. The lower bound gives payout/charge upper bounds. -/
lemma Number.to_rep_downward_floor (n : Number) (r : Int64)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : n.to_rep .downward = .ok r) :
    (r.toInt : ℚ) ≤ n.toRat ∧ n.toRat < (r.toInt : ℚ) + 1 := by
  have hupper : n.toRat < (r.toInt : ℚ) + 1 := by
    have hw := to_rep_within_one n .downward r hn hok
    rw [abs_lt] at hw; linarith [hw.1]
  refine ⟨?_, hupper⟩
  by_cases hexp0 : 0 ≤ n.exponent
  · rw [to_rep_exact_of_exponent_nonneg n .downward r hn hexp0 hok]
  · push_neg at hexp0
    unfold Number.to_rep at hok
    simp only at hok
    by_cases hz : (n.mantissa == 0) = true
    · rw [if_pos hz] at hok
      have hr : r = 0 := by injection hok with h; exact h.symm
      have hmant0 : n.mantissa.toInt = 0 := by rw [beq_iff_eq] at hz; rw [hz]; decide
      have htr : n.toRat = 0 := by rw [← mantissa_mul_exponent_eq_toRat n hn, hmant0]; norm_num
      rw [hr, htr, show (0 : Int64).toInt = 0 from by decide]; norm_num
    · rw [if_neg hz] at hok
      have hmag_nn : 0 ≤ n.mantissa.toInt := (mantissa_sign n).2 hneg
      have hmagM_le : n.mantissa.toInt.natAbs ≤ maxRep.toNat := mantissa_natAbs_le_maxRep n hn
      rw [hneg] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      rw [if_pos hexp0, if_neg (by omega : ¬ n.exponent ≥ 0)] at hok
      simp only at hok
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      set k : ℕ := (-n.exponent).toNat with hkdef
      have hk_cast : (k : ℤ) = -n.exponent := by rw [hkdef]; omega
      have hsp2_sbit : sp.2.sbit_ = false := by
        rw [hspdef, Number.to_rep_shift_sbit n.mantissa n.exponent Guard.new]; rfl
      have hDf : sp.1.toInt = n.mantissa.toInt / 10 ^ k := by
        rw [hspdef]; exact shift_fst_eq n.mantissa n.exponent Guard.new hmag_nn
      have hsp_nn : 0 ≤ sp.1.toInt := by rw [hDf]; exact Int.ediv_nonneg hmag_nn (by positivity)
      have hsp_le : sp.1.toInt ≤ (maxRep.toNat : ℤ) := by
        rw [hDf]
        calc n.mantissa.toInt / 10 ^ k ≤ n.mantissa.toInt := Int.ediv_le_self _ hmag_nn
          _ ≤ (maxRep.toNat : ℤ) := by omega
      -- the `.downward` round decision never bumps (guard sign bit is clear)
      set pof : Guard := sp.2.pushOverflow sp.1.toUInt64 .downward with hpof_def
      have hpof_sbit : pof.sbit_ = false := by rw [hpof_def, Guard.pushOverflow_sbit, hsp2_sbit]
      have hround_val : pof.round .downward = -1 ∨ pof.round .downward = -2 := by
        unfold Guard.round
        by_cases he : pof.empty = true
        · rw [if_pos he]; right; rfl
        · rw [if_neg he, hpof_sbit]; left; rfl
      have hb : (pof.round .downward == 1 || (pof.round .downward == 0 && sp.1 % 2 == 1)) = false := by
        rcases hround_val with h | h <;> rw [h] <;> simp
      rw [hb] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      rw [if_neg (show ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) from fun hc => by
        have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
        rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
        omega)] at hok
      have hr : r = sp.1 := by injection hok with h; exact h.symm
      rw [hr]
      -- floor bound: `sp.1 = ⌊n.mantissa / 10^k⌋ ≤ n.toRat`
      have h10k_ne : (10 : ℤ) ^ k ≠ 0 := by positivity
      have hmul_le : sp.1.toInt * 10 ^ k ≤ n.mantissa.toInt := by
        rw [hDf]; exact Int.ediv_mul_le _ h10k_ne
      have hmul_le_q : (sp.1.toInt : ℚ) * 10 ^ k ≤ (n.mantissa.toInt : ℚ) := by exact_mod_cast hmul_le
      rw [← mantissa_mul_exponent_eq_toRat n hn]
      have hexp_pow : (10 : ℚ) ^ n.exponent = ((10 : ℚ) ^ k)⁻¹ := by
        rw [show n.exponent = -(k : ℤ) from by omega, zpow_neg, zpow_natCast]
      rw [hexp_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℚ) < 10 ^ k)]
      exact hmul_le_q

/-! ## Lemma 4: `.to_nearest` `to_rep` rounds within `1/2` -/

/-- Peel one decimal digit of an `emod` by a power of ten. -/
private lemma int_emod_pow10_succ (x : ℤ) (m : ℕ) :
    x % 10 ^ (m + 1) = x % 10 + 10 * ((x / 10) % 10 ^ m) := by
  have hpm : (10 : ℤ) ^ (m + 1) = 10 * 10 ^ m := by ring
  have hpos : (0 : ℤ) < 10 ^ m := by positivity
  have hr10 : 0 ≤ x % 10 ∧ x % 10 < 10 :=
    ⟨Int.emod_nonneg x (by norm_num), Int.emod_lt_of_pos x (by norm_num)⟩
  have hrm : 0 ≤ (x / 10) % 10 ^ m ∧ (x / 10) % 10 ^ m < 10 ^ m :=
    ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ hpos⟩
  have hdecomp : x = (x % 10 + 10 * ((x / 10) % 10 ^ m)) + 10 * 10 ^ m * ((x / 10) / 10 ^ m) := by
    have e1 : 10 * (x / 10) + x % 10 = x := Int.mul_ediv_add_emod x 10
    have e2 : 10 ^ m * ((x / 10) / 10 ^ m) + (x / 10) % 10 ^ m = x / 10 :=
      Int.mul_ediv_add_emod (x / 10) (10 ^ m)
    linear_combination -e1 - 10 * e2
  rw [hpm]
  conv_lhs => rw [hdecomp]
  rw [Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by nlinarith [hrm.1, hrm.2, hr10.2, hpos])]

/-- **`to_rep.shift` accumulates the dropped fraction in the guard.** Starting from
a guard representing `f`, shifting `D ≥ 0` down by `k = (-off).toNat` decimal places
leaves a guard representing `f / 10^k + (D mod 10^k) / 10^k`. -/
lemma Number.to_rep_shift_represents (D : Int64) (off : Int) (g : Guard) :
    0 ≤ D.toInt → ∀ f : ℚ, represents g f →
    represents (Number.to_rep.shift D off g).2
      (f / 10 ^ (-off).toNat + ((D.toInt % 10 ^ (-off).toNat : ℤ) : ℚ) / 10 ^ (-off).toNat) := by
  simp only [shift_eq_spec]
  induction D, off, g using shiftSpec.induct with
  | case1 drops offset gg hneg ih =>
    intro h0 f hg
    rw [shiftSpec, if_pos hneg]
    have hdiv_nn : 0 ≤ (drops / 10).toInt := by
      rw [toInt_div_ten_of_nonneg drops h0]; exact Int.ediv_nonneg h0 (by norm_num)
    have hd_toInt : ((drops % 10).toUInt64.toNat : ℤ) = drops.toInt % 10 := by
      have h1 := toUInt64_toNat_of_nonneg (drops % 10)
        (by rw [toInt_mod_ten_of_nonneg drops h0]; exact Int.emod_nonneg _ (by norm_num))
      rw [h1, toInt_mod_ten_of_nonneg drops h0]
    have hd_lt : (drops % 10).toUInt64.toNat < 10 := by
      have := toInt_mod_ten_of_nonneg drops h0
      have hlt : drops.toInt % 10 < 10 := Int.emod_lt_of_pos _ (by norm_num)
      omega
    have hpush := represents_push hg (d := (drops % 10).toUInt64) hd_lt
    have hgoal := ih hdiv_nn ((f + ((drops % 10).toUInt64.toNat : ℚ)) / 10) hpush
    have hk1 : (-(offset + 1)).toNat = (-offset).toNat - 1 := by omega
    have hk_pos : 1 ≤ (-offset).toNat := by omega
    set k : ℕ := (-offset).toNat with hkdef
    rw [hk1] at hgoal
    -- the accumulated fraction equals the target closed form
    have hEq : f / 10 ^ k + ((drops.toInt % 10 ^ k : ℤ) : ℚ) / 10 ^ k
        = (f + ((drops % 10).toUInt64.toNat : ℚ)) / 10 / 10 ^ (k - 1)
          + (((drops / 10).toInt % 10 ^ (k - 1) : ℤ) : ℚ) / 10 ^ (k - 1) := by
      rw [toInt_div_ten_of_nonneg drops h0]
      have hd0_q : ((drops % 10).toUInt64.toNat : ℚ) = ((drops.toInt % 10 : ℤ) : ℚ) := by
        exact_mod_cast hd_toInt
      rw [hd0_q]
      have hstep_q : ((drops.toInt % 10 ^ k : ℤ) : ℚ)
          = ((drops.toInt % 10 : ℤ) : ℚ) + 10 * (((drops.toInt / 10) % 10 ^ (k - 1) : ℤ) : ℚ) := by
        have h := int_emod_pow10_succ drops.toInt (k - 1)
        rw [show (k - 1) + 1 = k from by omega] at h
        rw [h]; push_cast; ring
      rw [hstep_q, show (10 : ℚ) ^ k = 10 ^ (k - 1) * 10 from by rw [← pow_succ]; congr 1; omega]
      field_simp
      ring
    rw [hEq]
    exact hgoal
  | case2 drops offset gg hnneg =>
    intro h0 f hg
    rw [shiftSpec, if_neg hnneg]
    have hk0 : (-offset).toNat = 0 := by omega
    rw [hk0]
    simp only [pow_zero, Int.emod_one, div_one, Int.cast_zero, add_zero]
    exact hg

/-- **`.to_nearest` `to_rep` on a normalized `Number` rounds within `1/2`.** The
round-to-nearest guard decision (`round = 1` for fraction `> 1/2`, `= 0` for
`= 1/2` with even tie-break, `= -1` for `< 1/2`) keeps the integer result within
half a unit of the value. Sharpens `to_rep_within_one` for `to_nearest`. -/
lemma Number.to_rep_to_nearest_within_half (n : Number) (r : Int64)
    (hn : n.isNormalized) (hneg : n.negative_ = false)
    (hok : n.to_rep .to_nearest = .ok r) :
    |(r.toInt : ℚ) - n.toRat| ≤ (1 / 2 : ℚ) := by
  by_cases hexp0 : 0 ≤ n.exponent
  · rw [to_rep_exact_of_exponent_nonneg n .to_nearest r hn hexp0 hok, sub_self, abs_zero]
    norm_num
  · push_neg at hexp0
    unfold Number.to_rep at hok
    simp only at hok
    by_cases hz : (n.mantissa == 0) = true
    · rw [if_pos hz] at hok
      have hr : r = 0 := by injection hok with h; exact h.symm
      have hmant0 : n.mantissa.toInt = 0 := by rw [beq_iff_eq] at hz; rw [hz]; decide
      have htr : n.toRat = 0 := by rw [← mantissa_mul_exponent_eq_toRat n hn, hmant0]; norm_num
      rw [hr, htr, show (0 : Int64).toInt = 0 from by decide]; norm_num
    · rw [if_neg hz] at hok
      have hmag_nn : 0 ≤ n.mantissa.toInt := (mantissa_sign n).2 hneg
      have hmagM_le : n.mantissa.toInt.natAbs ≤ maxRep.toNat := mantissa_natAbs_le_maxRep n hn
      rw [hneg] at hok
      simp only [Bool.false_eq_true, if_false] at hok
      rw [if_pos hexp0, if_neg (by omega : ¬ n.exponent ≥ 0)] at hok
      simp only at hok
      set sp := Number.to_rep.shift n.mantissa n.exponent Guard.new with hspdef
      set k : ℕ := (-n.exponent).toNat with hkdef
      have hk_pos : 1 ≤ k := by rw [hkdef]; omega
      have hk_cast : (k : ℤ) = -n.exponent := by rw [hkdef]; omega
      -- floor value and its remainder fraction
      have hDf : sp.1.toInt = n.mantissa.toInt / 10 ^ k := by
        rw [hspdef]; exact shift_fst_eq n.mantissa n.exponent Guard.new hmag_nn
      have hsp_nn : 0 ≤ sp.1.toInt := by rw [hDf]; exact Int.ediv_nonneg hmag_nn (by positivity)
      have hval : n.toRat = (n.mantissa.toInt : ℚ) * (10 : ℚ) ^ n.exponent :=
        (mantissa_mul_exponent_eq_toRat n hn).symm
      have hexp_pow : (10 : ℚ) ^ n.exponent = ((10 : ℚ) ^ k)⁻¹ := by
        rw [show n.exponent = -(k : ℤ) from by omega, zpow_neg, zpow_natCast]
      -- `frac = n.toRat - sp.1 = (n.mantissa mod 10^k)/10^k`
      set frac : ℚ := ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) / 10 ^ k with hfrac_def
      have h10k_pos : (0 : ℚ) < 10 ^ k := by positivity
      have h10k_ne : (10 : ℚ) ^ k ≠ 0 := ne_of_gt h10k_pos
      have hd_q : (n.mantissa.toInt : ℚ)
          = 10 ^ k * ((n.mantissa.toInt / 10 ^ k : ℤ) : ℚ) + ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) := by
        exact_mod_cast (Int.mul_ediv_add_emod n.mantissa.toInt (10 ^ k)).symm
      have hval_frac : n.toRat = (sp.1.toInt : ℚ) + frac := by
        have key : (n.mantissa.toInt : ℚ) = (sp.1.toInt : ℚ) * 10 ^ k + ((n.mantissa.toInt % 10 ^ k : ℤ) : ℚ) := by
          rw [hDf]; linear_combination hd_q
        rw [hval, hexp_pow, ← div_eq_mul_inv, hfrac_def, key]
        field_simp
      have hfrac_nn : 0 ≤ frac := by
        rw [hfrac_def]; apply div_nonneg _ (le_of_lt h10k_pos)
        exact_mod_cast Int.emod_nonneg _ (by positivity)
      have hfrac_lt : frac < 1 := by
        rw [hfrac_def, div_lt_one h10k_pos]
        exact_mod_cast Int.emod_lt_of_pos _ (by positivity)
      -- the guard represents `frac`, and `pushOverflow` is a no-op (`sp.1 < maxRep`)
      have hrep : represents sp.2 frac := by
        have := Number.to_rep_shift_represents n.mantissa n.exponent Guard.new hmag_nn 0 represents_new
        rw [← hspdef, ← hkdef] at this
        simpa [hfrac_def] using this
      have hsp_lt : sp.1.toUInt64.toNat < maxRep.toNat := by
        have h2 : n.mantissa.toInt ≤ (maxRep.toNat : ℤ) := by omega
        have hsp_lt_int : sp.1.toInt < (maxRep.toNat : ℤ) := by
          by_contra hcon
          push_neg at hcon
          have hmul_le : sp.1.toInt * 10 ^ k ≤ n.mantissa.toInt := by
            rw [hDf]; exact Int.ediv_mul_le _ (by positivity)
          have h10k_ge : (10 : ℤ) ≤ 10 ^ k := by
            calc (10 : ℤ) = 10 ^ 1 := by norm_num
              _ ≤ 10 ^ k := pow_le_pow_right₀ (by norm_num) hk_pos
          have hmr : (1 : ℤ) ≤ maxRep.toNat := by decide
          nlinarith [hmul_le, h2, hcon, h10k_ge, hmr,
            mul_le_mul_of_nonneg_right hcon (show (0 : ℤ) ≤ 10 ^ k from by positivity),
            mul_le_mul_of_nonneg_left h10k_ge (show (0 : ℤ) ≤ (maxRep.toNat : ℤ) from by positivity)]
        have hnat : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
        omega
      have hpof : sp.2.pushOverflow sp.1.toUInt64 .to_nearest = sp.2 :=
        pushOverflow_noop_of_lt_maxRep hsp_lt sp.2 .to_nearest
      rw [hpof] at hok
      -- cusp clamp never fires, and the round decision drives the ±1/2 bound
      have hno_cusp : ¬ (maxRep.toInt64 < sp.1 ∧ sp.1 < maxRepUp.toInt64) := fun hc => by
        have hlt := (Int64.lt_iff_toInt_lt).mp hc.1
        rw [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at hlt
        have hnat : (sp.1.toUInt64.toNat : ℤ) = sp.1.toInt := toUInt64_toNat_of_nonneg sp.1 hsp_nn
        omega
      by_cases hb : (sp.2.round .to_nearest == 1 || (sp.2.round .to_nearest == 0 && sp.1 % 2 == 1)) = true
      · -- round up: fraction ≥ 1/2, so `1 - frac ≤ 1/2`
        rw [if_pos hb] at hok
        by_cases hovf : sp.1 ≥ maxRep.toInt64
        · rw [if_pos hovf] at hok; exact absurd hok (by simp)
        · rw [if_neg hovf] at hok
          have hovf' : sp.1.toInt < (maxRep.toNat : ℤ) := by
            have := (Int64.lt_iff_toInt_lt).mp (Int64.not_le.mp hovf)
            rwa [show maxRep.toInt64.toInt = (maxRep.toNat : ℤ) from by decide] at this
          have hadd : (sp.1 + 1).toInt = sp.1.toInt + 1 := by
            rw [Int64.toInt_add, int64_one_toInt, Int.bmod_eq_iff (by norm_num)]
            rw [maxRep_val] at hovf'; refine ⟨by omega, by push_cast; omega⟩
          have hr : r = sp.1 + 1 := by injection hok with h; exact h.symm
          have hfrac_ge : (1 / 2 : ℚ) ≤ frac := by
            rw [Bool.or_eq_true] at hb
            rcases hb with h1 | h1
            · rw [beq_iff_eq] at h1
              exact le_of_lt (represents_round_eq_one hrep h1)
            · rw [Bool.and_eq_true, beq_iff_eq] at h1
              exact le_of_eq (represents_round_eq_zero hrep h1.1).symm
          rw [hr, hadd, hval_frac]
          push_cast
          rw [abs_le]
          clear hovf hno_cusp hb hok hrep
          constructor <;> linarith
      · -- no round up: fraction ≤ 1/2
        have hfrac_le : frac ≤ (1 / 2 : ℚ) := by
          by_contra hcon
          push_neg at hcon
          have : sp.2.round .to_nearest = 1 := represents_f_gt_half hrep hcon
          rw [this] at hb; simp at hb
        rw [if_neg hb] at hok
        rw [if_neg hno_cusp] at hok
        have hr : r = sp.1 := by injection hok with h; exact h.symm
        rw [hr, hval_frac]
        rw [abs_le]
        clear hno_cusp hb hok hrep
        constructor <;> linarith

end XRPL.Model.Protocol
