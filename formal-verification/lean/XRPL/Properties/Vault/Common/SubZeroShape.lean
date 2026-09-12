import XRPL.Properties.Vault.Common.NumberBridge
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.SameSign
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.DiffSignRepresents

/-! # Zero-record shape chain for `operator_sub`

Every mantissa-`0` output of the `to_nearest` add/sub pipeline (on normalized
operands) is the literal `Number.zero`. This upgrades the `NumberBridge`
normalization lemmas to unconditional form: a `to_nearest` subtraction result is
always normalized, so its `operator_eq Number.zero` test coincides with
`mantissa_ = 0`.

These are copies of the `LawfulSupport` lemmas of the same name, isolated here in
an upstream module so the charge proofs can use them without importing
`LawfulSupport` (which carries a duplicate `withdraw_success_reduces` clashing
with the `WithdrawReduction` copy the charge proofs already pull in). -/

namespace XRPL.Model.Protocol

/-- `bringIntoRange` output: the canonical zero record, or nonzero mantissa. -/
lemma Guard.bringIntoRange_cases_sz (neg : Bool) (m : UInt64) (e : Int) (minM : UInt64) :
    Guard.bringIntoRange neg m e minM
      = ({ negative_ := false, mantissa_ := 0, exponent_ := -2147483648 } : RoundResult) ∨
    (Guard.bringIntoRange neg m e minM).mantissa_ ≠ 0 := by
  unfold Guard.bringIntoRange
  rcases hp : (if m < minM ∧ m ≠ 0 then (m * 10, e - 1) else (m, e)) with ⟨m', e'⟩
  dsimp only
  by_cases hz : e' < minExponent ∨ m' = 0
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    push_neg at hz
    exact Or.inr hz.2

/-- A mantissa-`0` `doRoundUp` result converts to the literal `Number.zero`. -/
lemma Guard.doRoundUp_zero_shape_sz (g : Guard) (neg : Bool) (m : UInt64) (e : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (loc : Error) (res : RoundResult)
    (hok : g.doRoundUp neg m e minM maxM mode loc = .ok res)
    (h0 : res.mantissa_ = 0) : res.toNumber = Number.zero := by
  have key : ∃ (n' : Bool) (m' : UInt64) (e' : Int),
      res = Guard.bringIntoRange n' m' e' minM := by
    unfold Guard.doRoundUp Guard.doDropDigit at hok
    dsimp only at hok
    repeat' split at hok
    all_goals
      first
      | exact ⟨_, _, _, (Except.ok.inj hok).symm⟩
      | simp at hok
  obtain ⟨n', m', e', hres⟩ := key
  rcases Guard.bringIntoRange_cases_sz n' m' e' minM with hc | hc
  · rw [hres, hc]; rfl
  · rw [← hres] at hc
    exact absurd h0 hc

/-- A mantissa-`0` `doNormalize128` result is the literal `Number.zero`. -/
lemma doNormalize128_zero_shape_sz (zn : Bool) (M : UInt128) (e : Int) (sticky : Bool)
    (mode : rounding_mode) (result : Number)
    (hok : doNormalize128 zn M e largeRange.min largeRange.max mode sticky = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  unfold doNormalize128 at hok
  by_cases hM : (M == 0) = true
  · rw [if_pos hM] at hok
    exact (Except.ok.inj hok).symm
  · rw [if_neg hM] at hok
    simp only [] at hok
    rcases hsu : doNormalize128.scaleUp largeRange.min M e with ⟨M₁, e₁⟩
    rw [hsu] at hok
    simp only [] at hok
    set g₀ : Guard := (if sticky = true
        then (if zn then Guard.new.set_negative else Guard.new).set_sticky
        else (if zn then Guard.new.set_negative else Guard.new)) with hg₀_def
    cases hsd : doNormalize_scaleDown128 largeRange.max M₁ e₁ g₀ with
    | error err => rw [hsd] at hok; simp at hok
    | ok sd =>
      obtain ⟨m₂, e₂, g₂⟩ := sd
      rw [hsd] at hok
      simp only [] at hok
      by_cases hund : (e₂ < minExponent || m₂ < toUInt128 largeRange.min) = true
      · rw [if_pos hund] at hok
        exact (Except.ok.inj hok).symm
      · rw [if_neg hund] at hok
        cases hcap : doNormalize_capAtMaxRep (toUInt64 m₂) e₂ g₂ with
        | error err => rw [hcap] at hok; simp at hok
        | ok cp =>
          obtain ⟨m₃, e₃, g₃⟩ := cp
          rw [hcap] at hok
          simp only [] at hok
          cases hru : g₃.doRoundUp zn m₃ e₃ largeRange.min largeRange.max mode
              .normalize2 with
          | error err => rw [hru] at hok; simp at hok
          | ok res =>
            rw [hru] at hok
            simp only [] at hok
            have hres : result = res.toNumber := (Except.ok.inj hok).symm
            have hres0 : res.mantissa_ = 0 := by
              rw [hres] at h0; exact h0
            rw [hres]
            exact Guard.doRoundUp_zero_shape_sz g₃ zn m₃ e₃ largeRange.min largeRange.max mode
              .normalize2 res hru hres0

/-- A mantissa-`0` `to_nearest` addition result of normalized operands is the
literal `Number.zero`. -/
lemma Number.operator_add_zero_shape_sz (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y .to_nearest = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have h_result : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    subst h_result
    exact Number.eq_zero_of_mantissa_zero result hx h0
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have h_result : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    subst h_result
    exact Number.eq_zero_of_mantissa_zero result hy h0
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · unfold Number.operator_add at hok
    rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
    exact (Except.ok.inj
      (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
  have hx_mant_ne : x.mantissa_ ≠ 0 := by
    intro h
    exact hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
  have hy_mant_ne : y.mantissa_ ≠ 0 := by
    intro h
    exact hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
  by_cases h_sign_eq : x.negative_ = y.negative_
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hresult_ne, _, _⟩ :=
      operator_add_algorithmic_facts_same_sign_to_nearest x y result hx hy hx_mant_ne hy_mant_ne
        h_sign_eq heq_guard hok
    exact hresult_ne h0
  · obtain ⟨M, ze', δ, zn, sticky, _, _, _, _, _, _, _, hok128, _, _, _⟩ :=
      operator_add_algorithmic_facts_diff_sign_represents x y result .to_nearest hx hy
        hx_mant_ne hy_mant_ne h_sign_eq heq_guard hok
    exact doNormalize128_zero_shape_sz zn M ze' sticky .to_nearest result hok128 h0

/-- A mantissa-`0` `to_nearest` subtraction result of normalized operands is the
literal `Number.zero`. -/
lemma Number.operator_sub_zero_shape_sz (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  unfold Number.operator_sub at hok
  exact Number.operator_add_zero_shape_sz x y.operator_neg result hx
    (Number.operator_neg_isNormalized y hy) hok h0

/-- **Unconditional `to_nearest` subtraction normalization.** -/
lemma operator_sub_isNormalized_to_nearest_sz (x y result : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_sub x y .to_nearest = .ok result) :
    result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · rw [Number.operator_sub_zero_shape_sz x y result hx hy hok h0]
    exact Or.inl rfl
  · exact operator_sub_isNormalized_to_nearest x y result hx hy hok h0

/-- `divQuotient128` on a zero numerator yields a zero quotient (no remainder). -/
lemma divQuotient128_zero_sz (ym : UInt64) (xe ye : Int) :
    divQuotient128 0 ym xe ye = (0, xe - ye - 17, false) := by
  have hnum : toUInt128 (0 : UInt64) * (100000000000000000 : UInt128) = 0 := by decide
  have hmod : (0 : UInt128) % toUInt128 ym = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simp
  have hdiv : (0 : UInt128) / toUInt128 ym = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv]; simp
  unfold divQuotient128
  dsimp only
  rw [hnum, hmod, hdiv]
  norm_num

/-- `doNormalize128` on a zero mantissa is the literal `Number.zero`; the WF loop is
short-circuited by the leading `if mantissa == 0` guard, so the kernel never reduces
it. -/
lemma doNormalize128_zero_num_sz (zn : Bool) (e : Int) (minM maxM : UInt64)
    (mode : rounding_mode) (s : Bool) :
    doNormalize128 zn 0 e minM maxM mode s = .ok Number.zero := by
  unfold doNormalize128
  rw [if_pos (by decide : ((0 : UInt128) == 0) = true)]

/-- **A nonzero `operator_div` result forces a nonzero numerator.** A zero numerator
returns `x` (if it tests as zero) or drives `divQuotient128` to a zero quotient,
which `doNormalize128` normalizes to `Number.zero`; either way the result has zero
mantissa. -/
lemma operator_div_numerator_ne_zero_sz (x y result : Number) (mode : rounding_mode)
    (hyne : ¬ y.operator_eq Number.zero = true)
    (hok : Number.operator_div x y mode = .ok result) (hres : result.mantissa_ ≠ 0) :
    x.mantissa_ ≠ 0 := by
  intro hxz
  apply hres
  unfold Number.operator_div at hok
  rw [if_neg hyne] at hok
  by_cases hxe : x.operator_eq Number.zero = true
  · rw [if_pos hxe] at hok
    have hxr : x = result :=
      Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)
    rw [← hxr]; exact hxz
  · rw [if_neg hxe] at hok
    rw [hxz, divQuotient128_zero_sz] at hok
    simp only [] at hok
    rw [doNormalize128_zero_num_sz] at hok
    have : Number.zero = result :=
      Except.ok.inj (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)
    rw [← this]; rfl

end XRPL.Model.Protocol
