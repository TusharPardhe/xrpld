import Mathlib.Tactic

import XRPL.Model.Protocol.Number

/-! # The digit-dropping loops with and without the early exit

`alignDownSpec` and `shiftSpec` are the loops as implemented before rippled PR 7825: one
digit dropped per step, with no early exit.

`alignDown_eq_spec` equates `Number.operator_add.alignDown` with `alignDownSpec`, and
`shift_eq_spec` equates `Number.to_rep.shift` with `shiftSpec`: each pair returns the same
result on every input. -/

namespace XRPL.Model.Protocol

/-! ## `alignDown` (the `operator_add` exponent alignment) -/

/-- The alignment loop written without the early exit: one `doDropDigit` per step. -/
def alignDownSpec (m : UInt64) (e : Int) (g : Guard) (target : Int) : UInt64 × Int × Guard :=
  if e < target then
    alignDownSpec (g.doDropDigit m e).2.1 (g.doDropDigit m e).2.2 (g.doDropDigit m e).1 target
  else (m, e, g)
termination_by (target - e).toNat
decreasing_by simp [Guard.doDropDigit]; omega

lemma push_zero_fixed (g : Guard) (h : g.digits_ = 0) : g.push 0 = g := by
  obtain ⟨d, x, s⟩ := g
  subst h
  simp only [Guard.push]
  rw [Guard.mk.injEq]
  refine ⟨by decide, ?_, rfl⟩
  rw [show ((0 : UInt64) &&& 0xF) = 0 from by decide]
  simp

private lemma alignDownSpec_fixed_aux : ∀ (n : Nat) (e : Int) (g : Guard) (target : Int),
    g.digits_ = 0 → (target - e).toNat = n →
    alignDownSpec 0 e g target = (0, (if e < target then target else e), g) := by
  intro n
  induction n with
  | zero =>
    intro e g target _ hn
    have hge : ¬ e < target := by omega
    rw [alignDownSpec, if_neg hge, if_neg hge]
  | succ k ih =>
    intro e g target h hn
    rw [alignDownSpec]
    by_cases hlt : e < target
    · rw [if_pos hlt]
      have hstep : g.doDropDigit 0 e = (g, 0, e + 1) := by
        unfold Guard.doDropDigit
        simp only [show (0 : UInt64) % 10 = 0 from by decide,
                   show (0 : UInt64) / 10 = 0 from by decide, push_zero_fixed g h]
      rw [hstep]
      dsimp only
      rw [ih (e + 1) g target h (by omega)]
      rw [if_pos hlt]
      by_cases h2 : e + 1 < target
      · rw [if_pos h2]
      · have heq : e + 1 = target := by omega
        rw [if_neg h2, heq]
    · rw [if_neg hlt, if_neg hlt]

lemma alignDownSpec_fixed (e : Int) (g : Guard) (target : Int) (h : g.digits_ = 0) :
    alignDownSpec 0 e g target = (0, (if e < target then target else e), g) :=
  alignDownSpec_fixed_aux (target - e).toNat e g target h rfl

/-- `doDropDigitWithTargetU64` returns the same result as `alignDownSpec`: when it exits
early, the steps it skips would have left the mantissa and guard unchanged
(`alignDownSpec_fixed`). -/
private lemma doDropDigitWithTargetU64_eq_spec_aux :
    ∀ (n : Nat) (g : Guard) (m : UInt64) (e target : Int),
    (target - e).toNat = n →
    g.doDropDigitWithTargetU64 m e target = alignDownSpec m e g target := by
  intro n
  induction n with
  | zero =>
    intro g m e target hn
    have hge : ¬ e < target := by omega
    rw [Guard.doDropDigitWithTargetU64, alignDownSpec, if_neg hge, if_neg hge]
  | succ k ih =>
    intro g m e target hn
    by_cases hlt : e < target
    · by_cases hsc : (m == 0 && g.unrecoverable) = true
      · rw [Guard.doDropDigitWithTargetU64, if_pos hlt, if_pos hsc]
        have hm : m = 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq] at hsc; exact hsc.1
        have hd : g.digits_ = 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq, Guard.unrecoverable] at hsc
          exact hsc.2
        subst hm
        rw [alignDownSpec_fixed e g target hd, if_pos hlt]
      · rw [Guard.doDropDigitWithTargetU64, alignDownSpec, if_pos hlt, if_pos hlt, if_neg hsc]
        have he2 : (g.doDropDigit m e).2.2 = e + 1 := rfl
        have hmeas : (target - (g.doDropDigit m e).2.2).toNat = k := by rw [he2]; omega
        exact ih (g.doDropDigit m e).1 (g.doDropDigit m e).2.1 (g.doDropDigit m e).2.2 target hmeas
    · rw [Guard.doDropDigitWithTargetU64, alignDownSpec, if_neg hlt, if_neg hlt]

theorem doDropDigitWithTargetU64_eq_spec (g : Guard) (m : UInt64) (e target : Int) :
    g.doDropDigitWithTargetU64 m e target = alignDownSpec m e g target :=
  doDropDigitWithTargetU64_eq_spec_aux (target - e).toNat g m e target rfl

/-- `alignDown` calls `doDropDigitWithTargetU64`, so it equals `alignDownSpec`. -/
theorem alignDown_eq_spec (m : UInt64) (e : Int) (g : Guard) (target : Int) :
    Number.operator_add.alignDown m e g target = alignDownSpec m e g target := by
  rw [Number.operator_add.alignDown.eq_def]
  exact doDropDigitWithTargetU64_eq_spec g m e target

/-! ## `shift` (the `to_rep` mantissa shift) -/

/-- The `shift` loop written without the early exit: one digit dropped per step. -/
def shiftSpec (drops : rep) (offset : Int) (g : Guard) : rep × Guard :=
  if offset < 0 then shiftSpec (drops / 10) (offset + 1) (g.push (drops % 10).toUInt64)
  else (drops, g)
termination_by (-offset).toNat
decreasing_by omega

/-- With value `0` and an unrecoverable guard, each further step pushes a `0` digit and
leaves both the value and the guard unchanged. -/
private lemma shiftSpec_fixed_aux : ∀ (n : Nat) (offset : Int) (g : Guard),
    g.digits_ = 0 → (-offset).toNat = n → shiftSpec 0 offset g = (0, g) := by
  intro n
  induction n with
  | zero =>
    intro offset g _ hn
    have hge : ¬ offset < 0 := by omega
    rw [shiftSpec, if_neg hge]
  | succ k ih =>
    intro offset g h hn
    rw [shiftSpec]
    by_cases hlt : offset < 0
    · rw [if_pos hlt]
      have hpush : g.push ((0 : rep) % 10).toUInt64 = g := by
        rw [show ((0 : rep) % 10).toUInt64 = 0 from by decide]
        exact push_zero_fixed g h
      rw [show (0 : rep) / 10 = 0 from by decide, hpush]
      exact ih (offset + 1) g h (by omega)
    · rw [if_neg hlt]

lemma shiftSpec_fixed (offset : Int) (g : Guard) (h : g.digits_ = 0) :
    shiftSpec 0 offset g = (0, g) :=
  shiftSpec_fixed_aux (-offset).toNat offset g h rfl

private lemma doDropDigitWithTargetI64_eq_shiftSpec_aux :
    ∀ (n : Nat) (g : Guard) (drops : rep) (offset : Int),
    (-offset).toNat = n →
    g.doDropDigitWithTargetI64 drops offset 0 = shiftSpec drops offset g := by
  intro n
  induction n with
  | zero =>
    intro g drops offset hn
    have hge : ¬ offset < 0 := by omega
    rw [Guard.doDropDigitWithTargetI64, shiftSpec, if_neg hge, if_neg hge]
  | succ k ih =>
    intro g drops offset hn
    by_cases hlt : offset < 0
    · by_cases hsc : (drops == 0 && g.unrecoverable) = true
      · rw [Guard.doDropDigitWithTargetI64, if_pos hlt, if_pos hsc]
        have hm : drops = 0 := by simp only [Bool.and_eq_true, beq_iff_eq] at hsc; exact hsc.1
        have hd : g.digits_ = 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq, Guard.unrecoverable] at hsc; exact hsc.2
        subst hm
        rw [shiftSpec_fixed offset g hd]
      · rw [Guard.doDropDigitWithTargetI64, shiftSpec, if_pos hlt, if_pos hlt, if_neg hsc]
        exact ih (g.push (drops % 10).toUInt64) (drops / 10) (offset + 1) (by omega)
    · rw [Guard.doDropDigitWithTargetI64, shiftSpec, if_neg hlt, if_neg hlt]

lemma doDropDigitWithTargetI64_eq_shiftSpec (g : Guard) (drops : rep) (offset : Int) :
    g.doDropDigitWithTargetI64 drops offset 0 = shiftSpec drops offset g :=
  doDropDigitWithTargetI64_eq_shiftSpec_aux (-offset).toNat g drops offset rfl

/-- `Number.to_rep.shift` calls `doDropDigitWithTargetI64`, so it equals `shiftSpec`. -/
lemma shift_eq_spec (drops : rep) (offset : Int) (g : Guard) :
    Number.to_rep.shift drops offset g = shiftSpec drops offset g := by
  rw [Number.to_rep.shift.eq_def]
  exact doDropDigitWithTargetI64_eq_shiftSpec g drops offset

end XRPL.Model.Protocol
