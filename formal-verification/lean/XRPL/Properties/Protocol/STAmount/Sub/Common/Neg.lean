import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs

namespace XRPL.Model.Protocol

/-! ## `operator_neg` value and field invariants

`operator_neg` flips the sign flag (or is the identity on zero); it preserves the
numericType, offset, and magnitude, and negates the exact value. These let the
subtraction theorems reuse the addition engine via `v1 - v2 = v1 + (-v2)`. -/

lemma STAmount.operator_neg_mNumericType (s : STAmount) :
    s.operator_neg.mNumericType = s.mNumericType := by
  unfold STAmount.operator_neg; split <;> rfl

lemma STAmount.operator_neg_mOffset (s : STAmount) : s.operator_neg.mOffset = s.mOffset := by
  unfold STAmount.operator_neg; split <;> rfl

lemma STAmount.operator_neg_mValue (s : STAmount) : s.operator_neg.mValue = s.mValue := by
  unfold STAmount.operator_neg; split <;> rfl

/-- A zero-magnitude STAmount has value `0`. -/
lemma STAmount.toRat_eq_zero_of_mValue_zero (s : STAmount) (h : s.mValue = 0) : s.toRat = 0 := by
  have habs := STAmount.abs_toRat s
  rw [h] at habs
  simp only [UInt64.toNat_ofNat, Nat.zero_mod, Nat.cast_zero, zero_mul] at habs
  exact abs_eq_zero.mp habs

/-- `operator_neg` negates the exact value. -/
lemma STAmount.operator_neg_toRat (s : STAmount) : s.operator_neg.toRat = -s.toRat := by
  unfold STAmount.operator_neg
  split
  case isTrue h =>
    rw [beq_iff_eq] at h
    rw [STAmount.toRat_eq_zero_of_mValue_zero s h]; ring
  case isFalse h =>
    by_cases hn : s.mIsNegative = true
    · have h1 : ({s with mIsNegative := !s.mIsNegative} : STAmount).toRat
          = (s.mValue.toNat : ℚ) * 10 ^ s.mOffset := STAmount.toRat_of_nonneg _ (by simp [hn])
      have h2 : s.toRat = -((s.mValue.toNat : ℚ) * 10 ^ s.mOffset) := STAmount.toRat_of_neg s hn
      rw [h1, h2, neg_neg]
    · have hf : s.mIsNegative = false := by simpa using hn
      have h1 : ({s with mIsNegative := !s.mIsNegative} : STAmount).toRat
          = -((s.mValue.toNat : ℚ) * 10 ^ s.mOffset) := STAmount.toRat_of_neg _ (by simp [hf])
      have h2 : s.toRat = (s.mValue.toNat : ℚ) * 10 ^ s.mOffset := STAmount.toRat_of_nonneg s hf
      rw [h1, h2]

/-- `operator_neg` negates the signed-drops view. -/
lemma STAmount.operator_neg_signedDrops (s : STAmount) :
    s.operator_neg.signedDrops = -s.signedDrops := by
  unfold STAmount.signedDrops
  rw [STAmount.operator_neg_mValue]
  by_cases h : s.mValue = 0
  · have hz : s.mValue.toNat = 0 := by rw [h]; rfl
    rw [hz]; simp
  · have hne : ¬ (s.mValue == 0) = true := by rw [beq_iff_eq]; exact h
    have hneg : s.operator_neg.mIsNegative = !s.mIsNegative := by
      unfold STAmount.operator_neg; rw [if_neg hne]
    rw [hneg]
    rcases hn : s.mIsNegative <;> simp

/-- An `IntegralCanonical` amount stays `IntegralCanonical` under negation. -/
lemma STAmount.IntegralCanonical.operator_neg {s : STAmount} (h : s.IntegralCanonical) :
    s.operator_neg.IntegralCanonical where
  is_integral := by rw [STAmount.operator_neg_mNumericType]; exact h.is_integral
  offset_zero := by rw [STAmount.operator_neg_mOffset]; exact h.offset_zero
  in_range := by
    rw [STAmount.operator_neg_mNumericType, STAmount.operator_neg_mValue]; exact h.in_range

/-- An `IOUCanonical` amount stays `IOUCanonical` under negation (sign-flip only). -/
lemma STAmount.IOUCanonical.operator_neg {s : STAmount} (h : s.IOUCanonical) :
    s.operator_neg.IOUCanonical where
  is_fractional := by rw [STAmount.operator_neg_mNumericType]; exact h.is_fractional
  mant_lo := by rw [STAmount.operator_neg_mValue]; exact h.mant_lo
  mant_hi := by rw [STAmount.operator_neg_mValue]; exact h.mant_hi
  exp_lo := by rw [STAmount.operator_neg_mOffset]; exact h.exp_lo
  exp_hi := by rw [STAmount.operator_neg_mOffset]; exact h.exp_hi

end XRPL.Model.Protocol
