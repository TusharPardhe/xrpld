import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Protocol.IntAmount.ToNumber.ToNumber
import XRPL.Properties.Protocol.Common.AmountArith
import XRPL.Properties.Protocol.Number.Common.Constants

/-! # `STAmount.toNumber` exactness on canonical amounts

The vault exchange pipeline feeds `STAmount.toNumber` amounts produced by
`ofNumber`/`roundToExponent`, which are canonical for their type. The `Number`
tree proves `toNumber` exactness only for the two canonical shapes separately
(`toNumber_iou_canonical_*` for `IOUCanonical`, `IntAmount.toNumber_exact` for the
integral backing). This file packages both into a single "value-exact, normalized
`Number`" statement the vault reductions can apply.

* fractional (`IOUCanonical`): `toNumber` is the exact 19-digit lift.
* integral (`IntegralCanonical`, mantissa fits `Int64`): `toNumber` routes through
  `IntAmount.toNumber`, exact and integer-valued (`den = 1`). This branch also
  covers the integral zero (`STAmount.zero .int64`), so the vault's `sharesCreated`
  toNumber is handled uniformly.
-/

namespace XRPL.Model.Protocol

/-! ## Fractional (IOU) exactness -/

/-- **`toNumber` is value-exact and normalized on a canonical IOU amount.** The
19-digit lift preserves the value and is normalized. -/
lemma STAmount.toNumber_iou_exact (s : STAmount) (mode : rounding_mode)
    (hc : s.IOUCanonical) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized :=
  ⟨⟨s.mIsNegative, s.mValue * 10 * 10 * 10, s.mOffset - 3⟩,
    STAmount.toNumber_iou_canonical s mode hc,
    STAmount.toNumber_iou_canonical_toRat s hc,
    STAmount.toNumber_iou_canonical_isNormalized s hc⟩

/-! ## Integral exactness -/

/-- The value of a canonical (offset-`0`) integral amount is the cast of its
signed drops, an integer. -/
lemma STAmount.IntegralCanonical.toRat_eq_signedDrops (s : STAmount)
    (hc : s.IntegralCanonical) :
    s.toRat = (s.signedDrops : ℚ) := by
  rw [STAmount.toRat_signed, hc.offset_zero]
  unfold STAmount.signedDrops
  rcases hn : s.mIsNegative with _ | _ <;> simp

/-- A canonical integral amount is integer-valued. -/
lemma STAmount.IntegralCanonical.den_eq_one (s : STAmount) (hc : s.IntegralCanonical) :
    s.toRat.den = 1 := by
  rw [STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]
  exact Rat.den_intCast _

/-- **`toNumber` is value-exact, normalized, and integer-valued on a canonical
integral amount.** The stored magnitude must fit `Int64` (`maxValue ≤ maxRep`,
true for `native` and `int64`), so the signed-drops view never hits
`Int64.minValue`. Also covers the integral zero. -/
lemma STAmount.toNumber_integral_exact (s : STAmount) (mode : rounding_mode)
    (hc : s.IntegralCanonical)
    (hmax : s.mNumericType.maxValue.toNat ≤ maxRep.toNat) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized ∧
      s.toRat.den = 1 := by
  have hint : s.integral = true := hc.is_integral
  -- the magnitude fits Int64
  have hbnd : s.mValue.toNat ≤ 9223372036854775807 := by
    calc s.mValue.toNat ≤ s.mNumericType.maxValue.toNat := hc.in_range
      _ ≤ maxRep.toNat := hmax
      _ = 9223372036854775807 := maxRep_val
  -- signed drops are in Int64 range
  have hmin : Int64.minValue.toInt = (-9223372036854775808 : ℤ) := by decide
  have hmax' : Int64.maxValue.toInt = (9223372036854775807 : ℤ) := by decide
  have hsd_lo : Int64.minValue.toInt ≤ s.signedDrops := by
    unfold STAmount.signedDrops; rw [hmin]; split <;> omega
  have hsd_hi : s.signedDrops ≤ Int64.maxValue.toInt := by
    unfold STAmount.signedDrops; rw [hmax']; split <;> omega
  have hsd_toInt : s.signedDrops.toInt64.toInt = s.signedDrops :=
    XRPL.Model.Protocol.AmountArith.toInt_toInt64_self hsd_lo hsd_hi
  have h_ne_min : s.signedDrops.toInt64 ≠ Int64.minValue := by
    intro h
    have heq : s.signedDrops.toInt64.toInt = Int64.minValue.toInt := by rw [h]
    rw [hsd_toInt, hmin] at heq
    revert heq
    unfold STAmount.signedDrops
    split <;> omega
  -- `s.toNumber` routes through `IntAmount.toNumber` of the signed drops
  have hroute : s.toNumber mode = IntAmount.toNumber ⟨s.signedDrops.toInt64⟩ mode := by
    unfold STAmount.toNumber STAmount.intAmount
    rw [if_pos hint, if_pos hint]
  obtain ⟨xn, hok, hval, hnorm⟩ :=
    IntAmount.toNumber_exact ⟨s.signedDrops.toInt64⟩ mode h_ne_min
  refine ⟨xn, by rw [hroute]; exact hok, ?_, hnorm,
    STAmount.IntegralCanonical.den_eq_one s hc⟩
  rw [hval]
  show (s.signedDrops.toInt64.toInt : ℚ) = s.toRat
  rw [hsd_toInt, STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]

/-! ## Combined canonical exactness -/

/-- The canonical storage shapes `toNumber` is value-exact on: the fractional
canonical form, or the integral canonical form with the stored magnitude within
`Int64`. -/
def STAmount.ExactCanonical (s : STAmount) : Prop :=
  s.IOUCanonical ∨ (s.IntegralCanonical ∧ s.mValue.toNat ≤ 2 ^ 63 - 1)

/-- `toNumber` exactness on a small canonical integral amount (the size bound on
the stored magnitude replaces the type-level `maxValue` bound). -/
lemma STAmount.toNumber_integral_small_exact (s : STAmount) (mode : rounding_mode)
    (hc : s.IntegralCanonical) (hsz : s.mValue.toNat ≤ 2 ^ 63 - 1) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized := by
  have hint : s.integral = true := hc.is_integral
  have hmin : Int64.minValue.toInt = (-9223372036854775808 : ℤ) := by decide
  have hmax' : Int64.maxValue.toInt = (9223372036854775807 : ℤ) := by decide
  have hsd_lo : Int64.minValue.toInt ≤ s.signedDrops := by
    unfold STAmount.signedDrops; rw [hmin]; split <;> omega
  have hsd_hi : s.signedDrops ≤ Int64.maxValue.toInt := by
    unfold STAmount.signedDrops; rw [hmax']; split <;> omega
  have hsd_toInt : s.signedDrops.toInt64.toInt = s.signedDrops :=
    AmountArith.toInt_toInt64_self hsd_lo hsd_hi
  have h_ne_min : s.signedDrops.toInt64 ≠ Int64.minValue := by
    intro h
    have heq : s.signedDrops.toInt64.toInt = Int64.minValue.toInt := by rw [h]
    rw [hsd_toInt, hmin] at heq
    revert heq
    unfold STAmount.signedDrops
    split <;> omega
  have hroute : s.toNumber mode = IntAmount.toNumber ⟨s.signedDrops.toInt64⟩ mode := by
    unfold STAmount.toNumber STAmount.intAmount
    rw [if_pos hint, if_pos hint]
  obtain ⟨xn, hok, hval, hnorm⟩ :=
    IntAmount.toNumber_exact ⟨s.signedDrops.toInt64⟩ mode h_ne_min
  refine ⟨xn, by rw [hroute]; exact hok, ?_, hnorm⟩
  rw [hval]
  show (s.signedDrops.toInt64.toInt : ℚ) = s.toRat
  rw [hsd_toInt, STAmount.IntegralCanonical.toRat_eq_signedDrops s hc]

/-- `toNumber` is value-exact and normalized on any `ExactCanonical` amount. -/
lemma STAmount.toNumber_exact_canonical (s : STAmount) (mode : rounding_mode)
    (hc : s.ExactCanonical) :
    ∃ sn : Number, s.toNumber mode = .ok sn ∧ sn.toRat = s.toRat ∧ sn.isNormalized := by
  rcases hc with hiou | ⟨hint, hsz⟩
  · exact STAmount.toNumber_iou_exact s mode hiou
  · exact STAmount.toNumber_integral_small_exact s mode hint hsz

end XRPL.Model.Protocol
