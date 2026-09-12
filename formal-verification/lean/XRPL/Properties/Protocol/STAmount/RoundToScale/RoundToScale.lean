import XRPL.Properties.Protocol.STAmount.RoundToScale.Common.Proofs

/-! # `STAmount.roundToExponent` is correctly rounded onto the scale grid

`roundToExponent` quantizes an IOU `STAmount` onto the `10^s · ℤ` grid faithfully (in every
mode). Built from the `roundToExponent_sum_spec` workhorse in `RoundToScale.Common.Sum`. -/

namespace XRPL.Model.Protocol

/-- **`STAmount.roundToExponent` rounds `value.toRat` onto the `10^s` grid faithfully.**
Holds on the full IOU scale range `[-96, 80]` given a nonzero result: below `-81`
the 16-digit clamp only ever flushes a tiny grid coefficient to zero, so a nonzero
result is always the exact grid point. -/
theorem STAmount.roundToExponent_rounded (value result : STAmount) (s : ℤ)
    (mode : rounding_mode)
    (hc : value.IOUCanonical)
    (h_s : (-96 : ℤ) ≤ s) (h_s_hi : s ≤ 80)
    (hnz : result.mValue ≠ 0)
    (hok : STAmount.roundToExponent value s mode = .ok result) :
    RoundsToRepresentableAt result value.toRat s mode :=
  STAmount.roundToExponent_rounded_proof value result s mode hc h_s h_s_hi (Or.inl hnz) hok

/-- At a canonical IOU grid scale `[-81, 80]`, a successful downward round is
exactly the mathematical floor even when the result flushes to the zero
sentinel. The lower scale bound makes every positive grid point representable,
so the core proof's only underflow escape is unavailable. -/
theorem STAmount.roundToExponent_downward_rounded_at_canonical_scale
    (value result : STAmount) (s : ℤ)
    (hc : value.IOUCanonical) (hs_lo : (-81 : ℤ) ≤ s) (hs_hi : s ≤ 80)
    (hok : STAmount.roundToExponent value s .downward = .ok result) :
    result.toRat = (⌊value.toRat / 10 ^ s⌋ : ℚ) * 10 ^ s :=
  STAmount.roundToExponent_rounded_proof value result s .downward hc (by omega) hs_hi
    (Or.inr hs_lo) hok

end XRPL.Model.Protocol
