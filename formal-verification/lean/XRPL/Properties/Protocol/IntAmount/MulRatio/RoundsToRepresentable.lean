import XRPL.Properties.Protocol.IntAmount.MulRatio.Common.Ceil.Proofs
import XRPL.Properties.Protocol.IntAmount.MulRatio.Common.Floor.Proofs

/-! # Correctness of `IntAmount.mulRatio` -/

namespace XRPL.Model.Protocol

/-- **`mulRatio` rounds correctly.** A successful result is the correctly-rounded quotient of
`amt * num / den` (floor for `roundUp = false`, ceil for `roundUp = true`); a result below
`Int64.minValue` is rejected as overflow. -/
theorem IntAmount.mulRatio_rounds (amt : IntAmount) (num den : UInt32) (roundUp : Bool)
    (result : IntAmount)
    (hok : IntAmount.mulRatio amt num den roundUp = .ok result) :
    result.value = Int64.minValue ∨
      (if roundUp
       then amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) ≤ result.toRat ∧
            result.toRat - 1 < amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ)
       else result.toRat ≤ amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) ∧
            amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) < result.toRat + 1) :=
  IntAmount.mulRatio_rounds_proof amt num den roundUp result hok

/-- **`mulRatio` floors when `roundUp = false`.** -/
theorem IntAmount.mulRatio_rounds_floor (amt : IntAmount) (num den : UInt32)
    (result : IntAmount)
    (hok : IntAmount.mulRatio amt num den false = .ok result) :
    result.value = Int64.minValue ∨
      (result.toRat ≤ amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) ∧
       amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) < result.toRat + 1) :=
  IntAmount.mulRatio_rounds_floor_proof amt num den result hok

/-- **`mulRatio` ceils when `roundUp = true`.** -/
theorem IntAmount.mulRatio_rounds_ceil (amt : IntAmount) (num den : UInt32)
    (result : IntAmount)
    (hok : IntAmount.mulRatio amt num den true = .ok result) :
    result.value = Int64.minValue ∨
      (amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ) ≤ result.toRat ∧
       result.toRat - 1 < amt.toRat * (num.toNat : ℚ) / (den.toNat : ℚ)) :=
  IntAmount.mulRatio_rounds_ceil_proof amt num den result hok

end XRPL.Model.Protocol
