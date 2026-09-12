import XRPL.Properties.Protocol.IntAmount.ToNumber.Common.Proofs

/-! # Correctness of `IntAmount.toNumber` -/

namespace XRPL.Model.Protocol

/-- **`toNumber` is value-exact** unless drops is `Int64.minValue`. `from_rep` converts every
`Int64` exactly except `minValue`, whose magnitude `2^63` is one past the representable limit
`maxRep = 2^63 - 1`. `minValue` is not a valid IntAmount, so safe to hypothesise it will not happen. -/
theorem IntAmount.toNumber_exact (x : IntAmount) (mode : rounding_mode)
    (h_ne_min : x.value ≠ Int64.minValue) :
    ∃ xn : Number, x.toNumber mode = .ok xn ∧ xn.toRat = x.toRat ∧ xn.isNormalized :=
  IntAmount.toNumber_exact_proof x mode h_ne_min

end XRPL.Model.Protocol
