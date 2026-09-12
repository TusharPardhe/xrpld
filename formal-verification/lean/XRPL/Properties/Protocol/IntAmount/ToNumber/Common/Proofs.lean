import Mathlib.Tactic
import XRPL.Model.Protocol.IntAmount
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact

/-! # Proof body for the `IntAmount.toNumber` correctness headline.

`toNumber x mode = Number.from_rep x.value 0 …`, which (for `value ≠ Int64.minValue`) is
value-exact via `Number.from_rep_exact`. No rounding, since an exponent-0 integer mantissa
scales up into `largeRange` exactly. Mirrors `Number/ToRep/`. The thin headline lives in
`IntAmount.ToNumber.ToNumber`. -/

namespace XRPL.Model.Protocol

/-- **`toNumber` is value-exact** (drops `≠ Int64.minValue`): it produces a normalized
`Number` of value `toRat`. -/
theorem IntAmount.toNumber_exact_proof (x : IntAmount) (mode : rounding_mode)
    (h_ne_min : x.value ≠ Int64.minValue) :
    ∃ xn : Number, x.toNumber mode = .ok xn ∧ xn.toRat = x.toRat ∧ xn.isNormalized := by
  obtain ⟨xn, hok, hval, hnorm⟩ := Number.from_rep_exact x.value 0 mode h_ne_min
    (by have h : minExponent = -32768 := rfl; omega)
    (by have h : maxExponent = 32768 := rfl; omega)
  refine ⟨xn, hok, ?_, hnorm⟩
  rw [hval]; unfold IntAmount.toRat; norm_num

end XRPL.Model.Protocol
