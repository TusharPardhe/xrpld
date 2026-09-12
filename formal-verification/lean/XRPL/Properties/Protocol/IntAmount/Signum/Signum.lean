import XRPL.Properties.Protocol.IntAmount.Signum.Common.Proofs

/-! # Correctness of `IntAmount.signum`

`signum` returns the sign of the value (`1` / `-1` / `0`). -/

namespace XRPL.Model.Protocol

/-- **`signum` returns the sign of `toRat`.** -/
theorem IntAmount.signum_eq (x : IntAmount) :
    x.signum = if 0 < x.toRat then 1 else if x.toRat < 0 then -1 else 0 :=
  IntAmount.signum_eq_proof x

/-- **`signum = 1 ↔ value is positive`.** -/
theorem IntAmount.signum_eq_one_iff (x : IntAmount) : x.signum = 1 ↔ 0 < x.toRat :=
  IntAmount.signum_eq_one_iff_proof x

/-- **`signum = -1 ↔ value is negative`.** -/
theorem IntAmount.signum_eq_neg_one_iff (x : IntAmount) : x.signum = -1 ↔ x.toRat < 0 :=
  IntAmount.signum_eq_neg_one_iff_proof x

/-- **`signum = 0 ↔ value is zero`.** -/
theorem IntAmount.signum_eq_zero_iff (x : IntAmount) : x.signum = 0 ↔ x.toRat = 0 :=
  IntAmount.signum_eq_zero_iff_proof x

end XRPL.Model.Protocol
