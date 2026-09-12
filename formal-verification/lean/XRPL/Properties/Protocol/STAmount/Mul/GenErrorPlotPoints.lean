import XRPL.Model.Protocol.STAmount

open XRPL.Model.Protocol

/-- εMulIOUToNearest, exactly as in RoundsWithin.lean. -/
def epsTN : Rat :=
  5 / (2 ^ 63 + 7 : Rat) + (1 / 2) * (1 / (10 : Rat) ^ 15)
    + 5 / (2 ^ 63 + 7 : Rat) * ((1 / 2) * (1 / (10 : Rat) ^ 15))

def iouAsset : Asset := .issue noIssue

/-- Evaluate v1 = v2 = ⟨m, e, neg⟩ through the real model; emit
    `truthnum,truthden,errnum,errden,envnum,envden` (exact rationals).
    Skips overflow (`.error`) and underflow (`result = 0`): both are outside the
    ≤1-ULP theorem, whose hypothesis is `result.mValue ≠ 0`. -/
def emit (m : UInt64) (e : Int) : IO Unit := do
  let v1 : STAmount := ⟨.issue noIssue, m, e, false⟩
  match STAmount.multiply v1 v1 iouAsset .to_nearest with
  | .error _ => pure ()
  | .ok result =>
    if result.mValue == 0 then pure ()          -- underflowed to zero: skip
    else
      let v1r   : Rat := v1.toRat
      let truth : Rat := v1r * v1r
      let err   : Rat := |result.toRat - truth|
      let env   : Rat := truth * epsTN
      IO.println s!"{truth.num},{truth.den},{err.num},{err.den},{env.num},{env.den}"

/-- Single continuous sweep of the exponent field `eLo .. eHi` (inclusive) with
    `perExp` mantissa samples per exponent. Each exponent is one decade of `|v1|`,
    so this spans the whole positive value range in log scale, from the tiniest
    representable square up to the largest, with no gaps between decades.

    Mantissas are drawn from the full-precision 16-digit band `[10^15, 10^16)` by a
    single *global* low-discrepancy counter `k`: `m = 10^15 + (k·P mod 9·10^15)` with
    `P` coprime to `9·10^15`. Two things matter here:
    * `P` coprime to the band width spreads mantissas evenly and, being coprime to
      2/3/5, keeps every mantissa full-precision. (A plain arithmetic step from 10^15
      lands on multiples of a power of ten, whose squares are representable exactly,
      giving a spurious zero rounding error — a misleading sub-pattern.)
    * `k` is *not* reset per exponent. If it were, every decade would reuse the same
      mantissa grid and the scatter would show one repeating decade-pattern aliased
      across the whole range. Advancing `k` continuously decorrelates the sampling
      grid from the decade boundaries. -/
def sweep (eLo eHi : Int) (perExp : Nat) : IO Unit := do
  let base : Nat := 1000000000000000        -- 10^15
  let span : Nat := 9000000000000000        -- 9·10^15  (band width)
  let p    : Nat := 7477777777777783        -- coprime to 9·10^15 (not div. by 2, 3, 5)
  let mut k : Nat := 0
  let mut e : Int := eLo
  while e ≤ eHi do
    for _ in [0:perExp] do
      let m : UInt64 := (base + k * p % span).toUInt64
      emit m e
      k := k + 1
    e := e + 1

def main : IO Unit := do
  -- One log-scale sweep over the entire range of exponent fields that yield a
  -- representable, non-underflowing square. `emit` silently skips the ends where the
  -- square overflows (large e) or underflows to zero (small e), so a generous span
  -- covers the whole positive value range without hand-tuned brackets.
  sweep (-58) 35 800
