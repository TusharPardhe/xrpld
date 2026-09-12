import XRPL.Model.Vault.Vault

/-! # Single-asset vault state validity (exact-rational view) -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- The vault state in exact arithmetic -/
structure RawVault.Exact where
  assetsTotal : ℚ
  assetsAvailable : ℚ
  assetsMaximum : Option ℚ
  sharesTotal : ℕ
  lossUnrealized : ℚ

/-- The exact value of a vault state. Total: `sharesTotal` falls back to `0`-like
junk when the stored `Number` is not a nonnegative integer; `RawVault.WF` rules that
out. -/
def RawVault.toExact (rv : RawVault) : RawVault.Exact where
  assetsTotal := rv.assetsTotal.toRat
  assetsAvailable := rv.assetsAvailable.toRat
  assetsMaximum := rv.assetsMaximum.map Number.toRat
  sharesTotal := rv.sharesTotal.toRat.num.toNat
  lossUnrealized := rv.lossUnrealized.toRat

/-- `toExact`'s shares projection is faithful on well-formed records: casting the
`ℕ` value back to `ℚ` recovers the stored value. -/
theorem RawVault.WF.toExact_sharesTotal (rv : RawVault) (h : rv.WF) :
    ((rv.toExact.sharesTotal : ℕ) : ℚ) = rv.sharesTotal.toRat := by
  show ((rv.sharesTotal.toRat.num.toNat : ℕ) : ℚ) = rv.sharesTotal.toRat
  set q := rv.sharesTotal.toRat with hq
  have hden : q.den = 1 := h.sharesTotal_int
  have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr h.sharesTotal_nonneg
  have hcast : (q.num : ℚ) = q := by
    have hnd := Rat.num_div_den q
    rw [hden] at hnd; simpa using hnd
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum_nn, hcast]

/-- The vault invariant (XLS-0065 §4.5) in exact rationals. Equivalent
to the operator `RawVault.Valid` on a well-formed representation
(`RawVault.valid_iff_exact`). -/
structure RawVault.Exact.Valid (s : RawVault.Exact) : Prop where
  assetsTotal_nonneg : 0 ≤ s.assetsTotal
  assetsAvailable_nonneg : 0 ≤ s.assetsAvailable
  assetsAvailable_le : s.assetsAvailable ≤ s.assetsTotal
  assetsMaximum_pos : ∀ m ∈ s.assetsMaximum, 0 < m
  empty_shares : s.sharesTotal = 0 → s.assetsTotal = 0 ∧ s.assetsAvailable = 0
  cap : ∀ m ∈ s.assetsMaximum, s.assetsTotal ≤ m
  lossUnrealized_nonneg : 0 ≤ s.lossUnrealized
  lossUnrealized_le : s.lossUnrealized ≤ s.assetsTotal - s.assetsAvailable
  withdraw_nav_nonneg : 0 ≤ s.assetsTotal - s.lossUnrealized

end XRPL.Model.SingleAssetVault
