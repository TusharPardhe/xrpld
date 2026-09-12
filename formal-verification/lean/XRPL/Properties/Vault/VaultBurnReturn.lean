import XRPL.Model.Vault.VaultBurn
import XRPL.Properties.Vault.Common.BurnExits
import XRPL.Properties.Vault.Common.Preservation

/-! # `Vault.burnShares` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.canBurnShares` -/

/-- `tecNO_PERMISSION` is the only rejection `canBurnShares` can return. -/
theorem Vault.canBurnShares_rejected_code (ter : TER)
    (hok : v.canBurnShares = .ok (.error ter)) :
    ter = .tecNO_PERMISSION :=
  Vault.canBurnShares_rejected_code_proof v ter hok

/-- Force-burning shares is allowed only when shares are outstanding while both
asset totals are zero. When `sharesTotal` is zero, or `assetsTotal` or
`assetsAvailable` is nonzero: `.error .tecNO_PERMISSION`. -/
theorem Vault.canBurnShares_no_permission
    (hperm : v.sharesTotal.mantissa_ = 0 ∨
      v.assetsTotal.mantissa_ ≠ 0 ∨ v.assetsAvailable.mantissa_ ≠ 0) :
    v.canBurnShares = .ok (.error .tecNO_PERMISSION) :=
  Vault.canBurnShares_no_permission_proof v hperm

/-- The vault has outstanding shares and both `assetsTotal` and
`assetsAvailable` are zero: the result is the whole `sharesTotal` converted
to an `int64` amount. -/
theorem Vault.canBurnShares_ok (sharesTotalAmount : STAmount)
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (hat : v.assetsTotal.mantissa_ = 0)
    (hav : v.assetsAvailable.mantissa_ = 0)
    (hshares : STAmount.ofNumber .int64 v.sharesTotal .to_nearest = .ok sharesTotalAmount) :
    v.canBurnShares = .ok (.assets sharesTotalAmount) :=
  Vault.canBurnShares_ok_proof v sharesTotalAmount hsh hat hav hshares

/-! ## `Vault.burnShares` -/

/-- `burnShares` stores the rounded difference `sharesTotal - sharesDestroyed`
and changes no other field. The post-state is a `Vault` (`v'`): the in-op
`to_lawful` re-check succeeds via `burnShares_poststate_lawful`. -/
theorem Vault.burnShares_ok (sharesDestroyed sharesTotalAmount : STAmount)
    (sharesDestroyedNumber st' : Number)
    (hcan : v.canBurnShares = .ok (.assets sharesTotalAmount))
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sharesDestroyedNumber)
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st') :
    ∃ v' : Vault, v.burnShares sharesDestroyed = .ok v' ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st' } := by
  obtain ⟨v', htl, hlv'eq⟩ := Vault.burnShares_poststate_lawful v sharesDestroyed sharesTotalAmount
    sharesDestroyedNumber st' hcan hcanon hnn hle hfit hnum hst
  refine ⟨v', ?_, hlv'eq⟩
  unfold Vault.burnShares
  simp only []
  rw [hnum, ok_bind, hst, ok_bind, htl]

end XRPL.Model.SingleAssetVault
