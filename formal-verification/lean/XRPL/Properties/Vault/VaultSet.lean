import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Model.Vault.VaultSet

/-! # `RawVault.canVaultSet` exits -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.canVaultSet` -/

/-- A nonzero new maximum below the current assets total: `tecLIMIT_EXCEEDED`. -/
theorem Vault.canVaultSet_below_total (assetsMaximum : Number)
    (hne : assetsMaximum.operator_ne Number.zero = true) -- the new maximum is nonzero
    (hlt : assetsMaximum.operator_lt v.assetsTotal = true) : -- and compares below the assets total
    v.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED :=
  Vault.canVaultSet_below_total_proof v assetsMaximum hne hlt

/-- A new maximum that compares equal to zero, or does not compare below the
current assets total, passes. Zero requests removing the cap. -/
theorem Vault.canVaultSet_success (assetsMaximum : Number)
    -- the failure guard is off: the maximum is zero or not below the assets total
    (hok : (assetsMaximum.operator_ne Number.zero &&
        assetsMaximum.operator_lt v.assetsTotal) = false) :
    v.canVaultSet assetsMaximum = .tesSUCCESS :=
  Vault.canVaultSet_success_proof v assetsMaximum hok

/-- Every outcome of the check: `tecLIMIT_EXCEEDED` is the only rejection
`canVaultSet` can return. -/
theorem Vault.canVaultSet_error_codes (assetsMaximum : Number) :
    v.canVaultSet assetsMaximum = .tesSUCCESS ∨
    v.canVaultSet assetsMaximum = .tecLIMIT_EXCEEDED :=
  Vault.canVaultSet_error_codes_proof v assetsMaximum

/-- On a lawful vault, a normalized new maximum passes exactly when it is zero
or at least the exact assets total. -/
theorem Vault.lawful_canVaultSet_iff (v : Vault)
    (assetsMaximum : Number)
    (hnorm : assetsMaximum.isNormalized) : -- the new maximum is normalized
    v.canVaultSet assetsMaximum = .tesSUCCESS ↔
      assetsMaximum.toRat = 0 ∨ v.toExact.assetsTotal ≤ assetsMaximum.toRat :=
  Vault.lawful_canVaultSet_iff_proof v assetsMaximum hnorm

end XRPL.Model.SingleAssetVault
