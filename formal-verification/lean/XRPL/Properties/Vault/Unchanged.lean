import XRPL.Properties.Vault.Common.Unchanged

/-! # A rejected operation changes nothing and reports nothing

When an operation returns a `TER` in its result, the vault is the starting
vault and both amount fields are zero: nothing moved and the record says so.
A thrown error needs no theorem because the model returns no result at all. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

theorem Vault.deposit_error_unchanged (v : Vault) (amount : STAmount) (isDonation : Bool)
    (r : DepositResult) (hok : v.deposit amount isDonation = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.amountDeposit' = STAmount.zero v.numericType ∧
    r.sharesIssued = STAmount.zero .int64 :=
  Vault.deposit_error_rejected_proof v amount isDonation r hok herr

theorem Vault.withdraw_error_unchanged (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.assets' = STAmount.zero v.numericType ∧
    r.sharesBurned = STAmount.zero .int64 :=
  Vault.withdraw_error_rejected_proof v amount waiveUnrealizedLoss r hok herr

theorem Vault.clawback_error_unchanged (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : v.clawback assets holderShares = .ok r)
    (herr : r.error.isSome = true) :
    r.vault' = v ∧ r.assetsRecovered = STAmount.zero v.numericType ∧
    r.sharesDestroyed = STAmount.zero .int64 :=
  Vault.clawback_error_rejected_proof v assets holderShares r hok herr

end XRPL.Model.SingleAssetVault
