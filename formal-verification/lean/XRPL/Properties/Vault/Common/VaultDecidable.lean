import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback

/-! # Shared `DecidableEq` derivations for the vault witness leaves

The `native_decide` sharpness and round-trip witnesses (`DilutionWitness`,
`RoundtripProofs`) compare concrete vault states and operation results, so they
need `DecidableEq` for `RawVault`, `DepositResult`, `WithdrawResult`,
`ClawbackResult`, and `Except`. Deriving those instances in a single shared
module emits each auto-generated `decEq` aux declaration exactly once, so both
witness files can co-load under the `Properties` aggregator. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

deriving instance DecidableEq for Except
deriving instance DecidableEq for RawVault

-- `Vault` carries proof fields (`wf`, `valid`), so it cannot auto-derive
-- `DecidableEq`. Two lawful vaults are equal exactly when their raw records are:
-- the proofs are irrelevant.
instance : DecidableEq Vault := fun a b =>
  decidable_of_iff (a.toRawVault = b.toRawVault)
    ⟨fun h => by obtain ⟨av, _, _⟩ := a; obtain ⟨bv, _, _⟩ := b; cases h; rfl,
     fun h => by rw [h]⟩

deriving instance DecidableEq for DepositResult
deriving instance DecidableEq for WithdrawResult
deriving instance DecidableEq for ClawbackResult

end XRPL.Model.SingleAssetVault
