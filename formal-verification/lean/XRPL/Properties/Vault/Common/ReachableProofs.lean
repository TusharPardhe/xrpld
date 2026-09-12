import XRPL.Properties.Vault.Common.Preservation
import XRPL.Properties.Vault.Common.ReachableDefs

/-! # Reachability induction proofs

Proof bodies for the `Vault.Reachable` corollaries in `Reachable.lean`. Each is an
induction on `Vault.Reachable` (from `ReachableDefs.lean`, over `Vault`): one
base case `create` and one step case per operation, discharged by the field
preservation theorems in `Preservation.lean`. Reachable states are lawful by
construction (the ops return `Vault`), so no separate lawfulness proof is
needed: read `v.wf`/`v.exact` directly. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- `Vault.create_lawful` is a tactic-mode definition; reducing its `toRawVault` in the
-- `create` base case needs a deeper reduction budget.
set_option maxRecDepth 4000

/-- No operation changes `lossUnrealized`. -/
theorem Vault.Reachable.lossUnrealized_zero_proof (v : Vault) (hr : Vault.Reachable v) :
    v.toExact.lossUnrealized = 0 := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    simp only [Vault.create_lawful_toRawVault, RawVault.toExact, Number.toRat_zero]
  | deposit lw amount isDonation r hrv hdep _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [Vault.deposit_preserves_unrealized lw amount isDonation r hdep]; exact ih
  | withdraw lw amount waive r hrv hwd _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [Vault.withdraw_preserves_unrealized lw amount waive r hwd]; exact ih
  | clawback lw assets holderShares r hrv hcb _ _ _ _ _ _ ih =>
    show r.vault'.lossUnrealized.toRat = 0
    rw [Vault.clawback_preserves_unrealized lw assets holderShares r hcb]; exact ih
  | burnShares lw sharesDestroyed sharesTotalAmount lw' hrv hcan hcanon hnn hle hfit hburn ih =>
    show lw'.lossUnrealized.toRat = 0
    rw [Vault.burnShares_preserves_unrealized lw sharesDestroyed lw' hburn]; exact ih

/-- Every operation writes both asset fields with the identical update, so
record-level asset parity holds on all reachable states. -/
theorem Vault.Reachable.asset_parity_proof (v : Vault) (hr : Vault.Reachable v) :
    v.assetsAvailable = v.assetsTotal := by
  induction hr with
  | create nt scale am hn hp hi hl =>
    simp only [Vault.create_lawful_toRawVault]
  | deposit lw amount isDonation r hrv hdep _ _ _ ih =>
    exact Vault.deposit_asset_parity lw amount isDonation r ih hdep
  | withdraw lw amount waive r hrv hwd _ _ _ _ _ ih =>
    exact Vault.withdraw_asset_parity lw amount waive r ih hwd
  | clawback lw assets holderShares r hrv hcb _ _ _ _ _ _ ih =>
    exact Vault.clawback_asset_parity lw assets holderShares r ih hcb
  | burnShares lw sharesDestroyed sharesTotalAmount lw' hrv hcan hcanon hnn hle hfit hburn ih =>
    exact Vault.burnShares_asset_parity lw sharesDestroyed lw' ih hburn

end XRPL.Model.SingleAssetVault
