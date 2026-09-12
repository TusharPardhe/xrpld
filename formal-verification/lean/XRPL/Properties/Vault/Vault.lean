import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.Common.State

/-! # `Vault.isInsolvent`

On a lawful state, the insolvency query characterizes exactly one situation:
shares are outstanding while the vault holds no assets. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- On a lawful state, `isInsolvent` holds exactly when the vault has no assets
but shares outstanding. -/
theorem Vault.isInsolvent_iff (v : Vault) :
    v.isInsolvent = true ↔ v.toExact.assetsTotal = 0 ∧ 0 < v.toExact.sharesTotal :=
  Vault.isInsolvent_iff_proof v

end XRPL.Model.SingleAssetVault
