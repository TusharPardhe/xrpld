import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.Terminal

open XRPL.Model.Protocol (Number NumericType STAmount Error)
open XRPL.Model.SingleAssetVault

-- Complete C++ transaction entry point: raw clawback followed by exactly one
-- commit-time association pass on a successful post-state.
@[export lean_vault_clawback]
def lean_vault_clawback (v : Vault) (assets holderShares : STAmount) : Except Error ClawbackResult :=
  v.clawback_terminal assets holderShares

@[export lean_clawback_result_assets]
def lean_clawback_result_assets (r : ClawbackResult) : STAmount := r.assetsRecovered
@[export lean_clawback_result_shares]
def lean_clawback_result_shares (r : ClawbackResult) : STAmount := r.sharesDestroyed
@[export lean_clawback_result_vault]
def lean_clawback_result_vault (r : ClawbackResult) : Vault := r.vault'
@[export lean_clawback_result_error]
def lean_clawback_result_error (r : ClawbackResult) : Option Int32 := r.error.map (·.code)
