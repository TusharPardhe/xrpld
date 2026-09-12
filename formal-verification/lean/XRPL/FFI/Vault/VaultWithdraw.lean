import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.Terminal

open XRPL.Model.Protocol (Number NumericType STAmount Error)
open XRPL.Model.SingleAssetVault

@[export lean_shares_to_assets_withdraw]
def lean_shares_to_assets_withdraw (v : Vault) (shares : STAmount) (waiveUnrealizedLoss : UInt8) : Except Error STAmount :=
  v.sharesToAssetsWithdraw shares (waiveUnrealizedLoss != 0)

-- build a WithdrawAmount from C++ (byShares != 0 selects vault shares over vault assets).
@[export lean_mk_withdraw_amount]
def lean_mk_withdraw_amount (amount : STAmount) (byShares : UInt8) : WithdrawAmount :=
  if byShares != 0 then .vaultShares amount else .vaultAssets amount

-- Complete C++ transaction entry point: raw withdrawal followed by exactly one
-- commit-time association pass on a successful post-state.
@[export lean_vault_withdraw]
def lean_vault_withdraw (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : UInt8) : Except Error WithdrawResult :=
  v.withdraw_terminal amount (waiveUnrealizedLoss != 0)

@[export lean_withdraw_result_assets]
def lean_withdraw_result_assets (r : WithdrawResult) : STAmount := r.assets'
@[export lean_withdraw_result_shares]
def lean_withdraw_result_shares (r : WithdrawResult) : STAmount := r.sharesBurned
@[export lean_withdraw_result_vault]
def lean_withdraw_result_vault (r : WithdrawResult) : Vault := r.vault'
@[export lean_withdraw_result_error]
def lean_withdraw_result_error (r : WithdrawResult) : Option Int32 := r.error.map (·.code)
