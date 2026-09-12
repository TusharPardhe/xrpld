import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.Terminal

open XRPL.Model.Protocol (Number NumericType STAmount Error)
open XRPL.Model.SingleAssetVault

@[export lean_vault_burn_shares_raw]
def lean_vault_burn_shares_raw (v : Vault) (sharesDestroyed : STAmount) : Except Error Vault :=
  v.burnShares sharesDestroyed

/-- Complete C++ transaction boundary: raw burn followed by the one terminal
asset-association pass before exposing the updated Vault. -/
@[export lean_vault_burn_shares]
def lean_vault_burn_shares (v : Vault) (sharesDestroyed : STAmount) : Except Error Vault :=
  v.burnShares_terminal sharesDestroyed

@[export lean_can_burn_shares]
def lean_can_burn_shares (v : Vault) : Except Error CanBurnSharesResult :=
  v.canBurnShares

@[export lean_can_burn_result_assets]
def lean_can_burn_result_assets (r : CanBurnSharesResult) : Option STAmount :=
  match r with
  | .assets s => some s
  | .error _ => none
@[export lean_can_burn_result_code]
def lean_can_burn_result_code (r : CanBurnSharesResult) : Option Int32 :=
  match r with
  | .error t => some t.code
  | .assets _ => none
