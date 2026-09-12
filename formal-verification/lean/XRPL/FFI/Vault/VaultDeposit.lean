import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Vault.Terminal

open XRPL.Model.Protocol (Number NumericType STAmount Error)
open XRPL.Model.Result (RoundingResult)
open XRPL.Model.SingleAssetVault

@[export lean_rounded_deposit_amount]
def lean_rounded_deposit_amount (v : Vault) (amountDeposit : STAmount) : Except Error RoundingResult :=
  v.roundedDepositAmount amountDeposit

@[export lean_rounded_deposit_result_amount]
def lean_rounded_deposit_result_amount (r : RoundingResult) : Option STAmount :=
  match r with
  | .rounded s => some s
  | .rejected _ => none

@[export lean_rounded_deposit_result_code]
def lean_rounded_deposit_result_code (r : RoundingResult) : Option Int32 :=
  match r with
  | .rejected t => some t.code
  | .rounded _ => none

@[export lean_vault_is_insolvent]
def lean_vault_is_insolvent (v : Vault) : Bool :=
  v.isInsolvent

-- Complete C++ transaction entry point: raw deposit followed by exactly one
-- commit-time association pass on a successful post-state.
@[export lean_vault_deposit]
def lean_vault_deposit (v : Vault) (amountDeposit : STAmount) (isDonation : UInt8) : Except Error DepositResult :=
  v.deposit_terminal amountDeposit (isDonation != 0)

@[export lean_deposit_result_amount]
def lean_deposit_result_amount (r : DepositResult) : STAmount := r.amountDeposit'
@[export lean_deposit_result_shares]
def lean_deposit_result_shares (r : DepositResult) : STAmount := r.sharesIssued
@[export lean_deposit_result_vault]
def lean_deposit_result_vault (r : DepositResult) : Vault := r.vault'
@[export lean_deposit_result_error]
def lean_deposit_result_error (r : DepositResult) : Option Int32 :=
  r.error.map (·.code)
