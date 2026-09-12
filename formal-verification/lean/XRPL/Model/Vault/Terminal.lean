import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultBurn
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Lending.Loan.LoanAccept
import XRPL.Model.Lending.Loan.LoanDelete
import XRPL.Model.Lending.Loan.LoanManage
import XRPL.Model.Lending.Loan.LoanPay
import XRPL.Model.Lending.Loan.LoanSet

/-! # Source-faithful terminal Vault transitions

The pre-existing `Vault.deposit`, `Vault.withdraw`, and `Vault.clawback` APIs
are deliberately **raw** transition kernels. They stop before C++ commits the
updated SLE, so pricing and reduction proofs retain their exact rounded-output
contracts. The `*_terminal` APIs below model the complete C++ success path:
run that raw kernel once, then run `Vault.associateAsset` once before exposing
the post-state. A TER rejection is not a commit and is therefore returned
unchanged; an association error is an `Except` error with no final post-state.
-/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Terminal creation validates the raw fields and associates all present asset
fields, including an optional `assetsMaximum`, before the new SLE is exposed. -/
def RawVault.to_lawful_terminal (rv : RawVault) : Except Error Vault := do
  let vault ← rv.to_lawful
  vault.associateAsset

/-- Associate the successful branch of a raw deposit result. -/
def DepositResult.associateAssetTerminal (r : DepositResult) : Except Error DepositResult :=
  if r.error.isSome then
    .ok r
  else do
    let vault' ← r.vault'.associateAsset
    return { r with vault' }

/-- Complete C++-faithful deposit: raw arithmetic, then exactly one association
pass on a successful final Vault. -/
def Vault.deposit_terminal (v : Vault) (amountDeposit : STAmount) (isDonation : Bool)
    : Except Error DepositResult := do
  let result ← v.deposit amountDeposit isDonation
  result.associateAssetTerminal

/-- Associate the successful branch of a raw withdrawal result. -/
def WithdrawResult.associateAssetTerminal (r : WithdrawResult) : Except Error WithdrawResult :=
  if r.error.isSome then
    .ok r
  else do
    let vault' ← r.vault'.associateAsset
    return { r with vault' }

/-- Complete C++-faithful withdrawal: raw arithmetic, then exactly one
association pass on a successful final Vault. -/
def Vault.withdraw_terminal (v : Vault) (amount : WithdrawAmount) (waiveUnrealizedLoss : Bool)
    : Except Error WithdrawResult := do
  let result ← v.withdraw amount waiveUnrealizedLoss
  result.associateAssetTerminal

/-- Complete C++-faithful force-burn: raw share mutation, then exactly one
commit-time asset association on the successful Vault post-state. -/
def Vault.burnShares_terminal (v : Vault) (sharesDestroyed : STAmount) : Except Error Vault := do
  let vault' ← v.burnShares sharesDestroyed
  vault'.associateAsset

/-- Associate the successful branch of a raw clawback result. -/
def ClawbackResult.associateAssetTerminal (r : ClawbackResult) : Except Error ClawbackResult :=
  if r.error.isSome then
    .ok r
  else do
    let vault' ← r.vault'.associateAsset
    return { r with vault' }

/-- Complete C++-faithful clawback: raw arithmetic, then exactly one association
pass on a successful final Vault. -/
def Vault.clawback_terminal (v : Vault) (assets holderShares : STAmount)
    : Except Error ClawbackResult := do
  let result ← v.clawback assets holderShares
  result.associateAssetTerminal

end XRPL.Model.SingleAssetVault

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

/-- Lift an atomic terminal association through a lending result. Rejected
transaction results are unchanged because they do not commit any SLE. -/
def LoanResult.associateTerminal {α : Type} (associate : α → Except Error α)
    : LoanResult α → Except Error (LoanResult α)
  | .ok state => do
      let state' ← associate state
      return .ok state'
  | .rejected ter => .ok (.rejected ter)

def LendingState.associateVaultTerminal (state : LendingState) : Except Error LendingState := do
  let vault ← state.vault.associateAsset
  return { state with vault }

def BrokerVault.associateVaultTerminal (state : BrokerVault) : Except Error BrokerVault := do
  let vault ← state.vault.associateAsset
  return { state with vault }

def LoanVault.associateVaultTerminal (state : LoanVault) : Except Error LoanVault := do
  let vault ← state.vault.associateAsset
  return { state with vault }

/-- Complete source-facing forms of each modeled lending mutation that commits a
Vault SLE. Each invokes its raw endpoint once and associates only its successful
Vault post-state once. -/
def Loan.create_terminal (vaultIdentity : VaultIdentity) (loanIdentity : LoanIdentity) (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    : Except Error (LoanResult LendingState) := do
  let result ← Loan.create vaultIdentity loanIdentity vault broker principal rates fees schedule allowsOverpayment pending
  result.associateTerminal LendingState.associateVaultTerminal

def Loan.createPending_terminal (vaultIdentity : VaultIdentity) (loanIdentity : LoanIdentity) (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment : Bool)
    : Except Error (LoanResult LendingState) := do
  let result ← Loan.createPending vaultIdentity loanIdentity vault broker principal rates fees schedule allowsOverpayment
  result.associateTerminal LendingState.associateVaultTerminal

def Loan.createImmediate_terminal (vaultIdentity : VaultIdentity) (loanIdentity : LoanIdentity) (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment : Bool)
    : Except Error (LoanResult LendingState) := do
  let result ← Loan.createImmediate vaultIdentity loanIdentity vault broker principal rates fees schedule allowsOverpayment
  result.associateTerminal LendingState.associateVaultTerminal

def Loan.accept_terminal (loan : Loan) (vault : Vault) : Except Error (LoanResult LoanVault) := do
  let result ← Loan.accept loan vault
  result.associateTerminal LoanVault.associateVaultTerminal

def Loan.delete_terminal (loan : Loan) (vault : Vault) (broker : LoanBroker)
    : Except Error (LoanResult BrokerVault) := do
  let result ← Loan.delete loan vault broker
  result.associateTerminal BrokerVault.associateVaultTerminal

def Loan.regularPayment_terminal (loan : Loan) (vault : Vault) (broker : LoanBroker)
    (paymentType : LoanPaymentType) (amount : Number) (now : UInt32)
    : Except Error (LoanResult LendingState) := do
  let result ← Loan.regularPayment loan vault broker paymentType amount now
  result.associateTerminal LendingState.associateVaultTerminal

def Loan.latePayment_terminal (loan : Loan) (vault : Vault) (broker : LoanBroker)
    (amount : Number) (now : UInt32) : Except Error (LoanResult LendingState) := do
  let result ← Loan.latePayment loan vault broker amount now
  result.associateTerminal LendingState.associateVaultTerminal

def Loan.fullPayment_terminal (loan : Loan) (vault : Vault) (broker : LoanBroker)
    (amount : Number) (now : UInt32) : Except Error (LoanResult LendingState) := do
  let result ← Loan.fullPayment loan vault broker amount now
  result.associateTerminal LendingState.associateVaultTerminal

def Loan.manageImpair_terminal (loan : Loan) (vault : Vault) : Except Error (LoanResult Vault) := do
  let result ← Loan.manageImpair loan vault
  result.associateTerminal Vault.associateAsset

def Loan.manageUnimpair_terminal (loan : Loan) (vault : Vault) : Except Error (LoanResult Vault) := do
  let result ← Loan.manageUnimpair loan vault
  result.associateTerminal Vault.associateAsset

def Loan.manageDefault_terminal (loan : Loan) (vault : Vault) (broker : LoanBroker) (impaired : Bool)
    : Except Error (LoanResult BrokerVault) := do
  let result ← Loan.manageDefault loan vault broker impaired
  result.associateTerminal BrokerVault.associateVaultTerminal

end XRPL.Model.Lending
