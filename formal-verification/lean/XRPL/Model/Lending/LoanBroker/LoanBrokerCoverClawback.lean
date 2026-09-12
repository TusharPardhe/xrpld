import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Result
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

def LoanBroker.roundedCoverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : Except Error RoundingResult := do
  let nt := AssetPool.numericType pool
  let poolExponent ← AssetPool.exponent pool
  let minRequiredCover ← minimumBrokerCover nt lb.debtTotal lb.coverRateMinimum poolExponent
  let maxClawAmount ← lb.coverAvailable.operator_sub minRequiredCover .downward
  if maxClawAmount.signum ≤ 0 then
    return .rejected .tecINSUFFICIENT_FUNDS

  let claw ← match amount with
    | none => .pure maxClawAmount
    | some a =>
      if a.isZero then .pure maxClawAmount
      else do
        let magnitude ← a.toNumber .to_nearest
        .pure (if magnitude.operator_gt maxClawAmount then maxClawAmount else magnitude)

  return .rounded (← STAmount.ofNumber nt claw .to_nearest)


def LoanBroker.canCoverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : Except Error TER := do
  match ← lb.roundedCoverClawback pool amount with
  | .rejected ter => return ter
  | .rounded clawAmount =>
    canApplyToBrokerCover (AssetPool.numericType pool) lb.coverAvailable clawAmount


def LoanBroker.coverClawback {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : Option STAmount) : Except Error LoanBrokerCoverResult := do
  let nt := AssetPool.numericType pool
  let amount ← match (← lb.roundedCoverClawback pool amount) with
    | .rejected _ => return { status := .tecINTERNAL, loanBroker' := lb, amount' := STAmount.zero nt }
    | .rounded amount => .pure amount
  lb.applyCoverTransaction .debit amount

end XRPL.Model.Lending
