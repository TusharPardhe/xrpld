import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def LoanBroker.canCoverWithdraw {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    (amount : STAmount) : Except Error TER := do
  let nt := AssetPool.numericType pool
  let ter ← canApplyToBrokerCover nt lb.coverAvailable amount
  if ter.operator_bool then
    return ter

  let rounded ← match (← lb.roundedCoverAmount nt amount) with
    | .rejected ter => return ter
    | .rounded amount => .pure amount

  let poolExponent ← AssetPool.exponent pool
  let minimumCover ← minimumBrokerCover nt lb.debtTotal lb.coverRateMinimum poolExponent
  let amountNumber ← rounded.toNumber .to_nearest
  if lb.coverAvailable.operator_lt amountNumber then
    return .tecINSUFFICIENT_FUNDS
  let coverAvailable' ← lb.coverAvailable.operator_sub amountNumber .to_nearest
  if coverAvailable'.operator_lt minimumCover then
    return .tecINSUFFICIENT_FUNDS

  return .tesSUCCESS


def LoanBroker.coverWithdraw (lb : LoanBroker) (numericType : NumericType) (amount : STAmount)
    : Except Error LoanBrokerCoverResult := do
  let amount ← match (← lb.roundedCoverAmount numericType amount) with
    | .rejected _ => return { status := .tecINTERNAL, loanBroker' := lb, amount' := STAmount.zero numericType }
    | .rounded amount => .pure amount
  lb.applyCoverTransaction .debit amount

end XRPL.Model.Lending
