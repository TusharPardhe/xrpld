import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.AssetPool
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def LoanBroker.canDelete {α : Type} [AssetPool α] (lb : LoanBroker) (pool : α)
    : Except Error TER := do
  if lb.loanCount != 0 then
    return .tecHAS_OBLIGATIONS

  if lb.debtTotal.signum != 0 then
    -- defensive check: in case debt is non-zero but rounds to zero
    let poolExponent ← AssetPool.exponent pool
    let rounded ← STAmount.roundToNumericType (AssetPool.numericType pool) lb.debtTotal
      .towards_zero (.some poolExponent)
    if rounded.signum != 0 then
      return .tecHAS_OBLIGATIONS

  return .tesSUCCESS

end XRPL.Model.Lending
