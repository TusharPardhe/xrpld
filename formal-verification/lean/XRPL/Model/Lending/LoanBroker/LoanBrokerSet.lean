import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def LoanBroker.canCreate (debtMaximum : Option Number) (numericType : NumericType) : Except Error TER := do
  let some dm := debtMaximum | return .tesSUCCESS
  if !(← STAmount.equalAfterNumberConvert numericType dm) then
    return .tecPRECISION_LOSS
  return .tesSUCCESS

def LoanBroker.canUpdate (lb : LoanBroker) (debtMaximum : Option Number) (numericType : NumericType) : Except Error TER := do
  let some dm := debtMaximum | return .tesSUCCESS
  if dm.signum != 0 && dm.operator_lt lb.debtTotal then
    return .tecLIMIT_EXCEEDED
  if !(← STAmount.equalAfterNumberConvert numericType dm) then
    return .tecPRECISION_LOSS
  return .tesSUCCESS

structure LoanBrokerSetCreate where
  debtMaximum : Option Number
  managementFeeRate : Option TenthBips16
  coverRateMinimum : Option TenthBips32
  coverRateLiquidation : Option TenthBips32

structure LoanBrokerSetResult where
  loanBroker : LoanBroker
  ter : TER

def LoanBroker.create (identity : BrokerIdentity) (tx : LoanBrokerSetCreate) : LoanBroker :=
    { identity
    , managementFeeRate    := tx.managementFeeRate.getD 0
    , coverRateMinimum     := tx.coverRateMinimum.getD 0
    , coverRateLiquidation := tx.coverRateLiquidation.getD 0
    , debtMaximum          := tx.debtMaximum.getD Number.zero
    , debtTotal            := Number.zero
    , coverAvailable       := Number.zero
    , loanCount            := 0 }

def LoanBroker.update (lb : LoanBroker) (debtMaximum : Option Number) : LoanBroker :=
    { lb with debtMaximum := debtMaximum.getD lb.debtMaximum }

end XRPL.Model.Lending
