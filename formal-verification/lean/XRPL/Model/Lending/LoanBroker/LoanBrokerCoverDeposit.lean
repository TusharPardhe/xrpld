import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Lending.LoanBroker.BrokerCover

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def LoanBroker.coverDeposit (lb : LoanBroker) (numericType : NumericType) (amount : STAmount)
    : Except Error LoanBrokerCoverResult := do
  let amount ← match (← lb.roundedCoverAmount numericType amount) with
    | .rejected _ => return { status := .tecINTERNAL, loanBroker' := lb, amount' := STAmount.zero numericType }
    | .rounded amount => .pure amount
  lb.applyCoverTransaction .credit amount

end XRPL.Model.Lending
