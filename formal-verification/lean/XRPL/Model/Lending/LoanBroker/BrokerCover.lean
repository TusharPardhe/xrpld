import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Protocol.Result
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.Result

def roundToCoverScale (nt : NumericType) (coverAvailable : Number) (amount : STAmount)
    (mode : rounding_mode) : Except Error STAmount := do
  let exponent ← numberExponent coverAvailable nt
  STAmount.roundToExponent amount exponent mode

-- minimum first-loss cover for the debt, rounded up
def minimumBrokerCover (nt : NumericType) (debtTotal : Number) (coverRateMinimum : TenthBips32) (poolExponent : Int)
    : Except Error Number := do
  let raw ← tenthBipsOfValue debtTotal coverRateMinimum .upward
  STAmount.roundToNumericType nt raw .upward (some poolExponent)

-- reject a cover deposit/withdraw/clawback that rounds to zero at the cover's own scale
def canApplyToBrokerCover (nt : NumericType) (coverAvailable : Number) (amount : STAmount)
    : Except Error TER := do
  if amount.isZero then
    return .tecPRECISION_LOSS
  let rounded ← roundToCoverScale nt coverAvailable amount .to_nearest
  if rounded.signum == 0 then
    return .tecPRECISION_LOSS
  return .tesSUCCESS

-- the cover movement actually applied: sub-scale dust is rejected rather than truncated
def LoanBroker.roundedCoverAmount (lb : LoanBroker) (nt : NumericType) (amount : STAmount)
    : Except Error RoundingResult := do
  let rounded ← roundToCoverScale nt lb.coverAvailable amount .downward
  if rounded.signum == 0 then
    return .rejected .tecPRECISION_LOSS
  return .rounded rounded

structure LoanBrokerCoverResult where
  status : TER := .tesSUCCESS
  amount' : STAmount
  loanBroker' : LoanBroker

inductive CoverDirection where
  | credit
  | debit

-- settle a rounded cover movement against coverAvailable
def LoanBroker.applyCoverTransaction (lb : LoanBroker) (direction : CoverDirection) (amount : STAmount)
   : Except Error LoanBrokerCoverResult := do
  let magnitude ← amount.toNumber .to_nearest
  let coverAvailable' ← match direction with
    | .credit => lb.coverAvailable.operator_add magnitude .to_nearest
    | .debit => lb.coverAvailable.operator_sub magnitude .to_nearest
  return { status := .tesSUCCESS, amount' := amount,
           loanBroker' := { lb with coverAvailable := coverAvailable' } }

end XRPL.Model.Lending
