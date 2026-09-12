import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.Amortization

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

structure LoanState where
  valueOutstanding : Number
  principalOutstanding : Number
  interestDue : Number
  managementFeeDue : Number

structure LoanStateDeltas where
  totalValue : Number := Number.zero
  principal : Number := Number.zero
  interest : Number := Number.zero
  untrackedInterest : Number := Number.zero
  managementFee : Number := Number.zero
  untrackedManagementFee : Number := Number.zero
  isFinal : Bool := false

def LoanState.build (valueOutstanding principalOutstanding managementFeeDue : Number)
    : Except Error LoanState := do
  let valueAfterPrincipal ← valueOutstanding.operator_sub principalOutstanding .to_nearest
  let interestDue ← valueAfterPrincipal.operator_sub managementFeeDue .to_nearest

  return {
    valueOutstanding := valueOutstanding
    principalOutstanding := principalOutstanding
    interestDue := interestDue
    managementFeeDue := managementFeeDue
  }

-- The loan state after `paymentRemaining` payments left
def LoanState.buildTheoretical (periodicPayment periodicRate : Number) (paymentRemaining : UInt32)
    (managementFeeRate : TenthBips16) : Except Error LoanState := do
  if paymentRemaining == 0 then
    return {
      valueOutstanding := Number.zero
      principalOutstanding := Number.zero
      interestDue := Number.zero
      managementFeeDue := Number.zero
    }

  let paymentCount := Number.ofInt64 paymentRemaining.toUInt64.toInt64
  let valueOutstanding ← periodicPayment.operator_mul paymentCount .to_nearest
  let principalOutstanding ← loanPrincipalFromPeriodicPayment periodicPayment periodicRate paymentRemaining

  let interestGross ← valueOutstanding.operator_sub principalOutstanding .to_nearest
  let managementFeeDue ← tenthBipsOfValue interestGross managementFeeRate.toTenthBips32 .to_nearest
  let interestDue ← interestGross.operator_sub managementFeeDue .to_nearest

  return {
    valueOutstanding := valueOutstanding
    principalOutstanding := principalOutstanding
    interestDue := interestDue
    managementFeeDue := managementFeeDue
  }

def LoanState.grossInterestOutstanding (x : LoanState) : Except Error Number :=
  x.valueOutstanding.operator_sub x.principalOutstanding .to_nearest

def LoanStateDeltas.totalValueOutstanding (deltas : LoanStateDeltas) : Except Error Number := do
  let principalPlusInterest ← deltas.principal.operator_add deltas.interest .to_nearest
  principalPlusInterest.operator_add deltas.managementFee .to_nearest

-- The tracked interest a payment covers
def LoanStateDeltas.trackedInterest (deltas : LoanStateDeltas) : Except Error Number := do
  let valueAfterPrincipal ← deltas.totalValue.operator_sub deltas.principal .to_nearest
  valueAfterPrincipal.operator_sub deltas.managementFee .to_nearest

-- The amount due from the borrower: total value plus the untracked interest and fee.
def LoanStateDeltas.amountDue (deltas : LoanStateDeltas) : Except Error Number := do
  let valuePlusInterest ← deltas.totalValue.operator_add deltas.untrackedInterest .to_nearest
  valuePlusInterest.operator_add deltas.untrackedManagementFee .to_nearest

def LoanStateDeltas.nonNegative (deltas : LoanStateDeltas) : LoanStateDeltas :=
  { deltas with
    principal := if deltas.principal.signum < 0 then Number.zero else deltas.principal
    interest := if deltas.interest.signum < 0 then Number.zero else deltas.interest
    managementFee := if deltas.managementFee.signum < 0 then Number.zero else deltas.managementFee }

-- Reduce `value` by min(value, excess). Return the reduced value and the excess left over.
private def reduceCapped (value excess : Number) : Except Error (Number × Number) := do
  if excess.operator_gt Number.zero then
    let part := Number.min value excess
    let valueLeft ← value.operator_sub part .to_nearest
    let excessLeft ← excess.operator_sub part .to_nearest
    return (valueLeft, excessLeft)
  else
    return (value, excess)

-- Reduce an overpayment off interest, then management fee, then principal.
def LoanStateDeltas.reduceByExcess (deltas : LoanStateDeltas) (excess : Number) : Except Error LoanStateDeltas := do
  let (interest, excess) ← reduceCapped deltas.interest excess
  let (managementFee, excess) ← reduceCapped deltas.managementFee excess
  let (principal, _) ← reduceCapped deltas.principal excess
  return { deltas with principal, interest, managementFee }

def LoanState.calculateDeltas (x y : LoanState) : Except Error LoanStateDeltas := do
  return { principal := ← x.principalOutstanding.operator_sub y.principalOutstanding .to_nearest,
           interest := ← x.interestDue.operator_sub y.interestDue .to_nearest,
           managementFee := ← x.managementFeeDue.operator_sub y.managementFeeDue .to_nearest }

def LoanState.addDeltas (x : LoanState) (deltas : LoanStateDeltas) : Except Error LoanState := do
  let tot ← deltas.totalValueOutstanding
  return { valueOutstanding := ← x.valueOutstanding.operator_add tot .to_nearest,
           principalOutstanding := ← x.principalOutstanding.operator_add deltas.principal .to_nearest,
           interestDue := ← x.interestDue.operator_add deltas.interest .to_nearest,
           managementFeeDue := ← x.managementFeeDue.operator_add deltas.managementFee .to_nearest }

end XRPL.Model.Lending
