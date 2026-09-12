import XRPL.Model.Protocol.Number
import XRPL.Model.Lending.Interest

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

-- XLS-66 (6): payment factor rate*(1+m)/m, m = (1+rate)^paymentsRemaining - 1
def computePaymentFactor (rate paymentsRemainingNum : Number) (paymentsRemaining : UInt32)
    : Except Error Number := do
  if paymentsRemaining == 0 then return Number.zero
  if rate.operator_eq Number.zero then
    (Number.ofInt64 1).operator_div paymentsRemainingNum .to_nearest
  else
    let powerMinusOne ← computePowerMinusOneHybrid rate paymentsRemainingNum paymentsRemaining
    let raisedRate ← (Number.ofInt64 1).operator_add powerMinusOne .to_nearest
    let numerator ← rate.operator_mul raisedRate .to_nearest
    numerator.operator_div powerMinusOne .to_nearest

-- XLS-66 (7): fixed per-period payment
def loanPeriodicPayment (principal rate : Number) (paymentsRemaining : UInt32)
    : Except Error Number := do
  if principal.operator_eq Number.zero || paymentsRemaining == 0 then return Number.zero
  let paymentsRemainingNum := Number.ofInt64 paymentsRemaining.toUInt64.toInt64
  if rate.operator_eq Number.zero then
    principal.operator_div paymentsRemainingNum .to_nearest
  else
    let factor ← computePaymentFactor rate paymentsRemainingNum paymentsRemaining
    principal.operator_mul factor .to_nearest

-- XLS-66 (10): principal implied by a periodic payment
def loanPrincipalFromPeriodicPayment (periodicPayment rate : Number) (paymentsRemaining : UInt32)
    : Except Error Number := do
  if paymentsRemaining == 0 then return Number.zero
  let paymentsRemainingNum := Number.ofInt64 paymentsRemaining.toUInt64.toInt64
  if rate.operator_eq Number.zero then
    periodicPayment.operator_mul paymentsRemainingNum .to_nearest
  else
    let factor ← computePaymentFactor rate paymentsRemainingNum paymentsRemaining
    periodicPayment.operator_div factor .to_nearest

end XRPL.Model.Lending
