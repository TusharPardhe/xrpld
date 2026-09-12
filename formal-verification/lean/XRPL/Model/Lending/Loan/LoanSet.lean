import XRPL.Model.Protocol.Exponent
import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.Amortization
import XRPL.Model.Lending.Interest
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.LoanBroker.BrokerCover
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- C++ getValueFields: principalRequested and each fee must pass check
private def checkPrecisionFields (principal : Number) (fees : LoanFees) (checkFnc : Number → Except Error Bool)
    : Except Error TER := do
  for value in principal :: fees.amountFields do
    if !(← checkFnc value) then return .tecPRECISION_LOSS
  return .tesSUCCESS

-- LoanSet -> preclaim
def Loan.canCreate (vault : Vault) (principalRequested : Number) (fees : LoanFees) (schedule : LoanSchedule)
    (ledgerCloseTime : UInt32) (twoStep : Bool) : Except Error TER := do
  let scheduleTer := schedule.checkTimeAvailability
  if !scheduleTer.isTesSuccess then return scheduleTer

  let assetsMaximum := vault.assetsMaximum.getD Number.zero
  if assetsMaximum.operator_ne Number.zero && vault.assetsTotal.operator_ge assetsMaximum then
    return .tecLIMIT_EXCEEDED

  let precTer ← checkPrecisionFields principalRequested fees
    (STAmount.equalAfterNumberConvert vault.numericType)
  if !precTer.isTesSuccess then return precTer

  if twoStep && hasExpired ledgerCloseTime schedule.startDate then return .tecEXPIRED
  return .tesSUCCESS

-- derived loan values (mirrors computeLoanProperties)
structure LoanComputed where
  periodicPayment : Number
  totalValueOutstanding : Number
  managementFeeOutstanding : Number
  loanScale : Int
  principalOutstanding : Number
  firstPaymentPrincipal : Number

def computeLoanPropertiesFromPeriodicRate (principal periodicRate : Number) (paymentsRemaining : UInt32)
    (managementFeeRate : TenthBips16) (nt : NumericType) (minimumScale : Int)
    : Except Error LoanComputed := do
  let periodicPayment ← loanPeriodicPayment principal periodicRate paymentsRemaining

  -- round up when there's interest, else to nearest
  let mode : rounding_mode := if periodicRate.operator_eq Number.zero then .to_nearest else .upward
  let amount ← periodicPayment.operator_mul (Number.ofInt64 paymentsRemaining.toUInt64.toInt64) mode
  let amountSt ← STAmount.ofNumber nt amount mode
  let loanScale := max minimumScale amountSt.exponent
  let totalValueOutstanding ← STAmount.roundToNumericType nt amount mode (some loanScale)

  let roundedPrincipal ← STAmount.roundToNumericType nt principal .to_nearest (some loanScale)
  let totalInterest ← totalValueOutstanding.operator_sub roundedPrincipal .to_nearest
  let managementFeeOutstanding ← computeManagementFee nt totalInterest managementFeeRate loanScale

  let startPrincipal ← loanPrincipalFromPeriodicPayment periodicPayment periodicRate paymentsRemaining
  let nextPrincipal ← loanPrincipalFromPeriodicPayment periodicPayment periodicRate (paymentsRemaining - 1)
  let firstPaymentPrincipal ← startPrincipal.operator_sub nextPrincipal .to_nearest

  return {
    periodicPayment := periodicPayment
    totalValueOutstanding := totalValueOutstanding
    managementFeeOutstanding := managementFeeOutstanding
    loanScale := loanScale
    principalOutstanding := roundedPrincipal
    firstPaymentPrincipal := firstPaymentPrincipal
  }

def computeLoanProperties (principal : Number) (interestRate : TenthBips32)
    (paymentInterval paymentsRemaining : UInt32) (managementFeeRate : TenthBips16)
    (nt : NumericType) (minimumScale : Int) : Except Error LoanComputed := do
  let periodicRate ← loanPeriodicRate interestRate paymentInterval
  computeLoanPropertiesFromPeriodicRate principal periodicRate paymentsRemaining managementFeeRate nt minimumScale

def LoanComputed.checkGuards (computed : LoanComputed) (principal : Number)
    (interestRate : TenthBips32) (paymentsRemaining : UInt32) (nt : NumericType) : Except Error TER := do
  let expectInterest := interestRate != 0
  let totalInterest ← computed.totalValueOutstanding.operator_sub principal .to_nearest
  if expectInterest && totalInterest.signum ≤ 0 then return .tecPRECISION_LOSS
  if !expectInterest && totalInterest.signum > 0 then return .tecINTERNAL

  if computed.firstPaymentPrincipal.signum ≤ 0 then return .tecPRECISION_LOSS

  let roundedPayment ←
    STAmount.roundToNumericType nt computed.periodicPayment .upward (some computed.loanScale)
  if roundedPayment.operator_eq Number.zero then return .tecPRECISION_LOSS

  let ratio ← computed.totalValueOutstanding.operator_div roundedPayment .upward
  let computedPayments ← ratio.to_rep .upward
  if computedPayments != paymentsRemaining.toUInt64.toInt64 then return .tecPRECISION_LOSS

  if computed.managementFeeOutstanding.signum < 0 || computed.totalValueOutstanding.signum ≤ 0
      || computed.periodicPayment.signum ≤ 0 then return .tecINTERNAL
  return .tesSUCCESS

-- broker stays under its debt cap and keeps enough cover
def LoanBroker.checkLimits (broker : LoanBroker) (newDebtTotal : Number) (nt : NumericType)
    (vaultExponent : Int) : Except Error TER := do
  if broker.debtMaximum.operator_ne Number.zero && broker.debtMaximum.operator_lt newDebtTotal then
    return .tecLIMIT_EXCEEDED
  let minCover ← minimumBrokerCover nt newDebtTotal broker.coverRateMinimum vaultExponent
  if broker.coverAvailable.operator_lt minCover then return .tecINSUFFICIENT_FUNDS
  return .tesSUCCESS

def buildLoan (identity : LoanIdentity) (vaultIdentity : VaultIdentity) (computed : LoanComputed) (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule)
    (allowsOverpayment isPending : Bool) : Loan := {
  identity := identity
  vaultIdentity := vaultIdentity
  rates := rates
  fees := fees
  schedule := schedule
  paymentRemaining := schedule.paymentTotal
  periodicPayment := computed.periodicPayment
  principalOutstanding := computed.principalOutstanding
  totalValueOutstanding := computed.totalValueOutstanding
  managementFeeOutstanding := computed.managementFeeOutstanding
  loanScale := computed.loanScale
  previousPaymentDueDate := 0
  nextPaymentDueDate := schedule.startDate + schedule.paymentInterval
  isPending := isPending
  isImpaired := false
  isDefault := false
  allowsOverpayment := allowsOverpayment
}

-- LoanSet -> doApply
def Loan.create (vaultIdentity : VaultIdentity) (loanIdentity : LoanIdentity) (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment pending : Bool)
    : Except Error (LoanResult LendingState) := do
  let identityTer := LendingIdentity.valid vaultIdentity broker.identity loanIdentity
  if !identityTer.isTesSuccess then return .rejected identityTer
  if vault.assetsAvailable.operator_lt principal then return .rejected .tecINSUFFICIENT_FUNDS
  let vaultExponent ← numberExponent vault.assetsTotal vault.numericType

  let computed ← computeLoanProperties principal rates.interestRate
    schedule.paymentInterval schedule.paymentTotal broker.managementFeeRate vault.numericType vaultExponent
  let repTer ← checkPrecisionFields principal fees
    (fun v => isRounded vault.numericType v computed.loanScale)
  if !repTer.isTesSuccess then return .rejected repTer

  let guardTer ← computed.checkGuards principal rates.interestRate schedule.paymentTotal vault.numericType
  if !guardTer.isTesSuccess then return .rejected guardTer

  let newDebtTotal ← broker.debtTotal.operator_add principal .to_nearest
  let limitTer ← broker.checkLimits newDebtTotal vault.numericType vaultExponent
  if !limitTer.isTesSuccess then return .rejected limitTer

  let loan := buildLoan loanIdentity vaultIdentity computed rates fees schedule allowsOverpayment pending

  let availableAfter ← vault.assetsAvailable.operator_sub principal .to_nearest
  let reservedAfter ← if pending then vault.assetsReserved.operator_add principal .to_nearest
                      else pure vault.assetsReserved
  let rawVault' : RawVault := { vault.toRawVault with assetsAvailable := availableAfter, assetsReserved := reservedAfter }
  let vault' ← rawVault'.to_lawful

  let debtAfter ← adjustImpreciseNumber vault.numericType broker.debtTotal principal vaultExponent
  let broker' := { broker with debtTotal := debtAfter, loanCount := broker.loanCount + 1 }

  return .ok { vaultIdentity := vaultIdentity, vault := vault', broker := broker', loan := loan }

def Loan.createPending (vaultIdentity : VaultIdentity) (loanIdentity : LoanIdentity) (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment : Bool)
    : Except Error (LoanResult LendingState) :=
  Loan.create vaultIdentity loanIdentity vault broker principal rates fees schedule allowsOverpayment true

def Loan.createImmediate (vaultIdentity : VaultIdentity) (loanIdentity : LoanIdentity) (vault : Vault) (broker : LoanBroker) (principal : Number)
    (rates : LoanRates) (fees : LoanFees) (schedule : LoanSchedule) (allowsOverpayment : Bool)
    : Except Error (LoanResult LendingState) :=
  Loan.create vaultIdentity loanIdentity vault broker principal rates fees schedule allowsOverpayment false

end XRPL.Model.Lending
