import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Lending.Identity

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

def defaultPaymentTotal : UInt32 := 1      -- payments count
def defaultPaymentInterval : UInt32 := 60  -- seconds
def defaultGracePeriod : UInt32 := 60      -- seconds

-- UInt32 max (2³² − 1)
def maxTime : UInt32 := 4_294_967_295

def hasExpired (ledgerCloseTime expTime : UInt32) (exclusive : Bool := false) : Bool :=
  if exclusive then ledgerCloseTime > expTime else ledgerCloseTime ≥ expTime

-- 1/10 bips: 0.1 bp = 0.001% = 0.00001
structure LoanRates where
  interestRate : TenthBips32
  lateInterestRate : TenthBips32
  closeInterestRate : TenthBips32
  overpaymentInterestRate : TenthBips32
  overpaymentFee : TenthBips32

-- fixed fee amounts
structure LoanFees where
  originationFee : Number
  serviceFee : Number
  latePaymentFee : Number
  closePaymentFee : Number

-- fee amounts (C++ getValueFields, with principalRequested prepended)
def LoanFees.amountFields (fees : LoanFees) : List Number :=
  [fees.originationFee, fees.serviceFee, fees.latePaymentFee, fees.closePaymentFee]

structure LoanSchedule where
  paymentInterval : UInt32
  paymentTotal : UInt32
  gracePeriod : UInt32
  startDate : UInt32

-- build the schedule, filling defaults
def LoanSchedule.build (paymentInterval paymentTotal gracePeriod : Option UInt32)
    (startDate ledgerCloseTime : UInt32) (twoStep : Bool) : LoanSchedule :=
  { paymentInterval := paymentInterval.getD defaultPaymentInterval
    paymentTotal := paymentTotal.getD defaultPaymentTotal
    gracePeriod := gracePeriod.getD defaultGracePeriod
    -- C++ getStartDate: two-step keeps the provided StartDate, one-step uses ledgerCloseTime
    startDate := if twoStep then startDate else ledgerCloseTime }

def LoanSchedule.checkTimeAvailability (schedule : LoanSchedule) : TER :=
  let timeAvailable := maxTime - schedule.startDate
  if schedule.gracePeriod > timeAvailable
      || schedule.paymentInterval > timeAvailable
      || schedule.paymentTotal > timeAvailable  -- double check as paymentTotal is count, not seconds?
      || (timeAvailable - schedule.gracePeriod) / schedule.paymentInterval < schedule.paymentTotal then
    .tecKILLED
  else
    .tesSUCCESS

structure Loan where
  identity : LoanIdentity
  vaultIdentity : VaultIdentity
  rates : LoanRates
  fees : LoanFees
  schedule : LoanSchedule
  -- accounting
  paymentRemaining : UInt32
  periodicPayment : Number
  principalOutstanding : Number
  totalValueOutstanding : Number
  managementFeeOutstanding : Number
  loanScale : Int
  -- due dates in seconds
  previousPaymentDueDate : UInt32
  nextPaymentDueDate : UInt32
  -- modeled from the flags
  isPending : Bool
  isImpaired : Bool
  isDefault : Bool
  allowsOverpayment : Bool

end XRPL.Model.Lending
