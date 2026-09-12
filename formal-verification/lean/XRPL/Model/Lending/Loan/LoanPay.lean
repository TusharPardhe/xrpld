import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TenthBips
import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.CashBasis
import XRPL.Model.Lending.Interest
import XRPL.Model.Lending.Loan.Loan
import XRPL.Model.Lending.Loan.LoanResult
import XRPL.Model.Lending.Loan.LoanSet
import XRPL.Model.Lending.Loan.LoanState
import XRPL.Model.Lending.LoanBroker.LoanBroker

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- The outcome of re-amortizing the loan after an overpayment.
structure Reamortization where
  ignored : Bool                 -- true when a guard dropped the overpayment
  principalPaid : Number
  interestPaid : Number
  valueChange : Number
  state' : LoanState             -- the re-amortized loan state
  periodicPayment' : Number      -- the re-amortized periodic payment

inductive LoanPaymentType where
  | regular | late | full | overpayment
  deriving DecidableEq, Repr

-- A payment is late once the ledger close time passes the next due date
private def isPaymentLate (now nextPaymentDueDate : UInt32) : Bool := nextPaymentDueDate < now

-- Round the interest, then split it into the net interest and the management fee on it.
private def roundAndSplitInterest (interest : Number) (mgmtRate : TenthBips16) (mode : rounding_mode)
    (nt : NumericType) (scale : Int) : Except Error (Number × Number) := do
  let interest' ← STAmount.roundToNumericType nt interest mode (some scale)
  let managementFee ← computeManagementFee nt interest' mgmtRate scale
  let netInterest ← interest'.operator_sub managementFee .to_nearest
  return (netInterest, managementFee)

-- The tracked deltas of this loan's next scheduled instalment, regular or final.
private def Loan.scheduledComponents (loan : Loan) (vault : Vault) (broker : LoanBroker) : Except Error LoanStateDeltas := do
  let tvo := loan.totalValueOutstanding
  let po := loan.principalOutstanding
  let mfo := loan.managementFeeOutstanding
  let periodicPayment := loan.periodicPayment
  let periodicRate ← loanPeriodicRate loan.rates.interestRate loan.schedule.paymentInterval
  let paymentRemaining := loan.paymentRemaining
  let nt := vault.numericType
  let scale := loan.loanScale
  let periodicPayment' ← STAmount.roundToNumericType nt periodicPayment .upward (some scale)

  -- final payment
  if paymentRemaining == 1 || tvo.operator_le periodicPayment' then
    return { totalValue := tvo, principal := po, managementFee := mfo, isFinal := true }

  let currentState ← LoanState.build tvo po mfo
  let targetState ← LoanState.buildTheoretical periodicPayment periodicRate (paymentRemaining - 1) broker.managementFeeRate

  let targetPO ← STAmount.roundToNumericType nt targetState.principalOutstanding .upward (some scale)
  let targetInterest ← STAmount.roundToNumericType nt targetState.interestDue .downward (some scale)
  let targetMFO ← STAmount.roundToNumericType nt targetState.managementFeeDue .to_nearest (some scale)

  -- deltas = current minus target, floored at zero
  let deltas := ({ principal := ← currentState.principalOutstanding.operator_sub targetPO .to_nearest,
                   interest := ← currentState.interestDue.operator_sub targetInterest .to_nearest,
                   managementFee := ← currentState.managementFeeDue.operator_sub targetMFO .to_nearest }
                 : LoanStateDeltas).nonNegative

  -- cap each component: principal by what is outstanding, then the rest by the room left in the payment
  let cappedPrincipal := Number.min deltas.principal currentState.principalOutstanding

  let roomForInterest ← periodicPayment'.operator_sub cappedPrincipal .to_nearest
  let cappedInterest := Number.min (Number.min deltas.interest (Number.max Number.zero roomForInterest))
    currentState.interestDue
  let principalPlusInterest ← cappedPrincipal.operator_add cappedInterest .to_nearest

  let roomForFee ← periodicPayment'.operator_sub principalPlusInterest .to_nearest
  let cappedManagementFee := Number.min (Number.min deltas.managementFee roomForFee)
    currentState.managementFeeDue

  let deltas : LoanStateDeltas :=
    { principal := cappedPrincipal, interest := cappedInterest, managementFee := cappedManagementFee }

  -- remove any overpayment
  let overpayment ← (← deltas.totalValueOutstanding).operator_sub currentState.valueOutstanding .to_nearest
  let deltas ← if overpayment.operator_gt Number.zero then deltas.reduceByExcess overpayment else pure deltas

  -- if the deltas exceed the periodic payment, remove the excess
  let shortage ← periodicPayment'.operator_sub (← deltas.totalValueOutstanding) .to_nearest
  let deltas ← if shortage.signum < 0 then deltas.reduceByExcess shortage.operator_neg else pure deltas

  return { totalValue := Number.clamp (← deltas.totalValueOutstanding) Number.zero currentState.valueOutstanding
           principal := Number.clamp deltas.principal Number.zero currentState.principalOutstanding
           managementFee := Number.clamp deltas.managementFee Number.zero currentState.managementFeeDue
           isFinal := false }

-- Split an overpayment into its fee, its interest, and the principal it pays down.
private def computeOverpaymentComponents (overpayment : Number) (overRate overFeeRate : TenthBips32)
    (mgmtRate : TenthBips16) (nt : NumericType) (scale : Int) : Except Error LoanStateDeltas := do
  -- the fee, and the loan value that is left once the fee is taken
  let overpaymentFee ← tenthBipsOfValue overpayment overFeeRate .to_nearest
  let overpaymentFee' ← STAmount.roundToNumericType nt overpaymentFee .to_nearest (some scale)
  let valueDelta ← overpayment.operator_sub overpaymentFee' .to_nearest

  -- the interest, split into net interest and its management fee
  let overpaymentInterest ← tenthBipsOfValue overpayment overRate .to_nearest
  let (netInterest, managementFee) ← roundAndSplitInterest overpaymentInterest mgmtRate .to_nearest nt scale

  -- whatever is left after interest, management fee, and the fee pays down the principal
  let principalAfterInterest ← overpayment.operator_sub netInterest .to_nearest
  let principalAfterFee ← principalAfterInterest.operator_sub managementFee .to_nearest
  let principalDelta ← principalAfterFee.operator_sub overpaymentFee' .to_nearest

  return { totalValue := valueDelta, principal := principalDelta,
           managementFee := managementFee, isFinal := false,
           untrackedInterest := netInterest, untrackedManagementFee := overpaymentFee' }

-- Re-amortize the remaining schedule after an overpayment.
private def processOverpayment (opc : LoanStateDeltas) (oldState : LoanState)
    (periodicPayment periodicRate : Number) (paymentRemaining : UInt32) (mgmtRate : TenthBips16)
    (nt : NumericType) (scale : Int) : Except Error Reamortization := do
  -- re-amortize for the reduced principal
  let theoreticalState ← LoanState.buildTheoretical periodicPayment periodicRate paymentRemaining mgmtRate
  let deltaErrors ← LoanState.calculateDeltas oldState theoreticalState
  let reducedPrincipal := Number.max
    (← theoreticalState.principalOutstanding.operator_sub opc.principal .to_nearest) Number.zero
  let reamortizedProps ← computeLoanPropertiesFromPeriodicRate reducedPrincipal periodicRate paymentRemaining mgmtRate nt scale

  -- rebuild the state at the new payment, carrying the rounding errors
  let state ← LoanState.buildTheoretical reamortizedProps.periodicPayment periodicRate paymentRemaining mgmtRate
  let state ← state.addDeltas deltaErrors

  -- pin principal and fee to the actual post-overpayment values
  let pinnedPrincipal ← oldState.principalOutstanding.operator_sub opc.principal .to_nearest
  let grossInterest ← state.valueOutstanding.operator_sub pinnedPrincipal .to_nearest
  let pinnedMgmtFee ← tenthBipsOfValue grossInterest mgmtRate.toTenthBips32 .to_nearest
  let state ← LoanState.build state.valueOutstanding pinnedPrincipal pinnedMgmtFee

  -- round and clamp into the committed new state
  let po ← roundAndClamp state.principalOutstanding oldState.principalOutstanding .upward nt scale
  let interest ← state.grossInterestOutstanding
  let tvo ← po.operator_add interest .to_nearest
  let tvo' ← roundAndClamp tvo oldState.valueOutstanding .upward nt scale
  let mfo ← roundAndClamp state.managementFeeDue oldState.managementFeeDue .to_nearest nt scale
  let state ← LoanState.build tvo' po mfo

  -- the re-amortization guards
  let interestOut ← state.grossInterestOutstanding
  let expectInterest := interestOut.operator_ne Number.zero
  let roundedPayment ← STAmount.roundToNumericType nt reamortizedProps.periodicPayment .upward (some scale)
  let guardFail ← do
    if expectInterest && interestOut.operator_le Number.zero then pure true
    else if (!expectInterest) && interestOut.operator_gt Number.zero then pure true
    else if reamortizedProps.firstPaymentPrincipal.operator_le Number.zero then pure true
    else if roundedPayment.operator_eq Number.zero then pure true
    else
      let ratio ← tvo'.operator_div roundedPayment .upward
      let computedPayments ← ratio.to_rep .upward
      pure (computedPayments != paymentRemaining.toUInt64.toInt64)

  -- the deltas from the old state to the new one, and whether to ignore the overpayment
  let deltas ← LoanState.calculateDeltas oldState state
  let valueChange ← deltas.interest.operator_neg.operator_add opc.untrackedInterest .to_nearest
  let notDecreased := oldState.principalOutstanding.operator_le po
  let increasesValue := deltas.interest.operator_neg.operator_gt Number.zero
  let ignored := guardFail || notDecreased || increasesValue
  let principalPaid := deltas.principal

  return { ignored, principalPaid, interestPaid := opc.untrackedInterest,
           valueChange := ← valueChange.operator_add opc.untrackedInterest .to_nearest,
           state' := state, periodicPayment' := reamortizedProps.periodicPayment }

-- Apply the payment to the vault and broker, then rewrite the loan.
private def Loan.doPayment (loan : Loan) (vault : Vault) (broker : LoanBroker) (deltas : LoanStateDeltas)
    : Except Error (LendingState × Number) := do
  let principalPaid := deltas.principal
  let trackedInterest ← deltas.trackedInterest
  let interestPaid ← trackedInterest.operator_add deltas.untrackedInterest .to_nearest

  -- the broker takes the management fee plus the fixed service, late and close fees
  let feePaid ← deltas.managementFee.operator_add deltas.untrackedManagementFee .to_nearest
  let vb ← CashBasis.applyPayment loan.vaultIdentity vault broker principalPaid interestPaid feePaid

  if deltas.isFinal then
    let loan' := { loan with
      totalValueOutstanding := Number.zero, principalOutstanding := Number.zero,
      managementFeeOutstanding := Number.zero, paymentRemaining := 0,
      previousPaymentDueDate := loan.nextPaymentDueDate, nextPaymentDueDate := 0 }
    return ({ vaultIdentity := loan.vaultIdentity, vault := vb.vault, broker := vb.broker, loan := loan' }, interestPaid)
  else
    let loan' := { loan with
      totalValueOutstanding := ← loan.totalValueOutstanding.operator_sub deltas.totalValue .to_nearest
      principalOutstanding := ← loan.principalOutstanding.operator_sub deltas.principal .to_nearest
      managementFeeOutstanding := ← loan.managementFeeOutstanding.operator_sub deltas.managementFee .to_nearest
      paymentRemaining := loan.paymentRemaining - 1
      previousPaymentDueDate := loan.nextPaymentDueDate
      nextPaymentDueDate := loan.nextPaymentDueDate + loan.schedule.paymentInterval }
    return ({ vaultIdentity := loan.vaultIdentity, vault := vb.vault, broker := vb.broker, loan := loan' }, interestPaid)

-- Pay scheduled instalments one at a time while the amount covers the next due and the loan is unpaid, up to 100.
private def payScheduledInstalments (instalmentsLeft : Nat) (amount serviceFee : Number)
    (loan : Loan) (vault : Vault) (broker : LoanBroker) (totalPaid assetsTotalDelta : Number) (count : Nat)
    : Except Error (LendingState × Number × Number × Nat) := do
  -- the accumulated result to return when iteration stops
  let accumulated := (({ vaultIdentity := loan.vaultIdentity, vault, broker, loan } : LendingState), totalPaid, assetsTotalDelta, count)

  -- return when the per-transaction instalment cap is reached or the loan is fully paid
  match instalmentsLeft with
  | 0 => return accumulated
  | remaining + 1 =>
    if loan.paymentRemaining == 0 then return accumulated

    -- compute the next scheduled instalment and its amount due
    let pc ← loan.scheduledComponents vault broker
    let deltas : LoanStateDeltas := { pc with untrackedManagementFee := serviceFee }
    let due ← deltas.amountDue

    -- return when the remaining amount cannot cover the next instalment
    if amount.operator_lt (← totalPaid.operator_add due .to_nearest) then return accumulated

    -- apply the instalment and update the running totals
    let (s, interestPaid) ← loan.doPayment vault broker deltas
    let totalPaid ← totalPaid.operator_add due .to_nearest
    let assetsTotalDelta ← assetsTotalDelta.operator_add interestPaid .to_nearest

    if pc.isFinal then
      return (s, totalPaid, assetsTotalDelta, count + 1)
    else
      payScheduledInstalments remaining amount serviceFee
        s.loan s.vault s.broker totalPaid assetsTotalDelta (count + 1)

-- Pay as many scheduled instalments as the amount covers (up to 100), then apply any overpayment tail.
private def Loan.payInstalmentsAndOverpayment (loan : Loan) (vault : Vault) (broker : LoanBroker)
    (paymentType : LoanPaymentType) (amount : Number) : Except Error (LoanResult (LendingState × Number)) := do
  let (s, totalPaid, assetsTotalDelta, count) ←
    payScheduledInstalments 100 amount loan.fees.serviceFee loan vault broker Number.zero Number.zero 0
  if count == 0 then return .rejected .tecINSUFFICIENT_PAYMENT   -- amount covered no instalments

  let ⟨_vaultIdentity, vault, broker, loan⟩ := s
  let instalmentsResult : LoanResult (LendingState × Number) := .ok (s, assetsTotalDelta)

  -- the overpayment tail applies only to an overpayment transaction with remaining budget and payments
  let applyOverpayment := paymentType matches .overpayment
    && loan.allowsOverpayment && loan.paymentRemaining != 0 && totalPaid.operator_lt amount
  if !applyOverpayment then return instalmentsResult

  -- the unspent amount, capped at the outstanding value and rounded down at loan scale
  let unspent ← amount.operator_sub totalPaid .to_nearest
  let cappedUnspent := Number.min unspent loan.totalValueOutstanding
  let overpayment ← STAmount.roundToNumericType vault.numericType cappedUnspent .downward (some loan.loanScale)
  if !(overpayment.operator_gt Number.zero) then return instalmentsResult   -- the overpayment rounded to zero

  -- split the overpayment into principal, interest, and fees
  let opc ← computeOverpaymentComponents overpayment loan.rates.overpaymentInterestRate
    loan.rates.overpaymentFee broker.managementFeeRate vault.numericType loan.loanScale
  if !(opc.principal.operator_gt Number.zero) then return instalmentsResult  -- no principal left after fees and interest

  -- re-amortize the remaining schedule for the reduced principal
  let periodicRate ← loanPeriodicRate loan.rates.interestRate loan.schedule.paymentInterval
  let oldState ← LoanState.build loan.totalValueOutstanding loan.principalOutstanding loan.managementFeeOutstanding
  let reamortization ← processOverpayment opc oldState loan.periodicPayment periodicRate
    loan.paymentRemaining broker.managementFeeRate vault.numericType loan.loanScale
  if reamortization.ignored then return instalmentsResult   -- a re-amortization guard rejected the overpayment

  -- apply the overpayment to the vault and broker, then commit the re-amortized loan
  let feePaid ← opc.managementFee.operator_add opc.untrackedManagementFee .to_nearest
  let vb ← CashBasis.applyPayment loan.vaultIdentity vault broker reamortization.principalPaid reamortization.interestPaid feePaid
  let loan' := { loan with
    totalValueOutstanding := reamortization.state'.valueOutstanding
    principalOutstanding := reamortization.state'.principalOutstanding
    managementFeeOutstanding := reamortization.state'.managementFeeDue
    periodicPayment := reamortization.periodicPayment' }
  let assetsTotalDelta ← assetsTotalDelta.operator_add reamortization.interestPaid .to_nearest

  return .ok ({ vaultIdentity := loan.vaultIdentity, vault := vb.vault, broker := vb.broker, loan := loan' }, assetsTotalDelta)

-- Re-check the vault after a payment, matching the doApply checks once amounts are rounded
private def validatePostPayment (vault : Vault) (s : LendingState) (assetsTotalDelta : Number) : LoanResult LendingState :=
  let vault' := s.vault
  let assetsAvailableChanged := vault'.assetsAvailable.operator_ne vault.assetsAvailable
  let assetsTotalChanged := vault'.assetsTotal.operator_ne vault.assetsTotal
  let expectedChange := assetsTotalDelta.operator_ne Number.zero

  if !assetsAvailableChanged then .rejected .tecPRECISION_LOSS
  else if expectedChange && !assetsTotalChanged then .rejected .tecPRECISION_LOSS
  else if !expectedChange && assetsTotalChanged then .rejected .tecINTERNAL
  else if vault'.assetsAvailable.operator_gt vault'.assetsTotal then .rejected .tecINTERNAL
  else .ok s

-- LoanPay -> preclaim
def Loan.canPay (loan : Loan) (paymentType : LoanPaymentType) : TER :=
  if loan.isPending then
    .tecNO_PERMISSION
  else if (paymentType matches .overpayment) && !loan.allowsOverpayment then
    .tecNO_PERMISSION
  else if loan.paymentRemaining == 0 || loan.principalOutstanding.operator_eq Number.zero then
    .tecKILLED
  else
    .tesSUCCESS

-- Pay a regular (or overpayment) instalment.
def Loan.regularPayment (loan : Loan) (vault : Vault) (broker : LoanBroker) (paymentType : LoanPaymentType)
    (amount : Number) (now : UInt32) : Except Error (LoanResult LendingState) := do
  if loan.nextPaymentDueDate == 0 then return .rejected .tecINTERNAL
  if isPaymentLate now loan.nextPaymentDueDate then return .rejected .tecEXPIRED

  match ← loan.payInstalmentsAndOverpayment vault broker paymentType amount with
  | .rejected ter => return .rejected ter
  | .ok (s, assetsTotalDelta) => return validatePostPayment vault s assetsTotalDelta

-- Pay a late instalment: scheduled amount + penalty interest for the overdue seconds + fixed late fee.
def Loan.latePayment (loan : Loan) (vault : Vault) (broker : LoanBroker) (amount : Number) (now : UInt32)
    : Except Error (LoanResult LendingState) := do
  if loan.nextPaymentDueDate == 0 then return .rejected .tecINTERNAL
  if !(isPaymentLate now loan.nextPaymentDueDate) then return .rejected .tecTOO_SOON

  -- penalty interest for the overdue seconds, split into net interest + management fee
  let pc ← loan.scheduledComponents vault broker
  let lateInterest ← loanLatePaymentInterest loan.principalOutstanding loan.rates.lateInterestRate
    now loan.nextPaymentDueDate
  let (lateInterestNet, lateFeeSplit) ← roundAndSplitInterest lateInterest broker.managementFeeRate
    .to_nearest vault.numericType loan.loanScale

  -- untrackedFee = service fee + fixed late fee + management fee on the penalty interest
  let untrackedFee ← (← loan.fees.serviceFee.operator_add loan.fees.latePaymentFee .to_nearest).operator_add
    lateFeeSplit .to_nearest
  let deltas : LoanStateDeltas :=
    { pc with untrackedInterest := lateInterestNet, untrackedManagementFee := untrackedFee }
  if amount.operator_lt (← deltas.amountDue) then return .rejected .tecINSUFFICIENT_PAYMENT

  let (s, assetsTotalDelta) ← loan.doPayment vault broker deltas
  return validatePostPayment vault s assetsTotalDelta

-- Pay off the loan early: clear the whole outstanding value + early-payoff interest + close fee, then close it.
def Loan.fullPayment (loan : Loan) (vault : Vault) (broker : LoanBroker) (amount : Number) (now : UInt32)
    : Except Error (LoanResult LendingState) := do
  if loan.nextPaymentDueDate == 0 then return .rejected .tecINTERNAL
  if isPaymentLate now loan.nextPaymentDueDate then return .rejected .tecEXPIRED
  if loan.paymentRemaining ≤ 1 then return .rejected .tecKILLED   -- the last instalment must be a regular payment

  -- early-payoff interest up to now, split into net interest + management fee
  let periodicRate ← loanPeriodicRate loan.rates.interestRate loan.schedule.paymentInterval
  let theoreticalPO ← loanPrincipalFromPeriodicPayment loan.periodicPayment periodicRate loan.paymentRemaining
  let fullInterest ← computeFullPaymentInterest theoreticalPO periodicRate now loan.schedule.paymentInterval
    loan.previousPaymentDueDate loan.schedule.startDate loan.rates.closeInterestRate
  let (fullInterestNet, fullFeeSplit) ← roundAndSplitInterest fullInterest broker.managementFeeRate
    .downward vault.numericType loan.loanScale

  -- clear the whole outstanding value, with the close fee and extra early-payoff interest as untracked
  let state ← LoanState.build loan.totalValueOutstanding loan.principalOutstanding loan.managementFeeOutstanding
  let closePaymentFee ← STAmount.roundToNumericType vault.numericType loan.fees.closePaymentFee .to_nearest (some loan.loanScale)

  let trackedValue ← (← state.principalOutstanding.operator_add state.interestDue .to_nearest).operator_add
    state.managementFeeDue .to_nearest
  let untrackedFee ← (← closePaymentFee.operator_add fullFeeSplit .to_nearest).operator_sub state.managementFeeDue .to_nearest
  let untrackedInterest ← fullInterestNet.operator_sub state.interestDue .to_nearest

  let deltas : LoanStateDeltas :=
    { totalValue := trackedValue, principal := state.principalOutstanding
      managementFee := state.managementFeeDue, isFinal := true
      untrackedInterest := untrackedInterest, untrackedManagementFee := untrackedFee }
  if amount.operator_lt (← deltas.amountDue) then return .rejected .tecINSUFFICIENT_PAYMENT

  let (s, assetsTotalDelta) ← loan.doPayment vault broker deltas
  return validatePostPayment vault s assetsTotalDelta

end XRPL.Model.Lending
