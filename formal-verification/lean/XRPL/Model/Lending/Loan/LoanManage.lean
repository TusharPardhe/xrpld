import XRPL.Model.Lending.Loan.LoanPay

namespace XRPL.Model.Lending

open XRPL.Model.Protocol
open XRPL.Model.SingleAssetVault

-- The management action a transaction requests (only one may be set).
inductive LoanManageAction where
  | impair | unimpair | default
  deriving DecidableEq, Repr

-- Amount of the default the broker's first-loss cover absorbs
private def defaultCoveredAmount (broker : LoanBroker) (totalDefaultAmount : Number) (nt : NumericType) (scale : Int)
    : Except Error Number := do
  let minCoverAmount ← tenthBipsOfValue broker.debtTotal broker.coverRateMinimum .upward
  let liqAmount ← tenthBipsOfValue minCoverAmount broker.coverRateLiquidation .upward

  let coveredAmount := Number.min liqAmount totalDefaultAmount
  let coveredAmount' ← STAmount.roundToNumericType nt coveredAmount .upward (some scale)

  return Number.min coveredAmount' broker.coverAvailable

-- If AA exceeds AT by only a dust amount (more than 13 exponents smaller), raise AT to AA.
private def dustAdjustedAssetsTotal (assetsAvailable assetsTotal : Number) : Except Error Number := do
  if assetsAvailable.operator_le assetsTotal then
    return assetsTotal
  let overshoot ← assetsAvailable.operator_sub assetsTotal .to_nearest
  let isDust := assetsAvailable.exponent_ - overshoot.exponent_ > 13
  return (if isDust then assetsAvailable else assetsTotal)

-- LoanManage -> preclaim
def Loan.canManage (loan : Loan) (action : LoanManageAction) (now : UInt32) : TER :=
  let gracePeriodEnd := loan.nextPaymentDueDate + loan.schedule.gracePeriod

  if loan.isPending then
    .tecNO_PERMISSION
  else if loan.isDefault then
    .tecNO_PERMISSION
  else if loan.isImpaired && action == .impair then
    .tecNO_PERMISSION
  else if !(loan.isImpaired || loan.isDefault) && action == .unimpair then
    .tecNO_PERMISSION
  else if loan.paymentRemaining == 0 then
    .tecNO_PERMISSION
  else if action == .default && !hasExpired now gracePeriodEnd (exclusive := true) then
    .tecTOO_SOON
  else
    .tesSUCCESS

-- Record the loan's exposure as a paper loss.
def Loan.manageImpair (loan : Loan) (vault : Vault) : Except Error (LoanResult Vault) := do
  let exposure := loan.principalOutstanding
  let vaultScale ← numberExponent vault.assetsTotal vault.numericType
  let lossUnrealized' ← adjustImpreciseNumber vault.numericType vault.lossUnrealized exposure vaultScale

  -- a loss above the vault's unavailable assets would leave it inconsistent
  let gap ← vault.assetsTotal.operator_sub vault.assetsAvailable .to_nearest
  if lossUnrealized'.operator_gt gap then
    return .rejected .tecLIMIT_EXCEEDED

  let vault' ← ({ vault.toRawVault with lossUnrealized := lossUnrealized' } : RawVault).to_lawful
  return .ok vault'

-- Reverse the paper loss an impairment recorded
def Loan.manageUnimpair (loan : Loan) (vault : Vault) : Except Error (LoanResult Vault) := do
  let lossReversed := loan.principalOutstanding
  let vaultScale ← numberExponent vault.assetsTotal vault.numericType
  if vault.lossUnrealized.operator_lt lossReversed then
    return .rejected .tefBAD_LEDGER

  let lossUnrealized' ← adjustImpreciseNumber vault.numericType vault.lossUnrealized lossReversed.operator_neg vaultScale
  let vault' ← ({ vault.toRawVault with lossUnrealized := lossUnrealized' } : RawVault).to_lawful
  return .ok vault'

-- Default a loan: first-loss cover absorbs part of the loss, the rest reduces the vault's AssetsTotal.
def Loan.manageDefault (loan : Loan) (vault : Vault) (broker : LoanBroker) (impaired : Bool)
    : Except Error (LoanResult BrokerVault) := do
  let totalDefaultAmount := loan.principalOutstanding
  let defaultCovered ← defaultCoveredAmount broker totalDefaultAmount vault.numericType loan.loanScale

  -- the vault absorbs the remaining default amount by reducing AssetsTotal
  let vaultDefaultAmount ← totalDefaultAmount.operator_sub defaultCovered .to_nearest
  let vaultScale ← numberExponent vault.assetsTotal vault.numericType
  if vault.assetsTotal.operator_lt vaultDefaultAmount then
    return .rejected .tefBAD_LEDGER

  let vaultDefaultAmount' ← STAmount.roundToNumericType vault.numericType vaultDefaultAmount .downward (some vaultScale)
  let assetsTotal ← vault.assetsTotal.operator_sub vaultDefaultAmount' .to_nearest
  let assetsAvailable' ← vault.assetsAvailable.operator_add defaultCovered .to_nearest

  let assetsTotal' ← dustAdjustedAssetsTotal assetsAvailable' assetsTotal
  if assetsAvailable'.operator_gt assetsTotal' then
    return .rejected .tecINTERNAL

  let debtTotal' ← adjustImpreciseNumber vault.numericType broker.debtTotal totalDefaultAmount.operator_neg vaultScale
  if broker.coverAvailable.operator_lt defaultCovered then
    return .rejected .tefBAD_LEDGER
  let coverAvailable' ← broker.coverAvailable.operator_sub defaultCovered .to_nearest

  -- realize the loss only when the loan was already impaired: its paper loss is now real
  let lossUnrealized' ←
    if impaired then adjustImpreciseNumber vault.numericType vault.lossUnrealized totalDefaultAmount.operator_neg vaultScale
    else pure vault.lossUnrealized

  let rawVault' : RawVault := { vault.toRawVault with
    assetsTotal := assetsTotal'
    assetsAvailable := assetsAvailable'
    lossUnrealized := lossUnrealized'
  }
  let vault' ← rawVault'.to_lawful
  let broker' := { broker with debtTotal := debtTotal', coverAvailable := coverAvailable' }
  return .ok { vaultIdentity := loan.vaultIdentity, vault := vault', broker := broker' }

end XRPL.Model.Lending
