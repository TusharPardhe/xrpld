import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Result
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Result

-- model of `roundToVaultScale` from xrpld
def roundToVaultExponent (amountDeposit : STAmount) (assetsTotal : Number) : Except Error STAmount := do
  if amountDeposit.integral then
    return amountDeposit
  let postExponent ← postSumExponent assetsTotal amountDeposit
  STAmount.roundToExponent amountDeposit postExponent .downward

/-- The preclaim check on a deposit amount. An IOU vault cannot track digits
below the exponent its `assetsTotal` will have after the deposit, so any such
digits in `amountDeposit` are dropped before the deposit runs (integral assets
pass through unchanged). Returns the amount the deposit will actually use, or
`tecPRECISION_LOSS` when nothing of it survives. An `Error` from
`roundToVaultExponent` (e.g. overflow) propagates through the outer `Except`
(a C++ throw). -/
def Vault.roundedDepositAmount (v : Vault) (amountDeposit : STAmount)
    : Except Error RoundingResult := do
  let vault := v.toRawVault
  let roundedAmount ← roundToVaultExponent amountDeposit vault.assetsTotal
  if roundedAmount.isZero then
    return .rejected .tecPRECISION_LOSS
  return .rounded roundedAmount

structure DepositResult where
  error : Option TER
  vault' : Vault
  amountDeposit' : STAmount
  sharesIssued : STAmount

-- A rejection changes nothing and reports nothing: the vault is returned
-- unchanged and both amount fields are zero.
def DepositResult.rejected (v : Vault) (ter : TER) : DepositResult :=
  ⟨some ter, v, STAmount.zero v.numericType, STAmount.zero .int64⟩

def assetsToSharesDeposit (v : Vault) (amountDeposit : STAmount) : Except Error STAmount := do
  if v.assetsTotal.mantissa_ = 0 then
    let sharesNumber ← Number.normalized false amountDeposit.mantissa (amountDeposit.exponent + v.scale.toNat) largeRange.min largeRange.max .to_nearest
    let sharesNumber ← sharesNumber.truncate
    let shares ← STAmount.ofNumber .int64 sharesNumber .to_nearest
    return shares
  let amountDepositNumber ← amountDeposit.toNumber .to_nearest
  let sharesAssets ← v.sharesTotal.operator_mul amountDepositNumber .to_nearest
  let sharesNumber ← sharesAssets.operator_div v.assetsTotal .to_nearest
  let sharesNumber ← sharesNumber.truncate
  let shares ← STAmount.ofNumber .int64 sharesNumber .to_nearest
  return shares

def sharesToAssetsDeposit (v : Vault) (shares : STAmount) : Except Error STAmount := do
  if v.assetsTotal.mantissa_ = 0 then
    let assets ← STAmount.checked v.numericType shares.mantissa (shares.exponent - v.scale.toNat) false .to_nearest
    return assets
  let sharesNumber ← shares.toNumber .to_nearest
  let assetsShares ← v.assetsTotal.operator_mul sharesNumber .to_nearest
  let amountDepositNumber ← assetsShares.operator_div v.sharesTotal .to_nearest
  -- (waiting the C++ fix) round the charge up so a depositor never pays less than the issued shares are worth
  let amountDeposit ← STAmount.ofNumber v.numericType amountDepositNumber .upward
  return amountDeposit

inductive ComputeDepositResult where
  | error (error : TER)
  | success (assetDeposited : STAmount) (sharesCreated : STAmount)

def computeDeposit (v : Vault) (amountDeposit : STAmount) : Except Error ComputeDepositResult := do
  try
    let shares ← assetsToSharesDeposit v amountDeposit
    if shares.isZero then
      return .error .tecPRECISION_LOSS
    let amountDeposit' ← sharesToAssetsDeposit v shares
    if ← amountDeposit'.operator_gt amountDeposit then
      return .error .tecINTERNAL
    return .success amountDeposit' shares
  catch e =>
    if isOverflow e then
      return .error .tecPATH_DRY
    else
      throw e

/-- Raw/pre-association deposit kernel. It deliberately stops before the C++
commit-time `associateAsset` pass; use `Vault.deposit_terminal` for complete
transaction execution. -/
def Vault.deposit (v : Vault) (amountDeposit : STAmount) (isDonation : Bool) : Except Error DepositResult := do
  let vault := v.toRawVault
  let amount ← roundToVaultExponent amountDeposit vault.assetsTotal

  if amount.isZero then
    return .rejected v .tecINTERNAL

  if isDonation && vault.sharesTotal.mantissa_ == 0 then
    return .rejected v .tecNO_PERMISSION

  if v.isInsolvent && !isDonation then
    return .rejected v .tecLOCKED

  let mut assetDeposited := amount
  let mut sharesCreated := STAmount.zero .int64
  if !isDonation then
    match ← computeDeposit v amount with
    | .error e => return .rejected v e
    | .success assets shares =>
      assetDeposited ← clampToSumExponent vault.assetsTotal assets
      if ← assetDeposited.isFractionalNonPositive then
        return .rejected v .tecPRECISION_LOSS
      sharesCreated := shares

  let assetDepositedNumber ← assetDeposited.toNumber .to_nearest
  let vault' : RawVault := {
    vault with
    assetsTotal := ← vault.assetsTotal.operator_add assetDepositedNumber .to_nearest
    assetsAvailable := ← vault.assetsAvailable.operator_add assetDepositedNumber .to_nearest
    sharesTotal := ← vault.sharesTotal.operator_add (← sharesCreated.toNumber .to_nearest) .to_nearest
  }

  -- C++: if (maximum != 0 && assetsTotal > maximum)
  let assetsMaximum := vault.assetsMaximum.getD Number.zero
  if assetsMaximum.operator_ne Number.zero && vault'.assetsTotal.operator_gt assetsMaximum then
    return .rejected v .tecLIMIT_EXCEEDED

  let v' ← vault'.to_lawful
  return ⟨none, v', assetDeposited, sharesCreated⟩

end XRPL.Model.SingleAssetVault
