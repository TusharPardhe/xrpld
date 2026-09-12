import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.Rounding
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault
import XRPL.Model.Vault.VaultWithdraw

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

structure ComputeClawbackResult where
  error : Option TER
  assetsRecovered : STAmount
  sharesDestroyed : STAmount

structure ClawbackResult where
  error : Option TER
  vault' : Vault
  assetsRecovered : STAmount
  sharesDestroyed : STAmount

-- A rejection changes nothing and reports nothing: the vault is returned
-- unchanged and both amount fields are zero.
def ClawbackResult.rejected (v : Vault) (ter : TER) : ClawbackResult :=
  ⟨some ter, v, STAmount.zero v.numericType, STAmount.zero .int64⟩

def assetsToSharesClawback (v : Vault) (assets holderShares : STAmount) : Except Error STAmount := do
  if assets.isZero then
    -- zero means destroy "all" holder shares
    return holderShares
  assetsToSharesWithdraw v assets true false

def computeClawback (v : Vault) (assets holderShares : STAmount) : Except Error ComputeClawbackResult := do
  let result : ComputeClawbackResult := ⟨none, STAmount.zero v.numericType, STAmount.zero .int64⟩
  if assets.negative then
    return {result with error := some .tecINTERNAL}
  try
    let mut sharesDestroyed ← assetsToSharesClawback v assets holderShares
    let mut assetsRecovered ← v.sharesToAssetsWithdraw sharesDestroyed false

    let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
    if assetsRecoveredNumber.operator_gt v.assetsAvailable then
      assetsRecovered ← STAmount.ofNumber v.numericType v.assetsAvailable .to_nearest
      sharesDestroyed ← assetsToSharesWithdraw v assetsRecovered true false
      assetsRecovered ← v.sharesToAssetsWithdraw sharesDestroyed false

      let assetsRecoveredNumber ← assetsRecovered.toNumber .to_nearest
      if assetsRecoveredNumber.operator_gt v.assetsAvailable then
        return {result with error := some .tecINTERNAL}

    assetsRecovered ← clampToSumExponent v.assetsTotal assetsRecovered.operator_neg
    if ← assetsRecovered.isFractionalNonPositive then
      return {result with error := some .tecPRECISION_LOSS}
    return {result with assetsRecovered := assetsRecovered, sharesDestroyed := sharesDestroyed}
  catch e =>
    if isOverflow e then
      return ⟨.some .tecPATH_DRY, STAmount.zero v.numericType, STAmount.zero .int64⟩
    else
      throw e


/-- Raw/pre-association clawback kernel. It deliberately stops before the
commit-time `associateAsset` pass; use `Vault.clawback_terminal` for complete
transaction execution. -/
def Vault.clawback (v : Vault) (assets holderShares : STAmount) : Except Error ClawbackResult := do
  let vault := v.toRawVault
  let result ← computeClawback v assets holderShares
  if result.error.isSome then
    return ⟨result.error, v, STAmount.zero v.numericType, STAmount.zero .int64⟩

  if result.sharesDestroyed.isZero then
    return .rejected v .tecPRECISION_LOSS

  let sharesDestroyedNumber ← result.sharesDestroyed.toNumber .to_nearest
  let assetsRecoveredNumber ← result.assetsRecovered.toNumber .to_nearest
  let assetsTotal' ← vault.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest

  let assetsTotalRounded ← STAmount.ofNumber vault.numericType vault.assetsTotal .to_nearest
  let assetsTotalRounded' ← STAmount.ofNumber vault.numericType assetsTotal' .to_nearest
  if assetsRecoveredNumber.mantissa_ != 0 && assetsTotalRounded.operator_eq assetsTotalRounded' then
    return .rejected v .tecPRECISION_LOSS

  let vault' := {
    vault with
      sharesTotal := ← vault.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest
      assetsAvailable := ← vault.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest
      assetsTotal := assetsTotal'
  }
  -- re-validate the new state into a Vault. Clawback-all on a fractional vault can leave dust
  -- (sharesTotal=0, assetsTotal>0), which fails empty_shares, so this can error.
  let v' ← vault'.to_lawful
  return ⟨none, v', result.assetsRecovered, result.sharesDestroyed⟩

end XRPL.Model.SingleAssetVault
