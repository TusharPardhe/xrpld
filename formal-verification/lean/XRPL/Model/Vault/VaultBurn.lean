import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

inductive CanBurnSharesResult where
  | error (error : TER)
  | assets (amount : STAmount)

-- The owner may force-burn shares only when shares are outstanding while both
-- asset totals are zero. On success returns the whole share total.
def Vault.canBurnShares (v : Vault) : Except Error CanBurnSharesResult := do
  let vault := v.toRawVault
  if vault.sharesTotal.mantissa_ == 0 || (vault.assetsTotal.mantissa_ != 0 || vault.assetsAvailable.mantissa_ != 0) then do
    return .error .tecNO_PERMISSION
  return .assets (← STAmount.ofNumber .int64 vault.sharesTotal .to_nearest)

def Vault.burnShares (v : Vault) (sharesDestroyed : STAmount) : Except Error Vault := do
  let vault := v.toRawVault
  let sharesDestroyedNumber ← sharesDestroyed.toNumber .to_nearest
  let vault' := {
    vault with
      sharesTotal := ← vault.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest
  }
  vault'.to_lawful

end XRPL.Model.SingleAssetVault
