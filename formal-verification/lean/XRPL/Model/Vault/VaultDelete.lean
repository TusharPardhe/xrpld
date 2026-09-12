import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- Checks from VaultDelete::preclaim, in C++ order.
def Vault.canVaultDelete (v : Vault) : TER :=
  if v.assetsAvailable.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else if v.assetsTotal.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else if v.sharesTotal.operator_ne Number.zero then
    .tecHAS_OBLIGATIONS
  else
    .tesSUCCESS

end XRPL.Model.SingleAssetVault
