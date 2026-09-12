import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.TER
import XRPL.Model.Vault.Vault

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

def Vault.canVaultSet (v : Vault) (assetsMaximum : Number) : TER :=
  -- check from VaultSet::doApply
  if assetsMaximum.operator_ne Number.zero && assetsMaximum.operator_lt v.assetsTotal then
    .tecLIMIT_EXCEEDED
  else
    .tesSUCCESS

end XRPL.Model.SingleAssetVault
