import XRPL.Model.Vault.Vault
import XRPL.Model.Lending.AssetPool

namespace XRPL.Model.Lending1_1

open XRPL.Model.Lending (AssetPool)
open XRPL.Model.SingleAssetVault (Vault)

instance : AssetPool Vault where
  assets := (·.assetsTotal)
  numericType := (·.numericType)

end XRPL.Model.Lending1_1
