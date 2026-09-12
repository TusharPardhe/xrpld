import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Vault.VaultSet

open XRPL.Model.Protocol (Number NumericType Error)
open XRPL.Model.SingleAssetVault

@[export lean_can_vault_set]
def lean_can_vault_set (v : Vault) (maximum : Number) : Int32 :=
  (v.canVaultSet maximum).code
