import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.NumericType
import XRPL.Model.Vault.Terminal

open XRPL.Model.Protocol (Number NumericType Error)
open XRPL.Model.SingleAssetVault

-- Raw creation boundary for internal construction/proof consumers. It validates but
-- deliberately does not perform the C++ commit-time asset association pass.
@[export lean_vault_build_raw]
def lean_vault_build_raw (assetsTotal : Number) (assetsAvailable : Number)
    (assetsMaximum : Option Number)
    (numericType : NumericType) (scale : UInt8) (sharesTotal : Number) (lossUnrealized : Number)
    : Except Error Vault :=
  RawVault.to_lawful
    { assetsTotal, assetsAvailable,
      assetsReserved := Number.zero,
      assetsMaximum,
      numericType, scale, sharesTotal, lossUnrealized }

-- Complete C++ VaultCreate boundary: creation is only externally visible after
-- the single terminal association pass, which also handles assetsMaximum.
@[export lean_vault_build]
def lean_vault_build (assetsTotal : Number) (assetsAvailable : Number)
    (assetsMaximum : Option Number)
    (numericType : NumericType) (scale : UInt8) (sharesTotal : Number) (lossUnrealized : Number)
    : Except Error Vault :=
  RawVault.to_lawful_terminal
    { assetsTotal, assetsAvailable,
      assetsReserved := Number.zero,
      assetsMaximum,
      numericType, scale, sharesTotal, lossUnrealized }

@[export lean_vault_assets_total]
def lean_vault_assets_total (v : Vault) : Number := v.assetsTotal
@[export lean_vault_assets_available]
def lean_vault_assets_available (v : Vault) : Number := v.assetsAvailable
@[export lean_vault_assets_maximum]
def lean_vault_assets_maximum (v : Vault) : Option Number := v.assetsMaximum
@[export lean_vault_numeric_type]
def lean_vault_numeric_type (v : Vault) : NumericType := v.numericType
-- 3-way tag: 0 = native (XRP), 1 = int64 (MPT), 2 = fractional (IOU).
@[export lean_vault_numeric_tag]
def lean_vault_numeric_tag (v : Vault) : UInt8 :=
  match v.numericType with
  | .fractional => 2
  | .integral maxValue _ _ _ => if maxValue == 100000000000000000 then 0 else 1
@[export lean_vault_scale]
def lean_vault_scale (v : Vault) : UInt8 := v.scale
@[export lean_vault_shares_total]
def lean_vault_shares_total (v : Vault) : Number := v.sharesTotal
@[export lean_vault_loss_unrealized]
def lean_vault_loss_unrealized (v : Vault) : Number := v.lossUnrealized
