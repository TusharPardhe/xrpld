import XRPL.FFI.Lending.Wire.VaultBroker
import XRPL.Model.Vault.Terminal
import XRPL.Model.Vault.VaultDelete
import XRPL.Model.Vault.VaultSet

/-! # Canonical Vault wire surface

Vault uses the proven Lending `LWAB` envelope and primitive codecs.  It does
not introduce a second Vault schema: all `Number`, `STAmount`, `RawVault`, and
lawful `Vault` fields are encoded by the shared Lending wire implementation.
The distinct request/result records below preserve the raw/terminal boundary
and every modelled result field.
-/
namespace XRPL.FFI.Vault.Wire

open XRPL.FFI.Lending.Wire
open XRPL.Model.Protocol
open XRPL.Model.Result
open XRPL.Model.SingleAssetVault

/-- A model error is part of the result algebra, not a decoder failure. -/
def encodeResult (encode : α → Except DecodeError ByteArray) : Except Error α → Except DecodeError ByteArray
  | .ok value => return one 0 ++ (← encode value)
  | .error error => .ok (one 1 ++ encodeError error)

def readResult (decode : Cursor → Except DecodeError (α × Cursor))
    (c : Cursor) : Except DecodeError (Except Error α × Cursor) := do
  let (tag, c) ← readU8 c
  match tag with
  | 0 => let (value, c) ← decode c; pure (.ok value, c)
  | 1 => let (error, c) ← readError c; pure (.error error, c)
  | _ => .error (.badTag 0 tag)

def encodeRoundingResult : RoundingResult → Except DecodeError ByteArray
  | .rounded amount => return one 0 ++ (← encodeSTAmount amount)
  | .rejected ter => .ok (one 1 ++ encodeTER ter)

def readRoundingResult (c : Cursor) : Except DecodeError (RoundingResult × Cursor) := do
  let (tag, c) ← readU8 c
  match tag with
  | 0 => let (amount, c) ← readSTAmount c; pure (.rounded amount, c)
  | 1 => let (ter, c) ← readTER c; pure (.rejected ter, c)
  | _ => .error (.badTag 0 tag)

def encodeDepositResult (x : DepositResult) : Except DecodeError ByteArray :=
  return (← encodeOption (fun ter => .ok (encodeTER ter)) x.error) ++ (← encodeVault x.vault') ++
    (← encodeSTAmount x.amountDeposit') ++ (← encodeSTAmount x.sharesIssued)

def readDepositResult (c : Cursor) : Except DecodeError (DepositResult × Cursor) := do
  let (error, c) ← readOption readTER c
  let (vault', c) ← readVault c
  let (amountDeposit', c) ← readSTAmount c
  let (sharesIssued, c) ← readSTAmount c
  pure ({ error, vault', amountDeposit', sharesIssued }, c)

def encodeWithdrawAmount : WithdrawAmount → Except DecodeError ByteArray
  | .vaultAssets amount => return one 0 ++ (← encodeSTAmount amount)
  | .vaultShares amount => return one 1 ++ (← encodeSTAmount amount)

def readWithdrawAmount (c : Cursor) : Except DecodeError (WithdrawAmount × Cursor) := do
  let (tag, c) ← readU8 c
  let (amount, c) ← readSTAmount c
  match tag with
  | 0 => pure (.vaultAssets amount, c)
  | 1 => pure (.vaultShares amount, c)
  | _ => .error (.badTag 0 tag)

def encodeWithdrawResult (x : WithdrawResult) : Except DecodeError ByteArray :=
  return (← encodeOption (fun ter => .ok (encodeTER ter)) x.error) ++ (← encodeVault x.vault') ++
    (← encodeSTAmount x.assets') ++ (← encodeSTAmount x.sharesBurned)

def readWithdrawResult (c : Cursor) : Except DecodeError (WithdrawResult × Cursor) := do
  let (error, c) ← readOption readTER c
  let (vault', c) ← readVault c
  let (assets', c) ← readSTAmount c
  let (sharesBurned, c) ← readSTAmount c
  pure ({ error, vault', assets', sharesBurned }, c)

def encodeClawbackResult (x : ClawbackResult) : Except DecodeError ByteArray :=
  return (← encodeOption (fun ter => .ok (encodeTER ter)) x.error) ++ (← encodeVault x.vault') ++
    (← encodeSTAmount x.assetsRecovered) ++ (← encodeSTAmount x.sharesDestroyed)

def readClawbackResult (c : Cursor) : Except DecodeError (ClawbackResult × Cursor) := do
  let (error, c) ← readOption readTER c
  let (vault', c) ← readVault c
  let (assetsRecovered, c) ← readSTAmount c
  let (sharesDestroyed, c) ← readSTAmount c
  pure ({ error, vault', assetsRecovered, sharesDestroyed }, c)

def encodeCanBurnResult : CanBurnSharesResult → Except DecodeError ByteArray
  | .assets amount => return one 0 ++ (← encodeSTAmount amount)
  | .error ter => .ok (one 1 ++ encodeTER ter)

def readCanBurnResult (c : Cursor) : Except DecodeError (CanBurnSharesResult × Cursor) := do
  let (tag, c) ← readU8 c
  match tag with
  | 0 => let (amount, c) ← readSTAmount c; pure (.assets amount, c)
  | 1 => let (ter, c) ← readTER c; pure (.error ter, c)
  | _ => .error (.badTag 0 tag)

/-- One complete construction request serves both explicitly raw and terminal
construction routes; the route tag keeps the public distinction on the wire. -/
structure BuildRequest where
  assetsTotal : Number
  assetsAvailable : Number
  assetsMaximum : Option Number
  numericType : NumericType
  scale : UInt8
  sharesTotal : Number
  lossUnrealized : Number

def encodeBuildRequest (x : BuildRequest) : Except DecodeError ByteArray :=
  return (← encodeNumber x.assetsTotal) ++ (← encodeNumber x.assetsAvailable) ++
    (← encodeOption encodeNumber x.assetsMaximum) ++ (← encodeNumericType x.numericType) ++
    encodeU8 x.scale ++ (← encodeNumber x.sharesTotal) ++ (← encodeNumber x.lossUnrealized)

def readBuildRequest (c : Cursor) : Except DecodeError (BuildRequest × Cursor) := do
  let (assetsTotal, c) ← readNumber c; let (assetsAvailable, c) ← readNumber c
  let (assetsMaximum, c) ← readOption readNumber c; let (numericType, c) ← readNumericType c
  let (scale, c) ← readU8 c; let (sharesTotal, c) ← readNumber c; let (lossUnrealized, c) ← readNumber c
  pure ({ assetsTotal, assetsAvailable, assetsMaximum, numericType, scale, sharesTotal, lossUnrealized }, c)

structure AmountRequest where
  vault : Vault
  amount : STAmount

structure DonationRequest where
  vault : Vault
  amount : STAmount
  donation : Bool

structure WithdrawRequest where
  vault : Vault
  amount : WithdrawAmount
  waiveUnrealizedLoss : Bool

structure ClawbackRequest where
  vault : Vault
  assets : STAmount
  holderShares : STAmount

structure SetRequest where
  vault : Vault
  maximum : Number

def encodeAmountRequest (x : AmountRequest) : Except DecodeError ByteArray := return (← encodeVault x.vault) ++ (← encodeSTAmount x.amount)
def readAmountRequest (c : Cursor) : Except DecodeError (AmountRequest × Cursor) := do
  let (vault, c) ← readVault c; let (amount, c) ← readSTAmount c; pure ({ vault, amount }, c)
def encodeDonationRequest (x : DonationRequest) : Except DecodeError ByteArray := return (← encodeAmountRequest { vault := x.vault, amount := x.amount }) ++ encodeBool x.donation
def readDonationRequest (c : Cursor) : Except DecodeError (DonationRequest × Cursor) := do
  let (base, c) ← readAmountRequest c; let (donation, c) ← readBool c; pure ({ vault := base.vault, amount := base.amount, donation }, c)
def encodeWithdrawRequest (x : WithdrawRequest) : Except DecodeError ByteArray := return (← encodeVault x.vault) ++ (← encodeWithdrawAmount x.amount) ++ encodeBool x.waiveUnrealizedLoss
def readWithdrawRequest (c : Cursor) : Except DecodeError (WithdrawRequest × Cursor) := do
  let (vault, c) ← readVault c; let (amount, c) ← readWithdrawAmount c; let (waiveUnrealizedLoss, c) ← readBool c
  pure ({ vault, amount, waiveUnrealizedLoss }, c)
def encodeClawbackRequest (x : ClawbackRequest) : Except DecodeError ByteArray := return (← encodeVault x.vault) ++ (← encodeSTAmount x.assets) ++ (← encodeSTAmount x.holderShares)
def readClawbackRequest (c : Cursor) : Except DecodeError (ClawbackRequest × Cursor) := do
  let (vault, c) ← readVault c; let (assets, c) ← readSTAmount c; let (holderShares, c) ← readSTAmount c
  pure ({ vault, assets, holderShares }, c)
def encodeSetRequest (x : SetRequest) : Except DecodeError ByteArray := return (← encodeVault x.vault) ++ (← encodeNumber x.maximum)
def readSetRequest (c : Cursor) : Except DecodeError (SetRequest × Cursor) := do
  let (vault, c) ← readVault c; let (maximum, c) ← readNumber c; pure ({ vault, maximum }, c)

/-- Version-frame one request and exact response. Decoder errors remain exact
`DecodeError` payloads rather than becoming model errors. -/
def finish (tag : UInt8) (payload : Except DecodeError ByteArray) : ByteArray :=
  match encodeEnvelope tag (match payload with | .ok bytes => one 0 ++ bytes | .error error => one 1 ++ encodeDecodeError error) with
  | .ok bytes => bytes | .error _ => ByteArray.empty

def run (requestTag responseTag : UInt8) (decode : Cursor → Except DecodeError (α × Cursor))
    (encode : β → Except DecodeError ByteArray) (apply : α → β) (input : ByteArray) : ByteArray :=
  match decodeWhole requestTag decode input with
  | .error error => finish responseTag (.error error)
  | .ok request => finish responseTag (encode (apply request))

def rawBuild (r : BuildRequest) : Except Error Vault :=
  let raw : RawVault := {
    assetsTotal := r.assetsTotal
    assetsAvailable := r.assetsAvailable
    assetsReserved := Number.zero
    assetsMaximum := r.assetsMaximum
    numericType := r.numericType
    scale := r.scale
    sharesTotal := r.sharesTotal
    lossUnrealized := r.lossUnrealized }
  RawVault.to_lawful raw

def terminalBuild (r : BuildRequest) : Except Error Vault :=
  let raw : RawVault := {
    assetsTotal := r.assetsTotal
    assetsAvailable := r.assetsAvailable
    assetsReserved := Number.zero
    assetsMaximum := r.assetsMaximum
    numericType := r.numericType
    scale := r.scale
    sharesTotal := r.sharesTotal
    lossUnrealized := r.lossUnrealized }
  RawVault.to_lawful_terminal raw

def encodeVaultResult := encodeResult encodeVault
def encodeAmountResult := encodeResult encodeSTAmount
def encodeDepositResultWire := encodeResult encodeDepositResult
def encodeWithdrawResultWire := encodeResult encodeWithdrawResult
def encodeClawbackResultWire := encodeResult encodeClawbackResult
def encodeCanBurnResultWire := encodeResult encodeCanBurnResult

@[export lean_vault_raw_build_wire] def rawBuildWire := run 1 129 readBuildRequest encodeVaultResult rawBuild
@[export lean_vault_build_wire] def buildWire := run 2 130 readBuildRequest encodeVaultResult terminalBuild
@[export lean_vault_round_deposit_wire] def roundDepositWire := run 3 131 readAmountRequest (encodeResult encodeRoundingResult) fun r => r.vault.roundedDepositAmount r.amount
@[export lean_vault_deposit_wire] def depositWire := run 4 132 readDonationRequest encodeDepositResultWire fun r => r.vault.deposit_terminal r.amount r.donation
@[export lean_vault_shares_to_assets_withdraw_wire] def sharesToAssetsWithdrawWire := run 5 133 readWithdrawRequest encodeAmountResult fun r =>
  match r.amount with | .vaultShares shares => r.vault.sharesToAssetsWithdraw shares r.waiveUnrealizedLoss | .vaultAssets assets => r.vault.sharesToAssetsWithdraw assets r.waiveUnrealizedLoss
@[export lean_vault_withdraw_wire] def withdrawWire := run 6 134 readWithdrawRequest encodeWithdrawResultWire fun r => r.vault.withdraw_terminal r.amount r.waiveUnrealizedLoss
@[export lean_vault_clawback_wire] def clawbackWire := run 7 135 readClawbackRequest encodeClawbackResultWire fun r => r.vault.clawback_terminal r.assets r.holderShares
@[export lean_vault_burn_shares_raw_wire] def burnRawWire := run 8 136 readAmountRequest encodeVaultResult fun r => r.vault.burnShares r.amount
@[export lean_vault_burn_shares_wire] def burnWire := run 9 137 readAmountRequest encodeVaultResult fun r => r.vault.burnShares_terminal r.amount
@[export lean_vault_can_burn_shares_wire] def canBurnWire := run 10 138 readVault encodeCanBurnResultWire Vault.canBurnShares
@[export lean_vault_can_delete_wire] def canDeleteWire := run 11 139 readVault (fun ter => .ok (encodeTER ter)) Vault.canVaultDelete
@[export lean_vault_can_set_wire] def canSetWire := run 12 140 readSetRequest (fun ter => .ok (encodeTER ter)) fun r => r.vault.canVaultSet r.maximum

end XRPL.FFI.Vault.Wire
