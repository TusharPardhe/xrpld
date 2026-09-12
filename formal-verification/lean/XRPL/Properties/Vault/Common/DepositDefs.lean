import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Protocol.STAmount.Common.DiscreteDefs
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing

/-! # Exact-arithmetic reference values for `Vault.deposit`

The ideal (unrounded) exchange quantities and the relative-error budget the
`Vault.deposit` accuracy headlines are stated against. Kept in `Common` so both
the headline file and its proof files can see them. -/

namespace XRPL.Model.Protocol

/-- A deposit-ready amount: stored canonically for its representation kind, with
an integral type's carried bound within `maxRep` (true of `native` and `int64`).
Exactly the precondition under which `STAmount.toNumber` is value-exact. -/
def STAmount.Canonical (s : STAmount) : Prop :=
  (s.integral = true → s.IntegralCanonical ∧ s.mNumericType.maxValue.toNat ≤ maxRep.toNat) ∧
  (s.integral = false → s.IOUCanonical)

end XRPL.Model.Protocol

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Relative error budget of the `Number` stages of the deposit exchange
computations. Each stage is correctly rounded within `10 / (2 ^ 63 + 2)` and no
computation below chains more than three stages, so `10 ^ (-17)` covers every
composition. -/
def depositε : ℚ := (10 : ℚ) ^ (-17 : ℤ)

/-- Net asset value used to price a deposit: `assetsTotal`.
Unrealized loss is not subtracted when depositing. -/
def RawVault.depositNav (rv : RawVault) : ℚ :=
  rv.toExact.assetsTotal

/-- The exact share amount for a deposit, before any rounding. The XLS-0065
exchange formula: an empty vault issues `amount * 10 ^ scale` shares, otherwise
`sharesTotal * amount / nav`. -/
def RawVault.idealSharesDeposit (rv : RawVault) (amount : ℚ) : ℚ :=
  if rv.toExact.assetsTotal = 0 then amount * (10 : ℚ) ^ rv.scale.toNat
  else rv.toExact.sharesTotal * amount / rv.depositNav

/-- The exact `amountDeposit'` for issuing `shares`, before any rounding. The
XLS-0065 exchange formula: an empty vault takes `shares / 10 ^ scale`, otherwise
`nav * shares / sharesTotal`. -/
def RawVault.idealChargeDeposit (rv : RawVault) (shares : ℚ) : ℚ :=
  if rv.toExact.assetsTotal = 0 then shares / (10 : ℚ) ^ rv.scale.toNat
  else rv.depositNav * shares / rv.toExact.sharesTotal

end XRPL.Model.SingleAssetVault
