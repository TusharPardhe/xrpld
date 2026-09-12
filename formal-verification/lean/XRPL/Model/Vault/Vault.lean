import XRPL.Model.Protocol.Number
import XRPL.Model.Protocol.STAmount
import XRPL.Model.Protocol.TER

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- The vault tracks only the asset's `numericType` (integral vs fractional), not its account or
-- currency. Shares are always integral (an MPT), so they need no field.
structure RawVault where
  assetsTotal : Number
  assetsAvailable : Number
  assetsReserved : Number
  assetsMaximum : Option Number
  numericType : NumericType
  scale : UInt8
  sharesTotal : Number
  lossUnrealized : Number

-- Detect an overflow error surfaced by arithmetic ops.
def isOverflow (e : Error) : Bool := match e with | .overflow => true | _ => false

/-- Representation well-formed of the raw record. The per-issuance shares
bound (`OutstandingAmount ≤ MaximumAmount`) is not stated here: the issuance's
`MaximumAmount` is not part of this record. -/
structure RawVault.WF (rv : RawVault) : Prop where
  assetsTotal_norm : rv.assetsTotal.isNormalized
  assetsAvailable_norm : rv.assetsAvailable.isNormalized
  -- `sfAssetsReserved` is also an asset-valued SLE field and is serialized by
  -- the same `associateAsset` pass; retaining its normalization is required
  -- before any raw transition may be revalidated.
  assetsReserved_norm : rv.assetsReserved.isNormalized
  assetsMaximum_norm : ∀ m ∈ rv.assetsMaximum, m.isNormalized
  sharesTotal_norm : rv.sharesTotal.isNormalized
  lossUnrealized_norm : rv.lossUnrealized.isNormalized
  sharesTotal_nonneg : 0 ≤ rv.sharesTotal.toRat
  sharesTotal_int : rv.sharesTotal.toRat.den = 1
  scale_integral : rv.numericType.isIntegral = true → rv.scale = 0
  scale_le : rv.scale.toNat ≤ 18
  -- `assetsTotal - assetsAvailable` must be computable, so overflow doesn't happen
  assetsTotal_sub_ok : ∃ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d

/-- Associate one modeled `STNumber` with an asset. The final equality check is
an executable postcondition of the C++ `roundToAsset` contract: a successfully
associated `Number` must survive a second asset conversion unchanged. It makes
that postcondition explicit at the model boundary instead of silently retaining
an unrepresentable value. -/
def RawVault.associateAssetNumber (nt : NumericType) (value : Number) : Except Error Number := do
  let rounded ← STAmount.roundToNumericType nt value .to_nearest
  let stable ← STAmount.equalAfterNumberConvert nt rounded
  if stable then return rounded else throw .notLawful

/-- Model the `STNumber::associateAsset` pass run after a Vault transaction.

The C++ helper visits every present `kSmdNeedsAsset` field and applies
`roundToAsset(asset, value)`. `RawVault` keeps the asset identity as
`numericType`, so the modeled pass uses the same nearest-mode `STAmount →
Number` round trip for every modeled asset field: total, available, reserved,
unrealized loss, and the optional maximum. The share count and vault metadata
are deliberately not rewritten. -/
def RawVault.associateAsset (rv : RawVault) : Except Error RawVault := do
  let assetsTotal ← RawVault.associateAssetNumber rv.numericType rv.assetsTotal
  let assetsAvailable ← RawVault.associateAssetNumber rv.numericType rv.assetsAvailable
  let assetsReserved ← RawVault.associateAssetNumber rv.numericType rv.assetsReserved
  let lossUnrealized ← RawVault.associateAssetNumber rv.numericType rv.lossUnrealized
  let assetsMaximum ←
    match rv.assetsMaximum with
    | none => pure none
    | some maximum => do
      let rounded ← RawVault.associateAssetNumber rv.numericType maximum
      pure (some rounded)
  return { rv with assetsTotal, assetsAvailable, assetsReserved, assetsMaximum, lossUnrealized }

/-- The vault invariant (XLS-0065 §4.5) stated with the modeled `Number` operators -/
structure RawVault.Valid (rv : RawVault) : Prop where
  assetsTotal_nonneg : Number.zero.operator_le rv.assetsTotal = true
  assetsAvailable_nonneg : Number.zero.operator_le rv.assetsAvailable = true
  assetsAvailable_le : rv.assetsAvailable.operator_le rv.assetsTotal = true
  assetsMaximum_pos : ∀ m ∈ rv.assetsMaximum, Number.zero.operator_lt m = true
  empty_shares : rv.sharesTotal = Number.zero →
    rv.assetsTotal = Number.zero ∧ rv.assetsAvailable = Number.zero
  cap : ∀ m ∈ rv.assetsMaximum, rv.assetsTotal.operator_le m = true
  lossUnrealized_nonneg : Number.zero.operator_le rv.lossUnrealized = true
  lossUnrealized_le : ∀ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d →
    rv.lossUnrealized.operator_le d = true
  withdraw_nav_nonneg : rv.lossUnrealized.operator_le rv.assetsTotal = true

-- Deciding `WF` reduces to the conjunction of its clauses, each decidable above.
instance (rv : RawVault) : Decidable rv.WF :=
  decidable_of_iff
    (rv.assetsTotal.isNormalized ∧ rv.assetsAvailable.isNormalized ∧
      rv.assetsReserved.isNormalized ∧ (∀ m ∈ rv.assetsMaximum, m.isNormalized) ∧
      rv.sharesTotal.isNormalized ∧ rv.lossUnrealized.isNormalized ∧
      0 ≤ rv.sharesTotal.toRat ∧ rv.sharesTotal.toRat.den = 1 ∧
      (rv.numericType.isIntegral = true → rv.scale = 0) ∧ rv.scale.toNat ≤ 18 ∧
      (∃ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩⟩

-- Deciding `Valid` reduces to the conjunction of its clauses, each decidable above.
instance (rv : RawVault) : Decidable rv.Valid :=
  decidable_of_iff
    (Number.zero.operator_le rv.assetsTotal = true ∧
      Number.zero.operator_le rv.assetsAvailable = true ∧
      rv.assetsAvailable.operator_le rv.assetsTotal = true ∧
      (∀ m ∈ rv.assetsMaximum, Number.zero.operator_lt m = true) ∧
      (rv.sharesTotal = Number.zero → rv.assetsTotal = Number.zero ∧ rv.assetsAvailable = Number.zero) ∧
      (∀ m ∈ rv.assetsMaximum, rv.assetsTotal.operator_le m = true) ∧
      Number.zero.operator_le rv.lossUnrealized = true ∧
      (∀ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d →
        rv.lossUnrealized.operator_le d = true) ∧
      rv.lossUnrealized.operator_le rv.assetsTotal = true)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

/-- A `Vault` extends `RawVault` with proofs that the representation is
well-formed (`wf`) and satisfies the invariant (`valid`, in Number operators). -/
structure Vault extends RawVault where
  wf : toRawVault.WF
  valid : toRawVault.Valid

/-- Apply the total modeled `associateAsset` pass and revalidate the resulting
ledger state. A rounding or lawfulness failure is explicit; because the model
is pure, either failure leaves the input vault unchanged. -/
def Vault.associateAsset (v : Vault) : Except Error Vault := do
  let rv ← RawVault.associateAsset v.toRawVault
  if h : rv.WF ∧ rv.Valid then .ok { toRawVault := rv, wf := h.1, valid := h.2 }
  else .error .notLawful

/-- Build a lawful vault from a raw vault, or reject. -/
def RawVault.to_lawful (rv : RawVault) : Except Error Vault :=
  if h : rv.WF ∧ rv.Valid then .ok { toRawVault := rv, wf := h.1, valid := h.2 } else .error .notLawful

def Vault.isInsolvent (v : Vault) : Bool :=
  v.assetsTotal.mantissa_ = 0 && v.sharesTotal.signum = 1

def Vault.assetsRounded (v : Vault) : Prop :=
  STAmount.isRounded v.numericType v.assetsTotal ∨
  STAmount.isRounded v.numericType v.assetsAvailable ∨
  STAmount.isRounded v.numericType v.assetsReserved ∨
  STAmount.isRounded v.numericType v.lossUnrealized ∨
  ∃ m ∈ v.assetsMaximum, STAmount.isRounded v.numericType m

end XRPL.Model.SingleAssetVault
