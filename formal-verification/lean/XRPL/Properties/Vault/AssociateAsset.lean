import XRPL.Model.Vault.Vault
import XRPL.Properties.Vault.Common.Reduction

/-! # Vault `associateAsset`

`STNumber::associateAsset` associates the vault asset with every present
`kSmdNeedsAsset` field and immediately applies `roundToAsset`.  The modeled
operation lives at the raw-vault boundary and applies that same total pass to
all five modeled asset fields: `assetsTotal`, `assetsAvailable`,
`assetsReserved`, `lossUnrealized`, and optional `assetsMaximum`.

The operation is pure and returns an `Except`: an error therefore has no
post-state.  On success it leaves all non-asset vault data unchanged and every
returned asset `Number` is explicitly checked to survive a further asset
conversion unchanged. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

private theorem RawVault.associateAssetNumber_unrounded (nt : NumericType)
    (value result : Number)
    (hok : RawVault.associateAssetNumber nt value = .ok result) :
    STAmount.isRounded nt result = false := by
  unfold RawVault.associateAssetNumber at hok
  obtain ⟨rounded, hround, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨stable, hstable, hok⟩ := bind_ok_peel _ _ _ hok
  cases hs : stable with
  | false => simp [hs] at hok
  | true =>
    simp [hs] at hok
    change Except.ok rounded = Except.ok result at hok
    have hresult : rounded = result := Except.ok.inj hok
    rw [← hresult]
    unfold STAmount.isRounded
    rw [hstable, hs]
    rfl

/-- A successful raw-vault association has exactly one successful association
for every modeled `kSmdNeedsAsset` field.  The optional maximum is traversed
only when present, matching the C++ SLE field iteration. -/
theorem RawVault.associateAsset_success_fields (rv result : RawVault)
    (hok : rv.associateAsset = .ok result) :
    ∃ (assetsTotal assetsAvailable assetsReserved lossUnrealized : Number)
      (assetsMaximum : Option Number),
      RawVault.associateAssetNumber rv.numericType rv.assetsTotal = .ok assetsTotal ∧
      RawVault.associateAssetNumber rv.numericType rv.assetsAvailable = .ok assetsAvailable ∧
      RawVault.associateAssetNumber rv.numericType rv.assetsReserved = .ok assetsReserved ∧
      RawVault.associateAssetNumber rv.numericType rv.lossUnrealized = .ok lossUnrealized ∧
      (match rv.assetsMaximum, assetsMaximum with
       | none, none => True
       | some maximum, some rounded =>
           RawVault.associateAssetNumber rv.numericType maximum = .ok rounded
       | _, _ => False) ∧
      result = { rv with
        assetsTotal := assetsTotal, assetsAvailable := assetsAvailable,
        assetsReserved := assetsReserved, assetsMaximum := assetsMaximum,
        lossUnrealized := lossUnrealized } := by
  unfold RawVault.associateAsset at hok
  obtain ⟨assetsTotal, htotal, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨assetsAvailable, havail, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨assetsReserved, hreserved, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨lossUnrealized, hloss, hok⟩ := bind_ok_peel _ _ _ hok
  cases hmaximum : rv.assetsMaximum with
  | none =>
    simp [hmaximum] at hok
    let output : RawVault :=
      { assetsTotal := assetsTotal, assetsAvailable := assetsAvailable,
        assetsReserved := assetsReserved, assetsMaximum := none,
        numericType := rv.numericType, scale := rv.scale,
        sharesTotal := rv.sharesTotal, lossUnrealized := lossUnrealized }
    change Except.ok output = Except.ok result at hok
    have heq : output = result := Except.ok.inj hok
    exact ⟨assetsTotal, assetsAvailable, assetsReserved, lossUnrealized, none,
      htotal, havail, hreserved, hloss, trivial, heq.symm⟩
  | some maximum =>
    simp [hmaximum] at hok
    obtain ⟨assetsMaximum, hmax, hok⟩ := bind_ok_peel _ _ _ hok
    let output : RawVault :=
      { assetsTotal := assetsTotal, assetsAvailable := assetsAvailable,
        assetsReserved := assetsReserved, assetsMaximum := some assetsMaximum,
        numericType := rv.numericType, scale := rv.scale,
        sharesTotal := rv.sharesTotal, lossUnrealized := lossUnrealized }
    change Except.ok output = Except.ok result at hok
    have heq : output = result := Except.ok.inj hok
    exact ⟨assetsTotal, assetsAvailable, assetsReserved, lossUnrealized,
      some assetsMaximum, htotal, havail, hreserved, hloss, hmax, heq.symm⟩

/-- Every successfully associated Vault asset field is representable at the
associated asset's precision.  This is the kernel-side counterpart of the C++
postcondition that serialization does not need to round an associated
`STNumber` again. -/
theorem RawVault.associateAsset_success_unrounded (rv result : RawVault)
    (hok : rv.associateAsset = .ok result) :
    ¬ STAmount.isRounded result.numericType result.assetsTotal ∧
    ¬ STAmount.isRounded result.numericType result.assetsAvailable ∧
    ¬ STAmount.isRounded result.numericType result.assetsReserved ∧
    ¬ STAmount.isRounded result.numericType result.lossUnrealized ∧
    ∀ maximum ∈ result.assetsMaximum,
      ¬ STAmount.isRounded result.numericType maximum := by
  obtain ⟨assetsTotal, assetsAvailable, assetsReserved, lossUnrealized,
    assetsMaximum, htotal, havail, hreserved, hloss, hmaximum, hresult⟩ :=
      RawVault.associateAsset_success_fields rv result hok
  cases hresult
  constructor
  · simpa using RawVault.associateAssetNumber_unrounded _ _ _ htotal
  constructor
  · simpa using RawVault.associateAssetNumber_unrounded _ _ _ havail
  constructor
  · simpa using RawVault.associateAssetNumber_unrounded _ _ _ hreserved
  constructor
  · simpa using RawVault.associateAssetNumber_unrounded _ _ _ hloss
  intro maximum hmem
  cases hsource : rv.assetsMaximum with
  | none =>
    cases houtput : assetsMaximum with
    | none => simp [houtput] at hmem
    | some rounded => simp [hsource, houtput] at hmaximum
  | some source =>
    cases houtput : assetsMaximum with
    | none => simp [hsource, houtput] at hmaximum
    | some rounded =>
      have hmax : RawVault.associateAssetNumber rv.numericType source = .ok rounded := by
        simpa [hsource, houtput] using hmaximum
      simp [houtput] at hmem
      subst maximum
      simpa using RawVault.associateAssetNumber_unrounded _ _ _ hmax

/-- Association changes only fields marked `kSmdNeedsAsset`: the modeled share
count, numeric asset identity, and vault scale are identical in every
successful post-state. -/
theorem Vault.associateAsset_success_preserves_nonAsset (v result : Vault)
    (hok : v.associateAsset = .ok result) :
    result.sharesTotal = v.sharesTotal ∧
    result.numericType = v.numericType ∧
    result.scale = v.scale := by
  unfold Vault.associateAsset at hok
  obtain ⟨raw, hraw, hok⟩ := bind_ok_peel _ _ _ hok
  split at hok
  · next hvalid =>
      have hresult : { toRawVault := raw, wf := hvalid.1, valid := hvalid.2 } = result :=
        Except.ok.inj hok
      obtain ⟨_, _, _, _, _, -, -, -, -, -, hrawEq⟩ :=
        RawVault.associateAsset_success_fields v.toRawVault raw hraw
      cases hresult
      change raw.sharesTotal = v.sharesTotal ∧
        raw.numericType = v.numericType ∧ raw.scale = v.scale
      simpa [hrawEq]
  · simp at hok

/-- Successful lawful association inherits the raw pass's five-field
representability guarantee. -/
theorem Vault.associateAsset_success_unrounded (v result : Vault)
    (hok : v.associateAsset = .ok result) :
    ¬ STAmount.isRounded result.numericType result.assetsTotal ∧
    ¬ STAmount.isRounded result.numericType result.assetsAvailable ∧
    ¬ STAmount.isRounded result.numericType result.assetsReserved ∧
    ¬ STAmount.isRounded result.numericType result.lossUnrealized ∧
    ∀ maximum ∈ result.assetsMaximum,
      ¬ STAmount.isRounded result.numericType maximum := by
  unfold Vault.associateAsset at hok
  obtain ⟨raw, hraw, hok⟩ := bind_ok_peel _ _ _ hok
  split at hok
  · next hvalid =>
      have hresult : { toRawVault := raw, wf := hvalid.1, valid := hvalid.2 } = result :=
        Except.ok.inj hok
      cases hresult
      exact RawVault.associateAsset_success_unrounded v.toRawVault raw hraw
  · simp at hok

/-- Failure of the pure association transition is atomic: an error cannot also
produce a successful post-state. This is the model-level failure guarantee
used by transaction callers before they commit the new SLE. -/
theorem Vault.associateAsset_failure_atomic (v : Vault) (error : Error)
    (herror : v.associateAsset = .error error) (result : Vault) :
    v.associateAsset ≠ .ok result := by
  rw [herror]
  simp

end XRPL.Model.SingleAssetVault
