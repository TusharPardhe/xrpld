import XRPL.Properties.Vault.Defs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas

/-! # `Vault.create_lawful` lawfulness proof

The proof backing the `Vault.create_lawful` headline. A freshly created vault has
every `Number` field at `Number.zero`, so `WF` follows from `Number.zero` being
normalized and the two scale hypotheses, and every `Valid` clause is arithmetic
on zeros (the `assetsMaximum` clauses use the creation positivity hypothesis).
The result is packaged as a `Vault`, converting the exact-rational validity
to the operator invariant through `RawVault.valid_iff_exact`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A freshly created **raw/pre-association** vault, packaged directly as a
`Vault`. `create_lawful` intentionally retains the caller-supplied optional
maximum unchanged; complete source-faithful creation uses
`RawVault.to_lawful_terminal`, which associates that optional asset field before
exposing the final SLE. `create_lawful` remains the base of `Reachable` and of
raw create consumers. -/
def Vault.create_lawful (nt : NumericType) (scale : UInt8)
    (assetsMaximum : Option Number)
    (hmax_norm : ∀ m ∈ assetsMaximum, m.isNormalized)
    (hmax_pos : ∀ m ∈ assetsMaximum, 0 < m.toRat)
    (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) :
    Vault := by
  set rv : RawVault := { assetsTotal := Number.zero, assetsAvailable := Number.zero, assetsReserved := Number.zero, assetsMaximum := assetsMaximum, numericType := nt, scale := scale, sharesTotal := Number.zero, lossUnrealized := Number.zero } with hv_def
  have hz : Number.zero.isNormalized := Or.inl rfl
  have hAT : rv.toExact.assetsTotal = 0 := by
    simp only [hv_def, RawVault.toExact, Number.toRat_zero]
  have hAV : rv.toExact.assetsAvailable = 0 := by
    simp only [hv_def, RawVault.toExact, Number.toRat_zero]
  have hST : rv.toExact.sharesTotal = 0 := by
    simp only [hv_def, RawVault.toExact, Number.toRat_zero, Rat.num_zero, Int.toNat_zero]
  have hLU : rv.toExact.lossUnrealized = 0 := by
    simp only [hv_def, RawVault.toExact, Number.toRat_zero]
  have hAM : rv.toExact.assetsMaximum = assetsMaximum.map Number.toRat := rfl
  -- The loss subtraction is `zero - zero`, so it succeeds.
  have hsub : ∃ d, rv.assetsTotal.operator_sub rv.assetsAvailable .downward = .ok d :=
    Number.operator_sub_self_ok Number.zero .downward
  have hwf : rv.WF :=
    ⟨hz, hz, hz, hmax_norm, hz, hz,
     by simp only [hv_def, Number.toRat_zero, le_refl],
     by simp only [hv_def, Number.toRat_zero]; rfl,
     hscale_int, hscale_le, hsub⟩
  have hex : rv.toExact.Valid := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAT]
    · rw [hAV]
    · rw [hAV, hAT]
    · rw [hAM]; intro m hm; rw [Option.mem_map] at hm
      obtain ⟨n, hn, rfl⟩ := hm; exact hmax_pos n hn
    · rw [hST, hAT, hAV]; intro _; exact ⟨rfl, rfl⟩
    · rw [hAM, hAT]; intro m hm; rw [Option.mem_map] at hm
      obtain ⟨n, hn, rfl⟩ := hm; exact le_of_lt (hmax_pos n hn)
    · rw [hLU]
    · rw [hLU, hAT, hAV]; norm_num
    · rw [hAT, hLU]; norm_num
  exact ⟨rv, hwf, (RawVault.valid_iff_exact rv hwf).mpr hex⟩

/-- `create_lawful`'s underlying record is the fresh zero-field vault. Lets the
`Reachable` base case read the created state without reducing the packaged proofs. -/
@[simp] theorem Vault.create_lawful_toRawVault (nt : NumericType) (scale : UInt8)
    (assetsMaximum : Option Number)
    (hmax_norm : ∀ m ∈ assetsMaximum, m.isNormalized)
    (hmax_pos : ∀ m ∈ assetsMaximum, 0 < m.toRat)
    (hscale_int : nt.isIntegral = true → scale = 0) (hscale_le : scale.toNat ≤ 18) :
    (Vault.create_lawful nt scale assetsMaximum hmax_norm hmax_pos hscale_int hscale_le).toRawVault
      = { assetsTotal := Number.zero, assetsAvailable := Number.zero, assetsReserved := Number.zero, assetsMaximum := assetsMaximum, numericType := nt, scale := scale, sharesTotal := Number.zero, lossUnrealized := Number.zero } := rfl

end XRPL.Model.SingleAssetVault
