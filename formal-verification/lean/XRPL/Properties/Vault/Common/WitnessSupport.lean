import XRPL.Properties.Vault.Defs
import XRPL.Model.Vault.VaultDeposit
import XRPL.Properties.Vault.Common.Reduction
import XRPL.Properties.Protocol.Number.Common.Notation
import XRPL.Properties.Protocol.Number.Common.ProofTactics
import XRPL.Properties.Protocol.Number.Common.Rounding.Normalize
import XRPL.Properties.Protocol.Number.Common.Rounding.SmallRange
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Normalize.Common.ResultFacts
import XRPL.Properties.Protocol.Number.ToRep.Common.Proofs
import XRPL.Properties.Protocol.STAmount.Common.RoundToScalePlumbing
import XRPL.Properties.Protocol.STAmount.Common.RoundToScaleHelpers
import XRPL.Properties.Protocol.STAmount.Mul.Common.IOU

/-! # Witness plumbing for the `*_attained` sharpness theorems

Shared, value-agnostic helpers for lifting the vault-operation `*_attained`
witnesses (whose concrete records live, fully visible, in the headline files)
into kernel proofs. The decimal pipeline (`checked`/`canonicalize`/`normalize`
and the `Number` arithmetic ops) is a well-founded recursion the kernel cannot
reduce by `decide`/defeq, so a concrete run is stepped by hand: the structural
`Except` binds collapse with `ok_bind` (from `Common.Reduction`), and each
`Number` operation is traced through its equation lemmas the way the
`Number/*/Common/*/WitnessTrace.lean` files trace `operator_mul`/`operator_div`.

An in-range integral amount converts to the `Number` with the same mantissa at
exponent `0` (the `normalize` inside `from_rep` is the identity, discharged by
`doNormalize_id`); the value-specific version lives with each witness because the
`intAmount` step carries a concrete `Int64` mantissa literal. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Empty (`STAmount.zero`) integral amount converts to `Number.zero`. -/
theorem zero_int64_toNumber :
    (STAmount.zero .int64).toNumber .to_nearest = .ok Number.zero := by
  unfold STAmount.toNumber
  rw [if_pos (show (STAmount.zero .int64).integral = true from rfl),
    show (STAmount.zero .int64).intAmount = .ok { value := 0 } from by
      unfold STAmount.intAmount STAmount.signedDrops
      rw [if_pos (show (STAmount.zero .int64).integral = true from rfl)]; rfl]
  show IntAmount.toNumber { value := 0 } .to_nearest = _
  unfold IntAmount.toNumber Number.from_rep Number.normalized Number.normalize
  show doNormalize false 0 0 largeRange.min largeRange.max .to_nearest = _
  unfold doNormalize
  rw [show ((0 : UInt64) == 0) = true from rfl]; simp only [if_true]

/-- Adding `Number.zero` on the right is a no-op (the `operator_add` fast path). -/
theorem operator_add_zero_right (x : Number) :
    Number.operator_add x Number.zero .to_nearest = .ok x := by
  unfold Number.operator_add
  rw [if_pos (show (Number.zero).operator_eq Number.zero = true from by decide)]; rfl

/-- `toRat` of a non-negative canonical `Number` at exponent `0` is its mantissa. -/
theorem toRat_nat_exp0 (m : UInt64) :
    (⟨false, m, 0⟩ : Number).toRat = (m.toNat : ℚ) := by
  rw [Number.toRat_of_nonneg _ rfl]
  show (m.toNat : ℚ) * (10 : ℚ) ^ (0 : Int) = (m.toNat : ℚ)
  norm_num

/-- Subtracting `Number.zero` is a no-op (negating zero is zero, then the
`operator_add` fast path). -/
theorem operator_sub_zero_right (x : Number) (mode : rounding_mode) :
    Number.operator_sub x Number.zero mode = .ok x := by
  unfold Number.operator_sub
  rw [show Number.zero.operator_neg = Number.zero from rfl]
  unfold Number.operator_add
  rw [if_pos (show (Number.zero).operator_eq Number.zero = true from by decide)]
  rfl

/-- `tryCatch` on an `.ok` value skips the handler, definitional. -/
theorem ok_tryCatch {ε α} (a : α) (h : ε → Except ε α) :
    (tryCatch (Except.ok a) h) = Except.ok a := rfl

/-- `Except.bind` on an `.ok` value, definitional with the continuation
abstract (so instantiating it never forces the continuation's body). An
`| .error e => .error e | .ok a => f a` match is definitionally this `bind`,
so a `show` in bind form followed by this lemma steps such a match without the
kernel whnf-ing the scrutinee's well-founded internals. -/
theorem okE_bind {ε α β} (a : α) (f : α → Except ε β) :
    Except.bind (Except.ok a) f = f a := rfl

/-- One firing step of `Number.truncateAux` (a fractional digit is dropped). -/
theorem truncateAux_step (m : UInt64) (e : Int) (he : e < 0) (hm : m ≠ 0) :
    Number.truncateAux m e = Number.truncateAux (m / 10) (e + 1) := by
  conv_lhs => rw [Number.truncateAux]
  rw [if_pos ⟨he, hm⟩]

/-- `Number.truncateAux` stops at exponent `0`. -/
theorem truncateAux_stop (m : UInt64) : Number.truncateAux m 0 = (m, 0) := by
  rw [Number.truncateAux]
  rw [if_neg (by intro h; exact absurd h.1 (by decide))]

/-- One firing step of the `Number.to_rep` mantissa shift. -/
theorem to_rep_shift_step (d : Int64) (e : Int) (g : Guard) (he : e < 0) :
    Number.to_rep.shift d e g
      = Number.to_rep.shift (d / 10) (e + 1) (g.push (d % 10).toUInt64) := by
  rw [shift_eq_spec, shift_eq_spec]
  conv_lhs => rw [shiftSpec]
  rw [if_pos he]

/-- The `Number.to_rep` mantissa shift stops at offset `0`. -/
theorem to_rep_shift_stop (d : Int64) (g : Guard) :
    Number.to_rep.shift d 0 g = (d, g) := by
  rw [shift_eq_spec, shiftSpec, if_neg (by decide : ¬ ((0 : Int) < 0))]

/-- The `Number.to_rep` growth loop at offset `0` returns its input. -/
theorem to_rep_grow_zero (d : Int64) : Number.to_rep.grow d 0 = .ok d := by
  rw [Number.to_rep.grow]
  rw [if_neg (by decide : ¬ ((0 : Int) > 0))]

end XRPL.Model.SingleAssetVault
