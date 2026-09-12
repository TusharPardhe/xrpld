import XRPL.Model.Vault.VaultDeposit

/-! # Monadic reduction toolkit for `Vault.deposit`

Building blocks for stepping the `Except Error` do-blocks of the deposit
pipeline: the two `Except` bind identities (both `rfl`), a clean `if`-form
characterization of `roundedDepositAmount` once `roundToVaultExponent` is known,
and the two bridges that read that characterization back. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- `Except.ok`-bind step, definitional. -/
theorem ok_bind {ε α β} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- `Except.error`-bind short-circuit, definitional. -/
theorem err_bind {ε α β} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- `tryCatch` on a caught error runs the handler, definitional. -/
theorem tryCatch_error {ε α} (e : ε) (h : ε → Except ε α) :
    (tryCatch (Except.error e) h) = h e := rfl

/-- Peel one `Except`-bind out of an `.ok` result: the head succeeded and the
continuation reached the same `.ok`. -/
theorem bind_ok_peel {α β} (x : Except Error α) (f : α → Except Error β) (r : β)
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => rw [hx, err_bind] at h; exact absurd h (by simp)
  | ok a => rw [hx, ok_bind] at h; exact ⟨a, rfl, h⟩

/-- Clean `if`-form of `roundedDepositAmount` when `roundToVaultExponent` succeeds. -/
theorem roundedDepositAmount_ok (v : Vault) (amountDeposit ra' : STAmount)
    (hr : roundToVaultExponent amountDeposit v.assetsTotal = .ok ra') :
    v.roundedDepositAmount amountDeposit =
      (if ra'.isZero then .ok (.rejected .tecPRECISION_LOSS) else .ok (.rounded ra')) := by
  simp only [Vault.roundedDepositAmount, hr, ok_bind]; rfl

/-- `roundedDepositAmount` propagates a `roundToVaultExponent` error. -/
theorem roundedDepositAmount_err (v : Vault) (amountDeposit : STAmount) (e : Error)
    (hr : roundToVaultExponent amountDeposit v.assetsTotal = .error e) :
    v.roundedDepositAmount amountDeposit = .error e := by
  simp only [Vault.roundedDepositAmount, hr, err_bind]

/-- A `rounded` outcome means `roundToVaultExponent` produced exactly that nonzero
amount. -/
theorem roundedDepositAmount_rounded (v : Vault) (amountDeposit ra : STAmount)
    (h : v.roundedDepositAmount amountDeposit = .ok (.rounded ra)) :
    roundToVaultExponent amountDeposit v.assetsTotal = .ok ra ∧ ra.isZero = false := by
  cases hr : roundToVaultExponent amountDeposit v.assetsTotal with
  | error e => rw [roundedDepositAmount_err v amountDeposit e hr] at h; exact absurd h (by simp)
  | ok ra' =>
    rw [roundedDepositAmount_ok v amountDeposit ra' hr] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hz
      rw [Except.ok.injEq, RoundingResult.rounded.injEq] at h
      subst h
      exact ⟨rfl, by simpa using hz⟩

/-- A `rejected` outcome pins the code to `tecPRECISION_LOSS` and means
`roundToVaultExponent` produced a zero amount. -/
theorem roundedDepositAmount_rejected (v : Vault) (amountDeposit : STAmount) (ter : TER)
    (h : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    ∃ ra, roundToVaultExponent amountDeposit v.assetsTotal = .ok ra ∧ ra.isZero = true ∧
      ter = .tecPRECISION_LOSS := by
  cases hr : roundToVaultExponent amountDeposit v.assetsTotal with
  | error e => rw [roundedDepositAmount_err v amountDeposit e hr] at h; exact absurd h (by simp)
  | ok ra' =>
    rw [roundedDepositAmount_ok v amountDeposit ra' hr] at h
    split at h
    · rename_i hz
      rw [Except.ok.injEq, RoundingResult.rejected.injEq] at h
      exact ⟨ra', rfl, hz, h.symm⟩
    · exact absurd h (by simp)

end XRPL.Model.SingleAssetVault
