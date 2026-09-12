import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Protocol.Number.Add.Monotone
import XRPL.Properties.Protocol.STAmount.OfNumber.ExponentOrder

/-! # Withdrawal post-sum exponent ordering

A non-final fractional withdrawal calls `postSumExponent assetsTotal (-payout)`
before clamping the debit.  This helper records the ordering needed by the
clamp: a larger in-funds raw payout leaves a no-larger positive post-sum and
therefore selects a no-larger exponent.  The exact full-withdrawal boundary is
separate because `numberExponent Number.zero .fractional` deliberately returns
the `-100` zero sentinel rather than a positive IOU exponent.
-/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Peeling the executable `postSumExponent` binds identifies its final
`numberExponent` call when the negated payout conversion and addition are known. -/
private lemma postSumExponent_numberExponent_of_steps
    (v : Vault) (a : STAmount) (debit sum : Number) (scale : Int)
    (hfrac : a.mNumericType = .fractional)
    (hto : a.operator_neg.toNumber .to_nearest = .ok debit)
    (hadd : v.assetsTotal.operator_add debit .to_nearest = .ok sum)
    (hpost : postSumExponent v.assetsTotal a.operator_neg = .ok scale) :
    numberExponent sum .fractional = .ok scale := by
  unfold postSumExponent at hpost
  obtain ⟨d, hd, hpost⟩ := bind_ok_peel _ _ _ hpost
  have hd_eq : d = debit := Except.ok.inj (hd.symm.trans hto)
  subst d
  obtain ⟨total, htotal, hpost⟩ := bind_ok_peel _ _ _ hpost
  have htotal_eq : total = sum := Except.ok.inj (htotal.symm.trans hadd)
  subst total
  change numberExponent sum a.operator_neg.mNumericType = .ok scale at hpost
  rw [STAmount.operator_neg_mNumericType, hfrac] at hpost
  exact hpost

/-- Peeling a successful post-sum exponent all the way through the final
fractional `ofNumber` exposes the returned STAmount exponent. -/
private lemma postSumExponent_result_exponent_of_steps
    (v : Vault) (a result : STAmount) (debit sum : Number) (scale : Int)
    (hfrac : a.mNumericType = .fractional)
    (hto : a.operator_neg.toNumber .to_nearest = .ok debit)
    (hadd : v.assetsTotal.operator_add debit .to_nearest = .ok sum)
    (hof : STAmount.ofNumber .fractional sum .to_nearest = .ok result)
    (hpost : postSumExponent v.assetsTotal a.operator_neg = .ok scale) :
    result.exponent = scale := by
  have hnumber := postSumExponent_numberExponent_of_steps v a debit sum scale hfrac hto hadd hpost
  unfold numberExponent at hnumber
  obtain ⟨out, hout, hnumber⟩ := bind_ok_peel _ _ _ hnumber
  have hout_eq : out = result := Except.ok.inj (hout.symm.trans hof)
  subst out
  change Except.ok result.exponent = Except.ok scale at hnumber
  exact Except.ok.inj hnumber

/-- **Strict in-funds withdrawal post-sum antitonicity.**

The raw payouts `a₁ ≤ a₂` are nonnegative fractional amounts.  Their negations
convert to normalized `Number`s, so the larger payout supplies the smaller
right operand to the two `operator_add` calls.  The concrete cycle-35
addition-monotonicity theorem orders the positive post-sum `Number`s; the
cycle-38 general nearest-`ofNumber` exponent theorem then orders the scales.

`a₂ ≤ assetsAvailable ≤ assetsTotal` records the Vault funds invariant.  The
strict total bound, concrete positive post-sums, and cusp-gap premise are the
exact conditions needed by the executable nearest-addition theorem; no claim is
made for an overdraw (for example `assetsTotal = 1`, `a₁ = 1`, `a₂ = 2`). -/
theorem Vault.postSumExponent_withdraw_antitone_strict
    (v : Vault) (a₁ a₂ : STAmount) (debit₁ debit₂ sum₁ sum₂ : Number)
    (post₁ post₂ : STAmount) (s₁ s₂ : Int)
    (hfrac₁ : a₁.mNumericType = .fractional) (hfrac₂ : a₂.mNumericType = .fractional)
    (ha₁_nonneg : 0 ≤ a₁.toRat) (ha₂_nonneg : 0 ≤ a₂.toRat)
    (ha₁_le : a₁.toRat ≤ a₂.toRat)
    (ha₂_funds : a₂.toRat ≤ v.assetsAvailable.toRat)
    (ha₂_strict_total : a₂.toRat < v.assetsTotal.toRat)
    (hto₁ : a₁.operator_neg.toNumber .to_nearest = .ok debit₁)
    (hto₂ : a₂.operator_neg.toNumber .to_nearest = .ok debit₂)
    (hdebit₁_value : debit₁.toRat = -a₁.toRat)
    (hdebit₂_value : debit₂.toRat = -a₂.toRat)
    (hdebit₁_norm : debit₁.isNormalized) (hdebit₂_norm : debit₂.isNormalized)
    (hadd₁ : v.assetsTotal.operator_add debit₁ .to_nearest = .ok sum₁)
    (hadd₂ : v.assetsTotal.operator_add debit₂ .to_nearest = .ok sum₂)
    (hsum₁_pos : 0 < sum₁.toRat) (hsum₂_pos : 0 < sum₂.toRat)
    (hadd_gap : v.assetsTotal.toRat + debit₂.toRat < v.assetsTotal.toRat + debit₁.toRat →
      v.assetsTotal.toRat + debit₂.toRat ≤ (maxRepNat : ℚ) *
        ((v.assetsTotal.toRat + debit₁.toRat) - (v.assetsTotal.toRat + debit₂.toRat)))
    (hsum₁_range : sum₁.exponent_ + 4 ≤ maxExponent)
    (hsum₂_range : sum₂.exponent_ + 4 ≤ maxExponent)
    (hof₁ : STAmount.ofNumber .fractional sum₁ .to_nearest = .ok post₁)
    (hof₂ : STAmount.ofNumber .fractional sum₂ .to_nearest = .ok post₂)
    (hpost₁_nonzero : post₁.mValue ≠ 0) (hpost₂_nonzero : post₂.mValue ≠ 0)
    (hpost₁ : postSumExponent v.assetsTotal a₁.operator_neg = .ok s₁)
    (hpost₂ : postSumExponent v.assetsTotal a₂.operator_neg = .ok s₂) :
    s₂ ≤ s₁ := by
  have hassets_total_pos : 0 < v.assetsTotal.toRat := by
    have : 0 ≤ a₂.toRat := ha₂_nonneg
    linarith
  have hdebit_order : debit₂.toRat ≤ debit₁.toRat := by
    rw [hdebit₂_value, hdebit₁_value]
    linarith
  have htruth₂_pos : 0 < v.assetsTotal.toRat + debit₂.toRat := by
    rw [hdebit₂_value]
    linarith
  have htruth_order : v.assetsTotal.toRat + debit₂.toRat ≤
      v.assetsTotal.toRat + debit₁.toRat := by
    linarith
  have hsum_order : sum₂.toRat ≤ sum₁.toRat :=
    Number.operator_add_left_toRat_mono v.assetsTotal debit₂ debit₁ sum₂ sum₁
      v.wf.assetsTotal_norm hdebit₂_norm hdebit₁_norm hadd₂ hadd₁
      hsum₂_pos hsum₁_pos htruth₂_pos htruth_order hadd_gap
  have hsum₂_mantissa : sum₂.mantissa_ ≠ 0 := by
    intro hzero
    exact (ne_of_gt hsum₂_pos) (Number.toRat_eq_zero_of_mantissa_zero sum₂ hzero)
  have hsum₁_mantissa : sum₁.mantissa_ ≠ 0 := by
    intro hzero
    exact (ne_of_gt hsum₁_pos) (Number.toRat_eq_zero_of_mantissa_zero sum₁ hzero)
  have hsum₂_norm : sum₂.isNormalized :=
    operator_add_isNormalized_to_nearest v.assetsTotal debit₂ sum₂
      v.wf.assetsTotal_norm hdebit₂_norm hadd₂ hsum₂_mantissa
  have hsum₁_norm : sum₁.isNormalized :=
    operator_add_isNormalized_to_nearest v.assetsTotal debit₁ sum₁
      v.wf.assetsTotal_norm hdebit₁_norm hadd₁ hsum₁_mantissa
  have hexponent : post₂.exponent ≤ post₁.exponent :=
    STAmount.ofNumber_iou_to_nearest_exponent_le_of_normalized_pos_le
      sum₂ sum₁ post₂ post₁ hsum₂_norm hsum₁_norm hsum₂_pos hsum_order
      hsum₂_range hsum₁_range hof₂ hof₁ hpost₂_nonzero hpost₁_nonzero
  have hs₁ : post₁.exponent = s₁ :=
    postSumExponent_result_exponent_of_steps v a₁ post₁ debit₁ sum₁ s₁
      hfrac₁ hto₁ hadd₁ hof₁ hpost₁
  have hs₂ : post₂.exponent = s₂ :=
    postSumExponent_result_exponent_of_steps v a₂ post₂ debit₂ sum₂ s₂
      hfrac₂ hto₂ hadd₂ hof₂ hpost₂
  omega

/-- **Exact full-withdrawal boundary.** If the executable post-sum addition for
the larger in-funds payout is exactly `Number.zero`, its scale is the explicit
`-100` zero sentinel.  The other successful fractional post-sum exponent is
also never below that sentinel, so the antitone relation remains valid without
pretending that the zero post-sum is positive. -/
theorem Vault.postSumExponent_withdraw_full_zero_antitone
    (v : Vault) (a₁ a₂ : STAmount) (debit₁ debit₂ sum₁ : Number) (s₁ s₂ : Int)
    (hfrac₁ : a₁.mNumericType = .fractional) (hfrac₂ : a₂.mNumericType = .fractional)
    (ha₁_nonneg : 0 ≤ a₁.toRat) (ha₂_nonneg : 0 ≤ a₂.toRat)
    (ha₁_le : a₁.toRat ≤ a₂.toRat)
    (ha₂_funds : a₂.toRat ≤ v.assetsAvailable.toRat)
    (ha₂_full_total : a₂.toRat = v.assetsTotal.toRat)
    (hto₁ : a₁.operator_neg.toNumber .to_nearest = .ok debit₁)
    (hto₂ : a₂.operator_neg.toNumber .to_nearest = .ok debit₂)
    (hadd₁ : v.assetsTotal.operator_add debit₁ .to_nearest = .ok sum₁)
    (hadd₂_zero : v.assetsTotal.operator_add debit₂ .to_nearest = .ok Number.zero)
    (hpost₁ : postSumExponent v.assetsTotal a₁.operator_neg = .ok s₁)
    (hpost₂ : postSumExponent v.assetsTotal a₂.operator_neg = .ok s₂) :
    s₂ = -100 ∧ s₂ ≤ s₁ := by
  have hnumber₂ := postSumExponent_numberExponent_of_steps v a₂ debit₂ Number.zero s₂
    hfrac₂ hto₂ hadd₂_zero hpost₂
  have hs₂ : s₂ = -100 := by
    change numberExponent Number.zero .fractional = .ok s₂ at hnumber₂
    exact Except.ok.inj hnumber₂.symm
  have hnumber₁ := postSumExponent_numberExponent_of_steps v a₁ debit₁ sum₁ s₁
    hfrac₁ hto₁ hadd₁ hpost₁
  have hs₁_lower : (-100 : Int) ≤ s₁ := by
    rcases numberExponent_fractional_offset sum₁ s₁ hnumber₁ with hzero | ⟨hlow, _⟩
    · omega
    · omega
  constructor
  · exact hs₂
  · omega

end XRPL.Model.SingleAssetVault
