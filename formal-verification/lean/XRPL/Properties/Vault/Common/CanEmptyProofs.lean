import XRPL.Properties.Vault.Reachable
import XRPL.Properties.Vault.VaultWithdraw
import XRPL.Properties.Vault.VaultWithdrawReturn
import XRPL.Properties.Vault.Common.Preservation
import XRPL.Properties.Vault.Common.WithdrawTotality
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness

/-! # `CanEmpty`: every reachable loss-free vault can be emptied

Proof bodies for the `CanEmpty` headline in `CanEmpty.lean`.

The construction peels one share per withdrawal, driven by well-founded
induction on the stored share total `rv.toExact.sharesTotal` (a `ℕ`). A single
share withdrawal always runs to a success that strictly lowers the share total:

* a share count of at least two prices to at most half the net asset value, so
  the funds guard has ample margin and cannot fire, and the run is not the final
  withdrawal, so the stored share total drops by exactly one; and
* if that payout is below the representable floor it rounds to zero, which the
  precision-loss guard does not reject (that guard needs a nonzero payout), so
  the share is burned for free and the total still drops.

The share total therefore strictly decreases every step and the recursion
bottoms out at zero shares, the empty state.

The single arithmetic crux, that the one-share run reduces to a success record
whose stored share total is strictly smaller, is isolated as
`withdraw_one_share_step`; everything else (reachability closure, the share-domain
bound, and the induction) is discharged around it. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A den-`1` rational equals its integer numerator, cast back to `ℚ`. -/
private lemma ce_eq_intCast_of_den_one {q : ℚ} (h : q.den = 1) : q = (q.num : ℚ) := by
  conv_lhs => rw [← Rat.num_div_den q]
  rw [h]
  simp

/-- One vault share as a canonical `int64` amount: value one, offset zero,
nonnegative. Shares are always an integral (MPT) amount, so this is the smallest
positive share amount a withdrawal can name. -/
def oneShare : STAmount := ⟨.int64, 1, 0, false⟩

/-- `oneShare` embeds to the rational one. -/
theorem oneShare_toRat : oneShare.toRat = 1 := by
  decide

/-- `oneShare` carries the `int64` numeric type. -/
theorem oneShare_numericType : oneShare.mNumericType = .int64 := rfl

/-- `oneShare` is nonnegative. -/
theorem oneShare_negative : oneShare.negative = false := rfl

/-- `oneShare` is a canonical `int64` integral amount. -/
theorem oneShare_integralCanonical : oneShare.IntegralCanonical where
  is_integral := rfl
  offset_zero := rfl
  in_range := by decide

/-- `oneShare` is stored canonically, so `oneShare.toNumber` is value-exact. -/
theorem oneShare_canonical : oneShare.Canonical := by
  refine ⟨fun _ => ⟨oneShare_integralCanonical, ?_⟩, fun hf => ?_⟩
  · decide
  · exact absurd hf (by decide)

/-- `oneShare` converts to a value-one, normalized `Number` (forward totality of
`toNumber` on the canonical single share). -/
theorem oneShare_toNumber (mode : rounding_mode) :
    ∃ sn : Number, oneShare.toNumber mode = .ok sn ∧ sn.toRat = 1 ∧ sn.isNormalized := by
  obtain ⟨sn, hok, hval, hn⟩ :=
    STAmount.toNumber_integral_small_exact oneShare mode oneShare_integralCanonical (by decide)
  exact ⟨sn, hok, by rw [hval, oneShare_toRat], hn⟩

/-- **Compute-stage forwarding for the one-share withdrawal.** Once the exchange
`sharesToAssetsWithdraw` prices the single share to `assets`, the `try`/`catch`
wrapper `computeWithdrawByShares` forwards it to the no-error record. Proven glue
between the (open) exchange totality and the outer withdraw run. -/
theorem withdraw_oneShare_compute_of_exchange (v : Vault) (assets : STAmount)
    (hex : v.sharesToAssetsWithdraw oneShare false = .ok assets) :
    computeWithdrawByShares v oneShare false = .ok ⟨none, assets, oneShare⟩ :=
  computeWithdrawByShares_of_exchange_ok v oneShare false assets hex

/-- Reachability, a share total that fits the `int64` domain, the asset
representability rail, and the `int64` asset-type scope. Kept as one predicate so
the closure and the induction thread the same facts.

`assetsCap` is the representability guarantee C++ enforces at `accountSend` (the
asset can never exceed the asset type's max): `Vault.Reachable` over-approximates
here, admitting integral-donation histories whose `assetsTotal` exceeds
`numericType.maxValue` (C++ rejects them, the model omits that rail), so without
this hypothesis the one-share pricing `nav * 1 / sharesTotal` can overflow and the
withdrawal fails. It is preserved along the peeling sequence because a withdrawal
only decreases `assetsTotal` (`withdraw_oneShare_assetsTotal_le`).

`int64` restricts the scope to `int64`-typed (integral) asset vaults. This is
NECESSARY, not cosmetic: on a fractional vault the one-share payout can be smaller
than one ULP of the stored `assetsTotal`, so the (waiting-the-C++-fix)
precision-loss guard rejects the withdrawal with `tecPRECISION_LOSS`. A concrete
reachable fractional counterexample is `create .fractional` then a single deposit
of `10 ^ 17`: the one-share redemption is rejected, so one-share peeling does not
empty it. On an `int64` vault the payout is a whole unit and always lowers the
rounded total, so the guard never fires.

`assetsInt` records that the stored `assetsTotal` is a whole number. It is a true
invariant of `int64` vaults (every operation stores an integer difference), stated
here rather than derived from `Vault.Reachable` because that derivation is a
separate reachability induction outside the one-share pricing argument. It is
preserved along the peeling sequence (a whole `assetsTotal` minus a whole payout is
whole), and it supplies the magnitude floor `1 ≤ assetsTotal.toRat` (when nonzero)
that discharges the multiply operand bound `minExponent ≤ assetsTotal.exponent_`. -/
structure Vault.EmptyReady (v : Vault) : Prop where
  reachable : Vault.Reachable v
  fits : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1
  assetsCap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1
  int64 : v.numericType = .int64
  assetsInt : v.assetsTotal.toRat.den = 1

/-- A finite withdrawal sequence that drains the vault to zero shares. `done`
records that the vault already has no shares; `step` performs one non-loss-waiving
withdrawal that runs without a throw and then empties the resulting vault. -/
inductive CanEmpty : Vault → Prop where
  | done (v : Vault) : v.toExact.sharesTotal = 0 → CanEmpty v
  | step (v : Vault) (amount : WithdrawAmount) (r : WithdrawResult) :
      v.withdraw amount false = .ok r → r.error = none → CanEmpty r.vault' → CanEmpty v

/-- **Step 2 bridge: representability bounds the exponent.** A normalized,
nonnegative `Number` whose value fits `2 ^ 63 - 1` has a nonpositive exponent: its
mantissa is at least `10 ^ 18`, so `exponent_ ≥ 1` would force the value to at least
`10 ^ 19 > 2 ^ 63 - 1`. This is the bridge from the `assetsTotal` representability
rail to the front-half overflow preconditions. -/
theorem Number.exponent_le_zero_of_cap (n : Number) (hnorm : n.isNormalized)
    (hnn : 0 ≤ n.toRat) (hcap : n.toRat ≤ 2 ^ 63 - 1) :
    n.exponent_ ≤ 0 := by
  have hneg : n.negative_ = false := Number.negative_false_of_norm_nonneg n hnorm hnn
  rcases hnorm with hz | ⟨hmlo, _hmhi, _, _, _⟩
  · rw [hz]; decide
  · by_contra hcon
    push_neg at hcon
    have hexp_nn : (0 : ℤ) ≤ n.exponent_ := le_of_lt hcon
    have htoRat : n.toRat = (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_.toNat := by
      unfold Number.toRat
      rcases eq_or_ne n.mantissa_ 0 with hm | hm
      · simp [hm]
      · rw [if_neg hm]
        simp only [hneg, Bool.false_eq_true, if_false, ge_iff_le]
        rw [if_pos hexp_nn, Rat.mkRat_one]
        push_cast
        ring
    have hm_nat : 1000000000000000000 ≤ n.mantissa_.toNat := by
      have hle := UInt64.le_iff_toNat_le.mp hmlo
      rwa [largeRange_min_val] at hle
    have hm_q : (1000000000000000000 : ℚ) ≤ (n.mantissa_.toNat : ℚ) := by exact_mod_cast hm_nat
    have hexp1 : 1 ≤ n.exponent_.toNat := by omega
    have hpow : (10 : ℚ) ≤ 10 ^ n.exponent_.toNat := by
      calc (10 : ℚ) = 10 ^ 1 := (pow_one 10).symm
        _ ≤ 10 ^ n.exponent_.toNat := pow_le_pow_right₀ (by norm_num) hexp1
    have hge : (10000000000000000000 : ℚ) ≤ n.toRat := by
      rw [htoRat]
      calc (10000000000000000000 : ℚ) = 1000000000000000000 * 10 := by norm_num
        _ ≤ (n.mantissa_.toNat : ℚ) * 10 ^ n.exponent_.toNat :=
            mul_le_mul hm_q hpow (by norm_num) (by positivity)
    have hlt : n.toRat < 10000000000000000000 := lt_of_le_of_lt hcap (by norm_num)
    linarith

/-- **The normalized representation of the value `1` has exponent `-18`.** Its
mantissa lies in `[10 ^ 18, 10 ^ 19)`, and `mantissa · 10 ^ e = 1` pins `e` to the
single integer in `(-19, -18]`. Used to pin the exponent of `oneShare.toNumber`,
the multiply operand of the one-share pricing. -/
theorem oneShare_number_exp (sn : Number) (hnorm : sn.isNormalized) (hval : sn.toRat = 1) :
    sn.exponent_ = -18 := by
  have hneg : sn.negative_ = false := by
    apply Number.negative_false_of_norm_nonneg _ hnorm; rw [hval]; norm_num
  have hmne : sn.mantissa_ ≠ 0 := by
    rw [Number.mantissa_ne_zero_iff, hval]; norm_num
  obtain ⟨hlo, hhi⟩ := hnorm.mantissaBounds_nat hmne
  have htoRat : (sn.mantissa_.toNat : ℚ) * (10 : ℚ) ^ sn.exponent_ = 1 := by
    rw [← Number.toRat_of_nonneg sn hneg, hval]
  have hm_lo : (10 : ℚ) ^ (18 : ℕ) ≤ (sn.mantissa_.toNat : ℚ) := by exact_mod_cast hlo
  have hm_hi : (sn.mantissa_.toNat : ℚ) < (10 : ℚ) ^ (19 : ℕ) := by exact_mod_cast hhi
  have hmnn : (0 : ℚ) ≤ (sn.mantissa_.toNat : ℚ) := by positivity
  have he_le : sn.exponent_ ≤ -18 := by
    by_contra hc; push_neg at hc
    have hge : (10 : ℚ) ^ (-17 : ℤ) ≤ (10 : ℚ) ^ sn.exponent_ :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h1 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (-17 : ℤ) ≤
        (sn.mantissa_.toNat : ℚ) * (10 : ℚ) ^ sn.exponent_ :=
      mul_le_mul hm_lo hge (le_of_lt (zpow_pos (by norm_num) _)) hmnn
    have h2 : (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (-17 : ℤ) = 10 := by
      rw [show ((10 : ℚ) ^ (18 : ℕ)) = (10 : ℚ) ^ (18 : ℤ) from (zpow_natCast 10 18).symm,
        ← zpow_add₀ (by norm_num)]; norm_num
    rw [h2, htoRat] at h1; norm_num at h1
  have he_ge : -18 ≤ sn.exponent_ := by
    by_contra hc; push_neg at hc
    have hle : (10 : ℚ) ^ sn.exponent_ ≤ (10 : ℚ) ^ (-19 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hpp : (0 : ℚ) < (10 : ℚ) ^ (-19 : ℤ) := zpow_pos (by norm_num) _
    have h1 : (sn.mantissa_.toNat : ℚ) * (10 : ℚ) ^ sn.exponent_ ≤
        (sn.mantissa_.toNat : ℚ) * (10 : ℚ) ^ (-19 : ℤ) :=
      mul_le_mul_of_nonneg_left hle hmnn
    have h2 : (sn.mantissa_.toNat : ℚ) * (10 : ℚ) ^ (-19 : ℤ) <
        (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ (-19 : ℤ) :=
      mul_lt_mul_of_pos_right hm_hi hpp
    have h3 : (10 : ℚ) ^ (19 : ℕ) * (10 : ℚ) ^ (-19 : ℤ) = 1 := by
      rw [show ((10 : ℚ) ^ (19 : ℕ)) = (10 : ℚ) ^ (19 : ℤ) from (zpow_natCast 10 19).symm,
        ← zpow_add₀ (by norm_num)]; norm_num
    rw [htoRat] at h1; rw [h3] at h2; linarith
  omega

/-- **Zero `STAmount` converts to a value-zero normalized `Number`.** The zero of
any numeric type lifts to a normalized zero-valued `Number` under `toNumber`. -/
theorem STAmount.zero_toNumber (nt : NumericType) (mode : rounding_mode) :
    ∃ sn : Number, (STAmount.zero nt).toNumber mode = .ok sn ∧ sn.toRat = 0 ∧ sn.isNormalized := by
  by_cases hint : nt.isIntegral = true
  · have hIC : (STAmount.zero nt).IntegralCanonical := by
      refine ⟨?_, ?_, ?_⟩
      · show (STAmount.zero nt).mNumericType.isIntegral = true
        rw [show (STAmount.zero nt).mNumericType = nt from by cases nt <;> rfl]; exact hint
      · cases nt with
        | fractional => exact absurd hint (by decide)
        | integral mv mo ms msh => rfl
      · rw [STAmount.zero_mValue]; exact Nat.zero_le _
    obtain ⟨sn, hok, hval, hnorm⟩ :=
      STAmount.toNumber_integral_small_exact (STAmount.zero nt) mode hIC
        (by rw [STAmount.zero_mValue]; exact Nat.zero_le _)
    exact ⟨sn, hok, by rw [hval, STAmount.zero_toRat], hnorm⟩
  · have hfr : (STAmount.zero nt).integral = false := by
      show (STAmount.zero nt).mNumericType.isIntegral = false
      rw [show (STAmount.zero nt).mNumericType = nt from by cases nt <;> rfl]
      cases hh : nt.isIntegral with
      | true => exact absurd hh hint
      | false => rfl
    exact ⟨Number.zero, STAmount.toNumber_zero_fractional (STAmount.zero nt) mode hfr
      (STAmount.zero_mValue nt), Number.toRat_zero, Or.inl rfl⟩

/-- **Forward totality of the one-share pricing on an `int64` vault.** The
exchange `sharesToAssetsWithdraw oneShare` runs to a success `assets`, whose
`toNumber` lift `aN` is normalized, value-exact and integer-valued, and whose value
is a nonnegative amount at most the stored `assetsTotal`.

On the zero-mantissa (insolvent) `assetsTotal` the exchange short-circuits to the
canonical zero. Otherwise `assetsTotal` is a whole number `≥ 1`, so its exponent is
`≥ -18`; the multiply `assetsTotal * 1` and divide `_ / sharesTotal` clear the
`WithdrawTotality` operand bounds and are total, and the multiply is value-exact
(`nav * 1 = nav`). The downward `ofNumber .int64` never overpays: its output floors
the quotient, which is at most `assetsTotal`. -/
theorem withdraw_oneShare_exchange (v : Vault) (hr : Vault.Reachable v)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hpos : 0 < v.toExact.sharesTotal) (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (hint : v.numericType = .int64) (hAint : v.assetsTotal.toRat.den = 1) :
    ∃ (assets : STAmount) (aN : Number),
      v.sharesToAssetsWithdraw oneShare false = .ok assets ∧
      assets.toNumber .to_nearest = .ok aN ∧
      aN.isNormalized ∧ aN.toRat = assets.toRat ∧ aN.toRat.den = 1 ∧
      0 ≤ assets.toRat ∧ assets.toRat ≤ v.assetsTotal.toRat ∧
      assets.toRat ≤ v.assetsTotal.toRat / v.sharesTotal.toRat *
        (1 + 6 / (2 ^ 63 - 3)) := by
  have hL0 : v.lossUnrealized.mantissa_ = 0 :=
    Number.toRat_eq_zero_iff.mp (Vault.Reachable.lossUnrealized_zero v hr)
  have hAnorm : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
  have hAnn : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hAneg : v.assetsTotal.negative_ = false :=
    Number.negative_false_of_norm_nonneg _ hAnorm hAnn
  have hSTnorm : v.sharesTotal.isNormalized := v.wf.sharesTotal_norm
  have hSTcap : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]; exact hfit
  -- share total is a positive integer, so `1 ≤ sharesTotal`
  have hST1 : (1 : ℚ) ≤ v.sharesTotal.toRat := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
    have : (1 : ℕ) ≤ v.toExact.sharesTotal := hpos
    exact_mod_cast this
  have hSTm : v.sharesTotal.mantissa_ ≠ 0 :=
    Number.mantissa_ne_zero_of_toRat_ne_zero (by linarith)
  have h81 : (10 : ℚ) ^ (-81 : ℤ) ≤ 1 := by
    rw [show (1 : ℚ) = (10 : ℚ) ^ (0 : ℤ) from by norm_num]
    exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hSTexp_lo : (-99 : ℤ) ≤ v.sharesTotal.exponent_ := by
    have hlog := exponent_ge_of_toRat_ge ((10 : ℚ) ^ (-81 : ℤ))
      (zpow_pos (by norm_num) _) v.sharesTotal hSTnorm
      (by linarith [h81, hST1])
    have hlogq : Int.log 10 ((10 : ℚ) ^ (-81 : ℤ)) = -81 :=
      Int.log_zpow (by norm_num) _
    rw [hlogq] at hlog
    norm_num at hlog
    exact hlog
  rw [Vault.sharesToAssetsWithdraw_zeroLoss_reduces v oneShare hL0]
  by_cases hAm0 : v.assetsTotal.mantissa_ = 0
  · -- insolvent: the exchange returns the canonical zero
    rw [if_pos (by rw [hAm0]; rfl)]
    obtain ⟨aN, haN_ok, haN_val, haN_norm⟩ := STAmount.zero_toNumber v.numericType .to_nearest
    have hAT0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_iff.mpr hAm0
    refine ⟨STAmount.zero v.numericType, aN, rfl, haN_ok, haN_norm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [haN_val, STAmount.zero_toRat]
    · rw [haN_val]; rfl
    · rw [STAmount.zero_toRat]
    · rw [STAmount.zero_toRat]; exact hAnn
    · rw [STAmount.zero_toRat]
      exact mul_nonneg (div_nonneg hAnn (by linarith)) (by norm_num)
  · -- solvent: run the multiply / divide / ofNumber pipeline
    rw [if_neg (show ¬ (v.assetsTotal.mantissa_ == 0) = true from by
      rw [beq_false_of_ne hAm0]; exact Bool.false_ne_true)]
    have hAT_pos : (0 : ℚ) < v.assetsTotal.toRat :=
      lt_of_le_of_ne hAnn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hAm0))
    -- whole nonzero `assetsTotal` is `≥ 1`, giving `exponent_ ≥ -18`
    have hAT1 : (1 : ℚ) ≤ v.assetsTotal.toRat := by
      have hnum : 0 < v.assetsTotal.toRat.num := Rat.num_pos.mpr hAT_pos
      have : (1 : ℚ) ≤ (v.assetsTotal.toRat.num : ℚ) := by exact_mod_cast hnum
      calc (1 : ℚ) ≤ (v.assetsTotal.toRat.num : ℚ) := this
        _ = v.assetsTotal.toRat := by
            conv_rhs => rw [← Rat.num_div_den v.assetsTotal.toRat]
            rw [hAint]; push_cast; ring
    have hAexp_lo : (-99 : ℤ) ≤ v.assetsTotal.exponent_ := by
      have hlog := exponent_ge_of_toRat_ge ((10 : ℚ) ^ (-81 : ℤ))
        (zpow_pos (by norm_num) _) v.assetsTotal hAnorm
        (by linarith [h81, hAT1])
      have hlogq : Int.log 10 ((10 : ℚ) ^ (-81 : ℤ)) = -81 :=
        Int.log_zpow (by norm_num) _
      rw [hlogq] at hlog
      norm_num at hlog
      exact hlog
    have hAexp_hi : v.assetsTotal.exponent_ ≤ 0 :=
      Number.exponent_le_zero_of_cap v.assetsTotal hAnorm hAnn hcap
    -- share number = oneShare.toNumber, value 1, exponent -18
    obtain ⟨sn, hsn_ok, hsn_val, hsn_norm⟩ := oneShare_toNumber .to_nearest
    have hsn_exp : sn.exponent_ = -18 := oneShare_number_exp sn hsn_norm hsn_val
    have hsn_m0 : sn.mantissa_ ≠ 0 := Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hsn_val]; norm_num)
    rw [hsn_ok, ok_bind]
    -- multiply is total and value-exact (nav * 1 = nav)
    obtain ⟨NAVShares, hmul⟩ := Number.operator_mul_ok_of_normalized v.assetsTotal sn .to_nearest
      hAnorm hsn_norm hAm0 hsn_m0
      (by rw [hsn_exp]; unfold minExponent; omega) (by rw [hsn_exp]; unfold maxExponent; omega)
    rw [hmul, ok_bind]
    have hNAV_val : NAVShares.toRat = v.assetsTotal.toRat := by
      have h := Number.RoundsToRepresentable.eq_of_representable NAVShares
        (v.assetsTotal.toRat * sn.toRat)
        (operator_mul_rounded_to_nearest v.assetsTotal sn NAVShares hAnorm hsn_norm hmul)
        v.assetsTotal hAnorm (by rw [hsn_val]; ring)
      rw [hsn_val, mul_one] at h; exact h
    have hNAVm : NAVShares.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero (by rw [hNAV_val]; linarith)
    have hNAVnorm : NAVShares.isNormalized :=
      operator_mul_result_isNormalized v.assetsTotal sn NAVShares .to_nearest
        hAnorm hsn_norm hAm0 hsn_m0 hmul hNAVm
    have hNAVexp_hi : NAVShares.exponent_ ≤ 0 :=
      Number.exponent_le_zero_of_cap NAVShares hNAVnorm (by rw [hNAV_val]; exact hAnn)
        (by rw [hNAV_val]; exact hcap)
    -- divide is total
    obtain ⟨assetsNumber, hdiv⟩ := Number.operator_div_ok_of_normalized NAVShares v.sharesTotal
      .to_nearest hNAVnorm hSTnorm hNAVm hSTm (by unfold maxExponent; omega)
    rw [hdiv, ok_bind]
    -- the quotient rounds to a representable neighbour of `nav / sharesTotal`
    have hqrepr := operator_div_rounded_to_nearest NAVShares v.sharesTotal assetsNumber
      hNAVnorm hSTnorm hdiv
    have hST_pos : (0 : ℚ) < v.sharesTotal.toRat := by linarith
    have hq_le : NAVShares.toRat / v.sharesTotal.toRat ≤ v.assetsTotal.toRat := by
      rw [hNAV_val]; exact div_le_self hAnn hST1
    have hAN_le : assetsNumber.toRat ≤ v.assetsTotal.toRat :=
      Number.RoundsToRepresentable.le_of_le_normalized assetsNumber _ hqrepr v.assetsTotal hAnorm hq_le
    have hAN_nn : 0 ≤ assetsNumber.toRat :=
      Number.RoundsToRepresentable.nonneg_of_nonneg assetsNumber _ hqrepr
        (by rw [hNAV_val]; positivity)
    -- the quotient is `≥ 10⁻²⁰`, so it does not underflow to zero
    have hq_ge : (10 : ℚ) ^ (-20 : ℤ) ≤ NAVShares.toRat / v.sharesTotal.toRat := by
      rw [hNAV_val, le_div_iff₀ hST_pos]
      have hpow : (10 : ℚ) ^ (-20 : ℤ) * v.sharesTotal.toRat ≤ (10 : ℚ) ^ (-20 : ℤ) * (2 ^ 63 - 1) :=
        mul_le_mul_of_nonneg_left hSTcap (by positivity)
      have hnum : (10 : ℚ) ^ (-20 : ℤ) * (2 ^ 63 - 1) ≤ 1 := by
        rw [zpow_neg]; rw [show ((10:ℚ)^(20:ℤ)) = 100000000000000000000 from by norm_num]
        rw [inv_mul_le_iff₀ (by norm_num)]; norm_num
      linarith [hAT1]
    have hwit : ∃ w : Number, w.isNormalized ∧ w.toRat = (10 : ℚ) ^ (-20 : ℤ) := by
      refine ⟨⟨false, 1000000000000000000, -38⟩, Or.inr ⟨by decide, by decide, Or.inr (by decide), by
        unfold minExponent; decide, by unfold maxExponent; decide⟩, ?_⟩
      rw [Number.toRat_of_nonneg _ rfl]
      show ((1000000000000000000 : UInt64).toNat : ℚ) * (10 : ℚ) ^ (-38 : ℤ) = (10 : ℚ) ^ (-20 : ℤ)
      rw [show ((1000000000000000000 : UInt64).toNat : ℚ) = (10 : ℚ) ^ (18 : ℤ) from by
        norm_num [show (1000000000000000000 : UInt64).toNat = 1000000000000000000 from by decide]]
      rw [← zpow_add₀ (by norm_num : (10:ℚ) ≠ 0)]; norm_num
    obtain ⟨w, hw_norm, hw_val⟩ := hwit
    have hAN_pos : (0 : ℚ) < assetsNumber.toRat := by
      have hge := Number.RoundsToRepresentable.ge_of_ge_normalized assetsNumber _ hqrepr w hw_norm
        (by rw [hw_val]; exact hq_ge)
      rw [hw_val] at hge
      have : (0 : ℚ) < (10 : ℚ) ^ (-20 : ℤ) := by positivity
      linarith
    have hANm : assetsNumber.mantissa_ ≠ 0 :=
      Number.mantissa_ne_zero_of_toRat_ne_zero hAN_pos.ne'
    have hANnorm : assetsNumber.isNormalized :=
      operator_div_result_isNormalized NAVShares v.sharesTotal assetsNumber .to_nearest
        hNAVnorm hSTnorm hNAVm hSTm hdiv hANm
    have hANneg : assetsNumber.negative_ = false :=
      Number.negative_false_of_norm_nonneg _ hANnorm hAN_nn
    -- the downward `ofNumber .int64` conversion of the priced quotient
    obtain ⟨assetsOut, hof⟩ := STAmount.ofNumber_int64_ok assetsNumber .downward hANnorm hANneg
      (le_trans hAN_le hcap)
    obtain ⟨m, hm_val, hm_le, -, -⟩ :=
      ofNumber_downward_floor_int .int64 assetsNumber assetsOut (by decide) hANnorm hANneg hof
    obtain ⟨aN, haN_ok, haN_val, haN_norm⟩ :=
      STAmount.ofNumber_toNumber_exact_of_norm .int64 assetsNumber .downward assetsOut hANnorm hof
    have hassets_nn : 0 ≤ assetsOut.toRat :=
      STAmount.ofNumber_nonneg .int64 assetsNumber .downward assetsOut hANnorm hANneg hof
    -- relative payout bound: `assets ≤ (assetsTotal / sharesTotal) · (1 + ε)`
    have hpay_ub : assetsOut.toRat ≤
        v.assetsTotal.toRat / v.sharesTotal.toRat * (1 + 6 / (2 ^ 63 - 3)) := by
      have hqnn : (0 : ℚ) ≤ v.assetsTotal.toRat / v.sharesTotal.toRat :=
        div_nonneg hAnn (by linarith)
      have hqw := operator_div_rounds_to_nearest NAVShares v.sharesTotal assetsNumber
        hNAVnorm hSTnorm hdiv hANm
      simp only [RoundsWithin, RatValued.toRat] at hqw
      rw [hNAV_val, abs_of_nonneg hqnn] at hqw
      obtain ⟨-, hub⟩ := abs_le.mp hqw
      calc assetsOut.toRat = (m : ℚ) := hm_val
        _ ≤ assetsNumber.toRat := hm_le
        _ ≤ v.assetsTotal.toRat / v.sharesTotal.toRat * (1 + 6 / (2 ^ 63 - 3)) := by nlinarith [hub, hqnn]
    refine ⟨assetsOut, aN, ?_, haN_ok, haN_norm, haN_val, ?_, hassets_nn, ?_, hpay_ub⟩
    · rw [hint, hof]; rfl
    · rw [haN_val, hm_val]; exact Rat.den_intCast m
    · rw [hm_val]; exact le_trans hm_le hAN_le

/-- The emptied vault (all balances zero, no unrealized loss) re-validates: its
`to_lawful` re-check returns `.ok v'`. -/
private theorem emptyState_lawful (rv : RawVault) (hwf : rv.WF)
    (hLU0 : rv.lossUnrealized.toRat = 0)
    (hmpos : ∀ m ∈ rv.toExact.assetsMaximum, 0 < m) :
    ∃ v', ({rv with assetsAvailable := Number.zero, assetsTotal := Number.zero, sharesTotal := Number.zero} : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = {rv with assetsAvailable := Number.zero, assetsTotal := Number.zero, sharesTotal := Number.zero} := by
  set E : RawVault := {rv with assetsAvailable := Number.zero, assetsTotal := Number.zero, sharesTotal := Number.zero} with hE
  have hz : Number.zero.isNormalized := Or.inl rfl
  have hAT : E.toExact.assetsTotal = 0 := by simp only [hE, RawVault.toExact, Number.toRat_zero]
  have hAV : E.toExact.assetsAvailable = 0 := by simp only [hE, RawVault.toExact, Number.toRat_zero]
  have hST : E.toExact.sharesTotal = 0 := by
    simp only [hE, RawVault.toExact, Number.toRat_zero, Rat.num_zero, Int.toNat_zero]
  have hLU : E.toExact.lossUnrealized = 0 := hLU0
  have hAM : E.toExact.assetsMaximum = rv.toExact.assetsMaximum := rfl
  have hwfE : E.WF := ⟨hz, hz, hwf.assetsReserved_norm, hwf.assetsMaximum_norm, hz, hwf.lossUnrealized_norm,
      by simp only [hE, Number.toRat_zero, le_refl],
      by simp only [hE, Number.toRat_zero]; rfl, hwf.scale_integral, hwf.scale_le,
      Number.operator_sub_self_ok Number.zero .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · rw [hAT]
  · rw [hAV]
  · rw [hAV, hAT]
  · rw [hAM]; exact hmpos
  · rw [hST, hAT, hAV]; intro _; exact ⟨rfl, rfl⟩
  · rw [hAM, hAT]; intro m hm; exact le_of_lt (hmpos m hm)
  · rw [hLU]
  · rw [hLU, hAT, hAV]; norm_num
  · rw [hAT, hLU]; norm_num

/-- **The one-share withdrawal on an `int64` vault runs to a no-error success.** On
a reachable `int64`-asset vault with at least one share, a whole-number
`assetsTotal`, and both totals within `2 ^ 63 - 1`, the one-share withdrawal
returns `.ok r` with `r.error = none`.

The pricing prefix is total (`withdraw_oneShare_exchange`): the exchange returns a
priced `assets` at most `assetsTotal`, and the payout `toNumber` lift `aN` is
normalized and integer-valued. The `try`/`catch` wrapper forwards it
(`withdraw_oneShare_compute_of_exchange`), so the run reaches a success record.

Every guard is escaped:
* the funds guard cannot fire, since the payout is at most
  `assetsTotal = assetsAvailable` (`operator_lt_iff`);
* the share total conversion `ofNumber .int64 sharesTotal` is total
  (`ofNumber_int64_ok`);
* on the final exit (whole share total, `sharesTotal = 1`) the zero unrealized
  loss clears the `tefINTERNAL` guard and `ofNumber .int64 assetsAvailable` is
  total;
* on the non-final exit the stored decrements are total `operator_sub`s
  (`operator_sub_ok_of_normalized_cap`), and the precision-loss guard is escaped by
  the whole-unit dichotomy: a zero-mantissa payout skips the guard, and a nonzero
  (hence `≥ 1`) payout lowers the whole rounded `assetsTotal`, so the two rounded
  totals differ.

The `int64` scope is necessary; the statement is false for fractional vaults, where
a sub-ULP one-share payout trips the precision-loss guard (see `Vault.EmptyReady`).
-/
theorem withdraw_oneShare_run_ok (v : Vault) (hr : Vault.Reachable v)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hpos : 0 < v.toExact.sharesTotal)
    (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (hint : v.numericType = .int64)
    (hAint : v.assetsTotal.toRat.den = 1) :
    ∃ (r : WithdrawResult) (finalDebitNumber : Number),
      v.withdraw (.vaultShares oneShare) false = .ok r ∧ r.error = none ∧
      0 ≤ r.assets'.toRat ∧
      r.assets'.toNumber .to_nearest = .ok finalDebitNumber ∧
      finalDebitNumber.toRat = r.assets'.toRat ∧ finalDebitNumber.isNormalized := by
  have hpar : v.assetsAvailable = v.assetsTotal := Vault.Reachable.asset_parity v hr
  have hL0 : v.lossUnrealized.mantissa_ = 0 :=
    Number.toRat_eq_zero_iff.mp (Vault.Reachable.lossUnrealized_zero v hr)
  have hAnorm : v.assetsTotal.isNormalized := v.wf.assetsTotal_norm
  have hAnn : 0 ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
  have hAneg : v.assetsTotal.negative_ = false := Number.negative_false_of_norm_nonneg _ hAnorm hAnn
  have hAAnorm : v.assetsAvailable.isNormalized := v.wf.assetsAvailable_norm
  have hAAneg : v.assetsAvailable.negative_ = false := by rw [hpar]; exact hAneg
  have hAAcap : v.assetsAvailable.toRat ≤ 2 ^ 63 - 1 := by rw [hpar]; exact hcap
  have hSTnorm : v.sharesTotal.isNormalized := v.wf.sharesTotal_norm
  have hSTnn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
  have hSTneg : v.sharesTotal.negative_ = false := Number.negative_false_of_norm_nonneg _ hSTnorm hSTnn
  have hSTden : v.sharesTotal.toRat.den = 1 := v.wf.sharesTotal_int
  have hSTcap : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]; exact hfit
  have hST1 : (1 : ℚ) ≤ v.sharesTotal.toRat := by
    rw [← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
    have : (1 : ℕ) ≤ v.toExact.sharesTotal := hpos
    exact_mod_cast this
  -- the priced payout and its `toNumber` lift
  obtain ⟨assets, aN, hex, haN_ok, haN_norm, haN_val, haN_den, hassets_nn, hassets_le, hpay_ub⟩ :=
    withdraw_oneShare_exchange v hr hfit hpos hcap hint hAint
  have haN_neg : aN.negative_ = false :=
    Number.negative_false_of_norm_nonneg _ haN_norm (by rw [haN_val]; exact hassets_nn)
  have haN_cap : aN.toRat ≤ 2 ^ 63 - 1 := by rw [haN_val]; exact le_trans hassets_le hcap
  have hcompute : computeWithdrawByShares v oneShare false = .ok ⟨none, assets, oneShare⟩ :=
    withdraw_oneShare_compute_of_exchange v assets hex
  obtain ⟨sta, hsta⟩ := STAmount.ofNumber_int64_ok v.sharesTotal .to_nearest hSTnorm hSTneg hSTcap
  -- funds guard cannot fire: the payout is at most `assetsAvailable`
  have hfunds : v.assetsAvailable.operator_lt aN = false := by
    rw [Bool.eq_false_iff, ne_eq, operator_lt_iff v.assetsAvailable aN hAAnorm haN_norm, not_lt,
      hpar, haN_val]
    exact hassets_le
  -- zero unrealized loss clears the `tefINTERNAL` guard
  have hlossg : v.lossUnrealized.operator_ne Number.zero = false := by
    rw [Number.eq_zero_of_mantissa_zero v.lossUnrealized v.wf.lossUnrealized_norm hL0]; decide
  -- open the run, forward through the compute wrapper, the toNumber lift and the two guards
  unfold Vault.withdraw
  simp only []
  rw [hcompute, ok_bind,
      if_neg (show ¬ (⟨none, assets, oneShare⟩ : ComputeWithdrawResult).error.isSome = true from by simp),
      haN_ok, ok_bind,
      if_neg (show ¬ v.assetsAvailable.operator_lt aN = true from by rw [hfunds]; decide),
      hsta, ok_bind]
  by_cases hfin : oneShare.operator_eq sta = true
  · -- FINAL: the whole share total is redeemed, the vault is zeroed
    rw [if_pos hfin,
        if_neg (show ¬ v.lossUnrealized.operator_ne Number.zero = true from by rw [hlossg]; decide)]
    obtain ⟨allAvail, hallAvail⟩ :=
      STAmount.ofNumber_int64_ok v.assetsAvailable .to_nearest hAAnorm hAAneg hAAcap
    rw [hint, hallAvail, ok_bind]
    -- the emptied vault re-validates, so the `to_lawful` succeeds
    obtain ⟨v', htl, -⟩ :=
      emptyState_lawful v.toRawVault v.wf (Number.toRat_eq_zero_iff.mpr hL0) v.exact.assetsMaximum_pos
    rw [hint] at htl
    rw [htl, ok_bind]
    obtain ⟨finalDebitNumber, hfinalNumber, hfinalValue, hfinalNorm⟩ :=
      STAmount.ofNumber_toNumber_exact_of_norm .int64 v.assetsAvailable .to_nearest
        allAvail hAAnorm hallAvail
    refine ⟨_, finalDebitNumber, rfl, rfl, ?_, hfinalNumber, hfinalValue, hfinalNorm⟩
    exact STAmount.ofNumber_nonneg .int64 v.assetsAvailable .to_nearest allAvail
      hAAnorm hAAneg hallAvail
  · -- NON-FINAL: the stored balances decrement, and the precision guard is escaped
    have hfin' : oneShare.operator_eq sta = false := by
      cases h : oneShare.operator_eq sta with
      | true => exact absurd h hfin
      | false => rfl
    -- `sharesTotal ≥ 2`, so the whole payout is strictly below `assetsTotal`
    have hST2 : (2 : ℚ) ≤ v.sharesTotal.toRat := by
      have hiff := Vault.operator_eq_total_iff v sta oneShare (by rw [oneShare_toRat]; norm_num)
        oneShare_canonical oneShare_numericType hsta
      have hne : (1 : ℚ) ≠ v.sharesTotal.toRat := by
        rw [← oneShare_toRat]; intro heq
        rw [hiff.mpr heq] at hfin'; exact absurd hfin' (by decide)
      have hnum_q : (v.sharesTotal.toRat.num : ℚ) = v.sharesTotal.toRat := by
        have hh := Rat.num_div_den v.sharesTotal.toRat
        rw [hSTden, Nat.cast_one, div_one] at hh; exact hh
      rcases lt_or_eq_of_le hST1 with h | h
      · have h1 : (1 : ℤ) < v.sharesTotal.toRat.num := by
          have : (1 : ℚ) < (v.sharesTotal.toRat.num : ℚ) := by rw [hnum_q]; exact h
          exact_mod_cast this
        have h2 : (2 : ℚ) ≤ (v.sharesTotal.toRat.num : ℚ) := by exact_mod_cast (by omega : (2 : ℤ) ≤ v.sharesTotal.toRat.num)
        rw [hnum_q] at h2; exact h2
      · exact absurd h hne
    -- with `sharesTotal ≥ 2`, a positive `assetsTotal` strictly exceeds the whole payout
    have hpay_lt_of : 0 < v.assetsTotal.toRat → assets.toRat < v.assetsTotal.toRat := by
      intro hApos
      have hbound : v.assetsTotal.toRat / v.sharesTotal.toRat * (1 + 6 / (2 ^ 63 - 3)) <
          v.assetsTotal.toRat := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith [hApos, hST2]
      linarith [hpay_ub, hbound]
    -- shares burned lift, the two stored subtractions and the two roundings
    obtain ⟨sn, hsn_ok, hsn_val, hsn_norm⟩ := oneShare_toNumber .to_nearest
    obtain ⟨at', hat⟩ := Number.operator_sub_ok_of_normalized_cap v.assetsTotal aN .to_nearest
      hAnorm haN_norm hAneg haN_neg hcap haN_cap
    have hat_val : at'.toRat = v.assetsTotal.toRat - aN.toRat ∧ at'.toRat.den = 1 := by
      refine operator_sub_exact_int v.assetsTotal aN at' hAnorm haN_norm hAint haN_den ?_ hat
      have h1 : 0 ≤ v.assetsTotal.toRat - aN.toRat := by rw [haN_val]; linarith [hassets_le]
      have h2 : v.assetsTotal.toRat - aN.toRat ≤ 2 ^ 63 - 1 := by
        rw [haN_val]; linarith [hassets_nn, hcap]
      set d := v.assetsTotal.toRat - aN.toRat with hd
      have hden : d.den = 1 := by
        rw [hd, ce_eq_intCast_of_den_one hAint, ce_eq_intCast_of_den_one haN_den, ← Int.cast_sub]
        exact Rat.den_intCast _
      have hnum_q : (d.num : ℚ) = d := by
        have h := Rat.num_div_den d; rw [hden, Nat.cast_one, div_one] at h; exact h
      have hnum_nn : (0 : ℤ) ≤ d.num := by
        have : (0 : ℚ) ≤ (d.num : ℚ) := by rw [hnum_q]; exact h1
        exact_mod_cast this
      have hnum_le : d.num ≤ 2 ^ 63 - 1 := by
        have : (d.num : ℚ) ≤ 2 ^ 63 - 1 := by rw [hnum_q]; exact h2
        exact_mod_cast this
      show d.num.natAbs < 2 ^ 63
      omega
    have hat_nn : 0 ≤ at'.toRat := by rw [hat_val.1, haN_val]; linarith [hassets_le]
    have hat_norm : at'.isNormalized := by
      by_cases hAm0 : v.assetsTotal.mantissa_ = 0
      · -- insolvent: the payout is `0`, so `at' = assetsTotal` (a normalized zero)
        have haNm0 : aN.mantissa_ = 0 := by
          apply Number.toRat_eq_zero_iff.mp
          have hAT0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_iff.mpr hAm0
          rw [haN_val]; linarith [hassets_nn, hassets_le, hAT0]
        have heq : at' = v.assetsTotal :=
          Except.ok.inj (hat.symm.trans
            (Number.operator_sub_of_mantissa_zero v.assetsTotal aN .to_nearest haNm0))
        rw [heq]; exact hAnorm
      · have hApos : 0 < v.assetsTotal.toRat :=
          lt_of_le_of_ne hAnn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hAm0))
        have hp : 0 < at'.toRat := by rw [hat_val.1, haN_val]; linarith [hpay_lt_of hApos]
        exact operator_sub_isNormalized_to_nearest v.assetsTotal aN at' hAnorm haN_norm hat
          (Number.mantissa_ne_zero_of_toRat_ne_zero hp.ne')
    have hat_neg : at'.negative_ = false := Number.negative_false_of_norm_nonneg _ hat_norm hat_nn
    have hat_cap : at'.toRat ≤ 2 ^ 63 - 1 := by rw [hat_val.1, haN_val]; linarith [hassets_nn, hcap]
    have hsn_neg : sn.negative_ = false :=
      Number.negative_false_of_norm_nonneg _ hsn_norm (by rw [hsn_val]; norm_num)
    -- the two grid roundings and the two stored decrements
    obtain ⟨atr, hatr⟩ := STAmount.ofNumber_int64_ok v.assetsTotal .to_nearest hAnorm hAneg hcap
    obtain ⟨atr', hatr'⟩ := STAmount.ofNumber_int64_ok at' .to_nearest hat_norm hat_neg hat_cap
    obtain ⟨av', hav⟩ := Number.operator_sub_ok_of_normalized_cap v.assetsAvailable aN .to_nearest
      hAAnorm haN_norm hAAneg haN_neg hAAcap haN_cap
    obtain ⟨st', hst⟩ := Number.operator_sub_ok_of_normalized_cap v.sharesTotal sn .to_nearest
      hSTnorm hsn_norm hSTneg hsn_neg hSTcap (by rw [hsn_val]; norm_num)
    -- the priced value is exact through the two roundings
    have hatr_val : atr.toRat = v.assetsTotal.toRat :=
      STAmount.ofNumber_integral_exact .int64 v.assetsTotal .to_nearest atr (by decide) hAnorm hAint hatr
    have hatr'_val : atr'.toRat = at'.toRat :=
      STAmount.ofNumber_integral_exact .int64 at' .to_nearest atr' (by decide) hat_norm hat_val.2 hatr'
    obtain ⟨hatrIC, hatrNT⟩ :=
      STAmount.ofNumber_integral_canonical .int64 v.assetsTotal .to_nearest atr (by decide) hatr
    obtain ⟨hatr'IC, hatr'NT⟩ :=
      STAmount.ofNumber_integral_canonical .int64 at' .to_nearest atr' (by decide) hatr'
    have hint64max : NumericType.int64.maxValue.toNat = 9223372036854775807 := by decide
    have hatrEC : atr.ExactCanonical := Or.inr ⟨hatrIC, by
      have h := hatrIC.in_range; rw [hatrNT, hint64max] at h; omega⟩
    have hatr'EC : atr'.ExactCanonical := Or.inr ⟨hatr'IC, by
      have h := hatr'IC.in_range; rw [hatr'NT, hint64max] at h; omega⟩
    have hcmpcomp : STAmount.areComparable atr atr' = true := by
      simp only [STAmount.areComparable, hatrNT, hatr'NT, beq_self_eq_true]
    -- precision-loss guard is escaped by the whole-unit dichotomy
    have hguard : (aN.mantissa_ != 0 && atr.operator_eq atr') = false := by
      by_cases ham : aN.mantissa_ = 0
      · rw [show (aN.mantissa_ != 0) = false from by rw [ham]; decide, Bool.false_and]
      · -- nonzero payout is a whole unit `≥ 1`, so the rounded totals differ
        have hpay_pos : 0 < aN.toRat :=
          lt_of_le_of_ne (by rw [haN_val]; exact hassets_nn)
            (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero aN ham))
        have hAT_pos : 0 < v.assetsTotal.toRat := lt_of_lt_of_le hpay_pos (by rw [haN_val]; exact hassets_le)
        have hat_pos : 0 < at'.toRat := by rw [hat_val.1, haN_val]; linarith [hpay_lt_of hAT_pos]
        have hCF : STAmount.CmpFaithful atr atr' :=
          STAmount.CmpFaithful.ofExactCanonical atr atr' hatrEC hatr'EC hcmpcomp
            (fun h => absurd ((STAmount.toRat_eq_zero_iff atr).mpr h)
              (by rw [hatr_val]; exact hAT_pos.ne'))
            (fun h => absurd ((STAmount.toRat_eq_zero_iff atr').mpr h)
              (by rw [hatr'_val]; exact hat_pos.ne'))
        have hne : atr.toRat ≠ atr'.toRat := by
          rw [hatr_val, hatr'_val, hat_val.1]; linarith [hpay_pos]
        rw [show (aN.mantissa_ != 0) = true from by rw [bne_iff_ne]; exact ham, Bool.true_and,
          STAmount.operator_eq_eq_proof atr atr' hCF]
        exact decide_eq_false hne
    -- The source clamps the negated raw payout before every non-final debit.
    -- On this integral one-share path the clamp is an executable sign-clear; it
    -- need not preserve the raw record, so we derive its final Number separately.
    obtain ⟨hshape_nt, hshape_off, hshape_val⟩ :=
      Vault.sharesToAssetsWithdraw_integral_shape v oneShare assets false
        (by rw [hint]; decide) hex
    have hneg_integral : assets.operator_neg.integral = true := by
      change assets.operator_neg.mNumericType.isIntegral = true
      rw [STAmount.operator_neg_mNumericType, hshape_nt, hint]
      decide
    let assetDebited : STAmount :=
      if assets.operator_neg.negative then assets.operator_neg.operator_neg else assets.operator_neg
    have hclamp : clampToSumExponent v.assetsTotal assets.operator_neg = .ok assetDebited := by
      unfold clampToSumExponent
      rw [hneg_integral]
      simp [assetDebited]
      rfl
    have hdebit_nt : assetDebited.mNumericType = v.numericType := by
      dsimp [assetDebited]
      split <;> simp [STAmount.operator_neg_mNumericType, hshape_nt]
    have hdebit_off : assetDebited.mOffset = 0 := by
      dsimp [assetDebited]
      split <;> simp [STAmount.operator_neg_mOffset, hshape_off]
    have hdebit_mag : assetDebited.mValue.toNat ≤ maxRep.toNat := by
      dsimp [assetDebited]
      split <;> simp [STAmount.operator_neg_mValue, hshape_val]
    have hdebit_integral : assetDebited.integral = true := by
      change assetDebited.mNumericType.isIntegral = true
      rw [hdebit_nt, hint]
      decide
    have hprecision : assetDebited.isFractionalNonPositive = .ok false := by
      unfold STAmount.isFractionalNonPositive
      rw [hdebit_integral]
      rfl
    have hsign_or_zero : assets.operator_neg.negative = true ∨ assets.toRat = 0 := by
      by_cases hnegative : assets.operator_neg.negative = true
      · exact Or.inl hnegative
      · right
        have hnegative_false : assets.operator_neg.negative = false :=
          Bool.eq_false_of_not_eq_true hnegative
        by_cases hzero : assets.mValue = 0
        · exact STAmount.toRat_eq_zero_of_mValue_zero assets hzero
        · have hbeq : (assets.mValue == 0) = false := beq_eq_false_iff_ne.mpr hzero
          have hraw_negative : assets.mIsNegative = true := by
            unfold STAmount.operator_neg at hnegative_false
            rw [hbeq] at hnegative_false
            change (!assets.mIsNegative) = false at hnegative_false
            cases hbit : assets.mIsNegative <;> simp [hbit] at hnegative_false ⊢
          have hnat_ne : assets.mValue.toNat ≠ 0 := by
            intro hnat
            apply hzero
            exact UInt64.toNat_inj.mp hnat
          have hnat : 0 < assets.mValue.toNat := Nat.pos_of_ne_zero hnat_ne
          have hpow : 0 < (10 : ℚ) ^ assets.mOffset := zpow_pos (by norm_num) _
          have hproduct : 0 < (assets.mValue.toNat : ℚ) * 10 ^ assets.mOffset :=
            mul_pos (by exact_mod_cast hnat) hpow
          rw [STAmount.toRat_of_neg assets hraw_negative] at hassets_nn
          linarith
    have hdebit_val : assetDebited.toRat = assets.toRat := by
      rcases hsign_or_zero with hneg | hzero
      · dsimp [assetDebited]
        rw [if_pos hneg, STAmount.operator_neg_toRat, STAmount.operator_neg_toRat]
        ring
      · dsimp [assetDebited]
        cases hbit : assets.operator_neg.negative with
        | false =>
          rw [if_neg (by simp [hbit]), STAmount.operator_neg_toRat, hzero]
          ring
        | true =>
          rw [if_pos (by simp [hbit]), STAmount.operator_neg_toRat,
            STAmount.operator_neg_toRat, hzero]
          ring
    obtain ⟨debitNumber, hdebit_ok, hdebit_number_val, hdebit_norm, -⟩ :=
      STAmount.toNumber_integral_exact' assetDebited .to_nearest
        (by rw [hdebit_nt, hint]; decide) hdebit_off hdebit_mag
    have hdebit_number_eq : debitNumber = aN :=
      hdebit_norm.toRat_inj haN_norm (by rw [hdebit_number_val, hdebit_val, haN_val])
    subst debitNumber
    -- forward the source-faithful non-final tail and read off the success record
    rw [if_neg (show ¬ oneShare.operator_eq sta = true from by rw [hfin']; decide),
      hclamp, ok_bind, hprecision, ok_bind, hdebit_ok, ok_bind,
      hsn_ok, ok_bind, hat, ok_bind, hint, hatr, ok_bind, hatr', ok_bind,
      if_neg (show ¬ (aN.mantissa_ != 0 && atr.operator_eq atr') = true from by rw [hguard]; decide),
      hav, ok_bind, hst, ok_bind]
    -- the decremented vault re-validates, so the in-op `to_lawful` succeeds:
    -- asset parity gives `assetsAvailable' = assetsTotal'`, and the share total
    -- drops by one whole unit but stays positive
    have hav_eq : av' = at' := by
      have h := hav; rw [hpar] at h; exact Except.ok.inj (h.symm.trans hat)
    have hsn_den : sn.toRat.den = 1 := by rw [hsn_val]; rfl
    have hst_val : st'.toRat = v.sharesTotal.toRat - sn.toRat ∧ st'.toRat.den = 1 := by
      refine operator_sub_exact_int v.sharesTotal sn st' hSTnorm hsn_norm hSTden hsn_den ?_ hst
      have h1 : 0 ≤ v.sharesTotal.toRat - sn.toRat := by rw [hsn_val]; linarith [hST2]
      have h2 : v.sharesTotal.toRat - sn.toRat ≤ 2 ^ 63 - 1 := by rw [hsn_val]; linarith [hSTcap]
      set d := v.sharesTotal.toRat - sn.toRat with hd
      have hden : d.den = 1 := by
        rw [hd, ce_eq_intCast_of_den_one hSTden, ce_eq_intCast_of_den_one hsn_den, ← Int.cast_sub]
        exact Rat.den_intCast _
      have hnum_q : (d.num : ℚ) = d := by
        have h := Rat.num_div_den d; rw [hden, Nat.cast_one, div_one] at h; exact h
      have hnum_nn : (0 : ℤ) ≤ d.num := by
        have : (0 : ℚ) ≤ (d.num : ℚ) := by rw [hnum_q]; exact h1
        exact_mod_cast this
      have hnum_le : d.num ≤ 2 ^ 63 - 1 := by
        have : (d.num : ℚ) ≤ 2 ^ 63 - 1 := by rw [hnum_q]; exact h2
        exact_mod_cast this
      show d.num.natAbs < 2 ^ 63
      omega
    have hst_pos : 0 < st'.toRat := by rw [hst_val.1, hsn_val]; linarith [hST2]
    have hst_norm : st'.isNormalized :=
      operator_sub_isNormalized_to_nearest v.sharesTotal sn st' hSTnorm hsn_norm hst
        (Number.mantissa_ne_zero_of_toRat_ne_zero hst_pos.ne')
    have haN_nn : 0 ≤ aN.toRat := by rw [haN_val]; exact hassets_nn
    have hLU0 : v.lossUnrealized.toRat = 0 := Number.toRat_eq_zero_iff.mpr hL0
    have hwfN : ({v with assetsAvailable := av', assetsTotal := at', sharesTotal := st'} : RawVault).WF :=
      ⟨hat_norm, by rw [hav_eq]; exact hat_norm, v.wf.assetsReserved_norm,
        v.wf.assetsMaximum_norm, hst_norm, v.wf.lossUnrealized_norm, le_of_lt hst_pos, hst_val.2, v.wf.scale_integral,
        v.wf.scale_le, by rw [hav_eq]; exact Number.operator_sub_self_ok at' .downward⟩
    have hvalidN : ({v with assetsAvailable := av', assetsTotal := at', sharesTotal := st'} : RawVault).Valid := by
      apply (RawVault.valid_iff_exact _ hwfN).mpr
      refine ⟨hat_nn, by show (0:ℚ) ≤ av'.toRat; rw [hav_eq]; exact hat_nn,
        by show av'.toRat ≤ at'.toRat; rw [hav_eq], v.exact.assetsMaximum_pos,
        ?_, ?_, ?_, ?_, ?_⟩
      · intro h0; exfalso
        have h0' : st'.toRat.num.toNat = 0 := h0
        have hp : 0 < st'.toRat.num := Rat.num_pos.mpr hst_pos
        omega
      · intro m hm; show at'.toRat ≤ m
        have hc : v.assetsTotal.toRat ≤ m := v.exact.cap m hm
        rw [hat_val.1]; linarith [haN_nn]
      · show (0:ℚ) ≤ v.lossUnrealized.toRat; rw [hLU0]
      · show v.lossUnrealized.toRat ≤ at'.toRat - av'.toRat; rw [hLU0, hav_eq]; simp
      · show (0:ℚ) ≤ at'.toRat - v.lossUnrealized.toRat; rw [hLU0, sub_zero]; exact hat_nn
    obtain ⟨v', htl, -⟩ := RawVault.to_lawful_ok_of hwfN hvalidN
    rw [hint] at htl
    rw [htl, ok_bind]
    refine ⟨_, aN, rfl, rfl, ?_, hdebit_ok, hdebit_number_val, hdebit_norm⟩
    rw [hdebit_val]
    exact hassets_nn

/-- **Preservation of the asset representability rail.** A one-share withdrawal
never increases `assetsTotal`: the final exit zeroes it, and a non-final exit
stores `operator_sub assetsTotal payout` with a nonnegative payout, which a
`to_nearest` subtraction keeps at or below `assetsTotal`. So the `EmptyReady`
`assetsCap` bound is maintained along the peeling sequence. -/
theorem withdraw_oneShare_assetsTotal_le (v : Vault) (hr : Vault.Reachable v)
    (r : WithdrawResult) (finalDebitNumber : Number)
    (hok : v.withdraw (.vaultShares oneShare) false = .ok r) (herr : r.error = none)
    (hfinalNN : 0 ≤ r.assets'.toRat)
    (hfinalNumber : r.assets'.toNumber .to_nearest = .ok finalDebitNumber)
    (hfinalValue : finalDebitNumber.toRat = r.assets'.toRat)
    (hfinalNorm : finalDebitNumber.isNormalized) :
    r.vault'.assetsTotal.toRat ≤ v.assetsTotal.toRat := by
  obtain ⟨cw, rawAssetsNumber, sta, hcomp, hcwerr, hraw, hlt, hsta, hsbeq, hbranch⟩ :=
    Vault.withdraw_success_reduces v (.vaultShares oneShare) false r hok herr
  rcases hbranch with ⟨_, _, allAvailable, _, _, hstate⟩ |
      ⟨_, _, debitNumber, assetsTotal', assetsAvailable', sharesTotal', assetDebited,
        assetsTotalRounded, assetsTotalRounded', hsbn, hclamp, hprecision, hdebitNumber,
        hat, hatr, hatr', hguard, hav, hst, hrAssets, hstate⟩
  · -- final: assetsTotal is zeroed
    rw [hstate]
    show (Number.zero).toRat ≤ v.assetsTotal.toRat
    rw [Number.toRat_zero]
    exact v.exact.assetsTotal_nonneg
  · -- non-final: the final (clamped) debit—not the raw quote—drives `hat`.
    have hnumberEq : finalDebitNumber = debitNumber := by
      rw [hrAssets] at hfinalNumber
      exact Except.ok.inj (hfinalNumber.symm.trans hdebitNumber)
    have hdebitNorm : debitNumber.isNormalized := by rw [← hnumberEq]; exact hfinalNorm
    have hdebitNN : 0 ≤ debitNumber.toRat := by
      rw [← hnumberEq, hfinalValue]
      exact hfinalNN
    rw [hstate]
    show assetsTotal'.toRat ≤ v.assetsTotal.toRat
    exact operator_sub_le_of_le_normalized v.assetsTotal debitNumber assetsTotal' v.assetsTotal
      v.wf.assetsTotal_norm hdebitNorm hat v.wf.assetsTotal_norm (by linarith)

/-- **The arithmetic crux (single blocking lemma).** On a reachable, loss-free
vault with at least one share, withdrawing exactly one share runs to a success
record whose stored share total is strictly smaller.

The proof splits on the run's final / non-final branch (exposed by
`withdraw_success_reduces`). A final withdrawal zeroes the vault, dropping the
stored total to zero. A non-final withdrawal burns exactly one share
(`withdraw_sharesBurned_exact`), so `withdraw_vault_updates` stores
`sharesTotal - 1`, which is strictly smaller than `sharesTotal ≥ 1`. Both branches
therefore strictly lower the stored total.

The one remaining input, that the one-share run reaches a success record at all
(no throw, no rejecting `TER`), is isolated as `withdraw_oneShare_run_ok`. -/
theorem withdraw_one_share_step (v : Vault) (hr : Vault.Reachable v)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hpos : 0 < v.toExact.sharesTotal)
    (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (hint : v.numericType = .int64)
    (hAint : v.assetsTotal.toRat.den = 1) :
    ∃ (r : WithdrawResult) (finalDebitNumber : Number),
      v.withdraw (.vaultShares oneShare) false = .ok r ∧
      r.error = none ∧ 0 ≤ r.assets'.toRat ∧
      r.assets'.toNumber .to_nearest = .ok finalDebitNumber ∧
      finalDebitNumber.toRat = r.assets'.toRat ∧ finalDebitNumber.isNormalized ∧
      r.vault'.toExact.sharesTotal < v.toExact.sharesTotal := by
  obtain ⟨r, finalDebitNumber, hok, herr, hpnn, hfinalNumber, hfinalValue, hfinalNorm⟩ :=
    withdraw_oneShare_run_ok v hr hfit hpos hcap hint hAint
  refine ⟨r, finalDebitNumber, hok, herr, hpnn, hfinalNumber, hfinalValue, hfinalNorm, ?_⟩
  -- the run burns exactly the named single share
  have hsb : r.sharesBurned = oneShare :=
    Vault.withdraw_sharesBurned_exact v oneShare false r hok herr
  -- reduce the successful run to expose the final / non-final branch
  obtain ⟨cw, aN, sta, hcomp, hcwerr, haN, hlt, hsta, hsbeq, hbranch⟩ :=
    Vault.withdraw_success_reduces v (.vaultShares oneShare) false r hok herr
  rcases hbranch with ⟨_, _, allAvailable, _, hreq⟩ |
      ⟨hfineq, sbn, debitNumber, assetsTotal', assetsAvailable', sharesTotal', assetDebited,
        assetsTotalRounded, assetsTotalRounded', hsbn, hclamp, hprecision, hdebitNumber,
        hat, hatr, hatr', hguard, hav, hst, hstate⟩
  · -- final withdrawal: the vault is zeroed, so the stored total drops to `0`
    have hz : r.vault'.sharesTotal = Number.zero := by rw [hreq.2]
    have hzz : r.vault'.toExact.sharesTotal = 0 := by
      show r.vault'.sharesTotal.toRat.num.toNat = 0
      rw [hz, Number.toRat_zero]; simp
    rw [hzz]; exact hpos
  · -- non-final withdrawal: the stored total drops by exactly one share
    have hL : v.toExact.lossUnrealized = 0 := Vault.Reachable.lossUnrealized_zero v hr
    have hfin : r.sharesBurned.operator_eq sta = false := by rw [hsbeq]; exact hfineq
    have hpnn' : 0 ≤ r.assets'.toRat := hpnn
    -- The success reduction already exposes the final share-debit and exact
    -- state equation.  Use that final state, never a raw/final identity.
    have hsbn_r : r.sharesBurned.toNumber .to_nearest = .ok sbn := by
      rw [hsbeq]
      exact hsbn
    obtain ⟨sn, hsn_ok, hsn_val, hsn_norm, hsn_den⟩ :=
      STAmount.toNumber_integral_exact' r.sharesBurned .to_nearest
        (by rw [hsb]; decide) (by rw [hsb]; rfl) (by rw [hsb]; decide)
    have hsb_eq : sbn = sn := by
      rw [hsn_ok] at hsbn_r
      exact (Except.ok.inj hsbn_r).symm
    subst sbn
    have hsn_den' : sn.toRat.den = 1 := by
      rw [hsn_val, hsb, oneShare_toRat]
      rfl
    have hst_val : sharesTotal'.toRat = v.sharesTotal.toRat - sn.toRat ∧
        sharesTotal'.toRat.den = 1 := by
      refine operator_sub_exact_int v.sharesTotal sn sharesTotal' v.wf.sharesTotal_norm hsn_norm
        v.wf.sharesTotal_int hsn_den' ?_ hst
      have h1 : 0 ≤ v.sharesTotal.toRat - sn.toRat := by
        rw [hsn_val, hsb, oneShare_toRat, ← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
        have hnat : (1 : ℚ) ≤ (v.toExact.sharesTotal : ℚ) := by
          exact_mod_cast (show 1 ≤ v.toExact.sharesTotal from hpos)
        linarith
      have h2 : v.sharesTotal.toRat - sn.toRat ≤ 2 ^ 63 - 1 := by
        rw [hsn_val, hsb, oneShare_toRat, ← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf]
        linarith [hfit]
      set d := v.sharesTotal.toRat - sn.toRat with hd
      have hden : d.den = 1 := by
        rw [hd, ce_eq_intCast_of_den_one v.wf.sharesTotal_int,
          ce_eq_intCast_of_den_one hsn_den', ← Int.cast_sub]
        exact Rat.den_intCast _
      have hnum_q : (d.num : ℚ) = d := by
        have h := Rat.num_div_den d
        rw [hden, Nat.cast_one, div_one] at h
        exact h
      have hnum_nn : (0 : ℤ) ≤ d.num := by
        have : (0 : ℚ) ≤ (d.num : ℚ) := by rw [hnum_q]; exact h1
        exact_mod_cast this
      have hnum_le : d.num ≤ 2 ^ 63 - 1 := by
        have : (d.num : ℚ) ≤ 2 ^ 63 - 1 := by rw [hnum_q]; exact h2
        exact_mod_cast this
      show d.num.natAbs < 2 ^ 63
      omega
    have hNpos : 1 ≤ v.toExact.sharesTotal := hpos
    have hstateShares : r.vault'.sharesTotal = sharesTotal' := by
      change r.vault'.toRawVault.sharesTotal = sharesTotal'
      rw [hstate.2]
    have hqeq : r.vault'.sharesTotal.toRat = ((v.toExact.sharesTotal - 1 : ℕ) : ℚ) := by
      rw [hstateShares, hst_val.1, hsn_val, hsb, oneShare_toRat,
        ← RawVault.WF.toExact_sharesTotal v.toRawVault v.wf, Nat.cast_sub hNpos, Nat.cast_one]
    show r.vault'.sharesTotal.toRat.num.toNat < v.toExact.sharesTotal
    rw [hqeq]
    have hnn' : (0 : ℤ) ≤ ((v.toExact.sharesTotal - 1 : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [show (((v.toExact.sharesTotal - 1 : ℕ) : ℚ)).num.toNat = v.toExact.sharesTotal - 1 from by
      rw [Rat.num_natCast, Int.toNat_natCast]]
    omega

/-- **A one-share `int64` withdrawal preserves the `int64` type and the whole-number
`assetsTotal`.** The result vault carries the vault's numeric type unchanged (both
exits rewrite only the three balance fields), and its stored `assetsTotal` is a whole
number: the final exit zeroes it, the non-final exit stores the integer difference
`assetsTotal - payout` (both whole, the payout being an `int64` amount). -/
theorem withdraw_oneShare_result_int64 (v : Vault) (hr : Vault.Reachable v)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hpos : 0 < v.toExact.sharesTotal)
    (hint : v.numericType = .int64) (hAint : v.assetsTotal.toRat.den = 1)
    (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (r : WithdrawResult)
    (hok : v.withdraw (.vaultShares oneShare) false = .ok r) (herr : r.error = none) :
    r.vault'.numericType = .int64 ∧ r.vault'.assetsTotal.toRat.den = 1 := by
  have hsb : r.sharesBurned = oneShare :=
    Vault.withdraw_sharesBurned_exact v oneShare false r hok herr
  obtain ⟨assets, rawNumber, hraw, hrawNumber, hrawNorm, hrawValue, hrawDen,
    hrawNN, hrawLe, hrawBound⟩ :=
    withdraw_oneShare_exchange v hr hfit hpos hcap hint hAint
  obtain ⟨cw, rawAssetsNumber, sta, hcomp, hcwerr, hrawToNumber, hlt, hsta, hsbeq, hbranch⟩ :=
    Vault.withdraw_success_reduces v (.vaultShares oneShare) false r hok herr
  rcases hbranch with ⟨_, _, allAvail, _, hreq⟩ |
      ⟨hfineq, sbn, debitNumber, at', av', st', assetDebited, atr, atr', hsbn, hclamp,
        hprecision, hdebitNumber, hat, hatr, hatr', hg, hav, hst2, hr'⟩
  · refine ⟨by rw [hreq.2]; exact hint, ?_⟩
    rw [hreq.2]
    show Number.zero.toRat.den = 1
    rw [Number.toRat_zero]
    norm_num
  · have hprice : v.sharesToAssetsWithdraw oneShare false = .ok cw.assets' :=
      (computeWithdrawByShares_none_reduces v oneShare false cw hcomp hcwerr).1
    have hcwassets : cw.assets' = assets :=
      Except.ok.inj (hprice.symm.trans hraw)
    have hrawN_eq : rawAssetsNumber = rawNumber := by
      rw [hcwassets] at hrawToNumber
      exact Except.ok.inj (hrawToNumber.symm.trans hrawNumber)
    subst rawAssetsNumber
    have hshape := Vault.sharesToAssetsWithdraw_integral_shape v oneShare assets false
      (by rw [hint]; decide) hraw
    obtain ⟨hshape_nt, hshape_off, hshape_val⟩ := hshape
    have hneg_integral : assets.operator_neg.integral = true := by
      change assets.operator_neg.mNumericType.isIntegral = true
      rw [STAmount.operator_neg_mNumericType, hshape_nt, hint]
      decide
    have hdebit_eq : assetDebited =
        if assets.operator_neg.negative then assets.operator_neg.operator_neg else assets.operator_neg := by
      rw [hcwassets] at hclamp
      unfold clampToSumExponent at hclamp
      simp only [hneg_integral, ↓reduceIte] at hclamp
      exact (Except.ok.inj hclamp).symm
    have hdebit_nt : assetDebited.mNumericType = v.numericType := by
      rw [hdebit_eq]
      split <;> simp [STAmount.operator_neg_mNumericType, hshape_nt]
    have hdebit_off : assetDebited.mOffset = 0 := by
      rw [hdebit_eq]
      split <;> simp [STAmount.operator_neg_mOffset, hshape_off]
    have hdebit_val : assetDebited.mValue.toNat ≤ maxRep.toNat := by
      rw [hdebit_eq]
      split <;> simp [STAmount.operator_neg_mValue, hshape_val]
    obtain ⟨finalNumber, hfinalOk, hfinalValue, hfinalNorm, hfinalDen⟩ :=
      STAmount.toNumber_integral_exact' assetDebited .to_nearest
        (by rw [hdebit_nt, hint]; decide) hdebit_off hdebit_val
    have hnumberEq : debitNumber = finalNumber := by
      rw [hfinalOk] at hdebitNumber
      exact (Except.ok.inj hdebitNumber).symm
    subst debitNumber
    have hsign_or_zero : assets.operator_neg.negative = true ∨ assets.toRat = 0 := by
      by_cases hnegative : assets.operator_neg.negative = true
      · exact Or.inl hnegative
      · right
        have hnegative_false : assets.operator_neg.negative = false := Bool.eq_false_of_not_eq_true hnegative
        by_cases hzero : assets.mValue = 0
        · exact STAmount.toRat_eq_zero_of_mValue_zero assets hzero
        · have hbeq : (assets.mValue == 0) = false := beq_eq_false_iff_ne.mpr hzero
          have hraw_negative : assets.mIsNegative = true := by
            unfold STAmount.operator_neg at hnegative_false
            rw [hbeq] at hnegative_false
            change (!assets.mIsNegative) = false at hnegative_false
            cases hbit : assets.mIsNegative <;> simp [hbit] at hnegative_false ⊢
          have hnat : 0 < assets.mValue.toNat := Nat.pos_of_ne_zero (fun hz => hzero (UInt64.toNat_inj.mp hz))
          have hpow : 0 < (10 : ℚ) ^ assets.mOffset := zpow_pos (by norm_num) _
          have hproduct : 0 < (assets.mValue.toNat : ℚ) * 10 ^ assets.mOffset :=
            mul_pos (by exact_mod_cast hnat) hpow
          rw [STAmount.toRat_of_neg assets hraw_negative] at hrawNN
          linarith
    have hfinalRaw : finalNumber.toRat = assets.toRat := by
      rw [hfinalValue, hdebit_eq]
      rcases hsign_or_zero with hneg | hzero
      · rw [if_pos hneg, STAmount.operator_neg_toRat, STAmount.operator_neg_toRat]
        ring
      · cases hbit : assets.operator_neg.negative <;>
          simp [hbit, STAmount.operator_neg_toRat, hzero]
    have hfinalDen' : finalNumber.toRat.den = 1 := by
      rw [hfinalValue]
      exact hfinalDen
    have hfinalNN : 0 ≤ finalNumber.toRat := by rw [hfinalRaw]; exact hrawNN
    have hfinalLe : finalNumber.toRat ≤ v.assetsTotal.toRat := by rw [hfinalRaw]; exact hrawLe
    refine ⟨by
      change r.vault'.toRawVault.numericType = .int64
      rw [hr'.2]
      exact hint, ?_⟩
    change r.vault'.toRawVault.assetsTotal.toRat.den = 1
    rw [hr'.2]
    refine (operator_sub_exact_int v.assetsTotal finalNumber at' v.wf.assetsTotal_norm hfinalNorm hAint
      hfinalDen' ?_ hat).2
    set d := v.assetsTotal.toRat - finalNumber.toRat with hd
    have h1 : 0 ≤ d := by rw [hd]; linarith
    have h2 : d ≤ 2 ^ 63 - 1 := by rw [hd]; linarith [v.exact.assetsTotal_nonneg, hcap, hfinalNN]
    have hden : d.den = 1 := by
      rw [hd, ce_eq_intCast_of_den_one hAint, ce_eq_intCast_of_den_one hfinalDen', ← Int.cast_sub]
      exact Rat.den_intCast _
    have hnum_q : (d.num : ℚ) = d := by
      have h := Rat.num_div_den d
      rw [hden, Nat.cast_one, div_one] at h
      exact h
    have hnum_nn : (0 : ℤ) ≤ d.num := by
      have : (0 : ℚ) ≤ (d.num : ℚ) := by rw [hnum_q]; exact h1
      exact_mod_cast this
    have hnum_le : d.num ≤ 2 ^ 63 - 1 := by
      have : (d.num : ℚ) ≤ 2 ^ 63 - 1 := by rw [hnum_q]; exact h2
      exact_mod_cast this
    show d.num.natAbs < 2 ^ 63
    omega

/-- The result of a one-share withdrawal on an `EmptyReady` vault is again
`EmptyReady`: reachability closes under the `withdraw` constructor (a single
canonical `int64` share within the share total), the share total (strictly
smaller) still fits the `int64` domain, the asset representability rail is
preserved because the withdrawal does not increase `assetsTotal`, and the `int64`
type and whole-number `assetsTotal` are preserved
(`withdraw_oneShare_result_int64`). -/
theorem withdraw_one_share_ready (v : Vault) (hv : Vault.EmptyReady v)
    (hpos : 0 < v.toExact.sharesTotal) (r : WithdrawResult) (finalDebitNumber : Number)
    (hok : v.withdraw (.vaultShares oneShare) false = .ok r) (herr : r.error = none)
    (hfinalNN : 0 ≤ r.assets'.toRat)
    (hfinalNumber : r.assets'.toNumber .to_nearest = .ok finalDebitNumber)
    (hfinalValue : finalDebitNumber.toRat = r.assets'.toRat)
    (hfinalNorm : finalDebitNumber.isNormalized)
    (hdec : r.vault'.toExact.sharesTotal < v.toExact.sharesTotal) :
    Vault.EmptyReady r.vault' := by
  have hsb : r.sharesBurned = oneShare :=
    Vault.withdraw_sharesBurned_exact v oneShare false r hok herr
  have hle : r.sharesBurned.toRat ≤ (v.toExact.sharesTotal : ℚ) := by
    rw [hsb, oneShare_toRat]
    have : (1 : ℕ) ≤ v.toExact.sharesTotal := hpos
    exact_mod_cast this
  have hreach : Vault.Reachable r.vault' :=
    Vault.Reachable.withdraw v (.vaultShares oneShare) false r hv.reachable hok
      (by rw [hsb]; exact oneShare_integralCanonical)
      (by rw [hsb]; exact oneShare_numericType)
      (by rw [hsb]; exact oneShare_negative)
      hle hv.fits
  obtain ⟨hnt', hAint'⟩ :=
    withdraw_oneShare_result_int64 v hv.reachable hv.fits hpos hv.int64 hv.assetsInt hv.assetsCap r hok herr
  refine ⟨hreach, ?_, ?_, hnt', hAint'⟩
  · have hcast : (r.vault'.toExact.sharesTotal : ℚ) < (v.toExact.sharesTotal : ℚ) := by
      exact_mod_cast hdec
    linarith [hv.fits]
  · exact le_trans (withdraw_oneShare_assetsTotal_le v hv.reachable r finalDebitNumber hok herr
      hfinalNN hfinalNumber hfinalValue hfinalNorm) hv.assetsCap

/-- Well-founded core: strong induction on the stored share total. At zero shares
the vault is already empty (`done`); otherwise one share is withdrawn, the total
strictly drops, and the smaller `EmptyReady` result is emptied by the induction
hypothesis (`step`). -/
theorem canEmpty_of_emptyReady_aux :
    ∀ (n : ℕ) (v : Vault), Vault.EmptyReady v → v.toExact.sharesTotal = n → CanEmpty v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv hn
    rcases Nat.eq_zero_or_pos n with hz | hposn
    · exact CanEmpty.done v (hn.trans hz)
    · have hpos : 0 < v.toExact.sharesTotal := hn ▸ hposn
      obtain ⟨r, finalDebitNumber, hok, herr, hpnn, hfinalNumber, hfinalValue, hfinalNorm, hdec⟩ :=
        withdraw_one_share_step v hv.reachable hv.fits hpos hv.assetsCap hv.int64 hv.assetsInt
      have hready : Vault.EmptyReady r.vault' :=
        withdraw_one_share_ready v hv hpos r finalDebitNumber hok herr hpnn hfinalNumber hfinalValue
          hfinalNorm hdec
      have hdecn : r.vault'.toExact.sharesTotal < n := hn ▸ hdec
      exact CanEmpty.step v (.vaultShares oneShare) r hok herr
        (ih _ hdecn r.vault' hready rfl)

/-- Every `EmptyReady` vault can be emptied. -/
theorem canEmpty_of_emptyReady (v : Vault) (hv : Vault.EmptyReady v) : CanEmpty v :=
  canEmpty_of_emptyReady_aux v.toExact.sharesTotal v hv rfl

/-- Proof body of the `CanEmpty` headline: a reachable `int64`-asset vault whose
stored share total fits the `int64` domain, whose `assetsTotal` is representable
(the C++ `accountSend` rail), and whose `assetsTotal` is a whole number can be
emptied. Loss-freeness is not assumed, it is a reachability corollary. The `int64`
scope is necessary: on a fractional vault a sub-ULP one-share payout trips the
precision-loss guard (see `Vault.EmptyReady`). -/
theorem Vault.Reachable.canEmpty_proof (v : Vault) (hr : Vault.Reachable v)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hcap : v.assetsTotal.toRat ≤ 2 ^ 63 - 1)
    (hint : v.numericType = .int64)
    (hAint : v.assetsTotal.toRat.den = 1) : CanEmpty v :=
  canEmpty_of_emptyReady v ⟨hr, hfit, hcap, hint, hAint⟩


end XRPL.Model.SingleAssetVault
