import XRPL.Properties.Vault.Common.PricingMono
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.DepositWiring
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.RoundCanonical
import XRPL.Properties.Vault.Common.RoundingMonotone
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact

/-! # Deposit shares monotonicity

`assetsToSharesDeposit` on a nonempty vault is `amount ↦ ofNumber.int64 (⌊(sharesTotal
* amount.toNumber) / nav⌋)`; the pricing chain is monotone (`Number.mul_div_num_mono`),
truncation is monotone (`truncate_toRat_mono`), and the integral conversion is exact
and monotone (`ofNumber_integral_toRat_mono`).

On an empty vault the first deposit prices through `Number.normalized` instead: a
positive canonical `amount` has a mantissa of at most 19 digits, so scaling it into
`largeRange` is exact (`doNormalize_largeRange_exact`) and the issued shares are
`⌊amount · 10^scale⌋`, monotone via `truncate_toRat_mono` and
`ofNumber_integral_toRat_mono`. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol
open XRPL.Model.Result

/-- Full nonempty-vault pricing chain of `assetsToSharesDeposit` with every stage's
normalization / nonzero-mantissa / positivity fact. -/
lemma deposit_nonempty_chain_facts (v : Vault) (hne : v.assetsTotal.mantissa_ ≠ 0)
    (amount shares : STAmount) (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hok : assetsToSharesDeposit v amount = .ok shares) (hnz : shares.isZero = false) :
    ∃ (amountN navN P T0 T : Number),
      amountN.toRat = amount.toRat ∧ amountN.isNormalized ∧ amountN.mantissa_ ≠ 0 ∧
      navN = v.assetsTotal ∧
      navN.isNormalized ∧ navN.mantissa_ ≠ 0 ∧ 0 < navN.toRat ∧
      v.sharesTotal.mantissa_ ≠ 0 ∧
      v.sharesTotal.operator_mul amountN .to_nearest = .ok P ∧
      P.isNormalized ∧ P.mantissa_ ≠ 0 ∧
      P.operator_div navN .to_nearest = .ok T0 ∧
      T0.isNormalized ∧ T0.mantissa_ ≠ 0 ∧ 0 < T0.toRat ∧
      T0.truncate = .ok T ∧ T.isNormalized ∧ T.mantissa_ ≠ 0 ∧ T.toRat.den = 1 ∧
      STAmount.ofNumber .int64 T .to_nearest = .ok shares := by
  have hmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  unfold assetsToSharesDeposit at hok
  rw [if_neg hne] at hok
  obtain ⟨_, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨amountN, hamN, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨P, hP, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨T0, hT0, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨T, hT, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
  have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
  rw [hsh'] at hsh
  have hTm : T.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 T .to_nearest shares (by decide) hsh hmv
  have hT0m : T0.mantissa_ ≠ 0 := Number.truncate_source_ne_zero T0 T hT hTm
  set navN := v.assetsTotal with hnavN_eq
  have hnavnorm : navN.isNormalized := v.wf.assetsTotal_norm
  have hnavm : navN.mantissa_ ≠ 0 :=
    operator_div_divisor_ne_zero P navN T0 .to_nearest hnavnorm hT0
  have hPm : P.mantissa_ ≠ 0 :=
    operator_div_numerator_ne_zero_sz P navN T0 .to_nearest
      (Number.not_operator_eq_zero_of_mantissa_ne hnavm) hT0 hT0m
  obtain ⟨an', han', hanval, hannorm⟩ := STAmount.toNumber_canonical_exact amount .to_nearest hc
  have haneq : an' = amountN := by rw [han'] at hamN; exact Except.ok.inj hamN
  rw [haneq] at hanval hannorm
  obtain ⟨hSTm, hanm⟩ :=
    operator_mul_operands_ne_zero v.wf.sharesTotal_norm hannorm hP hPm
  have hPnorm : P.isNormalized :=
    operator_mul_result_isNormalized v.sharesTotal amountN P .to_nearest
      v.wf.sharesTotal_norm hannorm hSTm hanm hP hPm
  have hT0norm : T0.isNormalized :=
    operator_div_result_isNormalized P navN T0 .to_nearest hPnorm hnavnorm hPm hnavm hT0 hT0m
  have hann : 0 ≤ amountN.toRat := by rw [hanval]; exact le_of_lt hpos
  have hSTnn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
  have hPnn : 0 ≤ P.toRat := by
    have hb : |P.toRat - v.sharesTotal.toRat * amountN.toRat|
        ≤ |v.sharesTotal.toRat * amountN.toRat| * (5 / (2 ^ 63 + 7 : ℚ)) :=
      operator_mul_rounds_to_nearest v.sharesTotal amountN P
        v.wf.sharesTotal_norm hannorm hP hPm
    rw [abs_of_nonneg (mul_nonneg hSTnn hann)] at hb
    have hab := abs_le.mp hb
    nlinarith [mul_nonneg hSTnn hann]
  obtain ⟨_, _, _, hnavpos⟩ := Vault.depositNav_facts v navN hne hnavm hnavN_eq
  have hPNnn : 0 ≤ P.toRat / navN.toRat := div_nonneg hPnn (le_of_lt hnavpos)
  have hT0nn : 0 ≤ T0.toRat := by
    have hb : |T0.toRat - P.toRat / navN.toRat|
        ≤ |P.toRat / navN.toRat| * (6 / (2 ^ 63 - 3 : ℚ)) :=
      operator_div_rounds_to_nearest P navN T0 hPnorm hnavnorm hT0 hT0m
    rw [abs_of_nonneg hPNnn] at hb
    have hab := abs_le.mp hb
    nlinarith [hPNnn]
  have hT0pos : 0 < T0.toRat :=
    lt_of_le_of_ne hT0nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero T0 hT0m))
  obtain ⟨hTval, hTnorm⟩ :=
    Number.truncate_floor T0 T hT0norm (Number.negative_false_of_pos T0 hT0pos) hT
  exact ⟨amountN, navN, P, T0, T, hanval, hannorm, hanm, hnavN_eq, hnavnorm, hnavm, hnavpos,
    hSTm, hP, hPnorm, hPm, hT0, hT0norm, hT0m, hT0pos, hT, hTnorm hTm, hTm,
    (by rw [hTval]; exact Rat.den_intCast _), hsh⟩

/-- **Empty-vault pricing chain of `assetsToSharesDeposit`.** On an empty vault the
`Number.normalized` step scales a `≤ 19`-digit mantissa into `largeRange` with no
rounding (`doNormalize_largeRange_exact`), so the exact source value of the truncation
is `amount · 10^scale`; the issued shares are its floor. -/
lemma deposit_empty_chain_facts (v : Vault) (hscale : v.scale.toNat ≤ 18)
    (amount shares : STAmount) (hc : amount.Canonical) (hpos : 0 < amount.toRat)
    (hmz : v.assetsTotal.mantissa_ = 0)
    (hok : assetsToSharesDeposit v amount = .ok shares) (hnz : shares.isZero = false) :
    ∃ (n1 n2 : Number),
      n1.isNormalized ∧ n1.negative_ = false ∧
      n1.toRat = amount.toRat * (10 : ℚ) ^ (v.scale.toNat : ℤ) ∧
      n1.truncate = .ok n2 ∧ n2.isNormalized ∧ n2.toRat.den = 1 ∧
      STAmount.ofNumber .int64 n2 .to_nearest = .ok shares := by
  have hshmv : shares.mValue ≠ 0 := ne_of_beq_false hnz
  unfold assetsToSharesDeposit at hok
  rw [if_pos hmz] at hok
  obtain ⟨n1, hn1, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨n2, hn2, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨sh', hsh, hlast⟩ := bind_ok_peel _ _ _ hok
  have hsh' : sh' = shares := Except.ok.inj (show Except.ok sh' = .ok shares from hlast)
  rw [hsh'] at hsh
  -- `amount` positive: non-negative sign and a nonzero mantissa
  have hposneg : amount.mIsNegative = false :=
    Number.negative_false_of_pos ⟨amount.mIsNegative, amount.mValue, amount.mOffset⟩
      (by rw [← STAmount.toRat_eq_number]; exact hpos)
  have hmv_ne : amount.mValue ≠ 0 := fun h =>
    absurd ((STAmount.toRat_eq_zero_iff amount).mpr h) (ne_of_gt hpos)
  have hmv1 : 1 ≤ amount.mValue.toNat := by
    have : amount.mValue.toNat ≠ 0 := fun h => hmv_ne (by rw [← UInt64.toNat_inj]; simpa using h)
    omega
  -- mantissa and exponent bounds shared by the integral and fractional cases
  have hmax : amount.mValue.toNat ≤ maxRep.toNat := by
    by_cases hint : amount.integral = true
    · obtain ⟨hic, hmr⟩ := hc.1 hint
      exact le_trans hic.in_range hmr
    · have hf : amount.integral = false := by
        cases hb : amount.integral with | false => rfl | true => exact absurd hb hint
      have hiou := hc.2 hf
      have := hiou.mant_hi; rw [maxRep_val]; omega
  have hexp : (-96 : ℤ) ≤ amount.exponent ∧ amount.exponent ≤ 80 := by
    by_cases hint : amount.integral = true
    · obtain ⟨hic, _⟩ := hc.1 hint
      rw [show amount.exponent = amount.mOffset from rfl, hic.offset_zero]; omega
    · have hf : amount.integral = false := by
        cases hb : amount.integral with | false => rfl | true => exact absurd hb hint
      have hiou := hc.2 hf
      exact ⟨hiou.exp_lo, hiou.exp_hi⟩
  obtain ⟨hexp_lo, hexp_hi⟩ := hexp
  -- the normalize step is value-exact
  obtain ⟨M, e1, hdn, hMval, hMnorm⟩ :=
    doNormalize_largeRange_exact false amount.mantissa (amount.exponent + (v.scale.toNat : ℤ))
      .to_nearest hmv1 hmax
      (by show minExponent + 18 ≤ amount.exponent + (v.scale.toNat : ℤ)
          have hs : (0 : ℤ) ≤ (v.scale.toNat : ℤ) := by positivity
          unfold minExponent; omega)
      (by show amount.exponent + (v.scale.toNat : ℤ) ≤ maxExponent - 1
          have hs : (v.scale.toNat : ℤ) ≤ 18 := by exact_mod_cast hscale
          unfold maxExponent; omega)
  have hn1eq : n1 = ⟨false, M, e1⟩ := by
    have hdn' : Number.normalized false amount.mantissa (amount.exponent + (v.scale.toNat : ℤ))
        largeRange.min largeRange.max .to_nearest = .ok (⟨false, M, e1⟩ : Number) := hdn
    exact Except.ok.inj (hn1.symm.trans hdn')
  have hn1nn : (0 : ℚ) ≤ n1.toRat := by rw [hn1eq, Number.toRat_of_nonneg _ rfl]; positivity
  have hn2m : n2.mantissa_ ≠ 0 :=
    STAmount.ofNumber_integral_source_ne_zero .int64 n2 .to_nearest shares (by decide) hsh hshmv
  obtain ⟨hn2val, hn2normfn⟩ :=
    Number.truncate_floor n1 n2 (by rw [hn1eq]; exact hMnorm) (by rw [hn1eq]) hn2
  refine ⟨n1, n2, by rw [hn1eq]; exact hMnorm, by rw [hn1eq], ?_, hn2, hn2normfn hn2m,
    by rw [hn2val]; exact Rat.den_intCast _, hsh⟩
  rw [hn1eq, Number.toRat_of_nonneg _ rfl, hMval, STAmount.toRat_of_nonneg amount hposneg]
  show (amount.mValue.toNat : ℚ) * 10 ^ (amount.mOffset + (v.scale.toNat : ℤ))
     = (amount.mValue.toNat : ℚ) * 10 ^ amount.mOffset * 10 ^ (v.scale.toNat : ℤ)
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; ring

/-- **`assetsToSharesDeposit` is monotone in the amount** on an empty vault: the exact
`⌊amount · 10^scale⌋` map is monotone via truncation and integral conversion. -/
lemma assetsToSharesDeposit_empty_mono (v : Vault) (hscale : v.scale.toNat ≤ 18)
    (amount₁ amount₂ shares₁ shares₂ : STAmount)
    (hc₁ : amount₁.Canonical) (hpos₁ : 0 < amount₁.toRat)
    (hc₂ : amount₂.Canonical) (hpos₂ : 0 < amount₂.toRat)
    (hmz : v.assetsTotal.mantissa_ = 0)
    (hok₁ : assetsToSharesDeposit v amount₁ = .ok shares₁) (hnz₁ : shares₁.isZero = false)
    (hok₂ : assetsToSharesDeposit v amount₂ = .ok shares₂) (hnz₂ : shares₂.isZero = false)
    (hle : amount₁.toRat ≤ amount₂.toRat) : shares₁.toRat ≤ shares₂.toRat := by
  obtain ⟨n1₁, n2₁, hn1n₁, hn1neg₁, hn1v₁, htr₁, hn2n₁, hden₁, hsh₁⟩ :=
    deposit_empty_chain_facts v hscale amount₁ shares₁ hc₁ hpos₁ hmz hok₁ hnz₁
  obtain ⟨n1₂, n2₂, hn1n₂, hn1neg₂, hn1v₂, htr₂, hn2n₂, hden₂, hsh₂⟩ :=
    deposit_empty_chain_facts v hscale amount₂ shares₂ hc₂ hpos₂ hmz hok₂ hnz₂
  have hn1le : n1₁.toRat ≤ n1₂.toRat := by
    rw [hn1v₁, hn1v₂]; exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hn2le : n2₁.toRat ≤ n2₂.toRat :=
    Number.truncate_toRat_mono n1₁ n1₂ n2₁ n2₂ hn1n₁ hn1n₂ hn1neg₁ hn1neg₂ htr₁ htr₂ hn1le
  exact STAmount.ofNumber_integral_toRat_mono .int64 n2₁ n2₂ shares₁ shares₂ .to_nearest .to_nearest
    (by decide) hn2n₁ hn2n₂ hden₁ hden₂ hsh₁ hsh₂ hn2le

/-- **`assetsToSharesDeposit` is monotone in the amount**: the pricing chain,
truncation, and integral conversion are each monotone (empty vault: the exact
`⌊amount · 10^scale⌋` map). -/
lemma assetsToSharesDeposit_mono (v : Vault)
    (amount₁ amount₂ shares₁ shares₂ : STAmount)
    (hc₁ : amount₁.Canonical) (hpos₁ : 0 < amount₁.toRat)
    (hc₂ : amount₂.Canonical) (hpos₂ : 0 < amount₂.toRat)
    (hok₁ : assetsToSharesDeposit v amount₁ = .ok shares₁) (hnz₁ : shares₁.isZero = false)
    (hok₂ : assetsToSharesDeposit v amount₂ = .ok shares₂) (hnz₂ : shares₂.isZero = false)
    (hle : amount₁.toRat ≤ amount₂.toRat) : shares₁.toRat ≤ shares₂.toRat := by
  by_cases hmz : v.assetsTotal.mantissa_ = 0
  · exact assetsToSharesDeposit_empty_mono v v.wf.scale_le amount₁ amount₂ shares₁ shares₂
      hc₁ hpos₁ hc₂ hpos₂ hmz hok₁ hnz₁ hok₂ hnz₂ hle
  have hne : v.assetsTotal.mantissa_ ≠ 0 := hmz
  obtain ⟨aN₁, navN₁, P₁, T0₁, T₁, hav₁, haN₁, ham₁, hnav₁, hnavn₁, hnavm₁, hnavp₁, hSTm₁,
      hP₁, hPn₁, hPm₁, hT0₁, hT0n₁, hT0m₁, hT0p₁, hT₁, hTn₁, hTm₁, hTden₁, hsh₁⟩ :=
    deposit_nonempty_chain_facts v hne amount₁ shares₁ hc₁ hpos₁ hok₁ hnz₁
  obtain ⟨aN₂, navN₂, P₂, T0₂, T₂, hav₂, haN₂, ham₂, hnav₂, hnavn₂, hnavm₂, hnavp₂, hSTm₂,
      hP₂, hPn₂, hPm₂, hT0₂, hT0n₂, hT0m₂, hT0p₂, hT₂, hTn₂, hTm₂, hTden₂, hsh₂⟩ :=
    deposit_nonempty_chain_facts v hne amount₂ shares₂ hc₂ hpos₂ hok₂ hnz₂
  have hnaveq : navN₁ = navN₂ := hnav₁.trans hnav₂.symm
  subst hnaveq
  have hSTpos : 0 < v.sharesTotal.toRat := lt_of_le_of_ne v.wf.sharesTotal_nonneg
    (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.sharesTotal hSTm₁))
  have hSTneg := Number.negative_false_of_pos v.sharesTotal hSTpos
  have hnavneg := Number.negative_false_of_pos navN₁ hnavp₁
  have haN₁neg := Number.negative_false_of_pos aN₁ (by rw [hav₁]; exact hpos₁)
  have haN₂neg := Number.negative_false_of_pos aN₂ (by rw [hav₂]; exact hpos₂)
  have haNle : aN₁.toRat ≤ aN₂.toRat := by rw [hav₁, hav₂]; exact hle
  have hT0le : T0₁.toRat ≤ T0₂.toRat :=
    Number.mul_div_num_mono v.sharesTotal navN₁ aN₁ aN₂ P₁ P₂ T0₁ T0₂
      v.wf.sharesTotal_norm hSTm₁ hSTneg hnavn₁ hnavm₁ hnavneg
      haN₁ ham₁ haN₁neg haN₂ ham₂ haN₂neg
      hP₁ hPm₁ hP₂ hPm₂ hT0₁ hT0m₁ hT0₂ hT0m₂ haNle
  have hTle : T₁.toRat ≤ T₂.toRat :=
    Number.truncate_toRat_mono T0₁ T0₂ T₁ T₂ hT0n₁ hT0n₂
      (Number.negative_false_of_pos T0₁ hT0p₁) (Number.negative_false_of_pos T0₂ hT0p₂)
      hT₁ hT₂ hT0le
  exact STAmount.ofNumber_integral_toRat_mono .int64 T₁ T₂ shares₁ shares₂ .to_nearest .to_nearest
    (by decide) hTn₁ hTn₂ hTden₁ hTden₂ hsh₁ hsh₂ hTle

/-- `roundedDepositAmount = .ok (.rounded r)` exposes the underlying
`roundToVaultExponent` output equal to `r`. -/
private lemma roundedDepositAmount_roundTo (v : Vault) (amountDeposit roundedAmount : STAmount)
    (h : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount)) :
    roundToVaultExponent amountDeposit v.assetsTotal = .ok roundedAmount := by
  unfold Vault.roundedDepositAmount at h
  simp only [] at h
  obtain ⟨ra, hra, h⟩ := bind_ok_peel _ _ _ h
  by_cases hz : ra.isZero = true
  · rw [if_pos hz] at h; exact absurd (Except.ok.inj h) (by simp)
  · rw [if_neg hz] at h
    have : ra = roundedAmount :=
      RoundingResult.rounded.inj (Except.ok.inj h)
    rw [this] at hra; exact hra

/-- **Deposit shares are monotone in the rounded amount.** Minimal added inputs over
the headline: `roundedAmount_i.Canonical` and `0 < roundedAmount_i.toRat` (as in the
sibling `deposit_sharesIssued`). Both the nonempty pricing chain and the empty-vault
`Number.normalized` map are monotone. -/
theorem Vault.deposit_shares_monotone_proof (v : Vault)
    (amountDeposit₁ amountDeposit₂ roundedAmount₁ roundedAmount₂ : STAmount)
    (r₁ r₂ : DepositResult)
    (hcanon₁ : roundedAmount₁.Canonical) (hcanon₂ : roundedAmount₂.Canonical)
    (hposR₁ : 0 < roundedAmount₁.toRat) (hposR₂ : 0 < roundedAmount₂.toRat)
    (hrounded₁ : v.roundedDepositAmount amountDeposit₁ = .ok (.rounded roundedAmount₁))
    (hrounded₂ : v.roundedDepositAmount amountDeposit₂ = .ok (.rounded roundedAmount₂))
    (hok₁ : v.deposit amountDeposit₁ false = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : v.deposit amountDeposit₂ false = .ok r₂) (herr₂ : r₂.error = none)
    (hle : roundedAmount₁.toRat ≤ roundedAmount₂.toRat) :
    r₁.sharesIssued.toRat ≤ r₂.sharesIssued.toRat := by
  obtain ⟨am₁, rawAssetDeposited₁, aD₁, sC₁, _, _, _, _, _, hround₁, _, _, _, _, hcomp₁, _, _, _, _, _, _, _, hr₁, _⟩ :=
    Vault.deposit_success_reduces v amountDeposit₁ false r₁ hok₁ herr₁
  obtain ⟨am₂, rawAssetDeposited₂, aD₂, sC₂, _, _, _, _, _, hround₂, _, _, _, _, hcomp₂, _, _, _, _, _, _, _, hr₂, _⟩ :=
    Vault.deposit_success_reduces v amountDeposit₂ false r₂ hok₂ herr₂
  -- amount = roundedAmount
  have haeq₁ : am₁ = roundedAmount₁ :=
    Except.ok.inj (hround₁.symm.trans (roundedDepositAmount_roundTo v _ _ hrounded₁))
  have haeq₂ : am₂ = roundedAmount₂ :=
    Except.ok.inj (hround₂.symm.trans (roundedDepositAmount_roundTo v _ _ hrounded₂))
  -- computeDeposit success → assetsToSharesDeposit + shares
  obtain ⟨sh₁, hats₁, hshz₁, _, _, hseq₁⟩ :=
    computeDeposit_success_reduces v am₁ rawAssetDeposited₁ sC₁ (hcomp₁ rfl).1
  obtain ⟨sh₂, hats₂, hshz₂, _, _, hseq₂⟩ :=
    computeDeposit_success_reduces v am₂ rawAssetDeposited₂ sC₂ (hcomp₂ rfl).1
  have hsi₁ : r₁.sharesIssued = sh₁ := by rw [hr₁]; exact hseq₁
  have hsi₂ : r₂.sharesIssued = sh₂ := by rw [hr₂]; exact hseq₂
  rw [hsi₁, hsi₂]
  exact assetsToSharesDeposit_mono v am₁ am₂ sh₁ sh₂
    (by rw [haeq₁]; exact hcanon₁) (by rw [haeq₁]; exact hposR₁)
    (by rw [haeq₂]; exact hcanon₂) (by rw [haeq₂]; exact hposR₂)
    hats₁ hshz₁ hats₂ hshz₂ (by rw [haeq₁, haeq₂]; exact hle)

end XRPL.Model.SingleAssetVault
