import XRPL.Properties.Vault.Common.RoundMonotoneCusp
import XRPL.Properties.Vault.Common.RoundMonotoneSat
import XRPL.Properties.Vault.Common.RoundMonotoneSatDiv
import XRPL.Properties.Vault.Common.RoundingMonotone

/-! # Pricing-chain monotonicity core

The vault share/asset pricing chain is `a ↦ (k * a) / d` on `Number`s (fixed
positive `k`, `d`), each stage rounded `.to_nearest`. Both the deposit shares path
(`sharesTotal * amount / nav`) and the withdraw payout path (`nav * shares /
sharesTotal`) are instances. Monotonicity in the varying operand `a` follows by
chaining `operator_mul_left_mono_of_cuspAware` and `operator_div_num_mono_of_cuspAware`,
discharging every `RoundsCuspAware` obligation with the satisfaction lemmas
`operator_mul_roundsCuspAware` / `operator_div_roundsCuspAware`. -/

namespace XRPL.Model.Protocol

/-- **Pricing chain monotone.** For fixed positive `k`, `d` (normalized, nonzero,
nonnegative), the map `a ↦ (k * a) / d` (`.to_nearest` at each stage) is monotone
in the varying positive operand `a`. -/
theorem Number.mul_div_num_mono (k d a₁ a₂ m₁ m₂ q₁ q₂ : Number)
    (hk : k.isNormalized) (hkm : k.mantissa_ ≠ 0) (hkneg : k.negative_ = false)
    (hd : d.isNormalized) (hdm : d.mantissa_ ≠ 0) (hdneg : d.negative_ = false)
    (ha₁ : a₁.isNormalized) (ha₁m : a₁.mantissa_ ≠ 0) (ha₁neg : a₁.negative_ = false)
    (ha₂ : a₂.isNormalized) (ha₂m : a₂.mantissa_ ≠ 0) (ha₂neg : a₂.negative_ = false)
    (hm₁ : k.operator_mul a₁ .to_nearest = .ok m₁) (hm₁m : m₁.mantissa_ ≠ 0)
    (hm₂ : k.operator_mul a₂ .to_nearest = .ok m₂) (hm₂m : m₂.mantissa_ ≠ 0)
    (hq₁ : m₁.operator_div d .to_nearest = .ok q₁) (hq₁m : q₁.mantissa_ ≠ 0)
    (hq₂ : m₂.operator_div d .to_nearest = .ok q₂) (hq₂m : q₂.mantissa_ ≠ 0)
    (hle : a₁.toRat ≤ a₂.toRat) : q₁.toRat ≤ q₂.toRat := by
  have hkpos := Number.toRat_pos_of_not_negative k hkneg hkm
  have hdpos := Number.toRat_pos_of_not_negative d hdneg hdm
  have ha₁pos := Number.toRat_pos_of_not_negative a₁ ha₁neg ha₁m
  have ha₂pos := Number.toRat_pos_of_not_negative a₂ ha₂neg ha₂m
  have hprod₁ : 0 < k.toRat * a₁.toRat := mul_pos hkpos ha₁pos
  have hprod₂ : 0 < k.toRat * a₂.toRat := mul_pos hkpos ha₂pos
  have hcm₁ := operator_mul_roundsCuspAware k a₁ m₁ hk ha₁ hkm ha₁m hm₁ hm₁m hprod₁
  have hcm₂ := operator_mul_roundsCuspAware k a₂ m₂ hk ha₂ hkm ha₂m hm₂ hm₂m hprod₂
  have hm₁neg : m₁.negative_ = false := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_mul_algorithmic_facts_to_nearest k a₁ m₁ hk ha₁ hkm ha₁m hm₁ hm₁m
    rw [hF.result_neg, hkneg, ha₁neg]; rfl
  have hm₂neg : m₂.negative_ = false := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_mul_algorithmic_facts_to_nearest k a₂ m₂ hk ha₂ hkm ha₂m hm₂ hm₂m
    rw [hF.result_neg, hkneg, ha₂neg]; rfl
  have hm₁pos := Number.toRat_pos_of_not_negative m₁ hm₁neg hm₁m
  have hm₂pos := Number.toRat_pos_of_not_negative m₂ hm₂neg hm₂m
  have hm₁norm := operator_mul_result_isNormalized k a₁ m₁ .to_nearest hk ha₁ hkm ha₁m hm₁ hm₁m
  have hm₂norm := operator_mul_result_isNormalized k a₂ m₂ .to_nearest hk ha₂ hkm ha₂m hm₂ hm₂m
  have hmle : m₁.toRat ≤ m₂.toRat :=
    operator_mul_left_mono_of_cuspAware k a₁ a₂ m₁ m₂ ha₁ ha₂ hm₁ hm₂ hcm₁ hcm₂
      hm₁pos hm₂pos hkpos ha₁pos hle
  have hquo₁ : 0 < m₁.toRat / d.toRat := div_pos hm₁pos hdpos
  have hquo₂ : 0 < m₂.toRat / d.toRat := div_pos hm₂pos hdpos
  have hcq₁ := operator_div_roundsCuspAware m₁ d q₁ hm₁norm hd hm₁m hdm hq₁ hq₁m hquo₁
  have hcq₂ := operator_div_roundsCuspAware m₂ d q₂ hm₂norm hd hm₂m hdm hq₂ hq₂m hquo₂
  have hq₁nn : 0 ≤ q₁.toRat := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_div_algorithmic_facts_to_nearest m₁ d q₁ hm₁norm hd hm₁m hdm hq₁ hq₁m
    exact hF.result_nonneg hquo₁
  have hq₂nn : 0 ≤ q₂.toRat := by
    obtain ⟨_, _, _, _, _, hF⟩ :=
      operator_div_algorithmic_facts_to_nearest m₂ d q₂ hm₂norm hd hm₂m hdm hq₂ hq₂m
    exact hF.result_nonneg hquo₂
  have hq₁pos : 0 < q₁.toRat :=
    lt_of_le_of_ne hq₁nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero q₁ hq₁m))
  have hq₂pos : 0 < q₂.toRat :=
    lt_of_le_of_ne hq₂nn (Ne.symm (Number.toRat_ne_zero_of_mantissa_ne_zero q₂ hq₂m))
  exact operator_div_num_mono_of_cuspAware m₁ m₂ d q₁ q₂ hm₁norm hm₂norm hq₁ hq₂ hcq₁ hcq₂
    hq₁pos hq₂pos hdpos hm₁pos hmle

end XRPL.Model.Protocol
