import XRPL.Properties.Vault.Common.DepositDefs
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.WithdrawDefs
import XRPL.Properties.Vault.Common.DepositAccuracy
import XRPL.Properties.Vault.Common.DepositChargeFrac
import XRPL.Properties.Vault.Common.DepositReduction
import XRPL.Properties.Vault.Common.DepositWitness
import XRPL.Properties.Vault.Common.Preservation
import XRPL.Properties.Vault.Common.WithdrawReduction
import XRPL.Properties.Vault.Common.WithdrawBounds
import XRPL.Properties.Vault.Common.State
import XRPL.Properties.Vault.VaultDeposit
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Properties.Vault.Common.VaultDecidable

/-! # Proof support for `Vault.deposit_withdraw_roundtrip` -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

-- The concrete `wvF` witness below crosses opaque FFI primitives.  Its closed
-- executions are independently derived from the stated rational vectors, so
-- `native_decide` is deliberately confined to those executable checks; the
-- symbolic universal theorem above remains kernel-checked.
set_option linter.style.nativeDecide false

/-- Raw-stage composition of the deposit-then-withdraw round trip on the value
path, in exact rationals. `Q` is the interior (pre-`ofNumber`) charge, `C` the
stored charge (`Q ≤ C ≤ Q + UC`), `at'` the stored total, `IA` the payout ideal.
The three raw relative stages (charge `19/(2^63-3)`, store `6/(2^63-3)`, payout
`12/(2^63-3)`) compose under `2·depositε`, and the two directed-rounding ULPs
(`UC` upward charge snap, `UA` downward payout snap) enter additively with
coefficient one each. -/
private lemma roundtrip_algebra
    (C A IC Q at' IA Av S STv UA UC : ℚ)
    (hS : 0 < S) (hSTv : 0 < STv) (_hAv : 0 ≤ Av)
    (hC : 0 < C) (hIC : 0 < IC)
    (hicid : Av * S = IC * STv)
    (hQlo : IC * (1 - 19 / (2 ^ 63 - 3)) ≤ Q)
    (hQhi : Q ≤ IC * (1 + 19 / (2 ^ 63 - 3)))
    (hQClo : Q ≤ C)
    (hQChi : C ≤ Q + UC)
    (hstlo : (Av + C) * (1 - 6 / (2 ^ 63 - 3)) ≤ at')
    (hsthi : at' ≤ (Av + C) * (1 + 6 / (2 ^ 63 - 3)))
    (hIAid : IA * (STv + S) = at' * S)
    (_hIAnn : 0 ≤ IA) (_hAnn : 0 ≤ A) (_hUAnn : 0 ≤ UA) (hUCnn : 0 ≤ UC)
    (hAhi : A ≤ IA * (1 + 12 / (2 ^ 63 - 3)))
    (hAlo : IA - A ≤ IA * (12 / (2 ^ 63 - 3)) + UA) :
    A ≤ C * (1 + 2 * depositε) ∧
    C - A ≤ C * (2 * depositε) + UA + UC := by
  have hP : (0 : ℚ) < STv + S := by positivity
  -- charge, one-sided in terms of C
  have hICleC : IC * (1 - 19 / (2 ^ 63 - 3)) ≤ C := le_trans hQlo hQClo
  have hCleIC : C ≤ IC * (1 + 19 / (2 ^ 63 - 3)) + UC := by linarith [hQChi, hQhi]
  -- coefficient facts
  have hf1 : (1 + 6 / (2 ^ 63 - 3) : ℚ)
      ≤ (1 - 19 / (2 ^ 63 - 3)) * (1 + 26 / (2 ^ 63 - 3)) := by norm_num
  -- IC·(1+6/d) ≤ C·(1+26/d)
  have hIC1 : IC * (1 + 6 / (2 ^ 63 - 3)) ≤ C * (1 + 26 / (2 ^ 63 - 3)) := by
    have h1 : IC * (1 + 6 / (2 ^ 63 - 3))
        ≤ IC * ((1 - 19 / (2 ^ 63 - 3)) * (1 + 26 / (2 ^ 63 - 3))) :=
      mul_le_mul_of_nonneg_left hf1 (le_of_lt hIC)
    have h3 : IC * (1 - 19 / (2 ^ 63 - 3)) * (1 + 26 / (2 ^ 63 - 3))
        ≤ C * (1 + 26 / (2 ^ 63 - 3)) :=
      mul_le_mul_of_nonneg_right hICleC (by norm_num)
    nlinarith [h1, h3]
  -- L1 : IA ≤ C·(1+26/d)
  have hL1 : IA ≤ C * (1 + 26 / (2 ^ 63 - 3)) := by
    have key : IA * (STv + S) ≤ C * (1 + 26 / (2 ^ 63 - 3)) * (STv + S) := by
      have e1 : IA * (STv + S) = at' * S := hIAid
      have e2 : at' * S ≤ (Av + C) * (1 + 6 / (2 ^ 63 - 3)) * S :=
        mul_le_mul_of_nonneg_right hsthi (le_of_lt hS)
      have e3 : (Av + C) * (1 + 6 / (2 ^ 63 - 3)) * S
          = (IC * STv + C * S) * (1 + 6 / (2 ^ 63 - 3)) := by
        have : (Av + C) * (1 + 6 / (2 ^ 63 - 3)) * S
            = (Av * S + C * S) * (1 + 6 / (2 ^ 63 - 3)) := by ring
        rw [this, hicid]
      have ha : IC * (1 + 6 / (2 ^ 63 - 3)) * STv ≤ C * (1 + 26 / (2 ^ 63 - 3)) * STv :=
        mul_le_mul_of_nonneg_right hIC1 (le_of_lt hSTv)
      have hb : C * S * (1 + 6 / (2 ^ 63 - 3)) ≤ C * S * (1 + 26 / (2 ^ 63 - 3)) :=
        mul_le_mul_of_nonneg_left (by norm_num) (mul_nonneg (le_of_lt hC) (le_of_lt hS))
      nlinarith [e1, e2, e3, ha, hb]
    exact le_of_mul_le_mul_right key hP
  -- C - IC ≤ UC + IC·19/d  and  IC·19/d ≤ C·20/d
  have hCIC : C - IC ≤ UC + IC * (19 / (2 ^ 63 - 3)) := by nlinarith [hCleIC]
  have hIC19 : IC * (19 / (2 ^ 63 - 3)) ≤ C * (20 / (2 ^ 63 - 3)) := by
    nlinarith [hICleC, hIC]
  -- L2 : C·(1-26/d) - UC ≤ IA
  have hL2 : C * (1 - 26 / (2 ^ 63 - 3)) - UC ≤ IA := by
    have key : (C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (STv + S) ≤ IA * (STv + S) := by
      have e1 : (IC * STv + C * S) * (1 - 6 / (2 ^ 63 - 3)) ≤ IA * (STv + S) := by
        have e2 : (Av + C) * (1 - 6 / (2 ^ 63 - 3)) * S ≤ at' * S :=
          mul_le_mul_of_nonneg_right hstlo (le_of_lt hS)
        have e3 : (Av + C) * (1 - 6 / (2 ^ 63 - 3)) * S
            = (IC * STv + C * S) * (1 - 6 / (2 ^ 63 - 3)) := by
          have : (Av + C) * (1 - 6 / (2 ^ 63 - 3)) * S
              = (Av * S + C * S) * (1 - 6 / (2 ^ 63 - 3)) := by ring
          rw [this, hicid]
        rw [← e3]; rw [hIAid]; exact e2
      -- (IC·STv + C·S)(1-6/d) ≥ (C(1-6/d) - (UC+IC·19/d))(STv+S)
      --   ≥ (C(1-26/d) - UC)(STv+S)
      have hkey2 : (C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (STv + S)
          ≤ (IC * STv + C * S) * (1 - 6 / (2 ^ 63 - 3)) := by
        nlinarith [hCIC, hIC19, hUCnn, hSTv, hS, hC, hIC,
          mul_nonneg (le_of_lt hSTv) hUCnn, mul_nonneg (le_of_lt hS) hUCnn,
          mul_pos hSTv hS]
      linarith [e1, hkey2]
    exact le_of_mul_le_mul_right key hP
  -- upper conjunct
  have hup : A ≤ C * (1 + 2 * depositε) := by
    have h1 : A ≤ C * (1 + 26 / (2 ^ 63 - 3)) * (1 + 12 / (2 ^ 63 - 3)) := by
      have := mul_le_mul_of_nonneg_right hL1 (by norm_num : (0:ℚ) ≤ 1 + 12 / (2 ^ 63 - 3))
      linarith [hAhi, this]
    have h2 : C * (1 + 26 / (2 ^ 63 - 3)) * (1 + 12 / (2 ^ 63 - 3)) ≤ C * (1 + 2 * depositε) := by
      have hfup : ((1 + 26 / (2 ^ 63 - 3)) * (1 + 12 / (2 ^ 63 - 3)) : ℚ) ≤ 1 + 2 * depositε := by
        rw [depositε_eq]; norm_num
      nlinarith [hfup, hC]
    linarith [h1, h2]
  -- loss conjunct
  have hloss : C - A ≤ C * (2 * depositε) + UA + UC := by
    have hA_lo : (C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (1 - 12 / (2 ^ 63 - 3)) - UA ≤ A := by
      have h1 : (C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (1 - 12 / (2 ^ 63 - 3))
          ≤ IA * (1 - 12 / (2 ^ 63 - 3)) :=
        mul_le_mul_of_nonneg_right hL2 (by norm_num)
      linarith [hAlo, h1]
    have hfin : C - ((C * (1 - 26 / (2 ^ 63 - 3)) - UC) * (1 - 12 / (2 ^ 63 - 3)) - UA)
        ≤ C * (2 * depositε) + UA + UC := by
      have hfl : (38 / (2 ^ 63 - 3) - 312 / (2 ^ 63 - 3) ^ 2 : ℚ) ≤ 2 * depositε := by
        rw [depositε_eq]; norm_num
      nlinarith [hfl, hC, hUCnn]
    linarith [hA_lo, hfin]
  exact ⟨hup, hloss⟩

/-- The interior charge `Q` of a nonzero nonempty-vault charge, with its raw
`19/(2^63-3)` band around the ideal, sandwiched by the upward `ofNumber` snap
`Q ≤ c ≤ Q + 10^c.exponent`. The deposit NAV is `assetsTotal`, so the ideal
collapses to `assetsTotal · shares / sharesTotal`. Feeds the charge inputs of
`roundtrip_algebra`. -/
private lemma roundtrip_charge_Q (v : Vault)
    (shares c : STAmount)
    (hshc : shares.IntegralCanonical) (hshnt : shares.mNumericType = .int64)
    (hshpos : 0 < shares.toRat)
    (hmz : v.assetsTotal.mantissa_ ≠ 0)
    (hcnz : c.isZero = false)
    (hsad : sharesToAssetsDeposit v shares = .ok c) :
    ∃ Q : Number,
      v.idealChargeDeposit shares.toRat * (1 - 19 / (2 ^ 63 - 3)) ≤ Q.toRat ∧
      Q.toRat ≤ v.idealChargeDeposit shares.toRat * (1 + 19 / (2 ^ 63 - 3)) ∧
      Q.toRat ≤ c.toRat ∧
      c.toRat ≤ Q.toRat + (10 : ℚ) ^ c.exponent ∧
      0 < v.idealChargeDeposit shares.toRat ∧
      v.idealChargeDeposit shares.toRat =
        v.toExact.assetsTotal * shares.toRat / (v.toExact.sharesTotal : ℚ) := by
  have hApos : 0 < v.toExact.assetsTotal := by
    rcases lt_or_eq_of_le v.exact.assetsTotal_nonneg with h | h
    · exact h
    · exact absurd h.symm (Number.toRat_ne_zero_of_mantissa_ne_zero v.assetsTotal hmz)
  have hideal_eq : v.idealChargeDeposit shares.toRat =
      v.toExact.assetsTotal * shares.toRat / (v.toExact.sharesTotal : ℚ) := by
    unfold RawVault.idealChargeDeposit RawVault.depositNav
    rw [if_neg (ne_of_gt hApos)]
  obtain ⟨Q, hcQ, hidpos, hQnz, hQz⟩ :=
    sharesToAssetsDeposit_charge_nonempty_raw v shares c hshc hshnt hshpos hmz hsad
  have hc0 : c.mValue ≠ 0 := ne_of_beq_false (by rw [STAmount.isZero] at hcnz; exact hcnz)
  have hQm : Q.mantissa_ ≠ 0 := by
    by_cases hint : v.numericType.isIntegral = true
    · exact STAmount.ofNumber_integral_source_ne_zero v.numericType Q .upward c hint hcQ hc0
    · have hfrac : v.numericType = .fractional := by
        cases hnt : v.numericType with
        | fractional => rfl
        | integral mv mo ms msh => rw [hnt] at hint; simp [NumericType.isIntegral] at hint
      exact STAmount.ofNumber_iou_mantissa_ne_zero v.numericType Q .upward c hfrac hcQ hc0
  obtain ⟨hQnorm, hQneg, hband⟩ := hQnz hQm
  have hbandle := abs_le.mp hband
  refine ⟨Q, ?_, ?_, ?_, ?_, hidpos, hideal_eq⟩
  · nlinarith [hbandle.1]
  · nlinarith [hbandle.2]
  · exact STAmount.ofNumber_upward_ge v.numericType Q c hQnorm hQneg hcQ hc0
  · -- upward `ofNumber` ceiling, single ULP
    by_cases hint : v.numericType.isIntegral = true
    · have hwithin := STAmount.ofNumber_integral_within_one v.numericType Q .upward c
        hint hQnorm hQneg hcQ
      have hcexp : c.exponent = 0 :=
        (sharesToAssetsDeposit_integral_canonical v shares c hint hsad).1.offset_zero
      rw [hcexp]; simp only [zpow_zero]
      have := (abs_lt.mp hwithin).2; linarith
    · obtain ⟨hr_lo, hr_hi⟩ := hQnorm.mantissaBounds_nat hQm
      have hre_lo : minExponent ≤ Q.exponent_ := by
        rcases hQnorm with h0 | ⟨_, _, _, hlo, _⟩
        · exact absurd (show Q.mantissa_ = 0 by rw [h0]; rfl) hQm
        · exact hlo
      have hintf : v.numericType.isIntegral = false := by
        cases h : v.numericType.isIntegral with
        | true => exact absurd h hint | false => rfl
      have hfrac : v.numericType = .fractional := by
        cases hnt : v.numericType with
        | fractional => rfl
        | integral mv mo ms msh => rw [hnt] at hintf; simp [NumericType.isIntegral] at hintf
      have hok' : STAmount.ofNumber .fractional Q .upward = .ok c := by rw [← hfrac]; exact hcQ
      have hre_hi : Q.exponent_ + 4 ≤ maxExponent :=
        STAmount.ofNumber_iou_success_exp_range Q .upward c hr_lo hr_hi hre_lo hok' hc0
      exact STAmount.ofNumber_upward_ceiling_bounds v.numericType Q c hfrac
        hr_lo hr_hi hre_lo hre_hi hcQ hc0

/-- Adding a nonzero `Number` on the right of `Number.zero` returns it verbatim (the
second fast path of `operator_add`). -/
private lemma zero_operator_add_ne (y : Number) (hy : y.operator_eq Number.zero = false) :
    Number.zero.operator_add y .to_nearest = .ok y := by
  unfold Number.operator_add
  rw [if_neg (by rw [hy]; exact Bool.false_ne_true),
      if_pos (show Number.zero.operator_eq Number.zero = true from by decide)]
  rfl

/-- Adding a value-zero `Number` on the right of `Number.zero` returns `Number.zero`
(the first fast path of `operator_add`). -/
private lemma zero_operator_add_zero (y : Number) (hy : y.operator_eq Number.zero = true) :
    Number.zero.operator_add y .to_nearest = .ok Number.zero := by
  unfold Number.operator_add
  rw [if_pos hy]
  rfl

/-- **`ofNumber ∘ toNumber` is value-preserving on a canonical charge.** The `toNumber`
lift of an `ExactCanonical` amount snaps back verbatim under `ofNumber` for the same
numeric type: integral amounts are integer-valued (`ofNumber_integral_exact`), fractional
amounts keep at most 16 significant digits so the 19-digit re-lift re-rounds losslessly
(`normalizeToRange_16_exact` recovers the 16-digit mantissa, `checked_iou_cases` re-packs
the canonical record). -/
private lemma ofNumber_charge_roundtrip (nt : NumericType) (c : STAmount) (cN : Number)
    (A : STAmount) (hnt : c.mNumericType = nt) (hc : c.ExactCanonical) (hcnn : 0 ≤ c.toRat)
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hA : STAmount.ofNumber nt cN .to_nearest = .ok A) (hAnz : A.mValue ≠ 0) :
    A.toRat = c.toRat := by
  rcases hc with hiou | ⟨hint, hsz⟩
  · -- fractional: the 19-digit lift re-rounds to the canonical 16-digit record verbatim
    have hntf : nt = .fractional := by rw [← hnt]; exact hiou.is_fractional
    subst hntf
    have hmv_pos : 0 < c.mValue.toNat := by have := hiou.mant_lo; omega
    have hcneg : c.mIsNegative = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      have hlt : c.toRat < 0 := by
        rw [STAmount.toRat_of_neg c h]
        have hp : (0:ℚ) < (c.mValue.toNat : ℚ) * 10 ^ c.mOffset :=
          mul_pos (by exact_mod_cast hmv_pos) (by positivity)
        linarith
      linarith
    have hcform : cN = ⟨false, c.mValue * 10 * 10 * 10, c.mOffset - 3⟩ := by
      have hcan := STAmount.toNumber_iou_canonical c .to_nearest hiou
      rw [hcneg] at hcan
      rw [hcan] at hcN
      exact (Except.ok.inj hcN).symm
    have hcNneg : cN.negative_ = false := by rw [hcform]
    have hcNmant : cN.mantissa_ = c.mValue * 10 * 10 * 10 := by rw [hcform]
    have hcNexp : cN.exponent_ = c.mOffset - 3 := by rw [hcform]
    have hM3 : (c.mValue * 10 * 10 * 10).toNat = c.mValue.toNat * 1000 :=
      m_mul_thousand_no_overflow hiou.mant_hi
    have hq3 : c.mValue * 10 * 10 * 10 / 10 / 10 / 10 = c.mValue := by
      apply UInt64.toNat_inj.mp
      rw [m_div_thousand_toNat, hM3]; omega
    set neg : Bool := decide (cN.signum < 0) with hneg_def
    set working : Number := if neg then cN.operator_neg else cN with hw_def
    have hneg0 : neg = false := by rw [hneg_def, Number.signum_neg_decide]; exact hcNneg
    have hwork : working = cN := by rw [hw_def, hneg0]; exact if_neg Bool.false_ne_true
    have hnz : working.normalizeToRange kMinValue kMaxValue .to_nearest
        = .ok (c.mValue.toInt64, c.mOffset) := by
      rw [hwork]
      have h : cN.normalizeToRange cMinValue cMaxValue .to_nearest
          = .ok (c.mValue.toInt64, c.mOffset) := by
        rw [normalizeToRange_16_exact cN .to_nearest
            (by rw [hcNmant, hM3]; have := hiou.mant_lo; omega)
            (by rw [hcNmant, hM3]; have := hiou.mant_hi; omega)
            (by rw [hcNmant, hM3]; omega)
            (by rw [hcNexp]; have := hiou.exp_lo; unfold minExponent; omega)
            (by rw [hcNexp]; have := hiou.exp_hi; unfold maxExponent; omega),
            hcNneg, if_neg Bool.false_ne_true, hcNmant, hq3, hcNexp,
            show c.mOffset - 3 + 3 = c.mOffset from by ring]
      exact h
    have hof : STAmount.ofNumber .fractional cN .to_nearest
        = STAmount.checked .fractional (c.mValue.toInt64).toUInt64 c.mOffset neg .to_nearest := by
      unfold STAmount.ofNumber
      rw [if_neg (by decide), ← hneg_def, ← hw_def, hnz]
    rw [hneg0] at hof
    rw [show (c.mValue.toInt64).toUInt64 = c.mValue from rfl] at hof
    rw [hof] at hA
    have hAeq : A = ⟨.fractional, c.mValue, c.mOffset, false⟩ :=
      (STAmount.checked_iou_cases .fractional c.mValue c.mOffset false .to_nearest rfl
        hiou.mant_lo hiou.mant_hi
        (by have := hiou.exp_lo; unfold minExponent; omega)
        (by have := hiou.exp_hi; unfold maxExponent; omega)
        A hA hAnz).2.2
    rw [hAeq, STAmount.toRat_of_nonneg (⟨.fractional, c.mValue, c.mOffset, false⟩ : STAmount) rfl,
        STAmount.toRat_of_nonneg c hcneg]
  · -- integral: integer-valued, exact via `ofNumber_integral_exact`
    have hnti : nt.isIntegral = true := by rw [← hnt]; exact hint.is_integral
    obtain ⟨an, han, hval, hnorm⟩ :=
      STAmount.toNumber_exact_canonical c .to_nearest (Or.inr ⟨hint, hsz⟩)
    have hancN : an = cN := by rw [han] at hcN; exact Except.ok.inj hcN
    have hval' : cN.toRat = c.toRat := hancN ▸ hval
    have hnorm' : cN.isNormalized := hancN ▸ hnorm
    have hden : cN.toRat.den = 1 := by rw [hval']; exact STAmount.IntegralCanonical.den_eq_one c hint
    rw [STAmount.ofNumber_integral_exact nt cN .to_nearest A hnti hnorm' hden hA]
    exact hval'

set_option maxHeartbeats 1000000 in
set_option linter.style.maxHeartbeats false in
/-- **Source-faithful deposit/withdraw roundtrip provenance.** A real deposit
first computes a raw exchange charge and then clamps it before storing it. A
subsequent share withdrawal first prices a raw payout and, on its non-final
path, clamps the negated payout before returning it and updating state. This
contract records those two distinct stages rather than identifying either raw
amount with its final amount. The final withdrawal path has no debit clamp: it
pays the available balance and zeroes the vault. -/
theorem Vault.deposit_withdraw_roundtrip_proof (v : Vault) (amountDeposit : STAmount)
    (r₁ : DepositResult) (r₂ : WithdrawResult)
    (_hL : v.toExact.lossUnrealized = 0)
    (_hpos : 0 < amountDeposit.toRat)
    (_hcanon : amountDeposit.Canonical)
    (_hAV : v.assetsAvailable = v.assetsTotal)
    (_hDc : r₁.amountDeposit'.ExactCanonical)
    (_hDnn : 0 ≤ r₁.amountDeposit'.toRat)
    (_hSsz : (v.toExact.sharesTotal : ℚ) + r₁.sharesIssued.toRat ≤ 2 ^ 63 - 1)
    (hok₁ : v.deposit amountDeposit false = .ok r₁) (herr₁ : r₁.error = none)
    (hok₂ : r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂)
    (herr₂ : r₂.error = none) :
    ∃ (rawDeposit : STAmount) (cw : ComputeWithdrawResult) (sharesTotalAmount : STAmount),
      clampToSumExponent v.assetsTotal rawDeposit = .ok r₁.amountDeposit' ∧
      computeWithdrawByShares r₁.vault' r₁.sharesIssued false = .ok cw ∧
      cw.error = none ∧
      STAmount.ofNumber .int64 r₁.vault'.sharesTotal .to_nearest = .ok sharesTotalAmount ∧
      r₂.sharesBurned = cw.sharesRedeemed ∧
      ((cw.sharesRedeemed.operator_eq sharesTotalAmount = true ∧
        r₁.vault'.lossUnrealized.operator_ne Number.zero = false ∧
        ∃ allAvailable : STAmount,
          STAmount.ofNumber r₁.vault'.numericType r₁.vault'.assetsAvailable .to_nearest = .ok allAvailable ∧
          r₂.assets' = allAvailable) ∨
       (cw.sharesRedeemed.operator_eq sharesTotalAmount = false ∧
        clampToSumExponent r₁.vault'.assetsTotal cw.assets'.operator_neg = .ok r₂.assets' ∧
        r₂.assets'.isFractionalNonPositive = .ok false)) := by
  obtain ⟨_, rawDeposit, finalDeposit, _, _, _, _, _, _, _, _, _, _, _, hcompute,
    _, _, _, _, _, _, hreturnedDeposit, _, _⟩ :=
    Vault.deposit_success_reduces v amountDeposit false r₁ hok₁ herr₁
  obtain ⟨cw, _, sharesTotalAmount, hwithdrawCompute, hcwError, _, _, hsharesTotal,
    hburned, hwithdrawBranch⟩ :=
    Vault.withdraw_success_reduces r₁.vault' (.vaultShares r₁.sharesIssued) false r₂ hok₂ herr₂
  have hdepositClamp : clampToSumExponent v.assetsTotal rawDeposit = .ok r₁.amountDeposit' := by
    rw [hreturnedDeposit]
    exact (hcompute rfl).2.1
  have hcomputeByShares : computeWithdrawByShares r₁.vault' r₁.sharesIssued false = .ok cw := by
    simpa using hwithdrawCompute
  refine ⟨rawDeposit, cw, sharesTotalAmount, hdepositClamp, hcomputeByShares,
    hcwError, hsharesTotal, hburned, ?_⟩
  rcases hwithdrawBranch with ⟨hfinal, hloss, allAvailable, hallAvailable, hfinalState⟩ |
      ⟨hfinal, _, _, _, _, _, finalDebit, _, _, _, hclamp, hprecision, _, _, _, _, _, _, _, hreturnedAssets, hreturnedDebit⟩
  · exact Or.inl ⟨hfinal, hloss, allAvailable, hallAvailable, hfinalState.1⟩
  · refine Or.inr ⟨hfinal, ?_, ?_⟩
    · rw [hreturnedAssets]
      exact hclamp
    · rw [hreturnedAssets]
      exact hprecision


/-! ## Witness for exact roundtrip cancellation with clamp corrections

The `wvF` run has two real, non-identity clamps. `computeDeposit` produces
`wcF = 0.9999999999999999`, while the deposit stores `wcfF =
0.9999999999999990`. The subsequent raw withdrawal quote is
`0.9999999999999996` and its final debit is again `wcfF`. Thus the old claim
that the final values lie strictly outside the relative band was false: their
absolute difference is exactly zero. This witness retains the economic
rounding evidence by independently exposing both nonzero raw-to-final clamp
corrections, then proves exact equality of the two final amounts. -/

private theorem wvF_shares_toRat' :
    (⟨false, 7000000000000000000, -3⟩ : Number).toRat = ((7000000000000000 : ℕ) : ℚ) := by
  rw [Number.toRat_of_nonneg _ rfl,
      show ((7000000000000000000 : UInt64).toNat) = 7000000000000000000 from by decide]
  norm_num

/-- The witness vault's representation is well-formed (kernel-checked). -/
private theorem wvF_WF : wvF.WF := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Number.operator_sub_self_ok wvF.assetsTotal .downward⟩
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized; norm_isNormalized
  · show (⟨false, 3000000000000000000, -18⟩ : Number).isNormalized; norm_isNormalized
  · exact Or.inl rfl
  · intro m hm; rw [show wvF.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · show (⟨false, 7000000000000000000, -3⟩ : Number).isNormalized; norm_isNormalized
  · exact Or.inl rfl
  · show (0 : ℚ) ≤ (⟨false, 7000000000000000000, -3⟩ : Number).toRat
    rw [wvF_shares_toRat']; positivity
  · show (⟨false, 7000000000000000000, -3⟩ : Number).toRat.den = 1
    rw [wvF_shares_toRat']; exact Rat.den_natCast _
  · intro _; rfl
  · change 0 ≤ 18; decide

/-- The witness vault satisfies the invariant (kernel-checked). -/
private theorem wvF_Valid : wvF.Valid := by
  have wvF_exact_assetsTotal : wvF.toExact.assetsTotal = 3 := by
    show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
    rw [Number.toRat_of_nonneg _ rfl,
        show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
    norm_num
  have wvF_exact_sharesTotal : wvF.toExact.sharesTotal = 7000000000000000 := by
    show wvF.sharesTotal.toRat.num.toNat = _
    rw [show wvF.sharesTotal = (⟨false, 7000000000000000000, -3⟩ : Number) from rfl, wvF_shares_toRat']
    norm_num
    rfl
  refine (RawVault.valid_iff_exact wvF wvF_WF).mpr ?_
  have hAT := wvF_exact_assetsTotal
  have hAA : wvF.toExact.assetsAvailable = 3 := by
    show (⟨false, 3000000000000000000, -18⟩ : Number).toRat = _
    rw [Number.toRat_of_nonneg _ rfl,
        show ((3000000000000000000 : UInt64).toNat) = 3000000000000000000 from by decide]
    norm_num
  have hST := wvF_exact_sharesTotal
  have hL : wvF.toExact.lossUnrealized = 0 := by
    simp only [RawVault.toExact]; exact Number.toRat_eq_zero_of_mantissa_zero _ rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAT]; norm_num
  · rw [hAA]; norm_num
  · rw [hAT, hAA]
  · intro m hm; rw [show wvF.toExact.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · intro h; rw [hST] at h; exact absurd h (by norm_num)
  · intro m hm; rw [show wvF.toExact.assetsMaximum = none from rfl] at hm; exact absurd hm (by simp)
  · rw [hL]
  · rw [hL, hAT, hAA]; norm_num
  · rw [hAT, hL]; norm_num

/-- The witness vault as a `Vault`. `.toRawVault` is defeq `wvF` by construction,
so the witness deposit/withdraw runs stay computable under `decide`. -/
private def wvF_lawful' : Vault := ⟨wvF, wvF_WF, wvF_Valid⟩

/-- Raw pre-clamp payout in the concrete `wvF` withdrawal. -/
private def wwRawF : STAmount := STAmount.unchecked .fractional 9999999999999996 (-16) false

/-- Concrete deposit execution, checked before using the final equality. -/
-- Executable check of the independently-derived concrete deposit trace. Kernel
-- `decide` cannot reduce the opaque FFI call.
private theorem wvF_deposit_run : wvF_lawful'.deposit waF false = .ok wrF := by
  native_decide

/-- Concrete withdrawal execution, checked before using the final equality. -/
-- Executable check of the independently-derived concrete withdrawal trace;
-- opaque FFI prevents reduction by kernel `decide`.
private theorem wvF_withdraw_run :
    wvF'L.withdraw (.vaultShares wsF) false =
      .ok ((wvF'L.withdraw (.vaultShares wsF) false).toOption.getD ⟨none, wvF'L, wcF, wsF⟩) := by
  native_decide

/-- Independently computed deposit clamp correction. -/
-- Executable check of the independently-derived nonzero deposit correction.
private theorem wvF_deposit_clamp_correction :
    clampToSumExponent wvF.assetsTotal wcF = .ok wrF.amountDeposit' ∧
      wcF.operator_eq wrF.amountDeposit' = false := by
  native_decide

/-- Independently computed withdrawal clamp correction. -/
-- Executable check of the independently-derived nonzero withdrawal correction.
private theorem wvF_withdraw_clamp_correction :
    (match computeWithdrawByShares wvF'L wsF false with
      | .ok cw => cw.assets'.operator_eq wwRawF
      | .error _ => false) = true ∧
    clampToSumExponent wvF'.assetsTotal wwRawF.operator_neg =
      .ok ((wvF'L.withdraw (.vaultShares wsF) false).toOption.getD ⟨none, wvF'L, wcF, wsF⟩).assets' ∧
    wwRawF.operator_eq
      ((wvF'L.withdraw (.vaultShares wsF) false).toOption.getD ⟨none, wvF'L, wcF, wsF⟩).assets' = false := by
  native_decide

/-- **Proof body of `Vault.deposit_withdraw_roundtrip_clamp_correction_attained`.**
The concrete executions and both raw-stage corrections are established first;
only then is the final exact cancellation checked. -/
theorem Vault.deposit_withdraw_roundtrip_clamp_correction_attained_proof :
    ∃ (v : Vault) (amountDeposit rawDeposit rawPayout : STAmount)
      (r₁ : DepositResult) (r₂ : WithdrawResult),
      0 < amountDeposit.toRat ∧
      v.toExact.lossUnrealized = 0 ∧
      v.deposit amountDeposit false = .ok r₁ ∧ r₁.error = none ∧
      clampToSumExponent v.assetsTotal rawDeposit = .ok r₁.amountDeposit' ∧
      rawDeposit.operator_eq r₁.amountDeposit' = false ∧
      (match computeWithdrawByShares r₁.vault' r₁.sharesIssued false with
        | .ok cw => cw.assets'.operator_eq rawPayout
        | .error _ => false) = true ∧
      r₁.vault'.withdraw (.vaultShares r₁.sharesIssued) false = .ok r₂ ∧ r₂.error = none ∧
      clampToSumExponent r₁.vault'.assetsTotal rawPayout.operator_neg = .ok r₂.assets' ∧
      rawPayout.operator_eq r₂.assets' = false ∧
      r₂.assets'.operator_eq r₁.amountDeposit' = true := by
  let r₂ := (wvF'L.withdraw (.vaultShares wsF) false).toOption.getD ⟨none, wvF'L, wcF, wsF⟩
  refine ⟨wvF_lawful', waF, wcF, wwRawF, wrF, r₂,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · exact wvF_deposit_run
  · native_decide
  · exact wvF_deposit_clamp_correction.1
  · exact wvF_deposit_clamp_correction.2
  · exact wvF_withdraw_clamp_correction.1
  · exact wvF_withdraw_run
  · native_decide
  · exact wvF_withdraw_clamp_correction.2.1
  · exact wvF_withdraw_clamp_correction.2.2
  · native_decide

end XRPL.Model.SingleAssetVault
