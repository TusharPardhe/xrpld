import XRPL.Properties.LoanBroker.Defs
import XRPL.Properties.Vault.Common.GuardProofs
import XRPL.Properties.Vault.Common.WithdrawTotality
import XRPL.Properties.Protocol.Number.Mul.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Constructors.FromRepExact
import XRPL.Properties.Protocol.Number.Common.Int64Lemmas
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.GridPoint
import XRPL.Properties.Protocol.Number.Common.Defs
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact
import XRPL.Properties.Protocol.Number.Common.Closest.Bounds
import XRPL.Properties.Protocol.Number.Mul.RoundsWithin
import XRPL.Properties.Protocol.Number.Mul.Common.Underflow
import XRPL.Properties.Protocol.Number.Mul.Common.Decompose
import XRPL.Properties.Vault.Common.LawfulSupport

/-! # `LoanBroker.Valid ↔ LoanBroker.Exact.Valid`

Most clauses match directly. Only `cover_floor` is subtle. It checks
`debtTotal * coverRateMinimum ≤ 100000 * coverAvailable`. Multiplying by
`100000 = 10^5` only shifts the exponent, so it is exact and the check is a true
iff. The side conditions on `valid_iff_exact` just say the two products do not
overflow. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- `ofInt64 m` has value `m` and is normalized, for any `m ≠ Int64.minValue`. -/
lemma Number.ofInt64_facts (m : Int64) (h : m ≠ Int64.minValue) :
    (Number.ofInt64 m).toRat = (m.toInt : ℚ) ∧ (Number.ofInt64 m).isNormalized := by
  obtain ⟨result, hok, hval, hnorm⟩ :=
    Number.from_rep_exact m 0 .to_nearest h (by unfold minExponent; omega)
      (by unfold maxExponent; omega)
  have hof : Number.ofInt64 m = result := by unfold Number.ofInt64; rw [hok]; rfl
  rw [hof]; refine ⟨?_, hnorm⟩; rw [hval]; norm_num

/-- `r.toNumber` has value `r.toNat` and is normalized. -/
lemma TenthBips32.toNumber_facts (r : TenthBips32) :
    (r.toNumber).toRat = (r.toNat : ℚ) ∧ (r.toNumber).isNormalized := by
  have hlt : r.toNat < 2 ^ 32 := r.toNat_lt
  have h63 : (r.toUInt64).toNat < 2 ^ 63 := by rw [UInt32.toNat_toUInt64]; omega
  have hval64 : (r.toUInt64.toInt64).toInt = (r.toNat : ℤ) := by
    rw [UInt64.toInt64_toInt_of_lt _ h63, UInt32.toNat_toUInt64]
  have hne : r.toUInt64.toInt64 ≠ Int64.minValue := by
    intro h; have := congrArg Int64.toInt h
    rw [hval64, show Int64.minValue.toInt = -9223372036854775808 from by decide] at this; omega
  obtain ⟨hv, hn⟩ := Number.ofInt64_facts r.toUInt64.toInt64 hne
  unfold TenthBips32.toNumber
  exact ⟨by rw [hv, hval64]; push_cast; ring, hn⟩

/-- `kTenthBipsPerUnity` as a `Number` is `100000` and normalized. -/
lemma kTenthBipsPerUnity_facts :
    (kTenthBipsPerUnity.toNumber).toRat = 100000 ∧ (kTenthBipsPerUnity.toNumber).isNormalized := by
  obtain ⟨hv, hn⟩ := TenthBips32.toNumber_facts kTenthBipsPerUnity
  exact ⟨by rw [hv]; rfl, hn⟩

/-- The debt cap `Number` is `2^63 − 1` and normalized. -/
lemma debtMaxCap_facts :
    (debtMaxCap).toRat = (2 : ℚ) ^ 63 - 1 ∧ (debtMaxCap).isNormalized := by
  obtain ⟨hv, hn⟩ := Number.ofInt64_facts (9223372036854775807 : Int64) (by decide)
  refine ⟨?_, hn⟩
  rw [show debtMaxCap = Number.ofInt64 (9223372036854775807 : Int64) from rfl, hv]
  norm_num [show (9223372036854775807 : Int64).toInt = 9223372036854775807 from by decide]

variable {lb : LoanBroker}

/-- `debtMaximum.operator_le debtMaxCap` says `debtMaximum.toRat ≤ 2^63 − 1`. -/
theorem LoanBroker.debtMaximum_cap_iff (hwf : lb.WF) :
    lb.debtMaximum.operator_le debtMaxCap = true ↔
      lb.debtMaximum.toRat ≤ (2 : ℚ) ^ 63 - 1 := by
  rw [operator_le_iff _ _ hwf.debtMaximum_norm debtMaxCap_facts.2, debtMaxCap_facts.1]

/-- `C * 100000` is representable: multiplying by `10^5` raises the exponent by 5,
still in range by `hhi`. -/
lemma LoanBroker.coverScale_repr (C : Number) (hC : C.isNormalized)
    (hhi : C.exponent_ + 5 ≤ maxExponent) :
    ∃ w : Number, w.isNormalized ∧ w.toRat = C.toRat * 100000 := by
  by_cases h0 : C.mantissa_ = 0
  · exact ⟨Number.zero, Or.inl rfl, by rw [Number.toRat_eq_zero_iff.mpr h0, Number.toRat_zero]; ring⟩
  · refine ⟨⟨C.negative_, C.mantissa_, C.exponent_ + 5⟩, ?_, ?_⟩
    · rcases hC with hz | ⟨hmin, hmax, hcusp, hlo, _⟩
      · subst hz; exact absurd rfl h0
      · refine Or.inr ⟨hmin, hmax, hcusp, ?_, ?_⟩
        · show minExponent ≤ C.exponent_ + 5; unfold minExponent at hlo ⊢; omega
        · show C.exponent_ + 5 ≤ maxExponent; exact hhi
    · have hpow : (10 : ℚ) ^ (C.exponent_ + 5) = (10 : ℚ) ^ C.exponent_ * 100000 := by
        rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; norm_num
      by_cases hneg : C.negative_ = true
      · rw [Number.toRat_of_neg ⟨C.negative_, C.mantissa_, C.exponent_ + 5⟩ hneg,
            Number.toRat_of_neg C hneg, hpow]; ring
      · have hf : C.negative_ = false := by simpa using hneg
        rw [Number.toRat_of_nonneg ⟨C.negative_, C.mantissa_, C.exponent_ + 5⟩ hf,
            Number.toRat_of_nonneg C hf, hpow]; ring

/-- A mantissa-`0` `doNormalize` (64-bit) result is the literal `Number.zero`. -/
lemma doNormalize_zero_shape (neg : Bool) (mantissa : UInt64) (exponent : Int)
    (minM maxM : UInt64) (mode : rounding_mode) (result : Number)
    (hok : doNormalize neg mantissa exponent minM maxM mode = .ok result)
    (h0 : result.mantissa_ = 0) : result = Number.zero := by
  unfold doNormalize at hok
  by_cases hm : (mantissa == 0) = true
  · rw [if_pos hm] at hok; exact (Except.ok.inj hok).symm
  · rw [if_neg hm] at hok
    simp only [] at hok
    rcases hsu : doNormalize_scaleUp minM mantissa exponent with ⟨m₁, e₁⟩
    rw [hsu] at hok; simp only [] at hok
    set g₀ : Guard := if neg then Guard.new.set_negative else Guard.new with hg₀
    cases hsd : doNormalize_scaleDown maxM m₁ e₁ g₀ with
    | error err => rw [hsd] at hok; simp at hok
    | ok sd =>
      obtain ⟨m₂, e₂, g₂⟩ := sd
      rw [hsd] at hok; simp only [] at hok
      by_cases hund : (e₂ < minExponent || m₂ < minM) = true
      · rw [if_pos hund] at hok; exact (Except.ok.inj hok).symm
      · rw [if_neg hund] at hok
        cases hcap : doNormalize_capAtMaxRep m₂ e₂ g₂ with
        | error err => rw [hcap] at hok; simp at hok
        | ok cp =>
          obtain ⟨m₃, e₃, g₃⟩ := cp
          rw [hcap] at hok; simp only [] at hok
          cases hru : g₃.doRoundUp neg m₃ e₃ minM maxM mode .normalize2 with
          | error err => rw [hru] at hok; simp at hok
          | ok res =>
            rw [hru] at hok; simp only [] at hok
            have hres : result = res.toNumber := (Except.ok.inj hok).symm
            rw [hres]
            exact Guard.doRoundUp_zero_shape g₃ neg m₃ e₃ minM maxM mode .normalize2 res hru
              (by rw [hres] at h0; exact h0)

/-- A product is always normalized. A zero operand returns that operand, otherwise
the result comes from `normalize`. -/
lemma operator_mul_isNormalized (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_mul x y mode = .ok result) : result.isNormalized := by
  by_cases h0 : result.mantissa_ = 0
  · unfold Number.operator_mul at hok
    by_cases hxg : x.operator_eq Number.zero = true
    · rw [if_pos hxg] at hok
      rw [← (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok))]; exact hx
    · rw [if_neg hxg] at hok
      by_cases hyg : y.operator_eq Number.zero = true
      · rw [if_pos hyg] at hok
        rw [← (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok))]; exact hy
      · rw [if_neg hyg] at hok
        simp only [] at hok
        rcases hsd : scaleDown128 (toUInt128 x.mantissa_ * toUInt128 y.mantissa_)
            (x.exponent_ + y.exponent_)
            (if x.negative_ != y.negative_ then Guard.new.set_negative else Guard.new) with ⟨zm, ze, g⟩
        rw [hsd] at hok; simp only [] at hok
        cases hru : g.doRoundUp (x.negative_ != y.negative_) zm ze largeRange.min largeRange.max mode .overflow with
        | error err => rw [hru] at hok; simp at hok
        | ok res =>
          rw [hru] at hok; simp only [] at hok
          unfold Number.normalize at hok
          rw [doNormalize_zero_shape _ _ _ _ _ _ result hok h0]; exact Or.inl rfl
  · obtain ⟨hxne, hyne⟩ := operator_mul_operands_ne_zero hx hy hok h0
    exact operator_mul_result_isNormalized x y result mode hx hy hxne hyne hok h0

/-- `Valid ↔ Exact.Valid` under `WF`. `hcover` keeps `coverAvailable * 100000` in
range, `htot` says the two `cover_floor` products succeed. Both hold for any real
broker. -/
theorem LoanBroker.valid_iff_exact (hwf : lb.WF)
    (hcover : lb.coverAvailable.exponent_ + 5 ≤ maxExponent)
    (htot : ∃ lhs rhs,
      lb.debtTotal.operator_mul lb.coverRateMinimum.toNumber .upward = .ok lhs ∧
      lb.coverAvailable.operator_mul kTenthBipsPerUnity.toNumber .to_nearest = .ok rhs) :
    lb.Valid ↔ lb.toExact.Valid := by
  -- shared: the right side of cover_floor is exactly `coverAvailable · 100000`
  obtain ⟨w, hw_norm, hw_val⟩ := LoanBroker.coverScale_repr lb.coverAvailable hwf.coverAvailable_norm hcover
  have hrhs_exact : ∀ rhs, lb.coverAvailable.operator_mul kTenthBipsPerUnity.toNumber .to_nearest = .ok rhs →
      rhs.toRat = lb.coverAvailable.toRat * 100000 ∧ rhs.isNormalized := by
    intro rhs hrhs
    have hround := operator_mul_rounded_to_nearest lb.coverAvailable kTenthBipsPerUnity.toNumber rhs
      hwf.coverAvailable_norm kTenthBipsPerUnity_facts.2 hrhs
    rw [kTenthBipsPerUnity_facts.1] at hround
    have hval : rhs.toRat = lb.coverAvailable.toRat * 100000 :=
      Number.RoundsToRepresentable.eq_of_representable rhs _ hround w hw_norm hw_val
    exact ⟨hval, operator_mul_isNormalized _ _ _ _ hwf.coverAvailable_norm
      kTenthBipsPerUnity_facts.2 hrhs⟩
  constructor
  · -- Valid → Exact.Valid
    intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h.identity_wellFormed
    · have := (operator_le_iff _ _ Number.zero_isNormalized hwf.debtTotal_norm).mp h.debtTotal_nonneg
      rwa [Number.toRat_zero] at this
    · have := (operator_le_iff _ _ Number.zero_isNormalized hwf.debtMaximum_norm).mp h.debtMaximum_nonneg
      rwa [Number.toRat_zero] at this
    · have := (operator_le_iff _ _ Number.zero_isNormalized hwf.coverAvailable_norm).mp h.coverAvailable_nonneg
      rwa [Number.toRat_zero] at this
    · exact (LoanBroker.debtMaximum_cap_iff hwf).mp h.debtMaximum_cap
    · intro hne
      have hdz : lb.debtMaximum ≠ Number.zero :=
        fun heq => hne (show lb.debtMaximum.toRat = 0 by rw [heq]; exact Number.toRat_zero)
      exact (operator_le_iff _ _ hwf.debtTotal_norm hwf.debtMaximum_norm).mp (h.debt_within_cap hdz)
    · obtain ⟨lhs, rhs, hlhs, hrhs⟩ := htot
      obtain ⟨hrhs_val, hrhs_norm⟩ := hrhs_exact rhs hrhs
      have hlhs_norm := operator_mul_isNormalized _ _ _ _ hwf.debtTotal_norm
        (TenthBips32.toNumber_facts _).2 hlhs
      have hle : lhs.toRat ≤ rhs.toRat :=
        (operator_le_iff _ _ hlhs_norm hrhs_norm).mp (h.cover_floor lhs rhs hlhs hrhs)
      rw [hrhs_val] at hle
      have hDnn : (0 : ℚ) ≤ lb.debtTotal.toRat := by
        have := (operator_le_iff _ _ Number.zero_isNormalized hwf.debtTotal_norm).mp h.debtTotal_nonneg
        rwa [Number.toRat_zero] at this
      have hDrle : lb.debtTotal.toRat * (lb.coverRateMinimum.toNat : ℚ) ≤ lhs.toRat := by
        by_cases hlz : lhs.mantissa_ = 0
        · have hz : lb.debtTotal.toRat * (lb.coverRateMinimum.toNat : ℚ) = 0 := by
            by_cases hDm : lb.debtTotal.mantissa_ = 0
            · rw [Number.toRat_eq_zero_iff.mpr hDm]; ring
            · by_cases hRm : lb.coverRateMinimum.toNumber.mantissa_ = 0
              · have hr0 : (lb.coverRateMinimum.toNat : ℚ) = 0 := by
                  have := Number.toRat_eq_zero_iff.mpr hRm
                  rwa [(TenthBips32.toNumber_facts _).1] at this
                rw [hr0]; ring
              · exfalso
                have hsmall := operator_mul_underflow_truth_small lb.debtTotal
                  lb.coverRateMinimum.toNumber lhs .upward hwf.debtTotal_norm
                  (TenthBips32.toNumber_facts _).2 hDm hRm hlhs hlz
                rw [(TenthBips32.toNumber_facts _).1] at hsmall
                have hDge := Number.abs_toRat_ge_spr lb.debtTotal hwf.debtTotal_norm hDm
                rw [abs_of_nonneg hDnn] at hDge
                have hrge1 : (1 : ℚ) ≤ (lb.coverRateMinimum.toNat : ℚ) := by
                  have hne : lb.coverRateMinimum.toNat ≠ 0 := by
                    intro h0'
                    apply hRm
                    rw [← Number.toRat_eq_zero_iff, (TenthBips32.toNumber_facts _).1]
                    exact_mod_cast h0'
                  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
                rw [abs_of_nonneg (by positivity)] at hsmall
                nlinarith [hDge, hrge1, hDnn, hsmall]
          rw [hz]; exact le_of_eq (Number.toRat_eq_zero_iff.mpr hlz).symm
        · have hround := operator_mul_rounds_upward lb.debtTotal lb.coverRateMinimum.toNumber lhs
            hwf.debtTotal_norm (TenthBips32.toNumber_facts _).2 hlhs hlz
          obtain ⟨hdir, _⟩ := hround
          rw [(TenthBips32.toNumber_facts _).1] at hdir
          exact hdir
      show lb.debtTotal.toRat * (lb.coverRateMinimum.toNat : ℚ) ≤ 100000 * lb.coverAvailable.toRat
      rw [mul_comm (100000 : ℚ) lb.coverAvailable.toRat]
      linarith [hDrle, hle]
    · intro h0
      have hlc : lb.loanCount = 0 :=
        UInt32.toNat_inj.mp (show lb.loanCount.toNat = (0 : UInt32).toNat from h0)
      show lb.debtTotal.toRat = 0
      rw [h.empty_broker hlc]; exact Number.toRat_zero
    · exact h.mgmtFee_cap
    · exact h.coverMin_cap
    · exact h.coverLiq_cap
    · exact h.rate_coupling
  · -- Exact.Valid → Valid
    intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h.identity_wellFormed
    · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.debtTotal_norm, Number.toRat_zero]
      exact h.debtTotal_nonneg
    · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.debtMaximum_norm, Number.toRat_zero]
      exact h.debtMaximum_nonneg
    · rw [operator_le_iff _ _ Number.zero_isNormalized hwf.coverAvailable_norm, Number.toRat_zero]
      exact h.coverAvailable_nonneg
    · exact (LoanBroker.debtMaximum_cap_iff hwf).mpr h.debtMaximum_cap
    · intro hdz
      rw [operator_le_iff _ _ hwf.debtTotal_norm hwf.debtMaximum_norm]
      have hmne : lb.debtMaximum.mantissa_ ≠ 0 :=
        fun hz => hdz (Number.eq_zero_of_mantissa_zero _ hwf.debtMaximum_norm hz)
      exact h.debt_within_cap (Number.mantissa_ne_zero_iff.mp hmne)
    · intro lhs rhs hlhs hrhs
      obtain ⟨hrhs_val, hrhs_norm⟩ := hrhs_exact rhs hrhs
      have hlhs_norm := operator_mul_isNormalized _ _ _ _ hwf.debtTotal_norm
        (TenthBips32.toNumber_facts _).2 hlhs
      rw [operator_le_iff _ _ hlhs_norm hrhs_norm, hrhs_val]
      by_cases hlz : lhs.mantissa_ = 0
      · rw [Number.toRat_eq_zero_iff.mpr hlz]
        exact mul_nonneg h.coverAvailable_nonneg (by norm_num)
      · have hround := operator_mul_rounded_upward lb.debtTotal lb.coverRateMinimum.toNumber lhs
          hwf.debtTotal_norm (TenthBips32.toNumber_facts _).2 hlhs hlz
        rw [(TenthBips32.toNumber_facts _).1] at hround
        obtain ⟨n, hlo, hlval⟩ := hround
        rw [hlval]
        have hex : lb.debtTotal.toRat * (lb.coverRateMinimum.toNat : ℚ)
            ≤ lb.coverAvailable.toRat * 100000 := by
          rw [mul_comm lb.coverAvailable.toRat (100000 : ℚ)]; exact h.cover_floor
        have := Number.upper_tight _ n hlo w hw_norm (by rw [hw_val]; exact hex)
        rwa [hw_val] at this
    · intro h0
      have h0n : lb.loanCount.toNat = 0 := by rw [h0]; rfl
      have : lb.debtTotal.toRat = 0 := h.empty_broker h0n
      exact Number.eq_zero_of_mantissa_zero _ hwf.debtTotal_norm (Number.toRat_eq_zero_iff.mp this)
    · exact h.mgmtFee_cap
    · exact h.coverMin_cap
    · exact h.coverLiq_cap
    · exact h.rate_coupling

end XRPL.Model.Lending
