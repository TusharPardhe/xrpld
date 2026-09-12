import XRPL.Properties.Vault.Defs
import XRPL.Properties.Protocol.Number.Compare.Compare
import XRPL.Properties.Protocol.Number.Common.ToRatLemmas
import XRPL.Properties.Protocol.Number.Common.Closest.Tightness
import XRPL.Properties.Protocol.Number.Common.Closest.OpExact
import XRPL.Properties.Protocol.Number.Sub.RoundsToRepresentable
import XRPL.Properties.Protocol.Number.Add.Common.Rounded
import XRPL.Properties.Protocol.Number.Add.Common.ToNearest.AlgorithmicFacts.DiffSignRepresents
import XRPL.Properties.Protocol.STAmount.Add.Common.IOU
import XRPL.Properties.Vault.Common.SubZeroShape

namespace XRPL.Model.Protocol

/-- Subtracting a `Number` from itself always succeeds: the different-sign add
takes its exact-cancellation guard. Reachable states have `assetsAvailable = assetsTotal`,
so this discharges `RawVault.WF.assetsTotal_sub_ok` there. -/
theorem Number.operator_sub_self_ok (x : Number) (mode : rounding_mode) :
    ∃ d, x.operator_sub x mode = .ok d := by
  unfold Number.operator_sub
  by_cases hx : x.mantissa_ = 0
  · refine ⟨x, ?_⟩
    have hneg : x.operator_neg = Number.zero := by
      unfold Number.operator_neg; rw [if_pos (by rw [hx]; rfl)]
    rw [hneg]; unfold Number.operator_add
    rw [if_pos (show Number.zero.operator_eq Number.zero = true by decide)]; rfl
  · refine ⟨Number.zero, ?_⟩
    have hnegm : x.operator_neg.mantissa_ ≠ 0 := by
      rw [Number.operator_neg_mantissa_of_ne x hx]; exact hx
    have hguard3 : x.operator_eq x.operator_neg.operator_neg = true := by
      rw [neg_neg_of_mant_ne hx]; unfold Number.operator_eq; simp
    unfold Number.operator_add
    rw [if_neg (Number.not_operator_eq_zero_of_mantissa_ne hnegm),
        if_neg (Number.not_operator_eq_zero_of_mantissa_ne hx), if_pos hguard3]; rfl

end XRPL.Model.Protocol

/-! # Equivalence of the operator and exact-rational vault invariants -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

private lemma zero_norm : (Number.zero).isNormalized := Or.inl rfl

/-- For a normalized `Number`, `toRat = 0` is equivalent to being the canonical zero. -/
private lemma toRat_eq_zero_iff_eq_zero {n : Number} (hn : n.isNormalized) :
    n.toRat = 0 ↔ n = Number.zero := by
  constructor
  · intro h; exact Number.eq_zero_of_mantissa_zero n hn (Number.toRat_eq_zero_iff.mp h)
  · intro h; rw [h, Number.toRat_zero]

/-- A normalized nonnegative `Number` has a clear sign bit. -/
private lemma neg_false_of_nonneg (n : Number) (hn : n.isNormalized) (h0 : 0 ≤ n.toRat) :
    n.negative_ = false := by
  by_contra hb
  have hb' : n.negative_ = true := by simpa using hb
  have hle := Number.toRat_nonpos_of_negative n hb'
  have hm0 : n.mantissa_ = 0 := Number.toRat_eq_zero_iff.mp (le_antisymm hle h0)
  rw [Number.eq_zero_of_mantissa_zero n hn hm0] at hb'; exact absurd hb' (by decide)

/-! ## Clause 8 (`lossUnrealized_le`) grid helpers -/

/-- **Flush corner of the downward difference.** When `x - y` (both normalized
nonnegative) rounds down to a zero-mantissa result, the result is the canonical
zero and the exact difference sits strictly below the smallest positive grid
magnitude. Reduces to the different-sign add facts (`x - y = x + (-y)`). -/
private lemma sub_downward_mantissa_zero (x y d : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hxneg : x.negative_ = false) (hyneg : y.negative_ = false)
    (hok : x.operator_sub y .downward = .ok d) (h0 : d.mantissa_ = 0) :
    d = Number.zero ∧
      |x.toRat - y.toRat| < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by
  have hspr_pos : (0 : ℚ) < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by positivity
  rw [Number.operator_sub] at hok
  set ny := y.operator_neg with hny_def
  have hnynorm : ny.isNormalized := Number.operator_neg_isNormalized y hy
  by_cases hyg : ny.operator_eq Number.zero = true
  · -- `-y = 0`: the add returns `x`, and `y` is zero.
    have hres : d = x := by
      rw [Number.operator_add] at hok; rw [if_pos hyg] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok d from hok)).symm
    have hxz : x = Number.zero := Number.eq_zero_of_mantissa_zero x hx (hres ▸ h0)
    have hnym0 : ny.mantissa_ = 0 := Number.mantissa_eq_zero_of_operator_eq_zero hyg
    have hym : y.mantissa_ = 0 := by
      by_contra hne
      have h1 : ny.mantissa_ = y.mantissa_ := by
        rw [hny_def]; exact Number.operator_neg_mantissa_of_ne y hne
      rw [h1] at hnym0; exact hne hnym0
    have hyz : y = Number.zero := Number.eq_zero_of_mantissa_zero y hy hym
    exact ⟨hres.trans hxz, by rw [hxz, hyz, Number.toRat_zero, sub_self, abs_zero]; exact hspr_pos⟩
  by_cases hxg : x.operator_eq Number.zero = true
  · -- `x = 0`: the add returns `-y`, which is zero, so `y` is zero.
    have hres : d = ny := by
      rw [Number.operator_add] at hok; rw [if_neg hyg, if_pos hxg] at hok
      exact (Except.ok.inj (show (Except.ok ny : Except Error Number) = .ok d from hok)).symm
    have hxtr : x.toRat = 0 :=
      Number.toRat_eq_zero_of_mantissa_zero x (Number.mantissa_eq_zero_of_operator_eq_zero hxg)
    have hnym0 : ny.mantissa_ = 0 := hres ▸ h0
    have hnyz : ny = Number.zero := Number.eq_zero_of_mantissa_zero ny hnynorm hnym0
    have hym : y.mantissa_ = 0 := by
      by_contra hne
      have h1 : ny.mantissa_ = y.mantissa_ := by
        rw [hny_def]; exact Number.operator_neg_mantissa_of_ne y hne
      rw [h1] at hnym0; exact hne hnym0
    have hytr : y.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero y hym
    exact ⟨hres.trans hnyz, by rw [hxtr, hytr, sub_self, abs_zero]; exact hspr_pos⟩
  by_cases heqg : x.operator_eq ny.operator_neg = true
  · -- exact cancellation: the add returns zero and `x.toRat = y.toRat`.
    have hres : d = Number.zero := by
      rw [Number.operator_add] at hok; rw [if_neg hyg, if_neg hxg, if_pos heqg] at hok
      exact (Except.ok.inj (show (Except.ok Number.zero : Except Error Number) = .ok d from hok)).symm
    have hxeq : x.toRat = ny.operator_neg.toRat :=
      (operator_eq_iff x ny.operator_neg hx (Number.operator_neg_isNormalized ny hnynorm)).mp heqg
    rw [Number.toRat_neg, hny_def, Number.toRat_neg, neg_neg] at hxeq
    exact ⟨hres, by rw [hxeq, sub_self, abs_zero]; exact hspr_pos⟩
  · -- generic different-sign body.
    have hxm : x.mantissa_ ≠ 0 := fun h =>
      hxg (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
    have hym : y.mantissa_ ≠ 0 := by
      intro h
      exact hyg (by rw [hny_def, Number.operator_neg, if_pos (by simp [h])]; decide)
    have hnym : ny.mantissa_ ≠ 0 := by
      rw [hny_def, Number.operator_neg_mantissa_of_ne y hym]; exact hym
    have hdiff : x.negative_ ≠ ny.negative_ := by
      rw [hxneg, hny_def, Number.operator_neg_negative_of_ne y hym, hyneg]; decide
    obtain ⟨M, ze', δ, zn, sticky, _, _, _, _, _, _, _, hok128, _⟩ :=
      operator_add_algorithmic_facts_diff_sign_represents x ny d .downward hx hnynorm hxm hnym
        hdiff heqg hok
    have hny_tr : ny.toRat = -y.toRat := by rw [hny_def, Number.toRat_neg]
    have hsmall := operator_add_underflow_truth_small x ny d .downward hx hnynorm hxm hnym
      hdiff heqg hok h0
    rw [hny_tr] at hsmall
    exact ⟨doNormalize128_zero_shape_sz zn M ze' sticky .downward d hok128 h0,
      by rw [← sub_eq_add_neg] at hsmall; exact hsmall⟩

/-- **Downward-subtraction grid maximality.** When `x.operator_sub y .downward = .ok d`,
any normalized `w` with `w.toRat ≤ x.toRat - y.toRat` is `≤ d.toRat`, provided the
result `d` is nonzero (the on-grid case). -/
private lemma sub_downward_grid_max_ne (x y d w : Number)
    (hx : x.isNormalized) (hy : y.isNormalized) (hw : w.isNormalized)
    (hok : x.operator_sub y .downward = .ok d) (hd : d.mantissa_ ≠ 0)
    (hwle : w.toRat ≤ x.toRat - y.toRat) : w.toRat ≤ d.toRat := by
  obtain ⟨n, hlo, hval⟩ := operator_sub_rounded_downward x y d hx hy hok hd
  rw [hval]
  exact Number.lower_tight (x.toRat - y.toRat) n hlo w hw hwle

/-- **General-mode add normalization.** A nonzero-mantissa add of two normalized
operands is normalized. Guard branches return an operand or the canonical zero;
the generic branch is the existing any-mode fact. -/
private lemma add_isNormalized_anyMode (x y result : Number) (mode : rounding_mode)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : Number.operator_add x y mode = .ok result)
    (hresult : result.mantissa_ ≠ 0) : result.isNormalized := by
  by_cases hy_guard : y.operator_eq Number.zero = true
  · have h_result : result = x := by
      unfold Number.operator_add at hok
      rw [if_pos hy_guard] at hok
      exact (Except.ok.inj (show (Except.ok x : Except Error Number) = .ok result from hok)).symm
    rw [h_result]; exact hx
  by_cases hx_guard : x.operator_eq Number.zero = true
  · have h_result : result = y := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_pos hx_guard] at hok
      exact (Except.ok.inj (show (Except.ok y : Except Error Number) = .ok result from hok)).symm
    rw [h_result]; exact hy
  by_cases heq_guard : x.operator_eq y.operator_neg = true
  · have h_result : result = Number.zero := by
      unfold Number.operator_add at hok
      rw [if_neg hy_guard, if_neg hx_guard, if_pos heq_guard] at hok
      exact (Except.ok.inj
        (show (Except.ok Number.zero : Except Error Number) = .ok result from hok)).symm
    exact absurd (show result.mantissa_ = 0 by rw [h_result]; rfl) hresult
  have hx_mant_ne : x.mantissa_ ≠ 0 := fun h =>
    hx_guard (by rw [Number.eq_zero_of_mantissa_zero x hx h]; decide)
  have hy_mant_ne : y.mantissa_ ≠ 0 := fun h =>
    hy_guard (by rw [Number.eq_zero_of_mantissa_zero y hy h]; decide)
  exact operator_add_result_isNormalized_anyMode x y result mode hx hy hx_mant_ne hy_mant_ne
    heq_guard hok hresult

/-- The downward-subtraction result is normalized in the nonzero (on-grid) case. -/
private lemma sub_downward_result_norm (x y d : Number)
    (hx : x.isNormalized) (hy : y.isNormalized)
    (hok : x.operator_sub y .downward = .ok d) (hd : d.mantissa_ ≠ 0) : d.isNormalized := by
  unfold Number.operator_sub at hok
  exact add_isNormalized_anyMode x y.operator_neg d .downward hx
    (Number.operator_neg_isNormalized y hy) hok hd

/-- If `loss.operator_le d = true` and `d` has zero mantissa (`d.toRat = 0`), then
`loss.toRat ≤ 0`. Read directly off the `operator_lt` Bool definition, so no
normalization of `d` is needed. -/
private lemma le_zero_of_operator_le_mantissa_zero (loss d : Number)
    (hle : loss.operator_le d = true) (hd : d.mantissa_ = 0) : loss.toRat ≤ 0 := by
  have hlt : Number.operator_lt d loss = false := by
    unfold Number.operator_le at hle; simpa using hle
  by_cases hln : loss.negative_ = true
  · exact Number.toRat_nonpos_of_negative loss hln
  · have hln' : loss.negative_ = false := by simpa using hln
    by_cases hdn : d.negative_ = true
    · -- d negative, loss nonneg ⇒ `d < loss`, contradicting `d ≮ loss`
      have heval : Number.operator_lt d loss = true := by
        simp [Number.operator_lt, hdn, hln']
      rw [heval] at hlt; exact absurd hlt (by simp)
    · have hdn' : d.negative_ = false := by simpa using hdn
      have heval : Number.operator_lt d loss = decide (loss.mantissa_ > 0) := by
        simp [Number.operator_lt, hdn', hln', hd]
      rw [heval] at hlt
      have hm0 : loss.mantissa_ = 0 := by
        by_contra hne
        exact absurd hlt (by simp [UInt64.pos_iff_ne_zero.mpr hne])
      rw [Number.toRat_eq_zero_of_mantissa_zero loss hm0]

/-- The forward `.ok` half of the eighth clause: from the operator bound on the
rounded difference, recover the exact bound. -/
private lemma lossUnrealized_le_forward_ok (aT aA loss d : Number)
    (hT : aT.isNormalized) (hA : aA.isNormalized) (hL : loss.isNormalized)
    (hAle : aA.toRat ≤ aT.toRat)
    (hok : aT.operator_sub aA .downward = .ok d)
    (hclause : loss.operator_le d = true) :
    loss.toRat ≤ aT.toRat - aA.toRat := by
  by_cases hd : d.mantissa_ = 0
  · -- `d.toRat = 0`; the operator bound gives `loss ≤ 0 ≤ aT - aA`.
    have := le_zero_of_operator_le_mantissa_zero loss d hclause hd
    linarith
  · have hdn : d.isNormalized := sub_downward_result_norm aT aA d hT hA hok hd
    have h1 : loss.toRat ≤ d.toRat := (operator_le_iff loss d hL hdn).mp hclause
    obtain ⟨n, hlo, hval⟩ := operator_sub_rounded_downward aT aA d hT hA hok hd
    have h2 : d.toRat ≤ aT.toRat - aA.toRat := by rw [hval]; exact Number.lower_le _ n hlo
    linarith

/-- For a well-formed representation, the operator invariant (`RawVault.Valid`) and
the exact-rational invariant coincide. `WF` is required because `operator_le` is
faithful to `≤` only on normalized `Number`s, and its `assetsTotal_sub_ok` clause
keeps the `lossUnrealized_le` subtraction from erroring. -/
theorem RawVault.valid_iff_exact (rv : RawVault) (hwf : rv.WF) :
    rv.Valid ↔ rv.toExact.Valid := by
  constructor
  · -- FORWARD: rv.Valid → rv.toExact.Valid
    intro hv
    refine
      { assetsTotal_nonneg := ?_
        assetsAvailable_nonneg := ?_
        assetsAvailable_le := ?_
        assetsMaximum_pos := ?_
        empty_shares := ?_
        cap := ?_
        lossUnrealized_nonneg := ?_
        lossUnrealized_le := ?_
        withdraw_nav_nonneg := ?_ }
    · -- 0 ≤ assetsTotal
      have := (operator_le_iff _ _ zero_norm hwf.assetsTotal_norm).mp hv.assetsTotal_nonneg
      rwa [Number.toRat_zero] at this
    · -- 0 ≤ assetsAvailable
      have := (operator_le_iff _ _ zero_norm hwf.assetsAvailable_norm).mp hv.assetsAvailable_nonneg
      rwa [Number.toRat_zero] at this
    · -- assetsAvailable ≤ assetsTotal
      exact (operator_le_iff _ _ hwf.assetsAvailable_norm hwf.assetsTotal_norm).mp hv.assetsAvailable_le
    · -- assetsMaximum positive
      intro m hm
      show 0 < m
      obtain ⟨m0, hm0, hval⟩ := Option.mem_map.mp hm
      have hm0norm := hwf.assetsMaximum_norm m0 hm0
      have := (operator_lt_iff _ _ zero_norm hm0norm).mp (hv.assetsMaximum_pos m0 hm0)
      rw [Number.toRat_zero] at this
      rwa [← hval]
    · -- empty_shares
      intro hsh
      have hsh0 : rv.sharesTotal.toRat = 0 := by
        have h := RawVault.WF.toExact_sharesTotal rv hwf
        rw [hsh] at h; simpa using h.symm
      have hszero : rv.sharesTotal = Number.zero :=
        (toRat_eq_zero_iff_eq_zero hwf.sharesTotal_norm).mp hsh0
      obtain ⟨hT, hA⟩ := hv.empty_shares hszero
      exact ⟨by show rv.assetsTotal.toRat = 0; rw [hT, Number.toRat_zero],
             by show rv.assetsAvailable.toRat = 0; rw [hA, Number.toRat_zero]⟩
    · -- cap
      intro m hm
      obtain ⟨m0, hm0, hval⟩ := Option.mem_map.mp hm
      have hm0norm := hwf.assetsMaximum_norm m0 hm0
      have := (operator_le_iff _ _ hwf.assetsTotal_norm hm0norm).mp (hv.cap m0 hm0)
      rwa [← hval]
    · -- 0 ≤ lossUnrealized
      have := (operator_le_iff _ _ zero_norm hwf.lossUnrealized_norm).mp hv.lossUnrealized_nonneg
      rwa [Number.toRat_zero] at this
    · -- lossUnrealized ≤ assetsTotal - assetsAvailable
      show rv.lossUnrealized.toRat ≤ rv.assetsTotal.toRat - rv.assetsAvailable.toRat
      have hAle : rv.assetsAvailable.toRat ≤ rv.assetsTotal.toRat :=
        (operator_le_iff _ _ hwf.assetsAvailable_norm hwf.assetsTotal_norm).mp hv.assetsAvailable_le
      cases hsub : rv.assetsTotal.operator_sub rv.assetsAvailable .downward with
      | ok d =>
        exact lossUnrealized_le_forward_ok rv.assetsTotal rv.assetsAvailable rv.lossUnrealized d
          hwf.assetsTotal_norm hwf.assetsAvailable_norm hwf.lossUnrealized_norm hAle hsub
          (hv.lossUnrealized_le d hsub)
      | error e =>
        -- Impossible: `WF.assetsTotal_sub_ok` says the subtraction succeeds.
        exfalso
        obtain ⟨d, hd⟩ := hwf.assetsTotal_sub_ok
        rw [hsub] at hd
        simp at hd
    · -- 0 ≤ assetsTotal - lossUnrealized
      have := (operator_le_iff _ _ hwf.lossUnrealized_norm hwf.assetsTotal_norm).mp hv.withdraw_nav_nonneg
      show (0 : ℚ) ≤ rv.assetsTotal.toRat - rv.lossUnrealized.toRat
      linarith
  · -- BACKWARD: rv.toExact.Valid → rv.Valid
    intro he
    refine
      { assetsTotal_nonneg := ?_
        assetsAvailable_nonneg := ?_
        assetsAvailable_le := ?_
        assetsMaximum_pos := ?_
        empty_shares := ?_
        cap := ?_
        lossUnrealized_nonneg := ?_
        lossUnrealized_le := ?_
        withdraw_nav_nonneg := ?_ }
    · -- 0 ≤ assetsTotal
      rw [operator_le_iff _ _ zero_norm hwf.assetsTotal_norm, Number.toRat_zero]
      exact he.assetsTotal_nonneg
    · rw [operator_le_iff _ _ zero_norm hwf.assetsAvailable_norm, Number.toRat_zero]
      exact he.assetsAvailable_nonneg
    · rw [operator_le_iff _ _ hwf.assetsAvailable_norm hwf.assetsTotal_norm]
      exact he.assetsAvailable_le
    · -- assetsMaximum positive
      intro m hm
      rw [operator_lt_iff _ _ zero_norm (hwf.assetsMaximum_norm m hm), Number.toRat_zero]
      exact he.assetsMaximum_pos m.toRat (Option.mem_map_of_mem _ hm)
    · -- empty_shares
      intro hsz
      have hsh : rv.toExact.sharesTotal = 0 := by
        show rv.sharesTotal.toRat.num.toNat = 0
        rw [hsz, Number.toRat_zero]; rfl
      obtain ⟨hT, hA⟩ := he.empty_shares hsh
      exact ⟨(toRat_eq_zero_iff_eq_zero hwf.assetsTotal_norm).mp hT,
             (toRat_eq_zero_iff_eq_zero hwf.assetsAvailable_norm).mp hA⟩
    · -- cap
      intro m hm
      rw [operator_le_iff _ _ hwf.assetsTotal_norm (hwf.assetsMaximum_norm m hm)]
      exact he.cap m.toRat (Option.mem_map_of_mem _ hm)
    · rw [operator_le_iff _ _ zero_norm hwf.lossUnrealized_norm, Number.toRat_zero]
      exact he.lossUnrealized_nonneg
    · -- lossUnrealized_le (backward): ∀ d, sub = .ok d → loss.operator_le d
      intro d hsub
      have hLnn : 0 ≤ rv.lossUnrealized.toRat := he.lossUnrealized_nonneg
      have hLle : rv.lossUnrealized.toRat ≤ rv.assetsTotal.toRat - rv.assetsAvailable.toRat := by
        have h := he.lossUnrealized_le
        change rv.lossUnrealized.toRat ≤ rv.assetsTotal.toRat - rv.assetsAvailable.toRat at h
        exact h
      have hAle : rv.assetsAvailable.toRat ≤ rv.assetsTotal.toRat := he.assetsAvailable_le
      by_cases hd : d.mantissa_ = 0
      · -- flush corner: the exact difference is sub-grid, so `loss` and `d` are both zero
        have hTneg : rv.assetsTotal.negative_ = false :=
          neg_false_of_nonneg _ hwf.assetsTotal_norm he.assetsTotal_nonneg
        have hAneg : rv.assetsAvailable.negative_ = false :=
          neg_false_of_nonneg _ hwf.assetsAvailable_norm he.assetsAvailable_nonneg
        obtain ⟨hdz, hsmall⟩ := sub_downward_mantissa_zero rv.assetsTotal rv.assetsAvailable d
          hwf.assetsTotal_norm hwf.assetsAvailable_norm hTneg hAneg hsub hd
        have hlt_spr : rv.assetsTotal.toRat - rv.assetsAvailable.toRat
            < (10 : ℚ) ^ (18 : ℕ) * (10 : ℚ) ^ (minExponent : ℤ) := by
          rwa [abs_of_nonneg (by linarith : (0:ℚ) ≤ rv.assetsTotal.toRat - rv.assetsAvailable.toRat)]
            at hsmall
        have hlossz : rv.lossUnrealized.toRat = 0 := by
          by_contra hne
          have hge := Number.abs_toRat_ge_spr rv.lossUnrealized hwf.lossUnrealized_norm
            (fun h => hne (Number.toRat_eq_zero_of_mantissa_zero _ h))
          rw [abs_of_nonneg hLnn] at hge
          linarith
        rw [(toRat_eq_zero_iff_eq_zero hwf.lossUnrealized_norm).mp hlossz, hdz]; decide
      · have hdn := sub_downward_result_norm rv.assetsTotal rv.assetsAvailable d
          hwf.assetsTotal_norm hwf.assetsAvailable_norm hsub hd
        rw [operator_le_iff _ _ hwf.lossUnrealized_norm hdn]
        exact sub_downward_grid_max_ne rv.assetsTotal rv.assetsAvailable d rv.lossUnrealized
          hwf.assetsTotal_norm hwf.assetsAvailable_norm hwf.lossUnrealized_norm hsub hd hLle
    · rw [operator_le_iff _ _ hwf.lossUnrealized_norm hwf.assetsTotal_norm]
      have h := he.withdraw_nav_nonneg
      change (0 : ℚ) ≤ rv.assetsTotal.toRat - rv.lossUnrealized.toRat at h
      linarith

/-- The exact-rational invariant of a lawful vault, derived from its operator
proof and well-formedness. -/
def Vault.exact (v : Vault) : v.toExact.Valid :=
  (RawVault.valid_iff_exact v.toRawVault v.wf).mp v.valid

/-- Bridge: when the ops' in-op re-validation succeeds (`to_lawful = .ok v`), the
packaged vault is the raw state it validated, and that state is well-formed and
valid. -/
theorem RawVault.to_lawful_ok {rv : RawVault} {v : Vault}
    (h : rv.to_lawful = .ok v) : v.toRawVault = rv ∧ rv.WF ∧ rv.Valid := by
  unfold RawVault.to_lawful at h
  split at h
  · rename_i hcond; injection h with h'; exact ⟨by rw [← h'], hcond.1, hcond.2⟩
  · exact absurd h (by simp)

/-- Bridge: a well-formed, valid raw state re-validates. Shows the ops' `to_lawful`
re-check fires the `.ok` branch (never `throw .notLawful`). -/
theorem RawVault.to_lawful_ok_of {rv : RawVault} (hwf : rv.WF) (hvalid : rv.Valid) :
    ∃ v, rv.to_lawful = .ok v ∧ v.toRawVault = rv := by
  refine ⟨⟨rv, hwf, hvalid⟩, ?_, rfl⟩
  unfold RawVault.to_lawful; rw [dif_pos ⟨hwf, hvalid⟩]

end XRPL.Model.SingleAssetVault
