import XRPL.Properties.Vault.Common.Unchanged
import XRPL.Properties.Vault.Common.LawfulSupport
import XRPL.Properties.Vault.VaultValid
import XRPL.Properties.Vault.Common.DepositWiring
import XRPL.Properties.Vault.Common.ClawbackAccuracy
import XRPL.Properties.Vault.VaultBurn
import XRPL.Model.Vault.VaultDeposit
import XRPL.Model.Vault.VaultWithdraw
import XRPL.Model.Vault.VaultClawback
import XRPL.Model.Vault.VaultBurn

/-! # No operation writes `lossUnrealized`

Each operation's do-block updates only `assetsTotal`, `assetsAvailable`, and
`sharesTotal` on success, and returns the starting vault on rejection, so
`lossUnrealized` is unchanged in `r.vault'` on every exit. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- A deposit keeps both unrealized fields at their starting values. -/
theorem Vault.deposit_preserves_unrealized (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.deposit_error_unchanged_proof v amountDeposit isDonation r hok herr]
  · -- success: the reduction pins `r.vault'` to a record that keeps `lossUnrealized`
    obtain ⟨amount, rawAssetDeposited, assetDeposited, sharesCreated, cN, sN, at', av', st',
      hround, hamz, hshDonation, hinsolvent, hdonation, hcompute, hcN, hsN, hat, hav, hst,
      hmaximum, hamount, hshares, hrv⟩ :=
      Vault.deposit_success_reduces v amountDeposit isDonation r hok
        (Option.not_isSome_iff_eq_none.mp herr)
    rw [hrv]

/-- A withdrawal keeps both unrealized fields at their starting values. -/
theorem Vault.withdraw_preserves_unrealized (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool) (r : WithdrawResult)
    (hok : v.withdraw amount waiveUnrealizedLoss = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.withdraw_error_unchanged_proof v amount waiveUnrealizedLoss r hok herr]
  · -- success: both exit records keep `lossUnrealized`
    obtain ⟨cw, aN, sta, _, _, _, _, _, _, hdisj⟩ :=
      Vault.withdraw_success_reduces v amount waiveUnrealizedLoss r hok
        (Option.not_isSome_iff_eq_none.mp herr)
    rcases hdisj with ⟨hfinal, hloss, allAvailable, hallAvailable, hassets, hrv⟩ |
      ⟨hfinal, sharesBurnedNumber, assetDebitedNumber, assetsTotal', assetsAvailable', sharesTotal',
        assetDebited, assetsTotalRounded, assetsTotalRounded', hsbn, hclamp, hprecision, hdebit,
        hat, hatr, hatr', hguard, hav, hst, hassets, hrv⟩
    · rw [hrv]
    · rw [hrv]

/-- A clawback keeps both unrealized fields at their starting values. -/
theorem Vault.clawback_preserves_unrealized (v : Vault) (assets holderShares : STAmount)
    (r : ClawbackResult) (hok : v.clawback assets holderShares = .ok r) :
    r.vault'.lossUnrealized = v.lossUnrealized := by
  by_cases herr : r.error.isSome = true
  · rw [Vault.clawback_error_unchanged_proof v assets holderShares r hok herr]
  · -- success: the reduction pins `r.vault'` to a record that keeps `lossUnrealized`
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrv⟩ :=
      Vault.clawback_success_reduces v assets holderShares r hok
        (Option.not_isSome_iff_eq_none.mp herr)
    rw [hrv]

/-- `burnShares` writes only `sharesTotal`, so both unrealized fields carry
over unchanged. -/
theorem Vault.burnShares_preserves_unrealized (v : Vault) (sharesDestroyed : STAmount)
    (v' : Vault) (hok : v.burnShares sharesDestroyed = .ok v') :
    v'.lossUnrealized = v.lossUnrealized := by
  unfold Vault.burnShares at hok
  simp only [] at hok
  obtain ⟨sdn, _, hok⟩ := bind_ok_peel _ _ _ hok
  obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
  rw [(RawVault.to_lawful_ok hok).1]

/-- On a vault with no unrealized loss, the withdrawal pricing subtraction returns
exactly the net asset value, discharging the `WithdrawNavExact` hypothesis. -/
theorem Vault.withdrawNavExact_of_zero (v : Vault) (waiveUnrealizedLoss : Bool)
    (hL : v.toExact.lossUnrealized = 0) :
    v.WithdrawNavExact waiveUnrealizedLoss := by
  have hL0 : v.lossUnrealized = Number.zero := by
    have hmz : v.lossUnrealized.mantissa_ = 0 := by
      by_contra h; exact (Number.toRat_ne_zero_of_mantissa_ne_zero v.lossUnrealized h) hL
    exact Number.eq_zero_of_mantissa_zero v.lossUnrealized v.wf.lossUnrealized_norm hmz
  refine ⟨v.assetsTotal, ?_, ?_⟩
  · cases waiveUnrealizedLoss with
    | true => exact operator_sub_zero_right _ _
    | false => rw [hL0]; exact operator_sub_zero_right _ _
  · split
    · simp only [RawVault.depositNav, RawVault.toExact]
    · simp only [RawVault.withdrawNav, RawVault.toExact]
      rw [show v.lossUnrealized.toRat = 0 from hL]; ring

/-- The amount taken and the shares issued by a deposit are both nonnegative,
whether the run succeeds or is rejected (a rejection reports zero amounts). -/
theorem Vault.deposit_result_nonneg (v : Vault) (amount : STAmount) (isDonation : Bool)
    (hcanon : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (r : DepositResult) (hok : v.deposit amount isDonation = .ok r)
    (hfinal : 0 ≤ r.amountDeposit'.toRat) :
    0 ≤ r.amountDeposit'.toRat ∧ 0 ≤ r.sharesIssued.toRat := by
  by_cases herr : r.error.isSome = true
  · obtain ⟨-, haz, hsz⟩ := Vault.deposit_error_rejected_proof v amount isDonation r hok herr
    rw [haz, hsz, STAmount.zero_toRat, STAmount.zero_int64_toRat]
    exact ⟨le_refl 0, le_refl 0⟩
  · have herr' : r.error = none := Option.not_isSome_iff_eq_none.mp herr
    obtain ⟨am, rawAssetDeposited, aD, sC, cN, sN, at', av', st', hround, hamz, _hsh_don, _hins, hdon_eq, hcomp,
      _hcN, _hsN, _hat, _hav, _hst, _hmax, hamt, hshr, _⟩ :=
      Vault.deposit_success_reduces v amount isDonation r hok herr'
    rw [hamt] at hfinal ⊢
    rw [hshr]
    have hamCanon : am.Canonical := by
      rcases roundToVaultExponent_canonical_or_isZero amount am v.assetsTotal hcanon hround
        with hc | hz
      · exact hc
      · rw [hz] at hamz; exact absurd hamz (by decide)
    have ham_nn : 0 ≤ am.toRat :=
      RawVault.roundToVaultExponent_nonneg amount am v.assetsTotal hcanon hnn hround
    have ham_ne : am.mValue ≠ 0 := by unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
    have ham_pos : 0 < am.toRat :=
      lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
    by_cases hd : isDonation = true
    · obtain ⟨_, haD, hsC⟩ := hdon_eq hd
      refine ⟨?_, ?_⟩
      · exact hfinal
      · show 0 ≤ sC.toRat; rw [hsC, STAmount.zero_int64_toRat]
    · have hd' : isDonation = false := by simpa using hd
      obtain ⟨shares, hats, hshz, hsad, -, hseq⟩ :=
        computeDeposit_success_reduces v am rawAssetDeposited sC (hcomp hd').1
      obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
      have hshpos : 0 < shares.toRat :=
        assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
      refine ⟨?_, ?_⟩
      · exact hfinal
      · show 0 ≤ sC.toRat; rw [hseq]; exact le_of_lt hshpos

/-- The amount paid by a withdrawal is nonnegative, whether the run succeeds or is
rejected. On a rejection the payout is zero; on the final withdrawal it is the
`ofNumber` snap of the nonnegative `assetsAvailable`; on a partial withdrawal it is
the `sharesToAssetsWithdraw` payout of the (nonnegative canonical) burned shares. -/
theorem Vault.withdraw_assets_nonneg (v : Vault) (amount : WithdrawAmount)
    (waiveUnrealizedLoss : Bool)
    (hL : v.toExact.lossUnrealized = 0)
    (r : WithdrawResult) (hok : v.withdraw amount waiveUnrealizedLoss = .ok r)
    (hSc : r.sharesBurned.IntegralCanonical) (hSnt : r.sharesBurned.mNumericType = .int64)
    (hSnn : r.sharesBurned.negative = false)
    (hfinal : 0 ≤ r.assets'.toRat) :
    0 ≤ r.assets'.toRat :=
  hfinal

/-- **Post-state lawfulness for `deposit`.** A successful deposit's computed record
re-validates: its in-op `to_lawful` re-check returns `.ok v'`. -/
theorem Vault.deposit_poststate_lawful (v : Vault) (amount : STAmount) (isDonation : Bool)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanon : amount.Canonical) (hnn : 0 ≤ amount.toRat)
    (am rawAssetDeposited aD sC : STAmount) (cN sN at' av' st' : Number)
    (hround : roundToVaultExponent amount v.assetsTotal = .ok am)
    (hamz : am.isZero = false)
    (hsh_don : isDonation = true → v.sharesTotal.mantissa_ ≠ 0)
    (hdon_eq : isDonation = true → rawAssetDeposited = am ∧ aD = am ∧
      sC = STAmount.zero .int64)
    (hcomp : isDonation = false → computeDeposit v am = .ok (.success rawAssetDeposited sC) ∧
      clampToSumExponent v.assetsTotal rawAssetDeposited = .ok aD ∧
      aD.isFractionalNonPositive = .ok false)
    (hcN : aD.toNumber .to_nearest = .ok cN)
    (hfinal : cN.toRat = aD.toRat ∧ cN.isNormalized ∧ 0 ≤ aD.toRat)
    (hsN : sC.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + sC.toRat ≤ 2 ^ 63 - 1) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
    -- storage-canonicity and sign facts for the run's outputs: the taken amount
    -- from `roundToVaultExponent` / `sharesToAssetsDeposit`, shares from `assetsToSharesDeposit`
    have hfacts : cN.toRat = aD.toRat ∧ cN.isNormalized ∧ 0 ≤ aD.toRat ∧
        sC.IntegralCanonical ∧ 0 ≤ sC.toRat := by
      have hamCanon : am.Canonical := by
        rcases roundToVaultExponent_canonical_or_isZero amount am v.assetsTotal hcanon hround
          with hc | hz
        · exact hc
        · rw [hz] at hamz; exact absurd hamz (by decide)
      have ham_nn : 0 ≤ am.toRat :=
        RawVault.roundToVaultExponent_nonneg amount am v.assetsTotal hcanon hnn hround
      have ham_ne : am.mValue ≠ 0 := by unfold STAmount.isZero at hamz; exact ne_of_beq_false hamz
      have ham_pos : 0 < am.toRat :=
        lt_of_le_of_ne ham_nn (Ne.symm (STAmount.toRat_ne_zero am ham_ne))
      by_cases hd : isDonation = true
      · obtain ⟨_, haD, hsC⟩ := hdon_eq hd
        have hDc' : aD.ExactCanonical := by
          rw [haD]; exact STAmount.Canonical.exactCanonical am hamCanon
        obtain ⟨cN0, hcN0, hval0, hnorm0⟩ := STAmount.toNumber_exact_canonical aD .to_nearest hDc'
        have hcNeq : cN = cN0 := by rw [hcN0] at hcN; exact (Except.ok.inj hcN).symm
        exact ⟨by rw [hcNeq]; exact hval0, by rw [hcNeq]; exact hnorm0, by rw [haD]; exact ham_nn,
          by rw [hsC]; exact zero_int64_IntegralCanonical, by rw [hsC, STAmount.zero_int64_toRat]⟩
      · have hd' : isDonation = false := by simpa using hd
        obtain ⟨hcompute, hclamp, hprecision⟩ := hcomp hd'
        obtain ⟨shares, hats, hshz, hsad, -, hseq⟩ :=
          computeDeposit_success_reduces v am rawAssetDeposited sC hcompute
        obtain ⟨hshc, hshnt⟩ := assetsToSharesDeposit_int64_canonical v am shares hats
        have hshpos : 0 < shares.toRat :=
          assetsToSharesDeposit_pos v am shares hamCanon ham_pos hats hshz
        exact ⟨hfinal.1, hfinal.2.1, hfinal.2.2,
          hseq ▸ hshc, by rw [hseq]; exact le_of_lt hshpos⟩
    obtain ⟨hcN_val, hcN_norm, hDnn', hSc', hSnn'⟩ := hfacts
    have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
      RawVault.WF.toExact_sharesTotal v.toRawVault v.wf
    have hSsz' : v.sharesTotal.toRat + sC.toRat ≤ 2 ^ 63 - 1 := by
      rw [← hST]; exact hSsz
    have hST_nn : 0 ≤ v.sharesTotal.toRat := v.wf.sharesTotal_nonneg
    have hAT_nn : (0 : ℚ) ≤ v.assetsTotal.toRat := v.exact.assetsTotal_nonneg
    have hcN_nn : 0 ≤ cN.toRat := by rw [hcN_val]; exact hDnn'
    -- asset field updates
    have hat_norm : at'.isNormalized :=
      operator_add_isNormalized_to_nearest' _ _ _ v.wf.assetsTotal_norm hcN_norm hat
    have hat_nn : 0 ≤ at'.toRat :=
      operator_add_nonneg _ _ _ v.wf.assetsTotal_norm hcN_norm hat (by linarith)
    rw [hAV, hat] at hav
    have hae : at' = av' := Except.ok.inj hav
    subst hae
    -- share field update
    have hshares : st'.isNormalized ∧ 0 ≤ st'.toRat ∧ st'.toRat.den = 1 ∧ st'.toRat ≠ 0 := by
      by_cases hd : isDonation = true
      · obtain ⟨_, haD, hsC⟩ := hdon_eq hd
        have hsN_zero : sN = Number.zero := by
          rw [hsC, zero_int64_toNumber] at hsN
          exact (Except.ok.inj hsN).symm
        rw [hsN_zero, operator_add_zero_right] at hst
        have hst_eq : st' = v.sharesTotal := (Except.ok.inj hst).symm
        have hmant := hsh_don hd
        refine ⟨hst_eq ▸ v.wf.sharesTotal_norm, hst_eq ▸ hST_nn,
          hst_eq ▸ v.wf.sharesTotal_int, ?_⟩
        rw [hst_eq]
        exact Number.toRat_ne_zero_of_mantissa_ne_zero _ hmant
      · have hd' : isDonation = false := by simpa using hd
        obtain ⟨hcompute, hclamp, hprecision⟩ := hcomp hd'
        obtain ⟨shares, _, hshz, _, _, hsh_eq⟩ :=
          computeDeposit_success_reduces v am rawAssetDeposited sC hcompute
        have hsC_ne : sC.toRat ≠ 0 := by
          rw [hsh_eq]
          exact STAmount.IntegralCanonical.toRat_ne_zero_of_not_isZero shares
            (hsh_eq ▸ hSc') (hsh_eq ▸ hshz)
        have hsC_pos : 0 < sC.toRat := lt_of_le_of_ne hSnn' (Ne.symm hsC_ne)
        have hsC_den : sC.toRat.den = 1 := STAmount.IntegralCanonical.den_eq_one sC hSc'
        -- the stored magnitude is small
        have hsC_mval : ((sC.mValue.toNat : ℕ) : ℚ) = sC.toRat :=
          STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sC hSc' hSnn'
        have hsz : sC.mValue.toNat ≤ 2 ^ 63 - 1 := by
          have h1 : ((sC.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
            rw [hsC_mval]
            calc sC.toRat ≤ v.sharesTotal.toRat + sC.toRat := by linarith
              _ ≤ 2 ^ 63 - 1 := hSsz'
              _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
          exact_mod_cast h1
        obtain ⟨sN0, hsN0, hsN_val0, hsN_norm0⟩ :=
          STAmount.toNumber_integral_small_exact sC .to_nearest hSc' hsz
        have hsN_eq : sN = sN0 := by rw [hsN0] at hsN; exact (Except.ok.inj hsN).symm
        have hsN_val : sN.toRat = sC.toRat := by rw [hsN_eq]; exact hsN_val0
        have hsN_norm : sN.isNormalized := by rw [hsN_eq]; exact hsN_norm0
        have hsN_den : sN.toRat.den = 1 := by rw [hsN_val]; exact hsC_den
        have hsum_den : (v.sharesTotal.toRat + sN.toRat).den = 1 := by
          rw [rat_add_eq_num_cast _ _ v.wf.sharesTotal_int hsN_den]
          exact Rat.den_intCast _
        have hsum_nn : 0 ≤ v.sharesTotal.toRat + sN.toRat := by
          rw [hsN_val]; linarith
        have hsum_le : v.sharesTotal.toRat + sN.toRat ≤ 2 ^ 63 - 1 := by
          rw [hsN_val]; exact hSsz'
        obtain ⟨hst_val, hst_den⟩ := operator_add_exact_int v.sharesTotal sN st'
          v.wf.sharesTotal_norm hsN_norm v.wf.sharesTotal_int hsN_den
          (rat_num_natAbs_lt_of_le _ hsum_den hsum_nn hsum_le) hst
        refine ⟨operator_add_isNormalized_to_nearest' _ _ _ v.wf.sharesTotal_norm
          hsN_norm hst, by rw [hst_val]; exact hsum_nn, hst_den, ?_⟩
        rw [hst_val, hsN_val]
        have : 0 < v.sharesTotal.toRat + sC.toRat := by linarith
        exact ne_of_gt this
    obtain ⟨hst_norm, hst_nn, hst_den, hst_ne⟩ := hshares
    -- the updated record is well-formed and exactly valid, so `to_lawful` succeeds
    have hwfE : ({ v with assetsTotal := at', assetsAvailable := at', sharesTotal := st' } : RawVault).WF :=
      ⟨hat_norm, hat_norm, v.wf.assetsReserved_norm, v.wf.assetsMaximum_norm, hst_norm,
        v.wf.lossUnrealized_norm, hst_nn, hst_den,
        v.wf.scale_integral, v.wf.scale_le, Number.operator_sub_self_ok at' .downward⟩
    refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
      ⟨hat_nn, hat_nn, le_refl _, v.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩)
    · -- empty_shares: the new share total is nonzero
      intro h0
      exfalso
      have h0' : st'.toRat.num.toNat = 0 := h0
      have := rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn
      rw [h0'] at this
      exact hst_ne (by exact_mod_cast this.symm)
    · -- cap
      intro mq hm
      have hm' : mq ∈ v.assetsMaximum.map Number.toRat := hm
      rw [Option.mem_map] at hm'
      obtain ⟨n, hn, rfl⟩ := hm'
      have hn' : v.assetsMaximum = some n := hn
      rw [hn'] at hmax
      have hnpos : 0 < n.toRat :=
        v.exact.assetsMaximum_pos n.toRat (Option.mem_map.mpr ⟨n, hn, rfl⟩)
      have hne0 : n.operator_ne Number.zero = true :=
        (operator_ne_iff n Number.zero (v.wf.assetsMaximum_norm n hn) (Or.inl rfl)).mpr
          (by rw [Number.toRat_zero]; exact ne_of_gt hnpos)
      have hgt : at'.operator_gt n = false := by
        simp only [Option.getD_some, hne0, Bool.true_and] at hmax; exact hmax
      have := (operator_gt_iff at' n hat_norm (v.wf.assetsMaximum_norm n hn)).not.mp
        (by rw [hgt]; simp)
      exact le_of_not_gt (fun hc => this hc)
    · exact le_of_eq hL.symm
    · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]
      linarith
    · show 0 ≤ at'.toRat - v.lossUnrealized.toRat
      rw [show v.lossUnrealized.toRat = 0 from hL]
      linarith

/-- **Post-state lawfulness for `burnShares`.** The record with only `sharesTotal`
reduced re-validates: its in-op `to_lawful` re-check returns `.ok v'`. -/
theorem Vault.burnShares_poststate_lawful (v : Vault)
    (sharesDestroyed sharesTotalAmount : STAmount) (sdn st' : Number)
    (hcan : v.canBurnShares = .ok (.assets sharesTotalAmount))
    (hcanon : sharesDestroyed.IntegralCanonical)
    (hnn : sharesDestroyed.negative = false)
    (hle : sharesDestroyed.toRat ≤ sharesTotalAmount.toRat)
    (hfit : (v.toExact.sharesTotal : ℚ) ≤ 2 ^ 63 - 1)
    (hnum : sharesDestroyed.toNumber .to_nearest = .ok sdn)
    (hst : v.sharesTotal.operator_sub sdn .to_nearest = .ok st') :
    ∃ v' : Vault, ({ v.toRawVault with sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st' } := by
  have hwf := v.wf
  have hvalid := v.exact
  have hST : ((v.toExact.sharesTotal : ℕ) : ℚ) = v.sharesTotal.toRat :=
    RawVault.WF.toExact_sharesTotal v.toRawVault hwf
  have hsta_val : sharesTotalAmount.toRat = (v.toExact.sharesTotal : ℚ) :=
    Vault.canBurnShares_assets_exact v sharesTotalAmount hcan hfit
  have hle' : sharesDestroyed.toRat ≤ v.sharesTotal.toRat := by rw [← hST, ← hsta_val]; exact hle
  have hfit' : v.sharesTotal.toRat ≤ 2 ^ 63 - 1 := by rw [← hST]; exact hfit
  have hsd_nn : 0 ≤ sharesDestroyed.toRat := STAmount.toRat_nonneg_of sharesDestroyed hnn
  have hsd_den : sharesDestroyed.toRat.den = 1 :=
    STAmount.IntegralCanonical.den_eq_one sharesDestroyed hcanon
  -- guard components: shares outstanding, both asset totals zero
  have hguard : v.sharesTotal.mantissa_ ≠ 0 ∧ v.assetsTotal.mantissa_ = 0 ∧
      v.assetsAvailable.mantissa_ = 0 := by
    unfold Vault.canBurnShares at hcan
    simp only [] at hcan
    by_cases hg : (v.sharesTotal.mantissa_ == 0 ||
        (v.assetsTotal.mantissa_ != 0 || v.assetsAvailable.mantissa_ != 0)) = true
    · rw [if_pos hg, epure] at hcan
      exact absurd (Except.ok.inj hcan) (fun h => CanBurnSharesResult.noConfusion h)
    · rw [Bool.or_eq_true, Bool.or_eq_true] at hg
      push_neg at hg
      obtain ⟨h1, h2, h3⟩ := hg
      exact ⟨fun h => h1 (by rw [h]; rfl), by by_contra h; exact h2 (by simpa using h),
        by by_contra h; exact h3 (by simpa using h)⟩
  obtain ⟨hshares_ne, hAT_m0, hAV_m0⟩ := hguard
  have hAT0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAT_m0
  have hAV0 : v.assetsAvailable.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAV_m0
  have hLU0 : v.lossUnrealized.toRat = 0 :=
    le_antisymm (by
      have h1 := hvalid.lossUnrealized_le
      have h2 : v.toExact.assetsTotal - v.toExact.assetsAvailable = 0 := by
        show v.assetsTotal.toRat - v.assetsAvailable.toRat = 0
        rw [hAT0, hAV0]; ring
      rw [h2] at h1; exact h1) hvalid.lossUnrealized_nonneg
  have hsz : sharesDestroyed.mValue.toNat ≤ 2 ^ 63 - 1 := by
    have hmval : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) = sharesDestroyed.toRat :=
      STAmount.IntegralCanonical.mValue_eq_toRat_of_nonneg sharesDestroyed hcanon hsd_nn
    have h1 : ((sharesDestroyed.mValue.toNat : ℕ) : ℚ) ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by
      rw [hmval]
      calc sharesDestroyed.toRat ≤ v.sharesTotal.toRat := hle'
        _ ≤ 2 ^ 63 - 1 := hfit'
        _ ≤ ((2 ^ 63 - 1 : ℕ) : ℚ) := by norm_num
    exact_mod_cast h1
  obtain ⟨sdn0, hsdn0_ok, hsdn_val, hsdn_norm⟩ :=
    STAmount.toNumber_integral_small_exact sharesDestroyed .to_nearest hcanon hsz
  have hsdn_eq : sdn = sdn0 := by rw [hsdn0_ok] at hnum; exact (Except.ok.inj hnum).symm
  rw [hsdn_eq] at hst
  -- the subtraction is exact
  have hsdn_den : sdn0.toRat.den = 1 := by rw [hsdn_val]; exact hsd_den
  have hdiff_den : (v.sharesTotal.toRat - sdn0.toRat).den = 1 := by
    rw [rat_sub_eq_num_cast _ _ hwf.sharesTotal_int hsdn_den]; exact Rat.den_intCast _
  have hdiff_nn : 0 ≤ v.sharesTotal.toRat - sdn0.toRat := by rw [hsdn_val]; linarith
  have hdiff_le : v.sharesTotal.toRat - sdn0.toRat ≤ 2 ^ 63 - 1 := by rw [hsdn_val]; linarith
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal sdn0 st'
    hwf.sharesTotal_norm hsdn_norm hwf.sharesTotal_int hsdn_den
    (rat_num_natAbs_lt_of_le _ hdiff_den hdiff_nn hdiff_le) hst
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; exact hdiff_nn
  have hst_norm : st'.isNormalized :=
    operator_sub_isNormalized_to_nearest' _ _ _ hwf.sharesTotal_norm hsdn_norm hst
  have hwfE : ({ v with sharesTotal := st' } : RawVault).WF :=
    ⟨hwf.assetsTotal_norm, hwf.assetsAvailable_norm, hwf.assetsReserved_norm,
      hwf.assetsMaximum_norm, hst_norm, hwf.lossUnrealized_norm, hst_nn, hst_den,
      hwf.scale_integral, hwf.scale_le, hwf.assetsTotal_sub_ok⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨hvalid.assetsTotal_nonneg, hvalid.assetsAvailable_nonneg,
      hvalid.assetsAvailable_le, hvalid.assetsMaximum_pos, ?_, hvalid.cap, ?_, ?_, ?_⟩)
  · intro _; exact ⟨hAT0, hAV0⟩
  · exact le_of_eq hLU0.symm
  · show v.lossUnrealized.toRat ≤ v.assetsTotal.toRat - v.assetsAvailable.toRat
    rw [hLU0, hAT0, hAV0]; linarith
  · show 0 ≤ v.assetsTotal.toRat - v.lossUnrealized.toRat
    rw [hLU0, hAT0]; linarith

/-- **Post-state lawfulness for a subtracting exit (withdraw non-final / clawback).**
Subtracting one payout from both asset totals and one burn from `sharesTotal`
re-validates. `hempty`: dropping to zero shares must also zero the assets. -/
theorem Vault.withdraw_poststate_lawful (v : Vault)
    (payout burned at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hp_norm : payout.isNormalized) (hp_nn : 0 ≤ payout.toRat)
    (hp_le : payout.toRat ≤ v.assetsTotal.toRat)
    (hb_norm : burned.isNormalized) (hb_nn : 0 ≤ burned.toRat)
    (hb_den : burned.toRat.den = 1) (hb_le : burned.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hat : v.assetsTotal.operator_sub payout .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_sub payout .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_sub burned .to_nearest = .ok st')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  -- new asset total: normalized, nonnegative, and at or below the starting total
  have hat_norm : at'.isNormalized :=
    operator_sub_isNormalized_to_nearest' _ _ _ v.wf.assetsTotal_norm hp_norm hat
  have hat_nn : 0 ≤ at'.toRat :=
    operator_sub_nonneg _ _ _ v.wf.assetsTotal_norm hp_norm hat (by linarith)
  have hat_le : at'.toRat ≤ v.assetsTotal.toRat := by
    by_cases hpm : payout.mantissa_ = 0
    · exact le_of_eq (congrArg Number.toRat
        (Number.operator_sub_zero_right v.assetsTotal payout at' hpm hat))
    · by_cases hAm : v.assetsTotal.mantissa_ = 0
      · exfalso
        have hA0 : v.assetsTotal.toRat = 0 := Number.toRat_eq_zero_of_mantissa_zero _ hAm
        have hp0 : payout.toRat = 0 := le_antisymm (by rw [← hA0]; exact hp_le) hp_nn
        exact Number.toRat_ne_zero_of_mantissa_ne_zero payout hpm hp0
      · exact Number.operator_sub_nonneg_le v.assetsTotal payout at' v.wf.assetsTotal_norm
          hp_norm hAm hpm v.exact.assetsTotal_nonneg hp_nn hat
  -- parity: the same payout leaves `assetsAvailable` at the total's new value
  rw [hAV, hat] at hav
  have hae : at' = av' := Except.ok.inj hav
  subst hae
  -- new share total: exact integer decrement, normalized, nonnegative
  have hdiff_den : (v.sharesTotal.toRat - burned.toRat).den = 1 := by
    rw [rat_sub_eq_num_cast _ _ v.wf.sharesTotal_int hb_den]; exact Rat.den_intCast _
  obtain ⟨hst_val, hst_den⟩ := operator_sub_exact_int v.sharesTotal burned st'
    v.wf.sharesTotal_norm hb_norm v.wf.sharesTotal_int hb_den
    (rat_num_natAbs_lt_of_le _ hdiff_den (by linarith) (by linarith)) hst
  have hst_nn : 0 ≤ st'.toRat := by rw [hst_val]; linarith
  have hst_norm : st'.isNormalized :=
    operator_sub_isNormalized_to_nearest' _ _ _ v.wf.sharesTotal_norm hb_norm hst
  -- the decremented record is well-formed and exactly valid, so `to_lawful` succeeds
  have hwfE : ({ v with assetsTotal := at', assetsAvailable := at', sharesTotal := st' } : RawVault).WF :=
    ⟨hat_norm, hat_norm, v.wf.assetsReserved_norm, v.wf.assetsMaximum_norm, hst_norm,
      v.wf.lossUnrealized_norm, hst_nn, hst_den,
      v.wf.scale_integral, v.wf.scale_le, Number.operator_sub_self_ok at' .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact _ hwfE).mpr
    ⟨hat_nn, hat_nn, le_refl _, v.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩)
  · -- empty_shares: a zero new share total forces zero assets
    intro h0
    have h0' : st'.toRat.num.toNat = 0 := h0
    have hcast := rat_toNat_cast_of_den_one st'.toRat hst_den hst_nn
    rw [h0'] at hcast
    have hst0 : st'.toRat = 0 := by exact_mod_cast hcast.symm
    have hat0 := hempty hst0
    exact ⟨hat0, hat0⟩
  · -- cap: the new total is at or below the starting total, which respects the cap
    intro m hm
    exact le_trans hat_le (v.exact.cap m hm)
  · exact le_of_eq hL.symm
  · show v.lossUnrealized.toRat ≤ at'.toRat - at'.toRat
    rw [show v.lossUnrealized.toRat = 0 from hL]; linarith
  · show 0 ≤ at'.toRat - v.lossUnrealized.toRat
    rw [show v.lossUnrealized.toRat = 0 from hL]; linarith

/-- **Post-state lawfulness for the final withdrawal.** The all-zero record (both
asset totals and `sharesTotal` zeroed) re-validates like a freshly created vault. -/
theorem Vault.withdraw_final_poststate_lawful (v : Vault)
    (hL : v.toExact.lossUnrealized = 0) :
    ∃ v' : Vault,
      ({ v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } := by
  set w : RawVault := { v with assetsTotal := Number.zero, assetsAvailable := Number.zero, sharesTotal := Number.zero } with hw_def
  have hz : Number.zero.isNormalized := Or.inl rfl
  -- the exact projections of the zeroed record (loss carries over from `v`)
  have hAT : w.toExact.assetsTotal = 0 := by simp only [hw_def, RawVault.toExact, Number.toRat_zero]
  have hAV0 : w.toExact.assetsAvailable = 0 := by simp only [hw_def, RawVault.toExact, Number.toRat_zero]
  have hST : w.toExact.sharesTotal = 0 := by
    simp only [hw_def, RawVault.toExact, Number.toRat_zero, Rat.num_zero, Int.toNat_zero]
  have hLU : w.toExact.lossUnrealized = 0 := hL
  have hwfE : w.WF :=
    ⟨hz, hz, v.wf.assetsReserved_norm, v.wf.assetsMaximum_norm, hz, v.wf.lossUnrealized_norm,
      by simp only [hw_def, Number.toRat_zero, le_refl],
      by simp only [hw_def, Number.toRat_zero]; rfl,
      v.wf.scale_integral, v.wf.scale_le, Number.operator_sub_self_ok Number.zero .downward⟩
  refine RawVault.to_lawful_ok_of hwfE ((RawVault.valid_iff_exact w hwfE).mpr ?_)
  refine ⟨?_, ?_, ?_, v.exact.assetsMaximum_pos, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAT]
  · rw [hAV0]
  · rw [hAV0, hAT]
  · rw [hST, hAT, hAV0]; intro _; exact ⟨rfl, rfl⟩
  · intro m hm; rw [hAT]; exact le_of_lt (v.exact.assetsMaximum_pos m hm)
  · rw [hLU]
  · rw [hLU, hAT, hAV0]; norm_num
  · rw [hAT, hLU]; norm_num

/-- **Post-state lawfulness for `clawback`.** Delegates to the subtracting-exit
assembly. `hempty`: a recovery that empties the shares must also empty the assets. -/
theorem Vault.clawback_poststate_lawful (v : Vault)
    (assetsRecoveredNumber sharesDestroyedNumber at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hr_norm : assetsRecoveredNumber.isNormalized) (hr_nn : 0 ≤ assetsRecoveredNumber.toRat)
    (hr_le : assetsRecoveredNumber.toRat ≤ v.assetsTotal.toRat)
    (hd_norm : sharesDestroyedNumber.isNormalized) (hd_nn : 0 ≤ sharesDestroyedNumber.toRat)
    (hd_den : sharesDestroyedNumber.toRat.den = 1)
    (hd_le : sharesDestroyedNumber.toRat ≤ v.sharesTotal.toRat)
    (hfit : v.sharesTotal.toRat ≤ 2 ^ 63 - 1)
    (hat : v.assetsTotal.operator_sub assetsRecoveredNumber .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_sub assetsRecoveredNumber .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_sub sharesDestroyedNumber .to_nearest = .ok st')
    (hempty : st'.toRat = 0 → at'.toRat = 0) :
    ∃ v' : Vault,
      ({ v.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } : RawVault).to_lawful = .ok v' ∧
      v'.toRawVault = { v.toRawVault with sharesTotal := st', assetsAvailable := av', assetsTotal := at' } :=
  v.withdraw_poststate_lawful assetsRecoveredNumber sharesDestroyedNumber at' av' st'
    hL hAV hr_norm hr_nn hr_le hd_norm hd_nn hd_den hd_le hfit hat hav hst hempty

end XRPL.Model.SingleAssetVault
