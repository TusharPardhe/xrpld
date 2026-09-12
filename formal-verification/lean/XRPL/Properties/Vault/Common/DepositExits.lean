import XRPL.Properties.Vault.Common.DepositReduction

/-! # Deposit exit reductions

`computeDeposit_codes` inventories every outcome of a `computeDeposit` that
runs without a throw, and `Vault.deposit_error_codes_proof` walks every exit of
`Vault.deposit` to inventory the codes a deposit can return. Both walks use
`bind_ok_peel`, `if`-elimination, and the `tryCatch` step lemmas only, keeping
the `checked`/`ofNumber` pipeline opaque. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

/-- Every outcome of a `computeDeposit` that runs without a throw: one of the
three error codes, or a success carrying the priced amounts. -/
theorem computeDeposit_codes (v : Vault) (amount : STAmount) (cres : ComputeDepositResult)
    (hok : computeDeposit v amount = .ok cres) :
    cres = .error .tecPRECISION_LOSS ∨
    cres = .error .tecINTERNAL ∨
    cres = .error .tecPATH_DRY ∨
    ∃ a s, cres = .success a s := by
  unfold computeDeposit at hok
  obtain ⟨rr, htc, hK⟩ := bind_ok_peel _ _ _ hok
  have handler_path_dry : ∀ (e : Error),
      tryCatch (Except.error e : Except Error (DoResultPR ComputeDepositResult ComputeDepositResult PUnit))
        (fun e => if isOverflow e = true then
            pure (DoResultPR.return (ComputeDepositResult.error TER.tecPATH_DRY) PUnit.unit)
          else throw e >>= fun y => pure (DoResultPR.pure y PUnit.unit)) = Except.ok rr →
      cres = ComputeDepositResult.error .tecPATH_DRY := by
    intro e htc'
    rw [tryCatch_error] at htc'
    by_cases hov : isOverflow e = true
    · rw [if_pos hov, epure] at htc'
      rw [← Except.ok.inj htc'] at hK
      have hK2 : Except.ok (ComputeDepositResult.error TER.tecPATH_DRY) = Except.ok cres := hK
      exact (Except.ok.inj hK2).symm
    · rw [if_neg hov, ethrow, err_bind] at htc'
      exact absurd htc' (by simp)
  cases hatsd : assetsToSharesDeposit v amount with
  | error e =>
    rw [hatsd, err_bind] at htc
    exact .inr (.inr (.inl (handler_path_dry e htc)))
  | ok shares =>
    simp only [hatsd, ok_bind, epure] at htc
    by_cases hz : shares.isZero = true
    · rw [if_pos hz, tryCatch_ok] at htc
      rw [← Except.ok.inj htc] at hK
      have hK2 : Except.ok (ComputeDepositResult.error TER.tecPRECISION_LOSS) = Except.ok cres := hK
      exact .inl (Except.ok.inj hK2).symm
    · rw [if_neg hz] at htc
      cases hsad : sharesToAssetsDeposit v shares with
      | error e2 =>
        rw [hsad, err_bind] at htc
        exact .inr (.inr (.inl (handler_path_dry e2 htc)))
      | ok amountDeposit' =>
        simp only [hsad, ok_bind] at htc
        cases hgt : amountDeposit'.operator_gt amount with
        | error e3 =>
          rw [hgt, err_bind] at htc
          exact .inr (.inr (.inl (handler_path_dry e3 htc)))
        | ok gtb =>
          simp only [hgt, ok_bind] at htc
          by_cases hgtb : gtb = true
          · rw [if_pos hgtb, tryCatch_ok] at htc
            rw [← Except.ok.inj htc] at hK
            have hK2 : Except.ok (ComputeDepositResult.error TER.tecINTERNAL) = Except.ok cres := hK
            exact .inr (.inl (Except.ok.inj hK2).symm)
          · rw [if_neg hgtb, tryCatch_ok] at htc
            rw [← Except.ok.inj htc] at hK
            have hK2 : Except.ok (ComputeDepositResult.success amountDeposit' shares) = Except.ok cres := hK
            exact .inr (.inr (.inr ⟨amountDeposit', shares, (Except.ok.inj hK2).symm⟩))

/-- Every outcome of a deposit that runs without a throw. -/
theorem Vault.deposit_error_codes_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecNO_PERMISSION ∨
    r.error = some .tecLOCKED ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecLIMIT_EXCEEDED := by
  unfold Vault.deposit at hok
  simp only [] at hok
  obtain ⟨amount, _, hok⟩ := bind_ok_peel _ _ _ hok
  by_cases h1 : amount.isZero = true
  · rw [if_pos h1] at hok
    injection hok with h; rw [← h]
    exact .inr (.inl rfl)
  · rw [if_neg h1] at hok
    by_cases h2 : (isDonation && v.sharesTotal.mantissa_ == 0) = true
    · rw [if_pos h2] at hok
      injection hok with h; rw [← h]
      exact .inr (.inr (.inl rfl))
    · rw [if_neg h2] at hok
      by_cases h3 : (v.isInsolvent && !isDonation) = true
      · rw [if_pos h3] at hok
        injection hok with h; rw [← h]
        exact .inr (.inr (.inr (.inl rfl)))
      · rw [if_neg h3] at hok
        simp only [pure_bind] at hok
        by_cases hd : isDonation = true
        · rw [if_neg (by simp [hd])] at hok
          obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
          obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
          by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
          · rw [if_pos hm] at hok
            injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr (.inr (.inr rfl)))))
          · rw [if_neg hm] at hok
            obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
            injection hok with h; rw [← h]
            exact .inl rfl
        · rw [if_pos (by simpa using hd)] at hok
          obtain ⟨cres, hcd, hok⟩ := bind_ok_peel _ _ _ hok
          rcases computeDeposit_codes v amount cres hcd with h5 | h5 | h5 | ⟨a, s, h5⟩
          · subst h5; injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr (.inl rfl))))
          · subst h5; injection hok with h; rw [← h]
            exact .inr (.inl rfl)
          · subst h5; injection hok with h; rw [← h]
            exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
          · subst h5
            simp only [] at hok
            obtain ⟨assetDeposited, _, hok⟩ := bind_ok_peel _ _ _ hok
            cases hprecision : assetDeposited.isFractionalNonPositive with
            | error e =>
              rw [hprecision, err_bind] at hok
              exact absurd hok (by simp)
            | ok isFractionalNonPositive =>
              simp only [hprecision, ok_bind] at hok
              by_cases hprecision' : isFractionalNonPositive = true
              · rw [if_pos hprecision'] at hok
                injection hok with h; rw [← h]
                exact .inr (.inr (.inr (.inr (.inl rfl))))
              · rw [if_neg hprecision'] at hok
                obtain ⟨n1, _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨at', _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨av', _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨n2, _, hok⟩ := bind_ok_peel _ _ _ hok
                obtain ⟨st', _, hok⟩ := bind_ok_peel _ _ _ hok
                by_cases hm : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true
                · rw [if_pos hm] at hok
                  injection hok with h; rw [← h]
                  exact .inr (.inr (.inr (.inr (.inr (.inr rfl)))))
                · rw [if_neg hm] at hok
                  obtain ⟨v', _, hok⟩ := bind_ok_peel _ _ _ hok
                  injection hok with h; rw [← h]
                  exact .inl rfl

/-- **Proof body of `roundedDepositAmount_rejected_code`.** -/
theorem Vault.roundedDepositAmount_rejected_code_proof (v : Vault) (amountDeposit : STAmount)
    (ter : TER) (hok : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS := by
  obtain ⟨ra, _, _, h⟩ := roundedDepositAmount_rejected v amountDeposit ter hok
  exact h

/-- **Proof body of `deposit_rejected_request`.** -/
theorem Vault.deposit_rejected_request_proof (v : Vault) (amountDeposit : STAmount)
    (isDonation : Bool) (ter : TER)
    (hrej : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    v.deposit amountDeposit isDonation = .ok (.rejected v .tecINTERNAL) := by
  obtain ⟨ra, hround, hz, _⟩ := roundedDepositAmount_rejected v amountDeposit ter hrej
  unfold Vault.deposit
  simp only []
  rw [hround, ok_bind, if_pos hz]
  rfl

/-- **Proof body of `deposit_rounded_zero`.** -/
theorem Vault.deposit_rounded_zero_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (isDonation : Bool)
    (hround : roundToVaultExponent amountDeposit v.assetsTotal = .ok roundedAmount)
    (hz : roundedAmount.isZero = true) :
    v.deposit amountDeposit isDonation = .ok (.rejected v .tecINTERNAL) := by
  unfold Vault.deposit
  simp only []
  rw [hround, ok_bind, if_pos hz]
  rfl

/-- **Proof body of `deposit_donation_no_shares`.** -/
theorem Vault.deposit_donation_no_shares_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ = 0) :
    v.deposit amountDeposit true = .ok (.rejected v .tecNO_PERMISSION) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_pos (by rw [Bool.true_and]; exact beq_iff_eq.mpr hsh)]
  rfl

/-- **Proof body of `deposit_insolvent`.** -/
theorem Vault.deposit_insolvent_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = true) :
    v.deposit amountDeposit false = .ok (.rejected v .tecLOCKED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_pos (by rw [hins]; rfl)]
  rfl

/-- **Proof body of `deposit_maximum_exceeded`.

For a non-donation, `computeDeposit` produces the raw asset amount.  The
implementation clamps that amount and accepts its precision before converting
and adding the final asset, so the update and maximum hypotheses intentionally
refer to `assetDeposited`, not `rawAssetDeposited`. -/
theorem Vault.deposit_maximum_exceeded_proof (v : Vault)
    (amountDeposit roundedAmount rawAssetDeposited assetDeposited s : STAmount)
    (cN sN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success rawAssetDeposited s))
    (hclamp : clampToSumExponent v.assetsTotal rawAssetDeposited = .ok assetDeposited)
    (hprecision : assetDeposited.isFractionalNonPositive = .ok false)
    (hcN : assetDeposited.toNumber .to_nearest = .ok cN)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero &&
      at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) :
    v.deposit amountDeposit false = .ok (.rejected v .tecLIMIT_EXCEEDED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [hins, Bool.false_and]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_pos (by simp)]
  simp only [hcomp, ok_bind]
  rw [hclamp, ok_bind, hprecision, ok_bind]
  rw [if_neg Bool.false_ne_true]
  simp only [hcN, hsN, hat, hav, hst, ok_bind]
  rw [if_pos hmax]
  rfl

/-- **Proof body of `deposit_donation_maximum`.** -/
theorem Vault.deposit_donation_maximum_proof (v : Vault) (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) :
    v.deposit amountDeposit true = .ok (.rejected v .tecLIMIT_EXCEEDED) := by
  obtain ⟨hround, hz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  unfold Vault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.true_and]; exact fun h => hsh (beq_iff_eq.mp h))]
  rw [if_neg (by rw [Bool.not_true, Bool.and_false]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_neg (by simp)]
  simp only [haN, hzN, hat, hav, hst, ok_bind]
  rw [if_pos hmax]
  rfl

end XRPL.Model.SingleAssetVault
