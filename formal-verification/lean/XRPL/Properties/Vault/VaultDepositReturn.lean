import XRPL.Properties.Vault.Common.DepositExits
import XRPL.Properties.Vault.Common.Preservation

/-! # `Vault.deposit` exits

One theorem per exit, each giving the exact result record. Conclusions are
about the public API, `Vault.roundedDepositAmount` and `Vault.deposit`.
Every rejection returns `DepositResult.rejected`: the vault unchanged and both
amount fields zero. The success cases return the post-state as a `Vault`
(`v'`), proving the `to_lawful` re-check succeeds via `deposit_poststate_lawful`,
so the `.notLawful` throw is unreachable. -/

namespace XRPL.Model.SingleAssetVault

open XRPL.Model.Protocol

variable (v : Vault)

/-! ## `Vault.roundedDepositAmount` -/

/-- `tecPRECISION_LOSS` is the only rejection `roundedDepositAmount` can
return. -/
theorem Vault.roundedDepositAmount_rejected_code (amountDeposit : STAmount) (ter : TER)
    (hok : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    ter = .tecPRECISION_LOSS :=
  Vault.roundedDepositAmount_rejected_code_proof v amountDeposit ter hok

/-! ## `Vault.deposit` -/

/-- An `amountDeposit` that `roundedDepositAmount` rejects makes `deposit`
fail with `tecINTERNAL`: the depositing transaction never runs on such
an amount. -/
theorem Vault.deposit_rejected_request (amountDeposit : STAmount) (isDonation : Bool)
    (ter : TER)
    (hrej : v.roundedDepositAmount amountDeposit = .ok (.rejected ter)) :
    v.deposit amountDeposit isDonation = .ok (.rejected v .tecINTERNAL) :=
  Vault.deposit_rejected_request_proof v amountDeposit isDonation ter hrej

/-- `amountDeposit` rounds to zero at the vault exponent: `tecINTERNAL`. -/
theorem Vault.deposit_rounded_zero (amountDeposit roundedAmount : STAmount) (isDonation : Bool)
    (hround : roundToVaultExponent amountDeposit v.assetsTotal = .ok roundedAmount)
    (hz : roundedAmount.isZero = true) :
    v.deposit amountDeposit isDonation = .ok (.rejected v .tecINTERNAL) :=
  Vault.deposit_rounded_zero_proof v amountDeposit roundedAmount isDonation hround hz

/-- A donation into a vault with no outstanding shares: `tecNO_PERMISSION`. -/
theorem Vault.deposit_donation_no_shares (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ = 0) :
    v.deposit amountDeposit true = .ok (.rejected v .tecNO_PERMISSION) :=
  Vault.deposit_donation_no_shares_proof v amountDeposit roundedAmount hrounded hsh

/-- A non-donation deposit into an insolvent vault: `tecLOCKED`. -/
theorem Vault.deposit_insolvent (amountDeposit roundedAmount : STAmount)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = true) :
    v.deposit amountDeposit false = .ok (.rejected v .tecLOCKED) :=
  Vault.deposit_insolvent_proof v amountDeposit roundedAmount hrounded hins

/-- The updated total after clamping the computed assets exceeds `assetsMaximum`:
`tecLIMIT_EXCEEDED`. -/
theorem Vault.deposit_maximum_exceeded
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
    v.deposit amountDeposit false = .ok (.rejected v .tecLIMIT_EXCEEDED) :=
  Vault.deposit_maximum_exceeded_proof v amountDeposit roundedAmount rawAssetDeposited assetDeposited s
    cN sN at' av' st' hrounded hins hcomp hclamp hprecision hcN hsN hat hav hst hmax

/-- A donation pushes the total above `assetsMaximum`: `tecLIMIT_EXCEEDED`. -/
theorem Vault.deposit_donation_maximum (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = true) :
    v.deposit amountDeposit true = .ok (.rejected v .tecLIMIT_EXCEEDED) :=
  Vault.deposit_donation_maximum_proof v amountDeposit roundedAmount aN zN at' av' st'
    hrounded hsh haN hzN hat hav hst hmax

/-- Every guard passes: the deposit returns the exact updated vault (still a
`Vault`), the taken `amountDeposit'`, and the issued shares. The
`to_lawful` re-check is proven to succeed via `deposit_poststate_lawful`. -/
theorem Vault.deposit_success (amountDeposit roundedAmount rawAssetDeposited c s : STAmount)
    (cN sN at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanonA : amountDeposit.Canonical) (hnnA : 0 ≤ amountDeposit.toRat)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hins : v.isInsolvent = false)
    (hcomp : computeDeposit v roundedAmount = .ok (.success rawAssetDeposited s))
    (hclamp : clampToSumExponent v.assetsTotal rawAssetDeposited = .ok c)
    (hprecision : c.isFractionalNonPositive = .ok false)
    (hcN : c.toNumber .to_nearest = .ok cN)
    (hfinal : cN.toRat = c.toRat ∧ cN.isNormalized ∧ 0 ≤ c.toRat)
    (hsN : s.toNumber .to_nearest = .ok sN)
    (hat : v.assetsTotal.operator_add cN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add cN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add sN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + s.toRat ≤ 2 ^ 63 - 1) :
    ∃ v' : Vault, v.deposit amountDeposit false = .ok ⟨none, v', c, s⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  obtain ⟨v', htl, hlv'eq⟩ := Vault.deposit_poststate_lawful v amountDeposit false hL hAV hcanonA hnnA
    roundedAmount rawAssetDeposited c s cN sN at' av' st' hround hnz
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ => ⟨hcomp, hclamp, hprecision⟩) hcN hfinal hsN hat hav hst hmax hSsz
  refine ⟨v', ?_, hlv'eq⟩
  unfold Vault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hnz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.false_and]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [hins, Bool.false_and]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_pos (by decide)]
  rw [hcomp, ok_bind]
  simp only
  rw [hclamp, ok_bind, hprecision, ok_bind]
  rw [if_neg (by decide)]
  simp only [hcN, hsN, hat, hav, hst, ok_bind]
  rw [if_neg (by rw [hmax]; exact Bool.false_ne_true), htl]
  rfl

/-- A donation with every guard passing: `roundedAmount` is taken, no shares
are issued, both asset totals grow, and the post-state is a `Vault`. -/
theorem Vault.deposit_donation_success (amountDeposit roundedAmount : STAmount)
    (aN zN at' av' st' : Number)
    (hL : v.toExact.lossUnrealized = 0)
    (hAV : v.assetsAvailable = v.assetsTotal)
    (hcanonA : amountDeposit.Canonical) (hnnA : 0 ≤ amountDeposit.toRat)
    (hrounded : v.roundedDepositAmount amountDeposit = .ok (.rounded roundedAmount))
    (hsh : v.sharesTotal.mantissa_ ≠ 0)
    (haN : roundedAmount.toNumber .to_nearest = .ok aN)
    (hzN : (STAmount.zero .int64).toNumber .to_nearest = .ok zN)
    (hat : v.assetsTotal.operator_add aN .to_nearest = .ok at')
    (hav : v.assetsAvailable.operator_add aN .to_nearest = .ok av')
    (hst : v.sharesTotal.operator_add zN .to_nearest = .ok st')
    (hmax : ((v.assetsMaximum.getD Number.zero).operator_ne Number.zero && at'.operator_gt (v.assetsMaximum.getD Number.zero)) = false)
    (hSsz : (v.toExact.sharesTotal : ℚ) + (STAmount.zero .int64).toRat ≤ 2 ^ 63 - 1) :
    ∃ v' : Vault, v.deposit amountDeposit true = .ok ⟨none, v', roundedAmount, STAmount.zero .int64⟩ ∧
      v'.toRawVault = { v.toRawVault with assetsTotal := at', assetsAvailable := av', sharesTotal := st' } := by
  obtain ⟨hround, hnz⟩ := roundedDepositAmount_rounded v amountDeposit roundedAmount hrounded
  have hfinal : aN.toRat = roundedAmount.toRat ∧ aN.isNormalized ∧ 0 ≤ roundedAmount.toRat := by
    have hroundedCanon : roundedAmount.Canonical :=
      Vault.roundedDepositAmount_canonical v amountDeposit roundedAmount hcanonA hrounded
    obtain ⟨aN0, haN0, hval0, hnorm0⟩ :=
      STAmount.toNumber_exact_canonical roundedAmount .to_nearest hroundedCanon.exactCanonical
    have haNeq : aN = aN0 := by rw [haN0] at haN; exact (Except.ok.inj haN).symm
    refine ⟨by rw [haNeq]; exact hval0, by rw [haNeq]; exact hnorm0, ?_⟩
    exact RawVault.roundToVaultExponent_nonneg amountDeposit roundedAmount v.assetsTotal hcanonA hnnA hround
  obtain ⟨v', htl, hlv'eq⟩ := Vault.deposit_poststate_lawful v amountDeposit true hL hAV hcanonA hnnA
    roundedAmount roundedAmount roundedAmount (STAmount.zero .int64) aN zN at' av' st' hround hnz
    (fun _ => hsh) (fun _ => ⟨rfl, rfl, rfl⟩) (fun h => absurd h (by decide)) haN hfinal hzN hat hav hst hmax hSsz
  refine ⟨v', ?_, hlv'eq⟩
  unfold Vault.deposit
  simp only []
  rw [hround, ok_bind, if_neg (by rw [hnz]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [Bool.true_and]; exact fun h => hsh (beq_iff_eq.mp h))]
  rw [if_neg (by rw [Bool.not_true, Bool.and_false]; exact Bool.false_ne_true)]
  simp only [pure_bind]
  rw [if_neg (by decide)]
  simp only [haN, hzN, hat, hav, hst, ok_bind]
  rw [if_neg (by rw [hmax]; exact Bool.false_ne_true), htl]
  rfl

/-- Every outcome of a deposit that runs without a throw. -/
theorem Vault.deposit_error_codes (amountDeposit : STAmount) (isDonation : Bool)
    (r : DepositResult)
    (hok : v.deposit amountDeposit isDonation = .ok r) :
    r.error = none ∨
    r.error = some .tecINTERNAL ∨
    r.error = some .tecNO_PERMISSION ∨
    r.error = some .tecLOCKED ∨
    r.error = some .tecPRECISION_LOSS ∨
    r.error = some .tecPATH_DRY ∨
    r.error = some .tecLIMIT_EXCEEDED :=
  Vault.deposit_error_codes_proof v amountDeposit isDonation r hok

end XRPL.Model.SingleAssetVault
