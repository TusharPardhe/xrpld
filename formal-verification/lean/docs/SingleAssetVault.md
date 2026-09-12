# Formal Verification of Single Asset Vault

## Modeling Philosophy

When modeling the Single Asset Vault in Lean 4, the goal was to capture the feature's core business logic and to clearly separate its essential concerns from peripheral implementation details.

The core business logic of the vault is to accept deposits of an asset, issue proportional vault shares, and allow share-holders to redeem their shares for the corresponding portion of the vault's assets. Additionally, the vault needs to support issuer-initiated clawback of the asset that it holds, as well as the ability to burn shares.

We have, in large part, considered every other concern peripheral to the vault. This includes, but is not limited to:

- the properties of the depositors and withdrawers, such as what their accounts look like or whether they are permitted to interact with the assets,
- the properties of the asset in the vault, such as who the issuer is, or whether it is frozen,
- how the asset is stored, the mechanisms of delivering value from accounts to assets and vice versa, or how users interact with the ledger,
- propagation of errors back to the transactor,
- the consensus mechanisms of XRPL, which transactions need to interact with the Vault, or even which other protocols will interact with the Vault.

The main objective when modeling was to establish a clear contract for the Vault, such that any consumer of it can abstract away reading and writing from storage, permissions, transaction parsing, or any other concern, and work against a simple, easy Vault API.
If tomorrow a new KYC feature is added to the ledger, or the Permissioned Domains are completely refactored, or freezing features are abstracted into a single module, the Vault API should not change.

While our Lean 4 design departs somewhat from the structure established in `xrpld`, we have kept exactly the same behavior, so that the Lean 4 Vault could be thought of as a drop-in replacement for the `xrpld` implementation.

## Modeling Challenges

During modeling and proving the Vault, we encountered several challenges when trying to keep the separation clear.

### Number and STAmount

XRPL, as well as the Vault, depends heavily on the `Number` and `STAmount` types, as well as on concrete asset implementations for IOU, MPT and XRP.
In principle, there is no reason why the Vault could not be extended to support any number representation. For example, outstanding shares could be represented using ℕ. We could have designed it abstractly to accept the number representation as input and output, but we found that to be overengineering at this point, which would have made both the model and the proofs much harder to read.
Using `STAmount` as input, and primarily `Number` as output, we have embedded their rounding rules and precision behaviors as part of the Vault's API.

This presents a challenge. The way the `xrpld` code is currently structured is to:

1. call Vault helpers that calculate the exchange rate and round it,
2. use the calculated values in `accountSend` to send the assets between the Vault's pseudoaccount and the holder's account,
3. use `associateAsset`, which both associates the asset and rounds it.

Since the Vault's concerns end at the first step, we could not assume that `accountSend` and `associateAsset` would not round the output of the Vault, essentially changing its output and potentially modifying `assetsTotal`, `assetsAvailable` and the pseudoaccount by different values.

We have attempted to provide the guarantee that any output of the Vault is exactly representable in `STAmount`, so that `accountSend` and `associateAsset` would not further round the output.
However, this is not correct at this time - the Vault does not yet guarantee its outputs are exactly `STAmount`-representable.

### Asset Type

In an ideal world, the Single Asset Vault would only need to know the mathematical properties of the asset that it holds.
This could be a floating-point decimal number, an unsigned integer, or `ℝ`. We have branded this `NumericType`, to point out the difference between an asset and its representation.

When it comes to XRPL, there are, broadly speaking, two types of assets: integral (representing XRP and MPT) and floating-point (IOUs). Our initial aim was to represent only those two types.
However, a lot of the arithmetic flows like `STAmount -> Number -> STAmount`, and casting a `Number` to an `STAmount` requires knowledge of not only whether the number is integral, but also the maximum value that it can store. If we lost that information, we would stop storing the final result the same way `xrpld` does, and we would potentially lose precision.
This might be a solvable problem, but for now we are still keeping the information about MPT vs XRP.

Due to this philosophy, we have decided not to care about the asset type in some other situations; for example, we have not modeled the check for whether we can hold the asset (the `tecWRONG_ASSET` preclaim check).
A natural model would be to have a function such as `Vault.canHoldAsset`, but for now we leave this compatibility check to the caller. Modeling the lending protocol might be a good time to reconsider this decision.

Another boundary is, for example, the `MaximumAmount` of the share issuance. We have decided not to model this, as the maximum amount an MPT can store is really a peripheral concern that the caller should check. If tomorrow `xrpld` increases this limit, the Vault does not need changing.

### Propagation of Errors

Every transaction returns either a success or an error. Currently, the codebase is structured so that errors returned by a helper are usually propagated back to the transactor.
To preserve this behavior, we had to tightly couple the Vault to the error codes.
In one solution, the Vault could return its own error representation, but defining this would clutter the API with its own set of error codes. An alternative would be to completely eliminate early returns from the Vault codebase, which would be ideal, but would still require a wrapper around the code that somehow translates the different conditions into errors. We have opted to keep early returns in the Vault implementation for simplicity and rely on the calling function to propagate the error.

### Holder Balances

Another important boundary we set is that the Vault does not know how many shares each holder has. Imagine a real-world scenario: a vault is an office with a teller. You come to the teller and ask to deposit some money, and the teller gives you a receipt for your number of shares. A few days later, you come back and give the teller your share certificate. The teller trusts the certificate and does not check it against their own ledger. They will only raise an eyebrow if you try to redeem more shares than the vault actually issued.

## Model

With all of that being said, the Single Asset Vault in Lean 4 still resembles the C++ implementation. The code is in the [Vault directory](../XRPL/Model/Vault). The files are:

`Vault.lean` holds the structure that describes the Vault state. This state is expected to be loaded by the caller.

```lean4
structure RawVault where
  assetsTotal : Number
  assetsAvailable : Number
  assetsReserved : Number
  assetsMaximum : Option Number
  numericType : NumericType
  scale : UInt8
  sharesTotal : Number
  lossUnrealized : Number
```

There are two types of functions that are implemented over `Vault`:

- Checks and helpers, such as `Vault.canVaultDelete` or `Vault.roundedDepositAmount` (which the `VaultDeposit` preclaim should use to obtain the rounded amount and check whether it will cause a precision loss). These functions are mostly used in preclaim checks, where verifying input against the state of the Vault is needed.
- Calculations, such as `Vault.deposit` or `Vault.withdraw`, which take the current `Vault` state and the intended input (such as the deposit amount), and return either an error, or a success with the new `Vault` state and potentially a delta of changes to key values.

Functions over the `Vault` structure should be considered public API, while free functions are private API. We have not used visibility modifiers, as we need universally public functions for theorems and proofs.

One notable discrepancy from `xrpld` is that we have split clawback functionality into clawback of assets and burning of shares, seeing them as separate concerns.

Also, we have modeled Vault creation. While this is in principle only a storage concern, it made it easier to reason about what the empty Vault looks like in theorems and proofs.

## Lawful Model

The [Vault properties](../XRPL/Properties/Vault) hold theorems about the Vault. Most notably, the properties introduce the idea of a **lawful** Vault. A lawful Vault is one that is both well-formed and, when represented in rational numbers, valid:

```lean4
structure RawVault.WF (v : RawVault) : Prop where
  assetsTotal_norm : v.assetsTotal.isNormalized
  assetsAvailable_norm : v.assetsAvailable.isNormalized
  assetsMaximum_norm : ∀ m ∈ v.assetsMaximum, m.isNormalized
  sharesTotal_norm : v.sharesTotal.isNormalized
  lossUnrealized_norm : v.lossUnrealized.isNormalized
  sharesTotal_nonneg : 0 ≤ v.sharesTotal.toRat
  sharesTotal_int : v.sharesTotal.toRat.den = 1
  scale_integral : v.numericType.isIntegral = true → v.scale = 0
  scale_le : v.scale.toNat ≤ 18
  assetsTotal_sub_ok : ∃ d, v.assetsTotal.operator_sub v.assetsAvailable .downward = .ok d

-- Exact means it's represented in toRat
structure RawVault.Exact.Valid (s : RawVault.Exact) : Prop where
  assetsTotal_nonneg : 0 ≤ s.assetsTotal
  assetsAvailable_nonneg : 0 ≤ s.assetsAvailable
  assetsAvailable_le : s.assetsAvailable ≤ s.assetsTotal
  assetsMaximum_pos : ∀ m ∈ s.assetsMaximum, 0 < m
  empty_shares : s.sharesTotal = 0 → s.assetsTotal = 0 ∧ s.assetsAvailable = 0
  cap : ∀ m ∈ s.assetsMaximum, s.assetsTotal ≤ m
  lossUnrealized_nonneg : 0 ≤ s.lossUnrealized
  lossUnrealized_le : s.lossUnrealized ≤ s.assetsTotal - s.assetsAvailable
  withdraw_nav_nonneg : 0 ≤ s.assetsTotal - s.lossUnrealized
```

In `Reachable.lean`, `Reachable` is a predicate on lawful vaults, and each operation carries a `Vault` to a `Vault`, so every state reachable from creation is lawful by construction.

The reason we have separated the lawfulness of the Vault from the `RawVault` structure (which may hold even an unlawful vault) is twofold:

1. to allow us to reason about an unlawful Vault as well,
2. to make it easier to change the rules of the Vault without changing the code that uses it.

For example, a new amendment may change what a lawful vault is, but it does not have to change the underlying representation of it.

## Theorems

We prove theorems for each of the operations:

- Burn
- Clawback
- Create
- Delete
- Deposit
- Set
- Withdraw

For some of these, namely Create, Delete and Set, we only provide constructor or helper functions: Delete and Set check whether a Vault can be modified or deleted when it is in a particular state, and Create builds the empty lawful vault.
For others, we provide two types of theorems:

- Vault accuracy theorems, which characterize arithmetic properties of the Vault.
- Return theorems, which characterize the return values of the functions.

Theorems suffixed `_attained` are witnesses: each exhibits a concrete run showing the corresponding bound is tight and cannot be tightened further.

Some theorems depend on unrealized loss being 0 - this is something that we will need to revisit and tighten when we implement the Lending Protocol, before we make an assumption on how they will be changed. For example, a hugely different scale to `assetsTotal` may cause a change in some theorems, but that scale discrepancy can only be triggered by the Lending Protocol.

Some theorems here are proven, but need to be tightened as the bugs are fixed, namely the dilution theorems - we should aim to have no dilution.

### Vault Theorems

| File                 | Theorem                                                           | Description                                                                                                                                                                                                                                                                                                      | Status         |
| -------------------- | ----------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------- |
| `Reachable.lean`     | `Vault.Reachable.asset_parity`                                    | every reachable vault has available assets equal to total assets                                                                                                                                                                                                                                                 | Proven         |
|                      | `Vault.Reachable.lossUnrealized_zero`                             | every reachable vault has zero unrealized loss                                                                                                                                                                                                                                                                   | Proven         |
| `Preservation.lean`  | `Vault.{deposit,withdraw,clawback,burnShares}_poststate_lawful`   | each operation's resulting state re-validates as a lawful vault via the `to_lawful` re-check, so every operation preserves lawfulness                                                                                                                                                                            | Proven         |
|                      | `Vault.withdraw_final_poststate_lawful`                           | the final withdrawal zeroes all stored fields, and the all-zero result re-validates like a freshly created vault                                                                                                                                                                                                 | Proven         |
| `Vault.lean`         | `Vault.isInsolvent_iff`                                           | on a lawful vault, `isInsolvent` is true exactly when `assetsTotal` is zero and `sharesTotal` is positive                                                                                                                                                                                                        | Proven         |
| `VaultDeposit.lean`  | `Vault.roundedDepositAmount_bounds` + `_truncation_attained`      | the rounded amount is the requested amount rounded down to the vault's stored precision, and is nonzero; witness: a requested amount that is strictly rounded down                                                                                                                                               | Proven         |
|                      | `Vault.roundedDepositAmount_integral`                             | for an integral asset, rounding leaves the requested amount unchanged                                                                                                                                                                                                                                            | Proven         |
|                      | `Vault.deposit_donation`                                          | a donation adds the amount to the vault but issues zero shares                                                                                                                                                                                                                                                   | Proven         |
|                      | `Vault.idealSharesDeposit_initial_rate`                           | when shares equal the net asset value times 10^scale, a deposit's ideal shares equal the deposited amount times 10^scale                                                                                                                                                                                         | Proven         |
|                      | `Vault.deposit_shares_monotone`                                   | depositing more never yields fewer shares                                                                                                                                                                                                                                                                        | Proven         |
|                      | `Vault.deposit_sharesIssued` + `_attained`                        | the shares issued match the ideal proportional amount, short by less than one share plus a small relative rounding error; witness: a run where the error reaches the bound                                                                                                                                       | Proven         |
|                      | `Vault.deposit_charge` + `_attained`                              | the amount taken is at most the requested amount and at least the value of the issued shares, above that value by at most a small relative rounding error plus 2 ULP; if the amount taken is zero, the ideal value was below the smallest representable amount; witness: a run where the error reaches the bound | Proven         |
|                      | `Vault.deposit_charge_integral`                                   | for an integral asset, the amount taken exceeds the value of the issued shares by less than one whole unit                                                                                                                                                                                                       | Proven         |
|                      | `Vault.deposit_vault_updates` + `_attained`                       | the stored total and available assets each increase by the amount taken, up to a small rounding error; the share total increases exactly; witness: a run where the stored total differs from the exact sum                                                                                                       | Proven         |
|                      | `Vault.deposit_vault_updates_integral`                            | for an integral asset, the stored totals increase by exactly the amount taken                                                                                                                                                                                                                                    | Proven         |
|                      | `Vault.deposit_under_maximum`                                     | if the requested amount keeps the total at or below the maximum, the deposit is not rejected with `tecLIMIT_EXCEEDED`                                                                                                                                                                                            | Proven         |
| `VaultWithdraw.lean` | `Vault.sharesToAssetsWithdraw_bounds` + `_attained`               | the assets priced for the burned shares match the ideal proportional value within the bound, never exceeding it; witness: a run where the error reaches the bound                                                                                                                                                | Proven         |
|                      | `Vault.sharesToAssetsWithdraw_total`                              | expresses the payout's total rounding error as the sum of the two pricing stages' errors                                                                                                                                                                                                                         | Proven         |
|                      | `Vault.withdraw_sharesBurned_exact`                               | when withdrawing by shares, exactly the requested shares are burned                                                                                                                                                                                                                                              | Proven         |
|                      | `Vault.withdraw_sharesBurned` + `_attained`                       | when withdrawing by assets, the shares burned match the ideal proportional amount within the bound; witness: a run where the error reaches the bound                                                                                                                                                             | Proven         |
|                      | `Vault.withdraw_payout` + `_attained`                             | the assets paid out match the ideal proportional value of the burned shares within the bound, never exceeding it; witness: a run where the error reaches the bound                                                                                                                                               | Proven         |
|                      | `Vault.withdraw_payout_integral`                                  | for an integral asset, the payout falls short of the ideal by less than one whole unit                                                                                                                                                                                                                           | Proven         |
|                      | `Vault.withdraw_payout_monotone`                                  | burning more shares never pays out less                                                                                                                                                                                                                                                                          | Proven         |
|                      | `Vault.withdraw_vault_updates` + `_attained`                      | the stored total and available assets each decrease by the payout, up to a small rounding error; the share total decreases exactly; witness: a run where the stored total differs from the exact difference                                                                                                      | Proven         |
|                      | `Vault.withdraw_vault_updates_integral`                           | for an integral asset, the stored totals decrease by exactly the payout                                                                                                                                                                                                                                          | Proven         |
|                      | `Vault.withdraw_payout_decreases_assets`                          | a non-final withdrawal strictly lowers the stored total assets and does not increase the available assets                                                                                                                                                                                                        | Proven         |
|                      | `Vault.withdraw_under_available`                                  | the payout never exceeds the available assets                                                                                                                                                                                                                                                                    | Proven         |
|                      | `Vault.withdraw_final_iff`                                        | characterizes exactly when a withdrawal redeems the last shares and empties the vault                                                                                                                                                                                                                            | Proven         |
|                      | `Vault.withdraw_final_payout`                                     | the final withdrawal pays out all remaining assets, within the rounding bound; the lower bound applies when the available assets are nonzero                                                                                                                                                                     | Proven         |
|                      | `Vault.withdraw_can_empty`                                        | "every lawful vault can be fully emptied by redeeming all its shares" -- FALSE: interior mul/div overshoot can reject a full redemption with `tecINSUFFICIENT_FUNDS`; commented out in the code                                                                                                                  | False          |
|                      | `Vault.Reachable.canEmpty` (int64)                                | proven for `.int64` vaults. A reachable `.int64` vault within the int64 cap (`assetsTotal <= 2^63-1`, MPT max) can be emptied by a finite withdrawal sequence.                                                                                                                                                   | Proven (int64) |
| `VaultClawback.lean` | `RawVault.idealAssetsClawback_idealSharesClawback`                | converting assets to ideal shares destroyed and back to ideal assets recovered returns the original amount                                                                                                                                                                                                       | Proven         |
|                      | `Vault.clawback_sharesDestroyed` + `_attained`                    | the shares destroyed match the ideal proportional amount for the clawed assets within the bound; witness: a run where the error reaches the bound                                                                                                                                                                | Proven         |
|                      | `Vault.clawback_sharesDestroyed_clamped` + `_attained`            | when the clawed amount exceeds the available assets, the shares destroyed match the ideal for the available assets instead; witness: a run where the error reaches the bound                                                                                                                                     | Proven         |
|                      | `Vault.clawback_assetsRecovered` + `_attained`                    | the assets recovered match the ideal proportional value within the bound; if they round to zero, the ideal was below the smallest representable amount; witness: a run where the error reaches the bound                                                                                                         | Proven         |
|                      | `Vault.clawback_assetsRecovered_integral`                         | for an integral asset, the recovery falls short of the ideal by less than one whole unit                                                                                                                                                                                                                         | Proven         |
|                      | `Vault.clawback_vault_updates` + `_attained`                      | the stored total and available assets each decrease by the recovery, up to a small rounding error; the share total decreases exactly; witness: a run where the stored total differs from the exact difference                                                                                                    | Proven         |
|                      | `Vault.clawback_vault_updates_integral`                           | for an integral asset, the stored totals decrease by exactly the recovery                                                                                                                                                                                                                                        | Proven         |
| `VaultBurn.lean`     | `Vault.canBurnShares_assets_exact`                                | the burn permission check reports the vault's share total exactly                                                                                                                                                                                                                                                | Proven         |
|                      | `Vault.burnShares_sharesTotal_exact`                              | burning subtracts exactly the destroyed shares from the total                                                                                                                                                                                                                                                    | Proven         |
| `Dilution.lean`      | `Vault.deposit_no_dilution` + `Vault.deposit_dilution_attained`   | on a vault with no unrealized loss, a deposit cannot lower the per-share value by more than a small rounding error; witness: a deposit that does lower it slightly                                                                                                                                               | Proven         |
|                      | `Vault.deposit_donation_no_dilution`                              | a donation strictly increases the per-share value (integral vaults require the total to stay within the integer domain)                                                                                                                                                                                          | Proven         |
|                      | `Vault.withdraw_no_dilution` + `Vault.withdraw_dilution_attained` | on a vault with no unrealized loss, a withdrawal that burns at most half the shares cannot lower the per-share value by more than a small rounding error; witness: a withdrawal that does lower it slightly                                                                                                      | Proven         |
|                      | `Vault.clawback_no_dilution` + `Vault.clawback_dilution_attained` | on a vault with no unrealized loss, a clawback that destroys at most half the shares cannot lower the per-share value by more than a small rounding error; witness: a clawback that does lower it slightly                                                                                                       | Proven         |
|                      | `Vault.ReachableFromIn.no_dilution` + `_dilution_attained`        | starting from a lawful vault with no unrealized loss and equal total and available assets, over any sequence of margin-respecting operations the per-share value drops by at most the accumulated rounding error; witness: a sequence whose rounding error accumulates                                           | Proven         |
| `Roundtrip.lean`     | `Vault.deposit_withdraw_roundtrip` + `_attained`                  | depositing then withdrawing returns almost the original amount, losing at most the combined rounding error of the two operations (unless the payout underflows to zero); witness: a deposit-then-withdraw that loses a little                                                                                    | Proven         |

### Return Theorems

| File                       | Theorem                                             | Exit condition                                                 | Status |
| -------------------------- | --------------------------------------------------- | -------------------------------------------------------------- | ------ |
| `VaultDepositReturn.lean`  | `Vault.roundedDepositAmount_rejected_code`          | rounding rejects only with `tecPRECISION_LOSS`                 | Proven |
|                            | `Vault.deposit_rejected_request`                    | amount rejected at rounding → `tecINTERNAL`                    | Proven |
|                            | `Vault.deposit_rounded_zero`                        | amount rounds to zero → `tecINTERNAL`                          | Proven |
|                            | `Vault.deposit_donation_no_shares`                  | donation into a vault with no shares → `tecNO_PERMISSION`      | Proven |
|                            | `Vault.deposit_insolvent`                           | non-donation into an insolvent vault → `tecLOCKED`             | Proven |
|                            | `Vault.deposit_maximum_exceeded`                    | new total exceeds the maximum → `tecLIMIT_EXCEEDED`            | Proven |
|                            | `Vault.deposit_donation_maximum`                    | donation exceeds the maximum → `tecLIMIT_EXCEEDED`             | Proven |
|                            | `Vault.deposit_success`                             | all guards pass → exact updated vault and amounts              | Proven |
|                            | `Vault.deposit_donation_success`                    | donation guards pass → exact updated vault                     | Proven |
|                            | `Vault.deposit_error_codes`                         | the full set of deposit return codes                           | Proven |
| `VaultWithdrawReturn.lean` | `RawVault.sharesToAssetsWithdraw_zero_nav`          | zero net asset value → zero payout                             | Proven |
|                            | `Vault.withdraw_insufficient_funds`                 | payout exceeds available → `tecINSUFFICIENT_FUNDS`             | Proven |
|                            | `Vault.withdraw_final_nonzero_loss`                 | final withdrawal with a nonzero loss → `tefINTERNAL`           | Proven |
|                            | `Vault.withdraw_final`                              | final withdrawal, no loss → vault zeroed, pays all available   | Proven |
|                            | `Vault.withdraw_payout_too_small`                   | payout too small to move the total → `tecPRECISION_LOSS`       | Proven |
|                            | `Vault.withdraw_success`                            | all guards pass → exact updated vault and payout               | Proven |
|                            | `Vault.withdraw_error_codes`                        | the full set of withdraw return codes                          | Proven |
| `VaultClawbackReturn.lean` | `Vault.clawback_negative_amount`                    | negative amount → `tecINTERNAL`, unchanged                     | Proven |
|                            | `Vault.clawback_zero_shares`                        | destroys zero shares → `tecPRECISION_LOSS`, unchanged          | Proven |
|                            | `Vault.clawback_recovery_too_small`                 | recovery too small to move the total → `tecPRECISION_LOSS`     | Proven |
|                            | `Vault.clawback_success`                            | all guards pass → exact updated vault and recovery             | Proven |
|                            | `Vault.clawback_error_codes`                        | the full set of clawback return codes                          | Proven |
| `VaultBurnReturn.lean`     | `Vault.canBurnShares_rejected_code`                 | the only burn-check rejection is `tecNO_PERMISSION`            | Proven |
|                            | `Vault.canBurnShares_no_permission`                 | no shares, or shares with nonzero assets → `tecNO_PERMISSION`  | Proven |
|                            | `Vault.canBurnShares_ok`                            | shares present, assets zero → returns the whole share total    | Proven |
|                            | `Vault.burnShares_ok`                               | stores `sharesTotal - sharesDestroyed`                         | Proven |
| `VaultSet.lean`            | `Vault.canVaultSet_below_total`                     | new maximum below the total → `tecLIMIT_EXCEEDED`              | Proven |
|                            | `Vault.canVaultSet_success`                         | otherwise → `tesSUCCESS`                                       | Proven |
|                            | `Vault.canVaultSet_error_codes`                     | success or `tecLIMIT_EXCEEDED`                                 | Proven |
|                            | `Vault.lawful_canVaultSet_iff`                      | success ⟺ the new maximum is zero or at least the total        | Proven |
| `VaultDelete.lean`         | `Vault.lawful_canVaultDelete_iff`                   | success ⟺ the vault is empty                                   | Proven |
|                            | `Vault.canVaultDelete_error_codes`                  | success or `tecHAS_OBLIGATIONS`                                | Proven |
|                            | `Vault.canVaultDelete_has_obligations_iff`          | `tecHAS_OBLIGATIONS` ⟺ some stored field is nonzero            | Proven |
| `Unchanged.lean`           | `Vault.{deposit,withdraw,clawback}_error_unchanged` | any rejected deposit / withdrawal / clawback → vault unchanged | Proven |
