use std::sync::Arc;

use basics::{
    base_uint::Uint256,
    number::{NumberParts as RuntimeNumber, RoundingMode},
};
use ledger::{has_expired, views::apply_view::ApplyView};
use protocol::{AccountID, Asset, STLedgerEntry, STTx, TenthBips16, TenthBips32, Ter, feature_id};

use super::common::*;
use super::helpers::*;

pub(super) struct LpLoanView {
    broker_id: Uint256,
    scale: i32,
    impaired: bool,
    _asset: Asset,
}

impl LpLoanView {
    fn from_sle(sle: &STLedgerEntry, asset: Asset) -> Self {
        Self {
            broker_id: sle.get_field_h256(sf("sfLoanBrokerID")),
            scale: if sle.is_field_present(sf("sfLoanScale")) {
                sle.get_field_i32(sf("sfLoanScale"))
            } else {
                0
            },
            impaired: (sle.get_field_u32(sf("sfFlags")) & protocol::lsfLoanImpaired) != 0,
            _asset: asset,
        }
    }
}

impl tx::LoanPayDoApplyLoan for LpLoanView {
    type BrokerId = Uint256;
    type Asset = Asset;
    fn broker_id(&self) -> &Uint256 {
        &self.broker_id
    }
    fn scale(&self) -> i32 {
        self.scale
    }
    fn is_impaired(&self) -> bool {
        self.impaired
    }
    fn associate_asset(&mut self, _asset: &Asset) { /* tracked via self.asset */
    }
}

/// Pre-cached broker view satisfying LoanPayDoApplyBroker's reference contracts.
pub(super) struct LpBrokerView {
    owner: AccountID,
    pseudo: AccountID,
    vault_id: Uint256,
    cover_available: RuntimeNumber,
    debt_total: RuntimeNumber,
    cover_rate_minimum: u32,
    _asset: Asset,
}

impl LpBrokerView {
    fn from_sle(sle: &STLedgerEntry, asset: Asset) -> Self {
        Self {
            owner: sle.get_account_id(sf("sfOwner")),
            pseudo: sle.get_account_id(sf("sfAccount")),
            vault_id: sle.get_field_h256(sf("sfVaultID")),
            cover_available: if sle.is_field_present(sf("sfCoverAvailable")) {
                sle.get_field_number(sf("sfCoverAvailable")).value()
            } else {
                RuntimeNumber::zero()
            },
            debt_total: if sle.is_field_present(sf("sfDebtTotal")) {
                sle.get_field_number(sf("sfDebtTotal")).value()
            } else {
                RuntimeNumber::zero()
            },
            cover_rate_minimum: if sle.is_field_present(sf("sfCoverRateMinimum")) {
                sle.get_field_u32(sf("sfCoverRateMinimum"))
            } else {
                0
            },
            _asset: asset,
        }
    }
}

impl tx::LoanPayDoApplyBroker for LpBrokerView {
    type AccountId = AccountID;
    type VaultId = Uint256;
    type Amount = RuntimeNumber;
    type Asset = Asset;
    fn owner(&self) -> &AccountID {
        &self.owner
    }
    fn pseudo_account(&self) -> &AccountID {
        &self.pseudo
    }
    fn vault_id(&self) -> &Uint256 {
        &self.vault_id
    }
    fn cover_available(&self) -> &RuntimeNumber {
        &self.cover_available
    }
    fn debt_total(&self) -> &RuntimeNumber {
        &self.debt_total
    }
    fn cover_rate_minimum(&self) -> u32 {
        self.cover_rate_minimum
    }
    fn add_cover_available(&mut self, amount: RuntimeNumber) {
        self.cover_available += amount;
    }
    fn adjust_debt_total(&mut self, delta: RuntimeNumber) {
        let new_val = self.debt_total + delta;
        self.debt_total = if new_val < RuntimeNumber::zero() {
            RuntimeNumber::zero()
        } else {
            new_val
        };
    }
    fn associate_asset(&mut self, _asset: &Asset) {}
}

/// Pre-cached vault view satisfying LoanPayDoApplyVault's reference contracts.
pub(super) struct LpVaultView {
    pseudo: AccountID,
    asset: Asset,
    assets_available: RuntimeNumber,
    assets_total: RuntimeNumber,
}

impl LpVaultView {
    fn from_sle(sle: &STLedgerEntry) -> Self {
        let asset = sle.get_field_issue(sf("sfAsset")).asset();
        Self {
            pseudo: sle.get_account_id(sf("sfAccount")),
            asset,
            assets_available: if sle.is_field_present(sf("sfAssetsAvailable")) {
                sle.get_field_number(sf("sfAssetsAvailable")).value()
            } else {
                RuntimeNumber::zero()
            },
            assets_total: if sle.is_field_present(sf("sfAssetsTotal")) {
                sle.get_field_number(sf("sfAssetsTotal")).value()
            } else {
                RuntimeNumber::zero()
            },
        }
    }
}

impl tx::LoanPayDoApplyVault for LpVaultView {
    type AccountId = AccountID;
    type Asset = Asset;
    type Amount = RuntimeNumber;
    fn pseudo_account(&self) -> &AccountID {
        &self.pseudo
    }
    fn asset(&self) -> &Asset {
        &self.asset
    }
    fn assets_available(&self) -> &RuntimeNumber {
        &self.assets_available
    }
    fn assets_total(&self) -> &RuntimeNumber {
        &self.assets_total
    }
    fn add_assets_available(&mut self, amount: RuntimeNumber) {
        self.assets_available += amount;
    }
    fn add_assets_total(&mut self, amount: RuntimeNumber) {
        self.assets_total += amount;
    }
    fn assets_available_exceeds_total(&self) -> bool {
        self.assets_available > self.assets_total
    }
    fn associate_asset(&mut self, _asset: &Asset) {}
}

pub fn apply_loan_pay<V: ApplyView>(view: &mut V, sttx: &STTx) -> Ter {
    if !view
        .rules()
        .enabled(&protocol::feature_id("LendingProtocol"))
    {
        return Ter::TEM_DISABLED;
    }
    if !lending_protocol_dependencies_enabled(view, sttx) {
        return Ter::TEM_DISABLED;
    }

    let loan_id = sttx.get_field_h256(sf("sfLoanID"));
    let amount = sttx.get_field_amount(sf("sfAmount"));
    let borrower = sttx.get_account_id(sf("sfAccount"));
    let flags = sttx.get_field_u32(sf("sfFlags"));
    let preflight = tx::run_loan_pay_preflight(tx::LoanPayPreflightFacts {
        loan_id_is_zero: loan_id.is_zero(),
        amount_is_positive: amount.signum() > 0,
        tx_specific_flags: flags & protocol::LOAN_PAY_FLAGS,
    });
    if preflight != Ter::TES_SUCCESS {
        return preflight;
    }

    let payment_type = tx::run_loan_pay_payment_type(
        flags & protocol::LOAN_LATE_PAYMENT_FLAG != 0,
        flags & protocol::LOAN_FULL_PAYMENT_FLAG != 0,
        flags & protocol::LOAN_OVERPAYMENT_FLAG != 0,
    );

    // Load and cache loan
    let loan_keylet = protocol::loan_keylet_from_key(loan_id);
    let mut loan_sle = match view.peek(loan_keylet) {
        Ok(Some(sle)) => sle,
        _ => return Ter::TEC_NO_ENTRY,
    };

    if payment_type == tx::LoanPayPaymentType::Overpayment
        && !loan_sle.is_flag(protocol::lsfLoanOverpayment)
    {
        return if view.rules().enabled(&protocol::fix_cleanup_3_1_3()) {
            Ter::TEC_NO_PERMISSION
        } else {
            Ter::TEM_INVALID_FLAG
        };
    }

    // Load and cache broker
    let broker_id = loan_sle.get_field_h256(sf("sfLoanBrokerID"));
    let broker_keylet = protocol::loan_broker_keylet_from_key(broker_id);
    let broker_sle = match view.peek(broker_keylet) {
        Ok(Some(sle)) => sle,
        _ => return Ter::TEF_BAD_LEDGER,
    };

    // Load and cache vault
    let vault_id = broker_sle.get_field_h256(sf("sfVaultID"));
    let vault_keylet = protocol::vault_keylet_from_key(vault_id);
    let mut vault_sle = match view.peek(vault_keylet) {
        Ok(Some(sle)) => sle,
        _ => return Ter::TEF_BAD_LEDGER,
    };

    let vault_asset = vault_sle.get_field_issue(sf("sfAsset")).asset();
    let payment_amount = amount_number(&amount);
    if payment_amount <= RuntimeNumber::zero() {
        return Ter::TEM_BAD_AMOUNT;
    }

    // rippled runs the complete LoanManage::unimpairLoan transition before
    // computing a payment: reverse vault loss, restore the due date, and clear
    // the flag.  Reload both SLEs so the payment cannot overwrite that state
    // from stale pre-unimpair snapshots.
    if loan_sle.is_flag(protocol::lsfLoanImpaired) {
        let result = super::manage::unimpair_loan(view, &loan_sle, &vault_sle, vault_asset);
        if result != Ter::TES_SUCCESS {
            return result;
        }
        loan_sle = match view.peek(loan_keylet) {
            Ok(Some(sle)) => sle,
            _ => return Ter::TEF_BAD_LEDGER,
        };
        vault_sle = match view.peek(vault_keylet) {
            Ok(Some(sle)) => sle,
            _ => return Ter::TEF_BAD_LEDGER,
        };
    }

    let loan_view = LpLoanView::from_sle(&loan_sle, vault_asset);
    let mut broker_view = LpBrokerView::from_sle(&broker_sle, vault_asset);
    let mut vault_view = LpVaultView::from_sle(&vault_sle);
    let loan_scale = loan_view.scale;
    let v_scale = vault_scale(&vault_sle, vault_asset);

    // Read loan payment state
    let periodic_payment = if loan_sle.is_field_present(sf("sfPeriodicPayment")) {
        loan_sle.get_field_number(sf("sfPeriodicPayment")).value()
    } else {
        RuntimeNumber::zero()
    };
    let service_fee = if loan_sle.is_field_present(sf("sfLoanServiceFee")) {
        loan_sle.get_field_number(sf("sfLoanServiceFee")).value()
    } else {
        RuntimeNumber::zero()
    };
    let close_payment_fee = if loan_sle.is_field_present(sf("sfClosePaymentFee")) {
        loan_sle.get_field_number(sf("sfClosePaymentFee")).value()
    } else {
        RuntimeNumber::zero()
    };
    let late_payment_fee = if loan_sle.is_field_present(sf("sfLatePaymentFee")) {
        loan_sle.get_field_number(sf("sfLatePaymentFee")).value()
    } else {
        RuntimeNumber::zero()
    };
    let management_fee_outstanding = if loan_sle.is_field_present(sf("sfManagementFeeOutstanding"))
    {
        loan_sle
            .get_field_number(sf("sfManagementFeeOutstanding"))
            .value()
    } else {
        RuntimeNumber::zero()
    };
    let principal_outstanding = if loan_sle.is_field_present(sf("sfPrincipalOutstanding")) {
        loan_sle
            .get_field_number(sf("sfPrincipalOutstanding"))
            .value()
    } else {
        RuntimeNumber::zero()
    };
    let total_value_outstanding = if loan_sle.is_field_present(sf("sfTotalValueOutstanding")) {
        loan_sle
            .get_field_number(sf("sfTotalValueOutstanding"))
            .value()
    } else {
        RuntimeNumber::zero()
    };
    let payments_remaining = if loan_sle.is_field_present(sf("sfPaymentRemaining")) {
        loan_sle.get_field_u32(sf("sfPaymentRemaining"))
    } else {
        0
    };
    let interest_rate = if loan_sle.is_field_present(sf("sfInterestRate")) {
        TenthBips32::new(loan_sle.get_field_u32(sf("sfInterestRate")))
    } else {
        TenthBips32::new(0)
    };
    let late_interest_rate = if loan_sle.is_field_present(sf("sfLateInterestRate")) {
        TenthBips32::new(loan_sle.get_field_u32(sf("sfLateInterestRate")))
    } else {
        TenthBips32::new(0)
    };
    let close_interest_rate = if loan_sle.is_field_present(sf("sfCloseInterestRate")) {
        TenthBips32::new(loan_sle.get_field_u32(sf("sfCloseInterestRate")))
    } else {
        TenthBips32::new(0)
    };
    let overpayment_interest_rate = if loan_sle.is_field_present(sf("sfOverpaymentInterestRate")) {
        TenthBips32::new(loan_sle.get_field_u32(sf("sfOverpaymentInterestRate")))
    } else {
        TenthBips32::new(0)
    };
    let overpayment_fee_rate = if loan_sle.is_field_present(sf("sfOverpaymentFee")) {
        TenthBips32::new(loan_sle.get_field_u32(sf("sfOverpaymentFee")))
    } else {
        TenthBips32::new(0)
    };
    let payment_interval = if loan_sle.is_field_present(sf("sfPaymentInterval")) {
        loan_sle.get_field_u32(sf("sfPaymentInterval"))
    } else {
        0
    };
    let previous_payment_date = if loan_sle.is_field_present(sf("sfPreviousPaymentDueDate")) {
        loan_sle.get_field_u32(sf("sfPreviousPaymentDueDate"))
    } else {
        0
    };
    let start_date = if loan_sle.is_field_present(sf("sfStartDate")) {
        loan_sle.get_field_u32(sf("sfStartDate"))
    } else {
        0
    };
    let management_fee_rate = if broker_sle.is_field_present(sf("sfManagementFeeRate")) {
        TenthBips16::new(broker_sle.get_field_u16(sf("sfManagementFeeRate")))
    } else {
        TenthBips16::new(0)
    };

    // Compute payment parts (reference loanMakePayment logic)
    let rounded_periodic_payment = round_number_to_asset_with_scale(
        vault_asset,
        periodic_payment,
        loan_scale,
        RoundingMode::Upward,
    );
    let regular_payment = rounded_periodic_payment + service_fee;
    let effective_overpayment_amount = effective_loan_pay_amount(
        payment_type,
        view.rules().enabled(&protocol::fix_cleanup_3_1_3()),
        view.rules().enabled(&feature_id("fixCleanup3_2_0")),
        vault_asset,
        payment_amount,
        loan_scale,
    );
    let (
        principal_paid,
        interest_paid,
        management_fee_paid,
        fee_paid,
        value_change,
        payment_remaining_decrement,
        periodic_payment_override,
    ) = match payment_type {
        tx::LoanPayPaymentType::Regular => {
            if regular_payment <= RuntimeNumber::zero() {
                let p = payment_amount.min(principal_outstanding);
                (
                    p,
                    RuntimeNumber::zero(),
                    RuntimeNumber::zero(),
                    RuntimeNumber::zero(),
                    RuntimeNumber::zero(),
                    1,
                    None,
                )
            } else if payment_amount < regular_payment {
                return Ter::TEC_INSUFFICIENT_PAYMENT;
            } else {
                let parts = compute_loan_pay_scheduled_payment_loop(
                    &view.rules(),
                    vault_asset,
                    loan_scale,
                    payment_amount,
                    total_value_outstanding,
                    principal_outstanding,
                    management_fee_outstanding,
                    periodic_payment,
                    interest_rate,
                    payment_interval,
                    payments_remaining,
                    management_fee_rate,
                    service_fee,
                );
                (parts.0, parts.1, parts.2, parts.3, parts.4, parts.5, None)
            }
        }
        tx::LoanPayPaymentType::Late => {
            let next_payment_due_date = loan_sle
                .is_field_present(sf("sfNextPaymentDueDate"))
                .then(|| loan_sle.get_field_u32(sf("sfNextPaymentDueDate")));
            if !has_expired(view, next_payment_due_date) {
                return Ter::TEC_TOO_SOON;
            }
            let components = compute_loan_pay_periodic_components(
                &view.rules(),
                vault_asset,
                loan_scale,
                total_value_outstanding,
                principal_outstanding,
                management_fee_outstanding,
                periodic_payment,
                interest_rate,
                payment_interval,
                payments_remaining,
                management_fee_rate,
            );
            let late_interest = round_number_to_asset_with_scale(
                vault_asset,
                loan_late_payment_interest(
                    principal_outstanding,
                    late_interest_rate,
                    view.parent_close_time().as_seconds(),
                    next_payment_due_date.unwrap_or(0),
                ),
                loan_scale,
                RoundingMode::ToNearest,
            );
            let (late_net_interest, late_management_fee) = compute_interest_and_fee_parts(
                vault_asset,
                late_interest,
                management_fee_rate,
                loan_scale,
            );
            let tracked_due = components.principal_paid
                + components.interest_paid
                + components.management_fee_paid;
            let fee = components.management_fee_paid
                + service_fee
                + late_payment_fee
                + late_management_fee;
            let total_due = tracked_due + service_fee + late_payment_fee + late_interest;
            if payment_amount < total_due {
                return Ter::TEC_INSUFFICIENT_PAYMENT;
            }
            (
                components.principal_paid,
                components.interest_paid + late_net_interest,
                components.management_fee_paid,
                fee,
                late_net_interest,
                1,
                None,
            )
        }
        tx::LoanPayPaymentType::Full => {
            if payments_remaining <= 1 {
                return Ter::TEC_KILLED;
            }
            let outstanding_interest =
                (total_value_outstanding - principal_outstanding - management_fee_outstanding)
                    .max(RuntimeNumber::zero());
            let periodic_rate = tx::loan_set_periodic_rate(interest_rate, payment_interval);
            let (full_interest_paid, full_fee_paid, value_change) = compute_full_payment_parts(
                &view.rules(),
                vault_asset,
                loan_scale,
                view.parent_close_time().as_seconds(),
                outstanding_interest,
                periodic_payment,
                periodic_rate,
                payments_remaining,
                previous_payment_date,
                start_date,
                payment_interval,
                close_interest_rate,
                close_payment_fee,
                management_fee_rate,
            );
            let needed =
                total_value_outstanding + value_change + full_fee_paid - management_fee_outstanding;
            if payment_amount < needed {
                return Ter::TEC_INSUFFICIENT_PAYMENT;
            }
            (
                principal_outstanding,
                full_interest_paid,
                management_fee_outstanding,
                full_fee_paid,
                value_change,
                payments_remaining,
                None,
            )
        }
        tx::LoanPayPaymentType::Overpayment => {
            if regular_payment <= RuntimeNumber::zero() {
                let p = effective_overpayment_amount.min(principal_outstanding);
                (
                    p,
                    RuntimeNumber::zero(),
                    RuntimeNumber::zero(),
                    RuntimeNumber::zero(),
                    RuntimeNumber::zero(),
                    1,
                    None,
                )
            } else {
                let (
                    mut principal_paid,
                    mut interest_paid,
                    mut management_fee_paid,
                    mut fee_paid,
                    mut value_change,
                    periods_paid,
                ) = compute_loan_pay_scheduled_payment_loop(
                    &view.rules(),
                    vault_asset,
                    loan_scale,
                    effective_overpayment_amount,
                    total_value_outstanding,
                    principal_outstanding,
                    management_fee_outstanding,
                    periodic_payment,
                    interest_rate,
                    payment_interval,
                    payments_remaining,
                    management_fee_rate,
                    service_fee,
                );
                let total_scheduled_paid = principal_paid + interest_paid + fee_paid;
                let mut periodic_payment_override = None;
                if loan_sle.is_flag(protocol::lsfLoanOverpayment)
                    && periods_paid < payments_remaining
                    && total_scheduled_paid < effective_overpayment_amount
                    && periods_paid < tx::LOAN_MAXIMUM_PAYMENTS_PER_TRANSACTION
                {
                    let current_total = (total_value_outstanding
                        - principal_paid
                        - interest_paid
                        - management_fee_paid)
                        .max(RuntimeNumber::zero());
                    let current_principal =
                        (principal_outstanding - principal_paid).max(RuntimeNumber::zero());
                    let current_management_fee = (management_fee_outstanding - management_fee_paid)
                        .max(RuntimeNumber::zero());
                    let remaining_payments = payments_remaining.saturating_sub(periods_paid);
                    let overpayment_raw =
                        (effective_overpayment_amount - total_scheduled_paid).min(current_total);
                    let overpayment = if view.rules().enabled(&feature_id("fixCleanup3_2_0")) {
                        round_number_to_asset_with_scale(
                            vault_asset,
                            overpayment_raw,
                            loan_scale,
                            RoundingMode::Downward,
                        )
                    } else {
                        overpayment_raw
                    };
                    let periodic_rate = tx::loan_set_periodic_rate(interest_rate, payment_interval);
                    if let Some(extra) = compute_overpayment_reamortization(
                        &view.rules(),
                        vault_asset,
                        loan_scale,
                        overpayment,
                        current_total,
                        current_principal,
                        current_management_fee,
                        periodic_payment,
                        interest_rate,
                        payment_interval,
                        periodic_rate,
                        remaining_payments,
                        management_fee_rate,
                        overpayment_interest_rate,
                        overpayment_fee_rate,
                    ) {
                        principal_paid += extra.principal_paid;
                        interest_paid += extra.interest_paid;
                        management_fee_paid += extra.management_fee_paid;
                        fee_paid += extra.fee_paid;
                        value_change += extra.value_change;
                        periodic_payment_override = Some(extra.periodic_payment);
                    }
                }
                (
                    principal_paid,
                    interest_paid,
                    management_fee_paid,
                    fee_paid,
                    value_change,
                    periods_paid.max(1),
                    periodic_payment_override,
                )
            }
        }
    };

    let total_to_vault = principal_paid + interest_paid;
    let total_to_broker = fee_paid;
    let total_paid = total_to_vault + total_to_broker;
    if total_paid <= RuntimeNumber::zero() {
        return Ter::TEC_INSUFFICIENT_PAYMENT;
    }

    // Broker fee routing (reference sendBrokerFeeToOwner)
    let required_cover = loan_pay_fee_route_minimum_cover(
        vault_asset,
        broker_view.debt_total,
        broker_view.cover_rate_minimum,
        loan_scale,
        v_scale,
        view.rules().enabled(&feature_id("fixCleanup3_2_0")),
    );
    let owner_deep_frozen = match asset_deep_frozen(view, &broker_view.owner, vault_asset) {
        Ok(frozen) => frozen,
        Err(ter) => return ter,
    };
    let owner_requires_strong_auth =
        match asset_requires_strong_auth(view, &broker_view.owner, vault_asset) {
            Ok(required) => required,
            Err(ter) => return ter,
        };
    let send_fee_to_owner = broker_view.cover_available >= required_cover
        && !owner_deep_frozen
        && !owner_requires_strong_auth;
    let broker_payee = if send_fee_to_owner {
        broker_view.owner
    } else {
        broker_view.pseudo
    };
    if !send_fee_to_owner {
        let ter = check_asset_deep_frozen(view, &broker_payee, vault_asset);
        if ter != Ter::TES_SUCCESS {
            return ter;
        }
    }

    // Update cached views and validate precision before moving funds. C++ applies these
    // guards before accountSendMulti so failed rounding does not transfer balances.
    let assets_available_before = vault_view.assets_available;
    let assets_total_before = vault_view.assets_total;
    let rounded_to_vault = round_number_to_asset_with_scale(
        vault_asset,
        total_to_vault,
        v_scale,
        RoundingMode::Downward,
    );
    vault_view.assets_available += rounded_to_vault;
    if value_change != RuntimeNumber::zero() {
        vault_view.assets_total += value_change;
    }
    let assets_available_after = vault_view.assets_available;
    let assets_total_after = vault_view.assets_total;
    if assets_available_after > assets_total_after {
        return Ter::TEC_INTERNAL;
    }
    if assets_available_after == assets_available_before {
        return Ter::TEC_PRECISION_LOSS;
    }
    if value_change != RuntimeNumber::zero() && assets_total_after == assets_total_before {
        return Ter::TEC_PRECISION_LOSS;
    }
    if value_change == RuntimeNumber::zero() && assets_total_after != assets_total_before {
        return Ter::TEC_INTERNAL;
    }
    if rounded_to_vault + total_to_broker > payment_amount {
        return Ter::TEC_INSUFFICIENT_PAYMENT;
    }

    let debt_reduction = total_to_vault - value_change;
    let new_debt = broker_view.debt_total + (-debt_reduction);
    broker_view.debt_total = if new_debt < RuntimeNumber::zero() {
        RuntimeNumber::zero()
    } else {
        new_debt
    };
    if !send_fee_to_owner && total_to_broker > RuntimeNumber::zero() {
        broker_view.cover_available += total_to_broker;
    }

    if view.rules().enabled(&protocol::fix_cleanup_3_1_3())
        && let Asset::MPTIssue(issue) = vault_asset
        && borrower == issue.issuer()
    {
        let mut total_send_amount = 0_u64;
        for value in [rounded_to_vault, total_to_broker] {
            if value <= RuntimeNumber::zero() {
                continue;
            }
            let Some(amount) = runtime_to_amount(vault_asset, value, RoundingMode::Downward) else {
                return Ter::TEC_INTERNAL;
            };
            let units = amount.mpt().value();
            let Ok(units) = u64::try_from(units) else {
                return Ter::TEC_INTERNAL;
            };
            let Some(next_total) = total_send_amount.checked_add(units) else {
                return Ter::TEC_PATH_DRY;
            };
            total_send_amount = next_total;
        }
        let issuance = match view.peek(protocol::mpt_issuance_keylet_from_mptid(issue.mpt_id())) {
            Ok(Some(issuance)) => issuance,
            Ok(None) => return Ter::TEC_OBJECT_NOT_FOUND,
            Err(_) => return Ter::TEF_BAD_LEDGER,
        };
        let maximum_amount = ledger::mptoken_helpers::max_mpt_amount(&issuance);
        let Ok(maximum_amount) = u64::try_from(maximum_amount) else {
            return Ter::TEC_INTERNAL;
        };
        if ledger::mptoken_helpers::mpt_send_exceeds_maximum_amount(
            0,
            issuance.get_field_u64(sf("sfOutstandingAmount")),
            maximum_amount,
            total_send_amount,
            true,
        ) {
            return Ter::TEC_PATH_DRY;
        }
    }

    // Fund transfers
    let Some(to_vault) = runtime_to_amount(vault_asset, rounded_to_vault, RoundingMode::Downward)
    else {
        return Ter::TEC_INTERNAL;
    };
    let Some(to_broker) = runtime_to_amount(vault_asset, total_to_broker, RoundingMode::Downward)
    else {
        return Ter::TEC_INTERNAL;
    };
    let transfer = account_send_multi(
        view,
        &borrower,
        vault_asset,
        &[(vault_view.pseudo, to_vault), (broker_payee, to_broker)],
    );
    if !protocol::is_tes_success(transfer) {
        return transfer;
    }

    // Persist loan update
    let loan_sle_now = match view.peek(loan_keylet) {
        Ok(Some(s)) => s,
        _ => return Ter::TEF_BAD_LEDGER,
    };
    let lo = loan_sle_now.clone_as_object();
    let mut lu = STLedgerEntry::from_stobject(lo, *loan_sle_now.key());
    lu.set_field_number(
        sf("sfPrincipalOutstanding"),
        with_asset_number(principal_outstanding - principal_paid, vault_asset),
    );
    lu.set_field_number(
        sf("sfManagementFeeOutstanding"),
        with_asset_number(
            (management_fee_outstanding - management_fee_paid).max(RuntimeNumber::zero()),
            vault_asset,
        ),
    );
    let tracked_value_paid = principal_paid + interest_paid + management_fee_paid - value_change;
    let new_total = total_value_outstanding - tracked_value_paid;
    lu.set_field_number(
        sf("sfTotalValueOutstanding"),
        with_asset_number(
            if new_total < RuntimeNumber::zero() {
                RuntimeNumber::zero()
            } else {
                new_total
            },
            vault_asset,
        ),
    );
    if let Some(periodic_payment) = periodic_payment_override {
        lu.set_field_number(
            sf("sfPeriodicPayment"),
            with_asset_number(periodic_payment, vault_asset),
        );
    }
    if lu.is_field_present(sf("sfPaymentRemaining")) {
        let r = lu.get_field_u32(sf("sfPaymentRemaining"));
        let dec = match payment_type {
            tx::LoanPayPaymentType::Full => r,
            _ => payment_remaining_decrement
                .min(r)
                .min(tx::LOAN_MAXIMUM_PAYMENTS_PER_TRANSACTION),
        };
        let remaining_after = r.saturating_sub(dec);
        lu.set_field_u32(sf("sfPaymentRemaining"), remaining_after);
        let next_due = lu.get_field_u32(sf("sfNextPaymentDueDate"));
        // rippled's doPayment chooses PaymentSpecialCase::Final from the
        // computed payment, not solely from tfLoanPayFull.  A regular payment
        // which consumes the last scheduled instalment therefore follows the
        // same terminal date cleanup as an explicitly full payment.
        if remaining_after == 0 {
            lu.set_field_u32(sf("sfPreviousPaymentDueDate"), next_due);
            lu.set_field_u32(sf("sfNextPaymentDueDate"), 0);
        } else if dec > 0 {
            let interval = lu.get_field_u32(sf("sfPaymentInterval"));
            lu.set_field_u32(
                sf("sfPreviousPaymentDueDate"),
                next_due.saturating_add(interval.saturating_mul(dec.saturating_sub(1))),
            );
            lu.set_field_u32(
                sf("sfNextPaymentDueDate"),
                next_due.saturating_add(interval.saturating_mul(dec)),
            );
        }
    }
    associate_asset_entry(&mut lu, vault_asset);
    if view.update(Arc::new(lu)).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    // Persist vault update
    let vs = match view.peek(vault_keylet) {
        Ok(Some(s)) => s,
        _ => return Ter::TEF_BAD_LEDGER,
    };
    let vo = vs.clone_as_object();
    let mut vu = STLedgerEntry::from_stobject(vo, *vs.key());
    vu.set_field_number(
        sf("sfAssetsAvailable"),
        with_asset_number(vault_view.assets_available, vault_asset),
    );
    vu.set_field_number(
        sf("sfAssetsTotal"),
        with_asset_number(vault_view.assets_total, vault_asset),
    );
    associate_asset_entry(&mut vu, vault_asset);
    if view.update(Arc::new(vu)).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    // Persist broker update
    let bs = match view.peek(broker_keylet) {
        Ok(Some(s)) => s,
        _ => return Ter::TEF_BAD_LEDGER,
    };
    let bo = bs.clone_as_object();
    let mut bu = STLedgerEntry::from_stobject(bo, *bs.key());
    bu.set_field_number(
        sf("sfDebtTotal"),
        with_asset_number(broker_view.debt_total, vault_asset),
    );
    bu.set_field_number(
        sf("sfCoverAvailable"),
        with_asset_number(broker_view.cover_available, vault_asset),
    );
    associate_asset_entry(&mut bu, vault_asset);
    if view.update(Arc::new(bu)).is_err() {
        return Ter::TEF_BAD_LEDGER;
    }

    Ter::TES_SUCCESS
}

#[cfg(test)]
mod loan_pay_effective_amount_tests {
    use super::super::common::{sf, with_asset_number};
    use super::super::helpers::{effective_loan_pay_amount, loan_pay_fee_route_minimum_cover};
    use super::super::loan_set::loan_set_debt_total_update;
    use basics::{
        base_uint::Uint160,
        number::{NumberParts as RuntimeNumber, get_mantissa_scale},
    };
    use protocol::{AccountID, Asset, LedgerEntryType, STLedgerEntry};
    use protocol::{Issue, currency_from_string};

    fn account(byte: u8) -> AccountID {
        AccountID::from_array([byte; 20])
    }

    fn usd_asset() -> Asset {
        Asset::Issue(Issue::new(currency_from_string("USD"), account(0x55)))
    }

    fn vault_with_assets_total(asset: Asset, assets_total: RuntimeNumber) -> STLedgerEntry {
        let keylet = protocol::vault_keylet(Uint160::from_void(account(0x54).data()), 1);
        let mut vault = STLedgerEntry::from_type_and_key(LedgerEntryType::Vault, keylet.key);
        vault.set_field_number(sf("sfAssetsTotal"), with_asset_number(assets_total, asset));
        vault.set_field_u8(sf("sfScale"), 2);
        vault
    }

    #[test]
    fn loan_pay_overpayment_amount_truncates_at_loan_scale_after_fix_cleanup_3_1_3() {
        let amount = RuntimeNumber::try_from_external_parts(123_456_789, -8, get_mantissa_scale())
            .expect("valid runtime number");

        let rounded = effective_loan_pay_amount(
            tx::LoanPayPaymentType::Overpayment,
            true,
            false,
            usd_asset(),
            amount,
            -6,
        );

        assert_eq!(
            rounded,
            RuntimeNumber::try_from_external_parts(1_234_567, -6, get_mantissa_scale())
                .expect("expected rounded number")
        );
    }

    #[test]
    fn loan_pay_overpayment_amount_keeps_legacy_precision_without_fix_cleanup_3_1_3() {
        let amount = RuntimeNumber::try_from_external_parts(123_456_789, -8, get_mantissa_scale())
            .expect("valid runtime number");

        let legacy = effective_loan_pay_amount(
            tx::LoanPayPaymentType::Overpayment,
            false,
            false,
            usd_asset(),
            amount,
            -6,
        );

        assert_eq!(legacy, amount);
    }

    #[test]
    fn loan_pay_regular_amount_keeps_precision_after_fix_cleanup_3_1_3() {
        let amount = RuntimeNumber::try_from_external_parts(123_456_789, -8, get_mantissa_scale())
            .expect("valid runtime number");

        let regular = effective_loan_pay_amount(
            tx::LoanPayPaymentType::Regular,
            true,
            true,
            usd_asset(),
            amount,
            -6,
        );

        assert_eq!(regular, amount);
    }

    #[test]
    fn loan_pay_overpayment_amount_truncates_at_loan_scale_after_fix_cleanup_3_2_0() {
        let amount = RuntimeNumber::try_from_external_parts(123_456_789, -8, get_mantissa_scale())
            .expect("valid runtime number");

        let rounded = effective_loan_pay_amount(
            tx::LoanPayPaymentType::Overpayment,
            false,
            true,
            usd_asset(),
            amount,
            -6,
        );

        assert_eq!(
            rounded,
            RuntimeNumber::try_from_external_parts(1_234_567, -6, get_mantissa_scale())
                .expect("expected rounded number")
        );
    }

    #[test]
    fn loan_pay_fee_route_cover_uses_loan_scale_before_cleanup_3_2_0() {
        let debt_total = RuntimeNumber::try_from_external_parts(12345, -4, get_mantissa_scale())
            .expect("valid debt total");

        let required =
            loan_pay_fee_route_minimum_cover(usd_asset(), debt_total, 100_000, -4, -2, false);

        assert_eq!(
            required,
            RuntimeNumber::try_from_external_parts(12345, -4, get_mantissa_scale())
                .expect("legacy loan-scale threshold")
        );
    }

    #[test]
    fn loan_pay_fee_route_cover_uses_vault_scale_after_cleanup_3_2_0() {
        let debt_total = RuntimeNumber::try_from_external_parts(12345, -4, get_mantissa_scale())
            .expect("valid debt total");

        let required =
            loan_pay_fee_route_minimum_cover(usd_asset(), debt_total, 100_000, -4, -2, true);

        assert_eq!(
            required,
            RuntimeNumber::try_from_external_parts(124, -2, get_mantissa_scale())
                .expect("post-fix vault-scale threshold")
        );
    }

    #[test]
    fn loan_set_debt_total_update_uses_loan_scale_before_cleanup_3_2_0() {
        let asset = usd_asset();
        let vault_total = RuntimeNumber::try_from_external_parts(100, -2, get_mantissa_scale())
            .expect("valid vault total");
        let vault = vault_with_assets_total(asset, vault_total);
        let adjustment = RuntimeNumber::try_from_external_parts(12345, -4, get_mantissa_scale())
            .expect("valid adjustment");

        let debt_total =
            loan_set_debt_total_update(asset, RuntimeNumber::zero(), adjustment, &vault, -4, false);

        assert_eq!(
            debt_total,
            RuntimeNumber::try_from_external_parts(12345, -4, get_mantissa_scale())
                .expect("legacy loan-scale debt total")
        );
    }

    #[test]
    fn loan_set_debt_total_update_uses_vault_scale_after_cleanup_3_2_0() {
        let asset = usd_asset();
        let vault_total = RuntimeNumber::try_from_external_parts(100, -2, get_mantissa_scale())
            .expect("valid vault total");
        let vault = vault_with_assets_total(asset, vault_total);
        let adjustment = RuntimeNumber::try_from_external_parts(12345, -4, get_mantissa_scale())
            .expect("valid adjustment");

        let debt_total =
            loan_set_debt_total_update(asset, RuntimeNumber::zero(), adjustment, &vault, -4, true);

        // With fix_cleanup_3_2_0 enabled, the debt total is rounded to the
        // vault's canonical assets-total scale rather than the loan scale.
        // vault_scale() derives that scale from the canonicalized sfAssetsTotal
        // STAmount, which for this IOU is -15 (finer than the -2 external
        // exponent, exactly as the vault_scale documentation warns). Rounding
        // 1.2345 to scale -15 leaves the value unchanged, so the expected
        // result is the full-precision 12345e-4, not a -2 truncation.
        assert_eq!(
            debt_total,
            RuntimeNumber::try_from_external_parts(12345, -4, get_mantissa_scale())
                .expect("post-fix vault-scale debt total")
        );
    }
}
