//! Lossless Vault view for cross-implementation adapters.
//!
//! This deliberately uses the runtime `NumberParts`, `STAmount`, `Asset`, and
//! `MPTIssue` representations.  It is separate from the legacy bounded
//! `i64` test adapter so no caller can silently lose exponent, sign, numeric
//! type, or asset identity while preparing a canonical wire request.

use basics::number::{NumberParts, RoundingMode};
use protocol::{
    Asset, MPTIssue, STAmount, STLedgerEntry, get_field_by_symbol, to_amount_from_number,
};

fn sf(name: &str) -> &'static protocol::SField {
    get_field_by_symbol(name)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VaultLossless {
    pub asset: Asset,
    pub share_issue: MPTIssue,
    pub assets_total: NumberParts,
    pub assets_available: NumberParts,
    pub assets_reserved: NumberParts,
    pub assets_maximum: Option<NumberParts>,
    pub scale: u8,
    pub shares_total: NumberParts,
    pub loss_unrealized: NumberParts,
}

impl VaultLossless {
    /// Reads every modeled Vault number without narrowing to an integer.
    pub fn from_ledger_entry(vault: &STLedgerEntry) -> Self {
        let number = |field| vault.get_field_number(sf(field)).value();
        Self {
            asset: vault.get_field_issue(sf("sfAsset")).asset(),
            share_issue: MPTIssue::new(vault.get_field_h192(sf("sfShareMPTID"))),
            assets_total: number("sfAssetsTotal"),
            assets_available: number("sfAssetsAvailable"),
            assets_reserved: number("sfAssetsReserved"),
            assets_maximum: vault
                .is_field_present(sf("sfAssetsMaximum"))
                .then(|| number("sfAssetsMaximum")),
            scale: vault.get_field_u8(sf("sfScale")),
            shares_total: number("sfSharesTotal"),
            loss_unrealized: number("sfLossUnrealized"),
        }
    }

    /// Rebuilds a fully typed asset amount, retaining the vault asset identity.
    pub fn asset_amount(
        &self,
        value: NumberParts,
        rounding: RoundingMode,
    ) -> Result<STAmount, basics::number::NumberArithmeticError> {
        to_amount_from_number(self.asset, value, rounding)
    }

    /// Rebuilds a fully typed share amount, retaining the MPT issuance identity.
    pub fn share_amount(
        &self,
        value: NumberParts,
        rounding: RoundingMode,
    ) -> Result<STAmount, basics::number::NumberArithmeticError> {
        to_amount_from_number(Asset::MPTIssue(self.share_issue), value, rounding)
    }
}
