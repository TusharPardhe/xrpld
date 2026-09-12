//! Bounded Vault transition adapter used by Lean↔Quaxar verification vectors.
//!
//! The full-fidelity canonical value codec lives in `wire`; this module remains
//! the bounded arithmetic adapter used by ledger tests.

pub mod lossless;
pub mod wire;

// This is not the ledger transaction engine. It makes the raw transition,
// terminal association boundary, clamp, and accumulated dilution correction
// explicit for the native-integer vectors exercised by the bridge.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawVault {
    pub assets_total: i64,
    pub assets_available: i64,
    pub shares_total: i64,
    pub loss_unrealized: i64,
    pub scale: u8,
    pub dilution_correction: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TerminalVault(RawVault);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Correction {
    pub raw: i64,
    pub clamped: i64,
    pub correction: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositResult {
    pub vault: TerminalVault,
    pub amount: Correction,
    pub shares_issued: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithdrawResult {
    pub vault: TerminalVault,
    pub assets: Correction,
    pub shares_burned: i64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VaultAdapterError {
    PrecisionLoss,
    InsufficientFunds,
    InvalidState,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WithdrawAmount {
    Assets(i64),
    Shares(i64),
}

impl RawVault {
    pub fn new(
        assets_total: i64,
        assets_available: i64,
        shares_total: i64,
        loss_unrealized: i64,
        scale: u8,
    ) -> Result<Self, VaultAdapterError> {
        if assets_total < 0
            || assets_available < 0
            || assets_available > assets_total
            || shares_total < 0
            || loss_unrealized < 0
            || loss_unrealized > assets_total
            || scale > 18
        {
            return Err(VaultAdapterError::InvalidState);
        }
        Ok(Self {
            assets_total,
            assets_available,
            shares_total,
            loss_unrealized,
            scale,
            dilution_correction: 0,
        })
    }

    /// Explicitly crosses the single terminal association boundary. Raw values
    /// are never returned by public transaction methods below.
    pub fn associate_terminal(self) -> TerminalVault {
        TerminalVault(self)
    }
}

impl TerminalVault {
    pub fn raw(self) -> RawVault {
        self.0
    }

    fn clamp(self, raw: i64) -> Result<Correction, VaultAdapterError> {
        let quantum = 10_i64
            .checked_pow(u32::from(self.0.scale))
            .ok_or(VaultAdapterError::PrecisionLoss)?;
        let clamped = raw / quantum * quantum;
        Ok(Correction {
            raw,
            clamped,
            correction: raw - clamped,
        })
    }

    fn terminal(mut raw: RawVault, correction: Correction) -> TerminalVault {
        raw.dilution_correction += correction.correction;
        raw.associate_terminal()
    }

    /// Raw quote → clamp/precision correction → terminal state. `donation`
    /// changes assets but intentionally does not issue shares.
    pub fn deposit(
        self,
        raw_amount: i64,
        donation: bool,
    ) -> Result<DepositResult, VaultAdapterError> {
        if raw_amount <= 0 {
            return Err(VaultAdapterError::PrecisionLoss);
        }
        let amount = self.clamp(raw_amount)?;
        if amount.clamped <= 0 {
            return Err(VaultAdapterError::PrecisionLoss);
        }
        let shares_issued = if donation {
            0
        } else if self.0.assets_total == 0 {
            amount.clamped
        } else {
            self.0.shares_total * amount.clamped / self.0.assets_total
        };
        if !donation && shares_issued == 0 {
            return Err(VaultAdapterError::PrecisionLoss);
        }
        let mut raw = self.0;
        raw.assets_total += amount.clamped;
        raw.assets_available += amount.clamped;
        raw.shares_total += shares_issued;
        Ok(DepositResult {
            vault: Self::terminal(raw, amount),
            amount,
            shares_issued,
        })
    }

    pub fn withdraw(
        self,
        request: WithdrawAmount,
        waive_unrealized_loss: bool,
    ) -> Result<WithdrawResult, VaultAdapterError> {
        let nav = self.0.assets_total
            - if waive_unrealized_loss {
                0
            } else {
                self.0.loss_unrealized
            };
        let (raw_assets, shares_burned) = match request {
            WithdrawAmount::Assets(assets) if assets > 0 && nav > 0 => {
                (assets, self.0.shares_total * assets / nav)
            }
            WithdrawAmount::Shares(shares) if shares > 0 && self.0.shares_total > 0 => {
                (nav * shares / self.0.shares_total, shares)
            }
            _ => return Err(VaultAdapterError::PrecisionLoss),
        };
        let assets = self.clamp(raw_assets)?;
        if assets.clamped <= 0 || assets.clamped > self.0.assets_available {
            return Err(VaultAdapterError::InsufficientFunds);
        }
        let mut raw = self.0;
        raw.assets_total -= assets.clamped;
        raw.assets_available -= assets.clamped;
        raw.shares_total -= shares_burned;
        Ok(WithdrawResult {
            vault: Self::terminal(raw, assets),
            assets,
            shares_burned,
        })
    }

    pub fn clawback(
        self,
        assets: i64,
        holder_shares: i64,
    ) -> Result<WithdrawResult, VaultAdapterError> {
        let request = if assets == 0 {
            WithdrawAmount::Shares(holder_shares)
        } else {
            WithdrawAmount::Assets(assets)
        };
        self.withdraw(request, false)
    }

    pub fn burn_shares_raw(self, shares: i64) -> Result<RawVault, VaultAdapterError> {
        if shares <= 0 || shares > self.0.shares_total {
            return Err(VaultAdapterError::InvalidState);
        }
        Ok(RawVault {
            shares_total: self.0.shares_total - shares,
            ..self.0
        })
    }

    pub fn burn_shares(self, shares: i64) -> Result<TerminalVault, VaultAdapterError> {
        Ok(self.burn_shares_raw(shares)?.associate_terminal())
    }

    pub fn can_burn_shares(self) -> bool {
        self.0.shares_total > 0 && self.0.assets_total == 0 && self.0.assets_available == 0
    }

    pub fn can_delete(self) -> bool {
        self.0.shares_total == 0 && self.0.assets_total == 0 && self.0.assets_available == 0
    }

    pub fn can_set_maximum(self, maximum: i64) -> bool {
        maximum == 0 || maximum >= self.0.assets_total
    }
}
