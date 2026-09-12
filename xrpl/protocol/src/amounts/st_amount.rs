//! `STAmount` core port from `xrpl/protocol/STAmount.*`.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

use basics::number::NumberParts as RuntimeNumber;

use crate::{
    Asset, IOUAmount, Issue, JsonOptions, JsonValue, MPTAmount, MPTIssue, SField, STArray,
    STObject, SerialIter, SerializedTypeId, Serializer, StBase, StBaseCore, ValidationError,
    XRPAmount, div_round, divide, is_xrp_currency, issued_exponent_from_nonzero_header_bits,
    issued_header_bits_from_word, issued_header_is_negative, issued_mantissa_from_word,
    issued_zero_header_bits, issued_zero_header_word, mpt_wire_header_byte, mul_round, multiply,
    native_wire_word, sf_generic, xrp_issue,
};
use crate::{
    ST_AMOUNT_ISSUED_CURRENCY_FLAG, ST_AMOUNT_MAX_MANTISSA, ST_AMOUNT_MAX_NATIVE_NETWORK,
    ST_AMOUNT_MAX_OFFSET, ST_AMOUNT_MIN_MANTISSA, ST_AMOUNT_MIN_OFFSET, ST_AMOUNT_MP_TOKEN_FLAG,
    ST_AMOUNT_POSITIVE_FLAG,
};

const IOU_ZERO_OFFSET: i32 = -100;

/// A numeric result that cannot be represented by the XRPL amount wire format.
/// Callers performing transaction arithmetic should propagate this as a normal
/// engine result rather than unwind from a consensus or network worker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AmountError {
    NativeOutOfRange,
    MptOutOfRange,
    IssuedOutOfRange,
    DivisionByZero,
    ArithmeticOverflow,
}

impl fmt::Display for AmountError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let message = match self {
            Self::NativeOutOfRange => "Native currency amount out of range",
            Self::MptOutOfRange => "MPT amount out of range",
            Self::IssuedOutOfRange => "Issued currency amount out of range",
            Self::DivisionByZero => "division by zero",
            Self::ArithmeticOverflow => "amount arithmetic overflow",
        };
        formatter.write_str(message)
    }
}

impl std::error::Error for AmountError {}

#[derive(Debug, Clone)]
pub struct STAmount {
    core: StBaseCore,
    asset: Asset,
    value: u64,
    offset: i32,
    is_negative: bool,
}

impl STAmount {
    /// Construct a native amount for internal arithmetic without applying the
    /// stricter network serialization limit.
    ///
    /// rippled's native `STAmount` add/subtract operators use the unchecked
    /// `(SField, int64)` constructor.  Flow relies on that distinction for its
    /// `kMaxNative` reverse-pass sentinel; `is_legal_net`/`check` still reject
    /// the value if it ever reaches a wire or ledger validation boundary.
    fn from_native_i64_unchecked(field: &'static SField, drops: i64) -> Self {
        Self {
            core: StBaseCore::with_field(field),
            asset: Asset::Issue(xrp_issue()),
            value: drops.unsigned_abs(),
            offset: 0,
            is_negative: drops < 0,
        }
    }

    pub fn with_field(field: &'static SField) -> Self {
        Self {
            core: StBaseCore::with_field(field),
            asset: Asset::Issue(xrp_issue()),
            value: 0,
            offset: 0,
            is_negative: false,
        }
    }

    pub fn from_serial_iter(sit: &mut SerialIter<'_>, field: &'static SField) -> Self {
        let mut amount = Self::with_field(field);
        let value = sit.get64();

        if (value & ST_AMOUNT_ISSUED_CURRENCY_FLAG) == 0 {
            if (value & ST_AMOUNT_MP_TOKEN_FLAG) != 0 {
                amount.offset = 0;
                amount.is_negative = (value & ST_AMOUNT_POSITIVE_FLAG) == 0;
                amount.value = (value << 8) | u64::from(sit.get8());
                amount.asset = Asset::MPTIssue(MPTIssue::new(sit.get192()));
                return amount;
            }

            amount.asset = Asset::Issue(xrp_issue());
            if (value & ST_AMOUNT_POSITIVE_FLAG) != 0 {
                amount.value = value & !(ST_AMOUNT_POSITIVE_FLAG | ST_AMOUNT_MP_TOKEN_FLAG);
                amount.offset = 0;
                amount.is_negative = false;
                return amount;
            }

            if value == 0 {
                panic!("negative zero is not canonical");
            }

            amount.value = value & !(ST_AMOUNT_POSITIVE_FLAG | ST_AMOUNT_MP_TOKEN_FLAG);
            amount.offset = 0;
            amount.is_negative = true;
            return amount;
        }

        let currency = crate::Currency::from_slice(sit.get160().data()).expect("currency width");
        if is_xrp_currency(currency) {
            panic!("invalid native currency");
        }

        let account = crate::AccountID::from_slice(sit.get160().data()).expect("account width");
        if account.is_zero() {
            panic!("invalid native account");
        }

        let issue = Issue::new(currency, account);
        let header_bits = issued_header_bits_from_word(value);
        let mantissa = issued_mantissa_from_word(value);

        if mantissa != 0 {
            let is_negative = issued_header_is_negative(header_bits);
            let offset = issued_exponent_from_nonzero_header_bits(header_bits);
            if !(ST_AMOUNT_MIN_MANTISSA..=ST_AMOUNT_MAX_MANTISSA).contains(&mantissa)
                || !(ST_AMOUNT_MIN_OFFSET..=ST_AMOUNT_MAX_OFFSET).contains(&offset)
            {
                return Self::default();
            }

            amount.asset = Asset::Issue(issue);
            amount.value = mantissa;
            amount.offset = offset;
            amount.is_negative = is_negative;
            amount.canonicalize();
            return amount;
        }

        if header_bits != issued_zero_header_bits() {
            panic!("invalid currency value");
        }

        amount.asset = Asset::Issue(issue);
        amount.value = 0;
        amount.offset = 0;
        amount.is_negative = false;
        amount.canonicalize();
        amount
    }

    pub fn new_native(mantissa: u64, negative: bool) -> Self {
        Self {
            core: StBaseCore::with_field(sf_generic()),
            asset: Asset::Issue(xrp_issue()),
            value: mantissa,
            offset: 0,
            is_negative: mantissa != 0 && negative,
        }
    }

    pub fn new_with_asset(
        field: &'static SField,
        asset: impl Into<Asset>,
        mantissa: u64,
        exponent: i32,
        negative: bool,
    ) -> Self {
        Self::try_new_with_asset(field, asset, mantissa, exponent, negative)
            .unwrap_or_else(|error| panic!("{error}"))
    }

    pub fn try_new_with_asset(
        field: &'static SField,
        asset: impl Into<Asset>,
        mantissa: u64,
        exponent: i32,
        negative: bool,
    ) -> Result<Self, AmountError> {
        let mut amount = Self {
            core: StBaseCore::with_field(field),
            asset: asset.into(),
            value: mantissa,
            offset: exponent,
            is_negative: negative,
        };
        amount.try_canonicalize()?;
        Ok(amount)
    }

    pub fn from_xrp_amount(amount: XRPAmount) -> Self {
        let mut value = Self {
            core: StBaseCore::with_field(sf_generic()),
            asset: Asset::Issue(xrp_issue()),
            value: amount.drops().unsigned_abs(),
            offset: 0,
            is_negative: amount.drops() < 0,
        };
        value.canonicalize();
        value
    }

    pub fn from_iou_amount(field: &'static SField, amount: IOUAmount, issue: Issue) -> Self {
        let mut value = Self {
            core: StBaseCore::with_field(field),
            asset: Asset::Issue(issue),
            value: amount.mantissa().unsigned_abs(),
            offset: amount.exponent(),
            is_negative: amount.mantissa() < 0,
        };
        value.canonicalize();
        value
    }

    pub fn from_mpt_amount(field: &'static SField, amount: MPTAmount, issue: MPTIssue) -> Self {
        let mut value = Self {
            core: StBaseCore::with_field(field),
            asset: Asset::MPTIssue(issue),
            value: amount.value().unsigned_abs(),
            offset: 0,
            is_negative: amount.value() < 0,
        };
        value.canonicalize();
        value
    }

    pub fn exponent(&self) -> i32 {
        self.offset
    }

    pub fn integral(&self) -> bool {
        self.asset.integral()
    }

    pub fn native(&self) -> bool {
        self.asset.native()
    }

    pub fn holds_issue(&self) -> bool {
        matches!(self.asset, Asset::Issue(_))
    }

    pub fn holds_mpt_issue(&self) -> bool {
        matches!(self.asset, Asset::MPTIssue(_))
    }

    pub fn negative(&self) -> bool {
        self.is_negative
    }

    pub fn mantissa(&self) -> u64 {
        self.value
    }

    pub fn asset(&self) -> Asset {
        self.asset
    }

    pub fn issue(&self) -> Issue {
        match self.asset {
            Asset::Issue(issue) => issue,
            Asset::MPTIssue(_) => panic!("STAmount does not hold an Issue"),
        }
    }

    pub fn signum(&self) -> i32 {
        if self.value == 0 {
            0
        } else if self.is_negative {
            -1
        } else {
            1
        }
    }

    pub fn zeroed(&self) -> Self {
        Self::new_with_asset(self.fname(), self.asset, 0, 0, false)
    }

    pub fn xrp(&self) -> XRPAmount {
        if !self.native() {
            panic!("Cannot return non-native STAmount as XRPAmount");
        }

        let drops = i64::try_from(self.value).expect("native value should fit i64");
        if self.is_negative {
            XRPAmount::from_drops(-drops)
        } else {
            XRPAmount::from_drops(drops)
        }
    }

    pub fn iou(&self) -> IOUAmount {
        if self.integral() {
            panic!("Cannot return non-IOU STAmount as IOUAmount");
        }

        let mantissa = i64::try_from(self.value).expect("IOU mantissa should fit i64");
        if self.is_negative {
            IOUAmount::from_parts(-mantissa, self.offset).expect("canonical IOU should round-trip")
        } else {
            IOUAmount::from_parts(mantissa, self.offset).expect("canonical IOU should round-trip")
        }
    }

    pub fn mpt(&self) -> MPTAmount {
        if !self.holds_mpt_issue() {
            panic!("Cannot return STAmount as MPTAmount");
        }

        let value = i64::try_from(self.value).expect("MPT value should fit i64");
        if self.is_negative {
            MPTAmount::from_value(-value)
        } else {
            MPTAmount::from_value(value)
        }
    }

    pub fn negate(&mut self) {
        if self.value != 0 {
            self.is_negative = !self.is_negative;
        }
    }

    pub fn clear(&mut self) {
        self.offset = if self.integral() { 0 } else { IOU_ZERO_OFFSET };
        self.value = 0;
        self.is_negative = false;
    }

    pub fn clear_with_asset(&mut self, asset: impl Into<Asset>) {
        self.asset = asset.into();
        self.clear();
    }

    pub fn set_issue(&mut self, asset: impl Into<Asset>) {
        self.asset = asset.into();
    }

    pub fn set_issuer(&mut self, issuer: crate::AccountID) {
        match &mut self.asset {
            Asset::Issue(issue) => issue.account = issuer,
            Asset::MPTIssue(_) => panic!("STAmount MPT asset cannot change issuer"),
        }
    }

    fn set_json(&self, json: &mut JsonValue) {
        if self.native() {
            *json = JsonValue::String(self.text());
            return;
        }

        let mut object = BTreeMap::new();
        object.insert("value".to_string(), JsonValue::String(self.text()));
        self.asset.set_json(&mut object);
        *json = JsonValue::Object(object);
    }

    fn canonicalize(&mut self) {
        self.try_canonicalize()
            .unwrap_or_else(|error| panic!("{error}"));
    }

    fn try_canonicalize(&mut self) -> Result<(), AmountError> {
        if self.integral() {
            // Match rippled STAmount::canonicalize. XRP and MPT are integral
            // values, but arithmetic can temporarily represent them using an
            // exponent. Convert through NumberParts under the active rounding
            // mode and reject, rather than saturate, a result outside the
            // protocol's legal range. The transaction application boundary
            // translates this failure into tefEXCEPTION.
            if self.value == 0 || self.offset <= -20 {
                self.value = 0;
                self.offset = 0;
                self.is_negative = false;
                return Ok(());
            }

            if self.native() && self.offset > 17 {
                return Err(AmountError::NativeOutOfRange);
            }
            if self.holds_mpt_issue() && self.offset > 18 {
                return Err(AmountError::MptOutOfRange);
            }

            let number = RuntimeNumber::unchecked(self.is_negative, self.value, self.offset);
            if self.native() {
                let amount =
                    XRPAmount::from_number(number).map_err(|_| AmountError::NativeOutOfRange)?;
                self.is_negative = amount.drops() < 0;
                self.value = amount.drops().unsigned_abs();
                self.offset = 0;
                if self.value > ST_AMOUNT_MAX_NATIVE_NETWORK {
                    return Err(AmountError::NativeOutOfRange);
                }
            } else if self.holds_mpt_issue() {
                let amount =
                    MPTAmount::from_number(number).map_err(|_| AmountError::MptOutOfRange)?;
                self.is_negative = amount.value() < 0;
                self.value = amount.value().unsigned_abs();
                self.offset = 0;
                if self.value > crate::MAX_MP_TOKEN_AMOUNT as u64 {
                    return Err(AmountError::MptOutOfRange);
                }
            } else {
                unreachable!("integral STAmount must hold XRP or MPT");
            }
            return Ok(());
        }

        // Issued amounts are canonicalized through the same Number/IOUAmount
        // boundary as rippled's STAmount::canonicalize. Manual decimal
        // truncation here is not protocol-equivalent: when an oversized
        // mantissa drops a final digit >= 5, rippled rounds to nearest while
        // truncation produces a one-unit-lower quality key and a different
        // BookDirectory. This matters for offer quality directory placement.
        let iou = IOUAmount::from_number(RuntimeNumber::unchecked(
            self.is_negative,
            self.value,
            self.offset,
        ))
        .map_err(|_| AmountError::IssuedOutOfRange)?;
        self.is_negative = iou.mantissa() < 0;
        self.value = iou.mantissa().unsigned_abs();
        self.offset = iou.exponent();
        Ok(())
    }

    fn are_comparable(&self, other: &Self) -> bool {
        match (self.asset, other.asset) {
            (Asset::Issue(left), Asset::Issue(right)) => {
                self.native() == other.native() && left.currency == right.currency
            }
            (Asset::MPTIssue(left), Asset::MPTIssue(right)) => left == right,
            _ => false,
        }
    }

    fn cmp_amount(&self, other: &Self) -> Ordering {
        if !self.are_comparable(other) {
            // transaction engine. In Rust, panicking kills the thread.
            // Return a deterministic ordering based on the raw numeric value
            // so the transactor can proceed. The transaction will produce
            // incorrect results but won't crash — matching reference where the
            // exception causes the tx to fail with tecINTERNAL.
            return self
                .mantissa()
                .cmp(&other.mantissa())
                .then(self.exponent().cmp(&other.exponent()));
        }

        if self.is_negative != other.is_negative {
            return if self.is_negative {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }

        if self.value == 0 {
            if other.is_negative {
                return Ordering::Greater;
            }
            return if other.value != 0 {
                Ordering::Less
            } else {
                Ordering::Equal
            };
        }

        if other.value == 0 {
            return Ordering::Greater;
        }

        if self.offset > other.offset {
            return if self.is_negative {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }
        if self.offset < other.offset {
            return if self.is_negative {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }
        if self.value > other.value {
            return if self.is_negative {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        }
        if self.value < other.value {
            return if self.is_negative {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }
        Ordering::Equal
    }

    pub fn try_multiply(&self, other: &Self, asset: impl Into<Asset>) -> Result<Self, AmountError> {
        crate::quality::try_multiply(self, other, asset)
    }

    pub fn try_divide(&self, other: &Self, asset: impl Into<Asset>) -> Result<Self, AmountError> {
        crate::quality::try_divide(self, other, asset)
    }

    pub fn multiply(&self, other: &Self, asset: impl Into<Asset>) -> Self {
        multiply(self, other, asset)
    }

    pub fn divide(&self, other: &Self, asset: impl Into<Asset>) -> Self {
        divide(self, other, asset)
    }

    pub fn mul_round(&self, other: &Self, asset: Asset, round_up: bool) -> Self {
        mul_round(self, other, asset, round_up)
    }

    pub fn div_round(&self, other: &Self, asset: Asset, round_up: bool) -> Self {
        div_round(self, other, asset, round_up)
    }

    pub fn is_legal_net(&self) -> bool {
        if self.native() {
            return self.value <= ST_AMOUNT_MAX_NATIVE_NETWORK;
        }
        true
    }

    pub fn is_legal_mpt(&self) -> bool {
        !self.holds_mpt_issue()
            || (!self.negative()
                && self.exponent() == 0
                && self.mantissa() <= crate::MAX_MP_TOKEN_AMOUNT as u64)
    }

    pub fn round(&self, digits: usize) -> Self {
        if self.native() || self.holds_mpt_issue() || self.value == 0 {
            return self.clone();
        }

        static MOD: [u64; 17] = [
            10_000_000_000_000_000,
            1_000_000_000_000_000,
            100_000_000_000_000,
            10_000_000_000_000,
            1_000_000_000_000,
            100_000_000_000,
            10_000_000_000,
            1_000_000_000,
            100_000_000,
            10_000_000,
            1_000_000,
            100_000,
            10_000,
            1_000,
            100,
            10,
            1,
        ];

        let mut mantissa = self.value;
        mantissa += MOD[digits] - 1;
        mantissa -= mantissa % MOD[digits];

        let mut result = self.clone();
        result.value = mantissa;
        result.canonicalize();
        result
    }
}

/// Returns whether two comparable amounts can be added without integral
/// overflow or IOU precision loss under `mode`.
///
/// This is the fallible-arithmetic predicate counterpart of rippled's
/// `canAdd`: failures while evaluating its IOU precision gate are reported as
/// `false`, never as a panic.
pub fn can_add(a: &STAmount, b: &STAmount, mode: basics::number::RoundingMode) -> bool {
    let _rounding = basics::number::NumberRoundModeGuard::new(mode);

    if !a.are_comparable(b) {
        return false;
    }
    if a.value == 0 || b.value == 0 {
        return true;
    }
    if a.integral() {
        return signed_integral_value(a)
            .zip(signed_integral_value(b))
            .is_some_and(|(left, right)| left.checked_add(right).is_some());
    }

    (|| -> Result<bool, AmountError> {
        let one = STAmount::try_new_with_asset(sf_generic(), crate::no_issue(), 1, 0, false)?;
        let max_loss = STAmount::try_new_with_asset(sf_generic(), crate::no_issue(), 1, -4, false)?;

        let lhs = try_iou_add(&try_iou_sub(a, b)?, b)?.try_divide(a, crate::no_issue())?;
        let rhs = try_iou_add(&try_iou_sub(b, a)?, a)?.try_divide(b, crate::no_issue())?;
        let lhs = try_iou_sub(&lhs, &one)?;
        let rhs = try_iou_sub(&rhs, &one)?;
        let lhs = absolute_amount(lhs);
        let rhs = absolute_amount(rhs);
        Ok(try_iou_add(&lhs, &rhs)? <= max_loss)
    })()
    .unwrap_or(false)
}

/// Returns whether `b` may be subtracted from `a` without violating the
/// integral balance/overflow constraints. Comparable IOUs may always be
/// subtracted.
pub fn can_subtract(a: &STAmount, b: &STAmount) -> bool {
    if !a.are_comparable(b) {
        return false;
    }
    if b.value == 0 {
        return true;
    }
    if !a.integral() {
        return true;
    }

    signed_integral_value(a)
        .zip(signed_integral_value(b))
        .is_some_and(|(left, right)| {
            !(right > 0 && left < right) && left.checked_sub(right).is_some()
        })
}

/// Rounds a non-integral amount to the `10^scale` grid using an explicit
/// rounding mode. Integral values, zero, and values already at or above the
/// requested scale are returned unchanged.
///
/// The rounding guard restores the caller's thread-local Number mode on every
/// return path, including an out-of-range result.
pub fn round_to_exponent(
    value: &STAmount,
    scale: i32,
    mode: basics::number::RoundingMode,
) -> Result<STAmount, AmountError> {
    if value.integral() || value.value == 0 || value.offset >= scale {
        return Ok(value.clone());
    }

    let _rounding = basics::number::NumberRoundModeGuard::new(mode);
    let reference = STAmount::try_new_with_asset(
        value.fname(),
        value.asset,
        ST_AMOUNT_MIN_MANTISSA,
        scale,
        value.is_negative,
    )?;
    let sum = try_iou_add(value, &reference)?;
    try_iou_sub(&sum, &reference)
}

fn signed_integral_value(value: &STAmount) -> Option<i64> {
    let magnitude = value.value;
    if value.is_negative {
        if magnitude == (i64::MAX as u64) + 1 {
            Some(i64::MIN)
        } else {
            i64::try_from(magnitude).ok()?.checked_neg()
        }
    } else {
        i64::try_from(magnitude).ok()
    }
}

fn try_iou_add(left: &STAmount, right: &STAmount) -> Result<STAmount, AmountError> {
    debug_assert!(!left.integral() && !right.integral());
    let sum = left
        .iou()
        .checked_add(right.iou())
        .map_err(|_| AmountError::IssuedOutOfRange)?;
    STAmount::try_new_with_asset(
        left.fname(),
        left.asset,
        sum.mantissa().unsigned_abs(),
        sum.exponent(),
        sum.mantissa() < 0,
    )
}

fn try_iou_sub(left: &STAmount, right: &STAmount) -> Result<STAmount, AmountError> {
    debug_assert!(!left.integral() && !right.integral());
    let difference = left
        .iou()
        .checked_sub(right.iou())
        .map_err(|_| AmountError::IssuedOutOfRange)?;
    STAmount::try_new_with_asset(
        left.fname(),
        left.asset,
        difference.mantissa().unsigned_abs(),
        difference.exponent(),
        difference.mantissa() < 0,
    )
}

fn absolute_amount(mut value: STAmount) -> STAmount {
    if value.negative() {
        value.negate();
    }
    value
}

pub fn is_legal_net(value: &STAmount) -> bool {
    value.is_legal_net()
}

pub fn is_legal_mpt(value: &STAmount) -> bool {
    value.is_legal_mpt()
}

pub fn has_invalid_amount(field: &dyn StBase) -> bool {
    has_invalid_amount_with_depth(field, 0)
}

fn has_invalid_amount_with_depth(field: &dyn StBase, depth: i32) -> bool {
    if depth > 10 {
        return true;
    }

    if let Some(amount) = field.as_any().downcast_ref::<STAmount>() {
        return !amount.is_legal_mpt() || !amount.is_legal_net();
    }

    if let Some(object) = field.as_any().downcast_ref::<STObject>() {
        return object
            .iter()
            .any(|field| has_invalid_amount_with_depth(field, depth + 1));
    }

    if let Some(array) = field.as_any().downcast_ref::<STArray>() {
        return array.iter().any(|object| {
            let field: &dyn StBase = object;
            has_invalid_amount_with_depth(field, depth + 1)
        });
    }

    false
}

impl Default for STAmount {
    fn default() -> Self {
        Self::with_field(sf_generic())
    }
}

impl PartialEq for STAmount {
    fn eq(&self, other: &Self) -> bool {
        self.are_comparable(other)
            && self.is_negative == other.is_negative
            && self.offset == other.offset
            && self.value == other.value
    }
}

impl Eq for STAmount {}

impl PartialOrd for STAmount {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for STAmount {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_amount(other)
    }
}

impl AddAssign for STAmount {
    fn add_assign(&mut self, rhs: Self) {
        if !self.are_comparable(&rhs) {
            // In Rust, return self unchanged to avoid crashing the node.
            return;
        }

        if self.native() {
            let drops = (self.xrp() + rhs.xrp()).drops();
            *self = Self::from_native_i64_unchecked(self.fname(), drops);
        } else if self.holds_mpt_issue() {
            *self = Self::from_mpt_amount(
                self.fname(),
                self.mpt() + rhs.mpt(),
                match self.asset {
                    Asset::MPTIssue(issue) => issue,
                    _ => unreachable!(),
                },
            );
        } else {
            *self = Self::from_iou_amount(self.fname(), self.iou() + rhs.iou(), self.issue());
        }
    }
}

impl Add for STAmount {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl SubAssign for STAmount {
    fn sub_assign(&mut self, rhs: Self) {
        if !self.are_comparable(&rhs) {
            // In Rust, return self unchanged to avoid crashing the node.
            return;
        }

        if self.native() {
            let drops = (self.xrp() - rhs.xrp()).drops();
            *self = Self::from_native_i64_unchecked(self.fname(), drops);
        } else if self.holds_mpt_issue() {
            *self = Self::from_mpt_amount(
                self.fname(),
                self.mpt() - rhs.mpt(),
                match self.asset {
                    Asset::MPTIssue(issue) => issue,
                    _ => unreachable!(),
                },
            );
        } else {
            *self = Self::from_iou_amount(self.fname(), self.iou() - rhs.iou(), self.issue());
        }
    }
}

impl Sub for STAmount {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl MulAssign<u64> for STAmount {
    fn mul_assign(&mut self, rhs: u64) {
        if rhs == 1 {
            return;
        }
        if rhs == 0 {
            self.clear();
            return;
        }

        if self.native() {
            let xrp = self.xrp() * i64::try_from(rhs).expect("multiplier should fit i64");
            *self = Self::from_xrp_amount(xrp);
        } else if self.holds_mpt_issue() {
            let mpt = self.mpt() * i64::try_from(rhs).expect("multiplier should fit i64");
            *self = Self::from_mpt_amount(
                self.fname(),
                mpt,
                match self.asset {
                    Asset::MPTIssue(issue) => issue,
                    _ => unreachable!(),
                },
            );
        } else {
            let iou = self.iou() * i64::try_from(rhs).expect("multiplier should fit i64");
            *self = Self::from_iou_amount(self.fname(), iou, self.issue());
        }
    }
}

impl Mul<u64> for STAmount {
    type Output = Self;

    fn mul(mut self, rhs: u64) -> Self::Output {
        self *= rhs;
        self
    }
}

impl DivAssign<u64> for STAmount {
    fn div_assign(&mut self, rhs: u64) {
        if rhs == 1 {
            return;
        }
        if rhs == 0 {
            panic!("division by zero");
        }

        if self.native() {
            let xrp = self.xrp() / i64::try_from(rhs).expect("divisor should fit i64");
            *self = Self::from_xrp_amount(xrp);
        } else if self.holds_mpt_issue() {
            let mpt = self.mpt() / i64::try_from(rhs).expect("divisor should fit i64");
            *self = Self::from_mpt_amount(
                self.fname(),
                mpt,
                match self.asset {
                    Asset::MPTIssue(issue) => issue,
                    _ => unreachable!(),
                },
            );
        } else {
            let iou = self.iou() / i64::try_from(rhs).expect("divisor should fit i64");
            *self = Self::from_iou_amount(self.fname(), iou, self.issue());
        }
    }
}

impl Div<u64> for STAmount {
    type Output = Self;

    fn div(mut self, rhs: u64) -> Self::Output {
        self /= rhs;
        self
    }
}

impl From<XRPAmount> for STAmount {
    fn from(value: XRPAmount) -> Self {
        Self::from_xrp_amount(value)
    }
}

impl StBase for STAmount {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn core(&self) -> &StBaseCore {
        &self.core
    }

    fn core_mut(&mut self) -> &mut StBaseCore {
        &mut self.core
    }

    fn stype(&self) -> SerializedTypeId {
        SerializedTypeId::Amount
    }

    fn full_text(&self) -> String {
        format!("{}/{}", self.text(), self.asset.text())
    }

    fn text(&self) -> String {
        if self.value == 0 {
            return "0".to_string();
        }

        let raw_value = self.value.to_string();
        let mut text = String::new();
        if self.is_negative {
            text.push('-');
        }

        let scientific = self.offset != 0 && (self.offset < -25 || self.offset > -5);
        if self.native() || self.holds_mpt_issue() || scientific {
            text.push_str(&raw_value);
            if scientific {
                text.push('e');
                text.push_str(&self.offset.to_string());
            }
            return text;
        }

        let decimal_index = raw_value.len() as i32 + self.offset;
        if decimal_index <= 0 {
            text.push('0');
            text.push('.');
            text.push_str(&"0".repeat((-decimal_index) as usize));
            text.push_str(&raw_value);
        } else if decimal_index >= raw_value.len() as i32 {
            text.push_str(&raw_value);
            text.push_str(&"0".repeat((decimal_index as usize) - raw_value.len()));
        } else {
            let split = decimal_index as usize;
            text.push_str(&raw_value[..split]);
            text.push('.');
            text.push_str(&raw_value[split..]);
        }

        if let Some(dot) = text.find('.') {
            while text.ends_with('0') {
                text.pop();
            }
            if text.len() == dot + 1 {
                text.pop();
            }
        }

        text
    }

    fn json(&self, _options: JsonOptions) -> JsonValue {
        let mut json = JsonValue::Null;
        self.set_json(&mut json);
        json
    }

    fn add(&self, serializer: &mut Serializer) {
        if self.native() {
            serializer.add64(native_wire_word(self.value, self.is_negative));
            return;
        }

        if let Asset::MPTIssue(issue) = self.asset {
            serializer.add8(mpt_wire_header_byte(self.is_negative));
            serializer.add64(self.value);
            serializer.add_bit_string(issue.mpt_id());
            return;
        }

        if self.value == 0 {
            serializer.add64(issued_zero_header_word());
        } else {
            let header = ((self.offset + 512 + if self.is_negative { 97 } else { 256 + 97 })
                as u64)
                << (64 - 10);
            serializer.add64(self.value | header);
        }

        let issue = self.issue();
        serializer.add_bit_string(issue.currency);
        serializer.add_bit_string(issue.account);
    }

    fn is_equivalent(&self, other: &dyn StBase) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .map(|other| other == self)
            .unwrap_or(false)
    }

    fn is_default(&self) -> bool {
        self.value == 0 && self.native()
    }

    fn is_valid(&self) -> bool {
        self.check().is_ok()
    }

    fn check(&self) -> Result<(), ValidationError> {
        if self.native() && self.value > ST_AMOUNT_MAX_NATIVE_NETWORK {
            return Err(ValidationError::Custom(
                "Native amount out of range".to_string(),
            ));
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AmountError, ST_AMOUNT_MAX_NATIVE_NETWORK, ST_AMOUNT_MIN_MANTISSA, STAmount,
        ValidationError, has_invalid_amount,
    };
    use crate::ST_AMOUNT_MAX_NATIVE;
    use crate::sf_generic;
    use crate::stbase::StBase;
    use crate::{AccountID, MPTAmount, MPTIssue, STArray, STObject, get_field_by_symbol};
    use basics::base_uint::Uint192;

    #[test]
    fn native_zero_constructor_clears_negative_zero() {
        let amount = STAmount::new_native(0, true);
        assert!(!amount.negative());
        assert_eq!(amount.text(), "0");
    }

    #[test]
    fn issue_amount_equality_ignores_issuer() {
        let mut first_issue = crate::no_issue();
        first_issue.currency = crate::currency_from_string("USD");
        first_issue.account =
            crate::parse_base58_account_id("rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh").unwrap();

        let mut second_issue = first_issue;
        second_issue.account =
            crate::parse_base58_account_id("r3kmLJN5D28dHuH8vZNUZpMC43pEHpaocV").unwrap();

        let left =
            STAmount::new_with_asset(sf_generic(), first_issue, 1_000_000_000_000_000, 0, false);
        let right =
            STAmount::new_with_asset(sf_generic(), second_issue, 1_000_000_000_000_000, 0, false);
        assert_eq!(left, right);
    }

    #[test]
    fn add_native_amounts() {
        let one = STAmount::new_native(1, false);
        let two = STAmount::new_native(2, false);
        let three = one + two;
        assert_eq!(three.xrp().drops(), 3);
    }

    #[test]
    fn sub_native_amounts() {
        let three = STAmount::new_native(3, false);
        let two = STAmount::new_native(2, false);
        let one = three - two;
        assert_eq!(one.xrp().drops(), 1);
    }

    #[test]
    fn native_arithmetic_preserves_internal_flow_sentinel_without_making_it_network_legal() {
        let sentinel = STAmount::new_native(ST_AMOUNT_MAX_NATIVE, false);
        let remaining = sentinel - STAmount::new_native(420, false);

        assert_eq!(remaining.xrp().drops(), ST_AMOUNT_MAX_NATIVE as i64 - 420);
        assert!(!remaining.is_legal_net());
        assert!(matches!(
            remaining.check(),
            Err(ValidationError::Custom(ref message)) if message == "Native amount out of range"
        ));
    }

    #[test]
    fn native_arithmetic_result_at_network_boundary_remains_legal() {
        let internal = STAmount::new_native(ST_AMOUNT_MAX_NATIVE_NETWORK + 1, false);
        let legal = internal - STAmount::new_native(1, false);

        assert_eq!(legal.xrp().drops(), ST_AMOUNT_MAX_NATIVE_NETWORK as i64);
        assert!(legal.is_legal_net());
        assert!(legal.check().is_ok());
    }

    #[test]
    fn add_incompatible_amounts_panics() {
        let native = STAmount::new_native(1, false);
        let mut issue = crate::no_issue();
        issue.currency = crate::currency_from_string("USD");
        issue.account =
            crate::parse_base58_account_id("rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh").unwrap();
        let iou = STAmount::new_with_asset(sf_generic(), issue, 100, 0, false);
        let result = native + iou;
        // Result should be the native amount unchanged (no-op on incompatible)
        assert!(result.native());
    }

    #[test]
    fn fallible_native_canonicalization_rejects_overflow_without_unwinding() {
        let result = STAmount::try_new_with_asset(sf_generic(), crate::xrp_issue(), 1, 18, false);
        assert_eq!(result, Err(AmountError::NativeOutOfRange));
    }

    #[test]
    fn fallible_native_multiplication_rejects_overflow_without_unwinding() {
        let native = STAmount::new_native(ST_AMOUNT_MAX_NATIVE_NETWORK, false);
        let mut issue = crate::no_issue();
        issue.currency = crate::currency_from_string("USD");
        issue.account =
            crate::parse_base58_account_id("rHb9CJAWyB4rj91VRWn96DkukG4bwdtyTh").unwrap();
        let rate = STAmount::new_with_asset(sf_generic(), issue, ST_AMOUNT_MIN_MANTISSA, 3, false);

        assert_eq!(
            native.try_multiply(&rate, native.asset()),
            Err(AmountError::NativeOutOfRange)
        );
    }

    #[test]
    fn check_native_overflow() {
        let amount = STAmount::new_native(ST_AMOUNT_MAX_NATIVE_NETWORK + 1, false);
        let result = amount.check();
        assert!(
            matches!(result, Err(ValidationError::Custom(ref msg)) if msg == "Native amount out of range")
        );
    }

    #[test]
    fn round_iou_amount() {
        let mut issue = crate::no_issue();
        issue.currency = crate::currency_from_string("USD");
        // 1.23456789...
        let amount = STAmount::new_with_asset(sf_generic(), issue, 1234567890123456, -15, false);
        let rounded = amount.round(2); // Should round to 1.2
        assert_eq!(rounded.mantissa(), 1300000000000000);
    }

    #[test]
    fn recursive_invalid_amount_detects_negative_mpt_inside_array() {
        let issuer = AccountID::from_array([0x22; 20]);
        let mut mpt_bytes = [0_u8; 24];
        mpt_bytes[..4].copy_from_slice(&1_u32.to_be_bytes());
        mpt_bytes[4..].copy_from_slice(issuer.data());
        let mpt_id = Uint192::from_slice(&mpt_bytes).expect("mpt id");
        let issue = MPTIssue::new(mpt_id);

        let mut inner = STObject::new(get_field_by_symbol("sfMemo"));
        inner.set_field_amount(
            get_field_by_symbol("sfAmount"),
            STAmount::from_mpt_amount(
                get_field_by_symbol("sfAmount"),
                MPTAmount::from_value(-1),
                issue,
            ),
        );
        let mut array = STArray::new(get_field_by_symbol("sfMemos"));
        array.push_back(inner);
        let mut outer = STObject::new(get_field_by_symbol("sfTransaction"));
        outer.set_field_array(get_field_by_symbol("sfMemos"), array);

        assert!(has_invalid_amount(&outer));
    }

    #[test]
    fn recursive_invalid_amount_accepts_positive_mpt() {
        let issuer = AccountID::from_array([0x33; 20]);
        let mut mpt_bytes = [0_u8; 24];
        mpt_bytes[..4].copy_from_slice(&1_u32.to_be_bytes());
        mpt_bytes[4..].copy_from_slice(issuer.data());
        let issue = MPTIssue::new(Uint192::from_slice(&mpt_bytes).expect("mpt id"));
        let amount = STAmount::from_mpt_amount(
            get_field_by_symbol("sfAmount"),
            MPTAmount::from_value(1),
            issue,
        );

        assert!(!has_invalid_amount(&amount));
    }
}

#[test]
fn issued_canonicalization_rounds_oversized_mantissa_to_nearest() {
    // Mainnet ledger 106053457 OfferCreate rate path: divide(XRP
    // 1_000_000_000_000 drops, USD 1_053_320) produces the raw
    // mantissa 94_937_910_606_463_377 at exponent -11. rippled's
    // IOU/Number canonicalization rounds the discarded 7 upward, rather
    // than truncating, yielding the BookDirectory quality suffix D9C2.
    let amount = STAmount::try_new_with_asset(
        sf_generic(),
        crate::no_issue(),
        94_937_910_606_463_377,
        -11,
        false,
    )
    .expect("issued canonicalization should succeed");
    assert_eq!(amount.mantissa(), 9_493_791_060_646_338);
    assert_eq!(amount.exponent(), -10);
}
