use basics::number::{
    MantissaScale, NUMBER_MAX_REP, NUMBER_MAX_REP_UP, NumberMantissaScaleGuard, NumberParts,
    NumberRoundModeGuard, RoundingMode,
};
use protocol::{MPTAmount, XRPAmount};

fn expected(value: i64, mode: RoundingMode) -> NumberParts {
    let mantissa = if value == i64::MIN && mode == RoundingMode::Downward {
        NUMBER_MAX_REP_UP
    } else {
        NUMBER_MAX_REP as u64
    };
    NumberParts::unchecked(value < 0, mantissa, 0)
}

#[test]
fn int_amount_extrema_use_rippled_number_normalization() {
    let _scale = NumberMantissaScaleGuard::new(MantissaScale::Large330);
    let cases = [i64::MIN, i64::MIN + 1, -i64::MAX, i64::MAX];

    for mode in [
        RoundingMode::ToNearest,
        RoundingMode::TowardsZero,
        RoundingMode::Downward,
        RoundingMode::Upward,
    ] {
        let _rounding = NumberRoundModeGuard::new(mode);
        for value in cases {
            let number = expected(value, mode);
            assert_eq!(NumberParts::from(MPTAmount::from(value)), number);
            assert_eq!(NumberParts::from(XRPAmount::from(value)), number);
        }
    }
}
