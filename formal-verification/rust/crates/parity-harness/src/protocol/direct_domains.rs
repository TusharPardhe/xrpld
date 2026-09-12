use basics::number::{MantissaScale, NumberParts, RoundingMode, set_rounding_mode};
use protocol::xrp_amount::mul_ratio;
use protocol::{IOUAmount, MPTAmount, STAmount, XRPAmount};

pub fn run() {
    let n = NumberParts::try_from_external_parts(1, 0, MantissaScale::Large330).unwrap();
    set_rounding_mode(RoundingMode::ToNearest);
    let iou = IOUAmount::from_number(n).unwrap();
    assert_eq!(iou.mantissa(), 1_000_000_000_000_000);
    assert_eq!(IOUAmount::from_number(n).unwrap(), iou);
    assert_eq!(XRPAmount::from_number(n).unwrap().drops(), 1);
    assert_eq!(MPTAmount::from_number(n).unwrap().value(), 1);
    assert_eq!(
        mul_ratio(XRPAmount::from_drops(-5), 1, 2, false)
            .unwrap()
            .drops(),
        -3
    );
    assert_eq!(
        protocol::mpt_amount::mul_ratio(MPTAmount::from_value(5), 1, 2, true)
            .unwrap()
            .value(),
        3
    );
    let native = STAmount::new_native(5, false);
    assert_eq!(
        (native.clone() + STAmount::new_native(7, false))
            .xrp()
            .drops(),
        12
    );
    assert!(native.native());
}
