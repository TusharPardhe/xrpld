use super::*;

pub(super) fn binary_checks(tag: u8) -> usize {
    let a = amount(0, 7, 0, false);
    let b = amount(0, 3, 0, false);
    let aw = wire(&a, 0);
    let bw = wire(&b, 0);
    same(
        ffi::binary(0, aw, bw, 0, false, tag),
        Ok(a.clone() + b.clone()),
        0,
        None,
    );
    same(
        ffi::binary(1, aw, bw, 0, false, tag),
        Ok(a.clone() - b.clone()),
        0,
        None,
    );
    let i = amount(2, 1_500_000_000_000_000, -15, false);
    let j = amount(2, 2_000_000_000_000_000, -15, false);
    let iw = wire(&i, 2);
    let jw = wire(&j, 2);
    same(
        ffi::binary(2, iw, jw, 2, false, tag),
        i.try_divide(&j, no_issue()),
        2,
        None,
    );
    same(
        ffi::binary(3, iw, jw, 2, false, tag),
        i.try_multiply(&j, no_issue()),
        2,
        None,
    );
    for (op, fun) in [
        (
            4,
            mul_round as fn(&STAmount, &STAmount, Asset, bool) -> STAmount,
        ),
        (5, mul_round_strict),
        (6, div_round),
        (7, div_round_strict),
    ] {
        let expected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            fun(&i, &j, Asset::Issue(no_issue()), true)
        }))
        .unwrap();
        assert_eq!(
            project(ffi::binary(op, iw, jw, 2, true, tag).unwrap()),
            project(wire(&expected, 2))
        );
    }
    assert_eq!(ffi::can(0, aw, bw, tag), Ok(can_add(&a, &b, mode(tag))));
    assert_eq!(ffi::can(1, aw, bw, tag), Ok(can_subtract(&a, &b)));
    same(
        ffi::round(iw, -14, tag),
        round_to_exponent(&i, -14, mode(tag)),
        2,
        None,
    );
    assert_eq!(ffi::rate(iw, jw, tag), get_rate(&i, &j));
    2 + 2 + 4 + 2 + 1 + 1 + crate::stamount_errors::run(tag)
}
