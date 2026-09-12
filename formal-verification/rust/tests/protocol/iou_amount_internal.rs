use protocol::st_number::{get_st_number_switchover, set_st_number_switchover};

use protocol::IOUAmount;

#[test]
fn addition_uses_pinned_number_path_independent_of_stnumber_wire_switch() {
    let saved = get_st_number_switchover();
    let value = IOUAmount::from_parts(9_750_144_547_690_000, -13).unwrap();
    let reference = IOUAmount::from_parts(1_000_000_000_000_000, -9).unwrap();

    set_st_number_switchover(false);
    let legacy_flag_result = value + reference - reference;
    set_st_number_switchover(true);
    let universal_flag_result = value + reference - reference;
    set_st_number_switchover(saved);

    assert_eq!(legacy_flag_result, value);
    assert_eq!(universal_flag_result, value);
}
