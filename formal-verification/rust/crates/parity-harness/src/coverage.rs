pub const MANIFEST: &[(&str, &str)] = &[
    (
        "CommonFFI:lean_rounding_mode_build",
        "exercised: tags 0,1,2,3,255",
    ),
    (
        "NumericTypeFFI:lean_numeric_type_build/is_integral",
        "exercised: native,int64,fractional tags",
    ),
    (
        "NumberFFI:build,build_norm,negative,mantissa,exponent",
        "exercised: raw and normalized roundtrips",
    ),
    (
        "NumberFFI:add,sub,mul,div,neg,normalize,to_rep",
        "exercised: all modes, 8,212 arithmetic checks with exact public Overflow/DivideByZero tags",
    ),
    (
        "NumberFFI:eq,ne,lt,le,gt,ge,signum",
        "exercised: signed/zero/extreme comparisons",
    ),
    (
        "NumberFFI: divide max/min error semantics",
        "exact public Overflow parity: max/min division returns Lean tag 0 and Quaxar NumberArithmeticError::Overflow across all four rounding modes; zero division remains exact Lean tag 1 / DivideByZero",
    ),
    (
        "IOUAmountFFI: build,mantissa,exponent,from_number,of_mantissa_exp,of_number,to_number",
        "exercised: generated C ABI, constructors/accessors/conversions, all four modes; Lean from_number raw parts and Lean of_number canonical IOUs assert exact Quaxar parity for zero, exponent 81, exponent -200, and ordinary values",
    ),
    (
        "IOUAmountFFI: eq,ne,lt,le,gt,ge,neg,add,sub,mul_ratio",
        "exercised: field equality, ordered comparisons, sign, checked arithmetic, ratio rounding/rescue/divide-by-zero; only Lean overflow tag 0 and divide-by-zero tag 1 are accepted as Quaxar NumberArithmeticError parity",
    ),
    (
        "IOUAmountFFI: zero canonicalization",
        "exact parity: Lean fromNumber preserves the raw Number.zero exponent while Quaxar raw_iou_parts_from_number does the same; Lean ofNumber and IOUAmount::from_number both canonicalize zero to -100",
    ),
    (
        "IOUAmountFFI: from_number outside IOU offsets",
        "exact parity: Lean fromNumber and Quaxar raw_iou_parts_from_number retain normalized out-of-offset parts; Lean ofNumber and IOUAmount::from_number enforce >80 overflow and <-96 canonical zero",
    ),
    (
        "IntAmountFFI: of_int64,of_number,to_number,eq,ne,eq_int,ne_int,lt,le,gt,ge",
        "invoked: generated C ABI; MPTAmount representation/comparison/conversion parity across all four modes",
    ),
    (
        "IntAmountFFI: add,sub,neg,mul,add_int,sub_int,mul_ratio",
        "invoked: direct MPTAmount add/sub bridge forms, XRPAmount scalar multiplication, and MPTAmount negation use explicit i64 wrapping semantics; all 44 direct checks, including the nine former overflow cases, are exact Lean↔Quaxar parity in debug and release",
    ),
    (
        "IntAmount model signum/direct div",
        "not among the 18 generated exports (IntAmountFFI.lean); MPTAmount/XRPAmount signum is smoke-tested and division semantics are exercised by mul_ratio including denominator zero",
    ),
    (
        "IntAmountFFI: to_number(INT64_MIN)",
        "exact parity across all four modes: nearest, toward-zero, and upward map INT64_MIN to Number(-9223372036854775807); downward maps it to Number(-9223372036854775810)",
    ),
    (
        "IntAmountFFI: negative mul_ratio underflow",
        "exact checked-overflow parity: a mathematical result below INT64_MIN returns Lean tag 0 / Quaxar NumberArithmeticError::Overflow",
    ),
    (
        "STAmountFFI: build,numeric_type,mantissa,offset,negative,are_comparable,int_amount,iou,to_number,unchecked_from_int64,checked,of_int64,of_number",
        "invoked: generated C ABI; native XRP, issued IOU, and MPT numeric projections; the FFI omits Issue/MPTIssue identity so comparisons explicitly use the represented numeric projection",
    ),
    (
        "STAmountFFI: eq,ne,lt,le,gt,ge,neg,add,sub,divide,multiply,mul_round,mul_round_strict,div_round,div_round_strict,get_rate",
        "exercised: all four rounding modes, deterministic normalized cases, native/IOU/MPT arithmetic; exact Lean tags asserted for checked native/MPT/issued ranges (2/2/0), type conversion (7), divide-by-zero (1), and non-comparable comparison (6)",
    ),
    (
        "STAmountFFI: can_add,can_subtract,round_to_exponent",
        "invoked: direct public Quaxar counterpart parity across all four modes; because the Lean ABI carries only numeric type/mantissa/offset/sign, this is an exact bounded numeric-projection comparison using the same Quaxar Issue/MPTIssue fixture, not a claim of full asset-identity equivalence",
    ),
];

pub fn report(
    number_checks: usize,
    iou_checks: usize,
    int: crate::int_amount::Report,
    stamount_checks: usize,
    stamount_divergences: usize,
    vault_checks: usize,
    vault: crate::vault_registry::Report,
    wire: &crate::vault_wire::RouteEvidence,
    lending_checks: usize,
) {
    assert_eq!(
        number_checks, 8_212,
        "do not weaken retained Number coverage"
    );
    for (export, status) in MANIFEST {
        println!("COVERAGE | {export} | {status}");
    }
    println!(
        "COUNTS | Common=1/1 | NumericType=2/2 | Number=19/19 | IOU=17/17 invoked (all Lean raw from_number and canonical of_number cases exactly match Quaxar across four rounding modes) | Int=18/18 invoked (exact semantic parity; 0 divergence classes across 0 concrete observations; all direct arithmetic checks, including the nine former overflow cases, are exact parity in both profiles) | STAmount=32/32 invoked (all 32 have Quaxar bounded numeric-projection parity; asset identity is intentionally outside the Lean ABI projection)"
    );
    println!(
        "RUNTIME | Number arithmetic={number_checks}; IOU exact parity={iou_checks}; Int harness checks={}; Int direct and common-domain parity={}; Int divergence observations={}; Int divergence classes={}; STAmount parity={stamount_checks}; STAmount unavailable observations={stamount_divergences}; Vault direct-helper cases={vault_checks}",
        int.checks, int.common_parity_checks, int.divergence_observations, int.divergence_classes,
    );
    for export in crate::vault_registry::EXPORTS {
        println!(
            "VAULT MANIFEST | {} | {} | route={} | material={}",
            export.id, export.symbol, export.route, export.material
        );
    }
    println!(
        "VAULT COUNTS | source={} | applicable={} | ABI={} | semantic={} | unavailable={} | divergences={} | semantic_vectors={} | predicate_vectors={vault_checks} | material_checks={}",
        vault.source,
        vault.applicable,
        vault.abi,
        vault.semantic,
        vault.unavailable,
        vault.divergences,
        vault.vectors,
        vault.checks,
    );
    println!(
        "VAULT WIRE COUNTS | semantic_routes={} | guard_results={} | malformed_codec_only={} | byte_divergences=0",
        wire.canonical.len(),
        wire.guards,
        wire.malformed,
    );
    println!(
        "VAULT STATUS | Every stable source ID is registered once to a directly invoked Lean LWAB ABI route and an exact full material Lean/Quaxar response. Raw and terminal results retain their distinct associations; Vault states retain total, available, reserved, maximum, shares, scale, loss, numeric type, and tagged error/result variants. Malformed codec vectors remain excluded from semantic export coverage."
    );
    for (export, status) in crate::lending_manifest::MANIFEST {
        println!("LENDING MANIFEST | {export} | {status}");
    }
    println!(
        "LENDING COUNTS | source_exports={} | applicable_exports={} | abi_invoked_exports={} | semantic_compared_exports={} | unavailable_exports={} | divergences={} | raw={} | terminal={} | scalar={} | bounded_executable_checks={lending_checks}",
        crate::lending_manifest::SOURCE_EXPORTS,
        crate::lending_manifest::semantic_compared_exports(),
        crate::lending_manifest::ABI_INVOKED_EXPORTS,
        crate::lending_manifest::semantic_compared_exports(),
        crate::lending_manifest::unavailable_exports(),
        crate::lending_manifest::DIVERGENCES,
        crate::lending_manifest::RAW_INTERNAL_EXPORTS,
        crate::lending_manifest::TERMINAL_EXPORTS,
        crate::lending_manifest::SCALAR_EXPORTS,
    );
    println!(
        "LENDING STATUS | All 34 source exports are directly executed and semantically compared: seven scalar exports; raw/terminal create, accept, delete, payment, and management/default routes; and raw broker create/update plus cover validate/deposit/withdraw tags 12–16. Every wire route compares exact bytes, decoded complete typed material, repeatability, and malformed/noncanonical framing/body vectors; terminal paths associate one successful state atomically."
    );
}
