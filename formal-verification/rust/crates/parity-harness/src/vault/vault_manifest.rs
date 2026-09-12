//! Authoritative stable-ID Vault export manifest.

use crate::vault_registry::Export;

macro_rules! export {
    ($id:literal, $symbol:literal, $route:literal, $material:literal) => {
        Export {
            id: $id,
            symbol: $symbol,
            route: $route,
            material: $material,
        }
    };
}

/// One source export per row; each route compares its complete material result.
pub const EXPORTS: [Export; 50] = [
    export!("V01", "lean_vault_build_raw", 1, "raw Vault/error"),
    export!("V02", "lean_vault_build", 2, "terminal Vault/error"),
    export!("V03", "lean_vault_assets_total", 2, "terminal total"),
    export!(
        "V04",
        "lean_vault_assets_available",
        2,
        "terminal available"
    ),
    export!(
        "V05",
        "lean_vault_assets_maximum",
        2,
        "terminal maximum option"
    ),
    export!("V06", "lean_vault_numeric_type", 2, "terminal numeric type"),
    export!("V07", "lean_vault_numeric_tag", 2, "terminal numeric tag"),
    export!("V08", "lean_vault_scale", 2, "terminal scale"),
    export!("V09", "lean_vault_shares_total", 2, "terminal shares"),
    export!("V10", "lean_vault_loss_unrealized", 2, "terminal loss"),
    export!(
        "V11",
        "lean_rounded_deposit_amount",
        3,
        "rounding result/error"
    ),
    export!(
        "V12",
        "lean_rounded_deposit_result_amount",
        3,
        "rounded amount"
    ),
    export!("V13", "lean_rounded_deposit_result_code", 3, "rounding TER"),
    export!(
        "V14",
        "lean_vault_is_insolvent",
        2,
        "lawful-state predicate"
    ),
    export!("V15", "lean_vault_deposit", 4, "deposit result/error"),
    export!("V16", "lean_deposit_result_amount", 4, "deposit amount"),
    export!("V17", "lean_deposit_result_shares", 4, "issued shares"),
    export!("V18", "lean_deposit_result_vault", 4, "post-deposit Vault"),
    export!("V19", "lean_deposit_result_error", 4, "deposit TER"),
    export!(
        "V20",
        "lean_shares_to_assets_withdraw",
        5,
        "asset quote/error"
    ),
    export!(
        "V21",
        "lean_mk_withdraw_amount",
        5,
        "asset/share discriminator"
    ),
    export!("V22", "lean_vault_withdraw", 6, "withdraw result/error"),
    export!("V23", "lean_withdraw_result_assets", 6, "withdrawn assets"),
    export!("V24", "lean_withdraw_result_shares", 6, "burned shares"),
    export!(
        "V25",
        "lean_withdraw_result_vault",
        6,
        "post-withdraw Vault"
    ),
    export!("V26", "lean_withdraw_result_error", 6, "withdraw TER"),
    export!("V27", "lean_vault_clawback", 7, "clawback result/error"),
    export!("V28", "lean_clawback_result_assets", 7, "recovered assets"),
    export!("V29", "lean_clawback_result_shares", 7, "destroyed shares"),
    export!(
        "V30",
        "lean_clawback_result_vault",
        7,
        "post-clawback Vault"
    ),
    export!("V31", "lean_clawback_result_error", 7, "clawback TER"),
    export!(
        "V32",
        "lean_vault_burn_shares_raw",
        8,
        "raw post-burn Vault/error"
    ),
    export!(
        "V33",
        "lean_vault_burn_shares",
        9,
        "terminal post-burn Vault/error"
    ),
    export!("V34", "lean_can_burn_shares", 10, "burn decision"),
    export!("V35", "lean_can_burn_result_assets", 10, "burnable shares"),
    export!("V36", "lean_can_burn_result_code", 10, "burn TER"),
    export!("V37", "lean_can_vault_delete", 11, "delete TER"),
    export!("V38", "lean_can_vault_set", 12, "set TER"),
    export!(
        "V39",
        "lean_vault_raw_build_wire",
        1,
        "full raw-build LWAB response"
    ),
    export!(
        "V40",
        "lean_vault_build_wire",
        2,
        "full terminal-build LWAB response"
    ),
    export!(
        "V41",
        "lean_vault_round_deposit_wire",
        3,
        "full rounding LWAB response"
    ),
    export!(
        "V42",
        "lean_vault_deposit_wire",
        4,
        "full deposit LWAB response"
    ),
    export!(
        "V43",
        "lean_vault_shares_to_assets_withdraw_wire",
        5,
        "full share-to-assets LWAB response"
    ),
    export!(
        "V44",
        "lean_vault_withdraw_wire",
        6,
        "full withdrawal LWAB response"
    ),
    export!(
        "V45",
        "lean_vault_clawback_wire",
        7,
        "full clawback LWAB response"
    ),
    export!(
        "V46",
        "lean_vault_burn_shares_raw_wire",
        8,
        "full raw-burn LWAB response"
    ),
    export!(
        "V47",
        "lean_vault_burn_shares_wire",
        9,
        "full terminal-burn LWAB response"
    ),
    export!(
        "V48",
        "lean_vault_can_burn_shares_wire",
        10,
        "full can-burn LWAB response"
    ),
    export!(
        "V49",
        "lean_vault_can_delete_wire",
        11,
        "full can-delete LWAB response"
    ),
    export!(
        "V50",
        "lean_vault_can_set_wire",
        12,
        "full can-set LWAB response"
    ),
];
