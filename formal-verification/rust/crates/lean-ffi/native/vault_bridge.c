#include "vault_bridge.h"

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

_Static_assert(sizeof(lean_vault_number) == 24, "Vault Number ABI size");
_Static_assert(_Alignof(lean_vault_number) == 8, "Vault Number ABI alignment");
_Static_assert(offsetof(lean_vault_number, negative) == 0, "Vault Number negative");
_Static_assert(offsetof(lean_vault_number, mantissa) == 8, "Vault Number mantissa");
_Static_assert(offsetof(lean_vault_number, exponent) == 16, "Vault Number exponent");
_Static_assert(sizeof(lean_vault_amount) == 32, "Vault STAmount ABI size");
_Static_assert(_Alignof(lean_vault_amount) == 8, "Vault STAmount ABI alignment");
_Static_assert(offsetof(lean_vault_amount, numeric_tag) == 0, "Vault STAmount type");
_Static_assert(offsetof(lean_vault_amount, mantissa) == 8, "Vault STAmount mantissa");
_Static_assert(offsetof(lean_vault_amount, exponent) == 16, "Vault STAmount exponent");
_Static_assert(offsetof(lean_vault_amount, negative) == 24, "Vault STAmount negative");
_Static_assert(sizeof(lean_vault_fields) == 144, "Vault fields ABI size");
_Static_assert(_Alignof(lean_vault_fields) == 8, "Vault fields ABI alignment");

extern lean_object *initialize_XRPL_XRPL_FFI_Vault_Wire(uint8_t);
extern lean_object *initialize_XRPL_XRPL_FFI_Vault_Vault(uint8_t);
extern lean_object *initialize_XRPL_XRPL_FFI_Vault_VaultDeposit(uint8_t);
extern lean_object *initialize_XRPL_XRPL_FFI_Vault_VaultWithdraw(uint8_t);
extern lean_object *initialize_XRPL_XRPL_FFI_Vault_VaultClawback(uint8_t);
extern lean_object *initialize_XRPL_XRPL_FFI_Vault_VaultBurn(uint8_t);
extern lean_object *initialize_XRPL_XRPL_FFI_Vault_VaultDelete(uint8_t);
extern lean_object *initialize_XRPL_XRPL_FFI_Vault_VaultSet(uint8_t);
extern lean_object *lean_number_build_norm(uint8_t, uint64_t, uint64_t);
extern lean_object *lean_numeric_type_build(uint8_t);
extern lean_object *lean_st_amount_build(lean_object *, uint64_t, uint64_t, uint8_t);
extern lean_object *lean_vault_build_raw(lean_object *, lean_object *, lean_object *, lean_object *, uint8_t, lean_object *, lean_object *);
extern lean_object *lean_vault_build(lean_object *, lean_object *, lean_object *, lean_object *, uint8_t, lean_object *, lean_object *);
extern lean_object *lean_vault_assets_total(lean_object *);
extern lean_object *lean_vault_assets_available(lean_object *);
extern lean_object *lean_vault_assets_maximum(lean_object *);
extern lean_object *lean_vault_numeric_type(lean_object *);
extern uint8_t lean_vault_numeric_tag(lean_object *);
extern uint8_t lean_vault_scale(lean_object *);
extern lean_object *lean_vault_shares_total(lean_object *);
extern lean_object *lean_vault_loss_unrealized(lean_object *);
extern lean_object *lean_rounded_deposit_amount(lean_object *, lean_object *);
extern lean_object *lean_rounded_deposit_result_amount(lean_object *);
extern lean_object *lean_rounded_deposit_result_code(lean_object *);
extern uint8_t lean_vault_is_insolvent(lean_object *);
extern lean_object *lean_vault_deposit(lean_object *, lean_object *, uint8_t);
extern lean_object *lean_deposit_result_amount(lean_object *);
extern lean_object *lean_deposit_result_shares(lean_object *);
extern lean_object *lean_deposit_result_vault(lean_object *);
extern lean_object *lean_deposit_result_error(lean_object *);
extern lean_object *lean_shares_to_assets_withdraw(lean_object *, lean_object *, uint8_t);
extern lean_object *lean_mk_withdraw_amount(lean_object *, uint8_t);
extern lean_object *lean_vault_withdraw(lean_object *, lean_object *, uint8_t);
extern lean_object *lean_withdraw_result_assets(lean_object *);
extern lean_object *lean_withdraw_result_shares(lean_object *);
extern lean_object *lean_withdraw_result_vault(lean_object *);
extern lean_object *lean_withdraw_result_error(lean_object *);
extern lean_object *lean_vault_clawback(lean_object *, lean_object *, lean_object *);
extern lean_object *lean_clawback_result_assets(lean_object *);
extern lean_object *lean_clawback_result_shares(lean_object *);
extern lean_object *lean_clawback_result_vault(lean_object *);
extern lean_object *lean_clawback_result_error(lean_object *);
extern lean_object *lean_vault_burn_shares_raw(lean_object *, lean_object *);
extern lean_object *lean_vault_burn_shares(lean_object *, lean_object *);
extern lean_object *lean_can_burn_shares(lean_object *);
extern lean_object *lean_can_burn_result_assets(lean_object *);
extern lean_object *lean_can_burn_result_code(lean_object *);
extern int32_t lean_can_vault_delete(lean_object *);
extern int32_t lean_can_vault_set(lean_object *, lean_object *);
extern lean_object *lean_st_amount_numeric_type(lean_object *);
extern uint64_t lean_st_amount_mantissa(lean_object *);
extern uint64_t lean_st_amount_offset(lean_object *);
extern uint8_t lean_st_amount_negative(lean_object *);
extern uint8_t lean_number_negative(lean_object *);
extern uint64_t lean_number_mantissa(lean_object *);
extern uint64_t lean_number_exponent(lean_object *);

static lean_object *retain(lean_object *value) { lean_inc_ref(value); return value; }
static lean_object *number(uint64_t value) { return lean_number_build_norm(0, value, 0); }
static lean_object *amount(uint64_t value, uint8_t tag) {
  return lean_st_amount_build(lean_numeric_type_build(tag), value, 0, 0);
}

static lean_object *take_ok(lean_object *result) {
  lean_object *value;
  if (lean_obj_tag(result) != 1) { lean_dec(result); return NULL; }
  value = lean_ctor_get(result, 0);
  lean_inc_ref(value);
  lean_dec(result);
  return value;
}

static lean_object *option_number(uint64_t present, uint64_t value) {
  lean_object *option;
  if (!present) return lean_box(0);
  option = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(option, 0, number(value));
  return option;
}

static lean_object *build_full(uint64_t total, uint64_t available, uint64_t maximum_present,
                               uint64_t maximum, uint8_t numeric, uint8_t scale,
                               uint64_t shares, uint64_t loss) {
  return take_ok(lean_vault_build(number(total), number(available),
                                 option_number(maximum_present, maximum),
                                 lean_numeric_type_build(numeric), scale,
                                 number(shares), number(loss)));
}

static lean_object *build(uint64_t total, uint64_t available, uint64_t shares, uint64_t loss) {
  return build_full(total, available, 0, 0, 0, 0, shares, loss);
}

static int initialized(lean_object *result) {
  if (lean_io_result_is_error(result)) { lean_dec(result); return 0; }
  lean_dec_ref(result);
  return 1;
}

static uint64_t numeric_tag(lean_object *owned) {
  uint64_t tag = lean_is_scalar(owned) ? 2 :
    (lean_ctor_get_uint64(owned, sizeof(void *)) == UINT64_C(100000000000000000) ? 0 : 1);
  lean_dec(owned);
  return tag;
}

static void read_number(lean_object *owned, lean_vault_number *out) {
  out->negative = lean_number_negative(retain(owned));
  out->mantissa = lean_number_mantissa(retain(owned));
  out->exponent = (int64_t)lean_number_exponent(owned);
}

static void read_amount(lean_object *owned, lean_vault_amount *out) {
  out->numeric_tag = numeric_tag(lean_st_amount_numeric_type(retain(owned)));
  out->mantissa = lean_st_amount_mantissa(retain(owned));
  out->exponent = (int64_t)lean_st_amount_offset(retain(owned));
  out->negative = lean_st_amount_negative(owned);
}

int lean_vault_initialize(void) {
  return initialized(initialize_XRPL_XRPL_FFI_Vault_Wire(1)) &&
         initialized(initialize_XRPL_XRPL_FFI_Vault_Vault(1)) &&
         initialized(initialize_XRPL_XRPL_FFI_Vault_VaultDeposit(1)) &&
         initialized(initialize_XRPL_XRPL_FFI_Vault_VaultWithdraw(1)) &&
         initialized(initialize_XRPL_XRPL_FFI_Vault_VaultClawback(1)) &&
         initialized(initialize_XRPL_XRPL_FFI_Vault_VaultBurn(1)) &&
         initialized(initialize_XRPL_XRPL_FFI_Vault_VaultDelete(1)) &&
         initialized(initialize_XRPL_XRPL_FFI_Vault_VaultSet(1));
}

int lean_vault_fields_projection_full(uint64_t total, uint64_t available,
                                      uint64_t maximum_present, uint64_t maximum,
                                      uint8_t numeric, uint8_t scale,
                                      uint64_t shares, uint64_t loss,
                                      lean_vault_fields *out) {
  lean_object *value = build_full(total, available, maximum_present, maximum,
                                  numeric, scale, shares, loss);
  lean_object *maximum_value;
  if (value == NULL) return 0;
  read_number(lean_vault_assets_total(retain(value)), &out->total);
  read_number(lean_vault_assets_available(retain(value)), &out->available);
  maximum_value = lean_vault_assets_maximum(retain(value));
  out->maximum_present = lean_obj_tag(maximum_value) != 0;
  if (out->maximum_present) {
    read_number(retain(lean_ctor_get(maximum_value, 0)), &out->maximum);
  } else {
    out->maximum.negative = 0;
    out->maximum.mantissa = 0;
    out->maximum.exponent = 0;
  }
  lean_dec(maximum_value);
  out->numeric_tag = numeric_tag(lean_vault_numeric_type(retain(value)));
  if (out->numeric_tag != lean_vault_numeric_tag(retain(value))) { lean_dec(value); return 0; }
  out->scale = lean_vault_scale(retain(value));
  read_number(lean_vault_shares_total(retain(value)), &out->shares);
  read_number(lean_vault_loss_unrealized(value), &out->loss);
  return 1;
}

int lean_vault_fields_projection(uint64_t total, uint64_t available, uint64_t shares,
                                 uint64_t loss, lean_vault_fields *out) {
  return lean_vault_fields_projection_full(total, available, 0, 0, 0, 0,
                                           shares, loss, out);
}

int lean_vault_insolvent_projection(uint64_t total, uint64_t shares) {
  lean_object *value = build(total, total, shares, 0);
  return value == NULL ? -1 : lean_vault_is_insolvent(value);
}

int lean_vault_withdraw_projection(uint64_t total, uint64_t loss, uint64_t shares_total,
                                   uint64_t shares, uint8_t waive, lean_vault_amount *out) {
  lean_object *value;
  lean_object *result;
  if (loss > total) return 0;
  value = build(total, total - loss, shares_total, loss);
  if (value == NULL) return 0;
  result = take_ok(lean_shares_to_assets_withdraw(value, amount(shares, 1), waive));
  if (result == NULL) return 0;
  read_amount(result, out);
  return 1;
}
