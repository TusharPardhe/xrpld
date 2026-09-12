#include "vault_bridge.h"
#include <lean/lean.h>
#include <stdint.h>

extern lean_object *lean_number_build_norm(uint8_t, uint64_t, uint64_t);
extern lean_object *lean_numeric_type_build(uint8_t);
extern lean_object *lean_st_amount_build(lean_object *, uint64_t, uint64_t, uint8_t);
extern lean_object *lean_vault_build_raw(lean_object *, lean_object *, lean_object *, lean_object *, uint8_t, lean_object *, lean_object *);
extern lean_object *lean_vault_build(lean_object *, lean_object *, lean_object *, lean_object *, uint8_t, lean_object *, lean_object *);
extern lean_object *lean_vault_assets_total(lean_object *); extern lean_object *lean_vault_assets_available(lean_object *);
extern lean_object *lean_vault_assets_maximum(lean_object *); extern lean_object *lean_vault_numeric_type(lean_object *);
extern uint8_t lean_vault_numeric_tag(lean_object *); extern uint8_t lean_vault_scale(lean_object *);
extern lean_object *lean_vault_shares_total(lean_object *); extern lean_object *lean_vault_loss_unrealized(lean_object *);
extern lean_object *lean_rounded_deposit_amount(lean_object *, lean_object *); extern lean_object *lean_rounded_deposit_result_amount(lean_object *); extern lean_object *lean_rounded_deposit_result_code(lean_object *);
extern uint8_t lean_vault_is_insolvent(lean_object *); extern lean_object *lean_vault_deposit(lean_object *, lean_object *, uint8_t);
extern lean_object *lean_deposit_result_amount(lean_object *); extern lean_object *lean_deposit_result_shares(lean_object *); extern lean_object *lean_deposit_result_vault(lean_object *); extern lean_object *lean_deposit_result_error(lean_object *);
extern lean_object *lean_shares_to_assets_withdraw(lean_object *, lean_object *, uint8_t); extern lean_object *lean_mk_withdraw_amount(lean_object *, uint8_t); extern lean_object *lean_vault_withdraw(lean_object *, lean_object *, uint8_t);
extern lean_object *lean_withdraw_result_assets(lean_object *); extern lean_object *lean_withdraw_result_shares(lean_object *); extern lean_object *lean_withdraw_result_vault(lean_object *); extern lean_object *lean_withdraw_result_error(lean_object *);
extern lean_object *lean_vault_clawback(lean_object *, lean_object *, lean_object *); extern lean_object *lean_clawback_result_assets(lean_object *); extern lean_object *lean_clawback_result_shares(lean_object *); extern lean_object *lean_clawback_result_vault(lean_object *); extern lean_object *lean_clawback_result_error(lean_object *);
extern lean_object *lean_vault_burn_shares_raw(lean_object *, lean_object *); extern lean_object *lean_vault_burn_shares(lean_object *, lean_object *); extern lean_object *lean_can_burn_shares(lean_object *); extern lean_object *lean_can_burn_result_assets(lean_object *); extern lean_object *lean_can_burn_result_code(lean_object *); extern int32_t lean_can_vault_delete(lean_object *); extern int32_t lean_can_vault_set(lean_object *, lean_object *);
extern int lean_vault_fields_projection(uint64_t, uint64_t, uint64_t, uint64_t, lean_vault_fields *); extern int lean_vault_insolvent_projection(uint64_t, uint64_t); extern int lean_vault_withdraw_projection(uint64_t, uint64_t, uint64_t, uint64_t, uint8_t, lean_vault_amount *);

static lean_object *retain(lean_object *x) { lean_inc_ref(x); return x; }
static lean_object *number(uint64_t x) { return lean_number_build_norm(0, x, 0); }
static lean_object *amount(uint64_t x, uint8_t tag) { return lean_st_amount_build(lean_numeric_type_build(tag), x, 0, 0); }
static lean_object *take_ok(lean_object *x) { if (lean_obj_tag(x) != 1) { lean_dec(x); return NULL; } lean_object *v = retain(lean_ctor_get(x, 0)); lean_dec(x); return v; }
static lean_object *build(uint64_t total, uint64_t available, uint64_t shares, uint64_t loss) { return take_ok(lean_vault_build(number(total), number(available), lean_box(0), lean_numeric_type_build(0), 0, number(shares), number(loss))); }
#define CALL_OBJ(expr) do { result = (expr); ++calls; lean_dec(result); } while (0)
#define CALL_OK(dst, expr) do { dst = take_ok(expr); ++calls; if (!(dst)) goto failed; } while (0)

int lean_vault_complete_adapter(void) {
  lean_object *raw = NULL, *terminal = NULL, *zero = NULL, *rounded = NULL, *deposit = NULL, *withdraw = NULL, *clawback = NULL, *can_burn = NULL, *result = NULL, *withdraw_amount = NULL; int calls = 0;
  CALL_OK(raw, lean_vault_build_raw(number(100), number(100), lean_box(0), lean_numeric_type_build(0), 0, number(100), number(0))); lean_dec(raw); raw = NULL;
  terminal = build(100, 100, 100, 0); ++calls; if (!terminal) goto failed;
  CALL_OBJ(lean_vault_assets_total(retain(terminal))); CALL_OBJ(lean_vault_assets_available(retain(terminal))); CALL_OBJ(lean_vault_assets_maximum(retain(terminal))); CALL_OBJ(lean_vault_numeric_type(retain(terminal)));
  (void)lean_vault_numeric_tag(retain(terminal)); ++calls; (void)lean_vault_scale(retain(terminal)); ++calls;
  CALL_OBJ(lean_vault_shares_total(retain(terminal))); CALL_OBJ(lean_vault_loss_unrealized(retain(terminal)));
  CALL_OK(rounded, lean_rounded_deposit_amount(retain(terminal), amount(10, 0))); CALL_OBJ(lean_rounded_deposit_result_amount(retain(rounded))); CALL_OBJ(lean_rounded_deposit_result_code(rounded)); rounded = NULL;
  (void)lean_vault_is_insolvent(retain(terminal)); ++calls;
  CALL_OK(deposit, lean_vault_deposit(retain(terminal), amount(10, 0), 0)); CALL_OBJ(lean_deposit_result_amount(retain(deposit))); CALL_OBJ(lean_deposit_result_shares(retain(deposit))); CALL_OBJ(lean_deposit_result_vault(retain(deposit))); CALL_OBJ(lean_deposit_result_error(deposit)); deposit = NULL;
  CALL_OK(result, lean_shares_to_assets_withdraw(retain(terminal), amount(10, 1), 0)); lean_dec(result); result = NULL;
  withdraw_amount = lean_mk_withdraw_amount(amount(10, 1), 1); ++calls; CALL_OK(withdraw, lean_vault_withdraw(retain(terminal), withdraw_amount, 0)); withdraw_amount = NULL;
  CALL_OBJ(lean_withdraw_result_assets(retain(withdraw))); CALL_OBJ(lean_withdraw_result_shares(retain(withdraw))); CALL_OBJ(lean_withdraw_result_vault(retain(withdraw))); CALL_OBJ(lean_withdraw_result_error(withdraw)); withdraw = NULL;
  CALL_OK(clawback, lean_vault_clawback(retain(terminal), amount(10, 0), amount(10, 1))); CALL_OBJ(lean_clawback_result_assets(retain(clawback))); CALL_OBJ(lean_clawback_result_shares(retain(clawback))); CALL_OBJ(lean_clawback_result_vault(retain(clawback))); CALL_OBJ(lean_clawback_result_error(clawback)); clawback = NULL;
  zero = build(0, 0, 100, 0); if (!zero) goto failed;
  CALL_OK(result, lean_vault_burn_shares_raw(retain(zero), amount(10, 1))); lean_dec(result); result = NULL; CALL_OK(result, lean_vault_burn_shares(retain(zero), amount(10, 1))); lean_dec(result); result = NULL;
  CALL_OK(can_burn, lean_can_burn_shares(retain(zero))); CALL_OBJ(lean_can_burn_result_assets(retain(can_burn))); CALL_OBJ(lean_can_burn_result_code(can_burn)); can_burn = NULL;
  (void)lean_can_vault_delete(zero); zero = NULL; ++calls; (void)lean_can_vault_set(terminal, number(100)); terminal = NULL; ++calls;
  return calls == 38 ? calls : 0;
failed: if (raw) lean_dec(raw); if (terminal) lean_dec(terminal); if (zero) lean_dec(zero); if (rounded) lean_dec(rounded); if (deposit) lean_dec(deposit); if (withdraw) lean_dec(withdraw); if (clawback) lean_dec(clawback); if (can_burn) lean_dec(can_burn); if (result) lean_dec(result); if (withdraw_amount) lean_dec(withdraw_amount); return 0;
}
int lean_vault_smoke(void) { lean_vault_fields fields; lean_vault_amount output; return lean_vault_fields_projection(100, 90, 100, 10, &fields) && lean_vault_insolvent_projection(0, 1) == 1 && lean_vault_withdraw_projection(100, 50, 100, 10, 0, &output) && lean_vault_complete_adapter() == 38; }
