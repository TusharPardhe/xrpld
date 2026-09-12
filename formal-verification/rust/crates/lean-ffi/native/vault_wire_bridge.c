#include "vault_bridge.h"
#include <lean/lean.h>
#include <stdlib.h>

typedef lean_object *(*vault_wire_fn)(lean_object *);
#define WIRE(name) extern lean_object *name(lean_object *);
WIRE(lean_vault_raw_build_wire) WIRE(lean_vault_build_wire)
WIRE(lean_vault_round_deposit_wire) WIRE(lean_vault_deposit_wire)
WIRE(lean_vault_shares_to_assets_withdraw_wire) WIRE(lean_vault_withdraw_wire)
WIRE(lean_vault_clawback_wire) WIRE(lean_vault_burn_shares_raw_wire)
WIRE(lean_vault_burn_shares_wire) WIRE(lean_vault_can_burn_shares_wire)
WIRE(lean_vault_can_delete_wire) WIRE(lean_vault_can_set_wire)

static vault_wire_fn const routes[] = {
  lean_vault_raw_build_wire, lean_vault_build_wire,
  lean_vault_round_deposit_wire, lean_vault_deposit_wire,
  lean_vault_shares_to_assets_withdraw_wire, lean_vault_withdraw_wire,
  lean_vault_clawback_wire, lean_vault_burn_shares_raw_wire,
  lean_vault_burn_shares_wire, lean_vault_can_burn_shares_wire,
  lean_vault_can_delete_wire, lean_vault_can_set_wire,
};

static lean_object *bytes_copy(const uint8_t *input, size_t size) {
  lean_object *bytes = lean_mk_empty_byte_array(lean_box(size));
  for (size_t i = 0; i < size; ++i) bytes = lean_byte_array_push(bytes, input[i]);
  return bytes;
}

int lean_vault_wire_invoke(uint32_t operation, const uint8_t *input, size_t input_len,
                           uint8_t **out, size_t *out_len) {
  if (!out || !out_len || operation == 0 || operation > 12 || (!input && input_len)) return 0;
  lean_object *result = routes[operation - 1](bytes_copy(input, input_len));
  size_t size = lean_unbox(lean_byte_array_size(result));
  uint8_t *copy = malloc(size ? size : 1);
  if (!copy) { lean_dec(result); return 0; }
  for (size_t i = 0; i < size; ++i) copy[i] = lean_byte_array_uget(result, i);
  lean_dec(result); *out = copy; *out_len = size; return 1;
}

void lean_vault_wire_free(uint8_t *out) { free(out); }
