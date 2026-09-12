#ifndef VAULT_BRIDGE_H
#define VAULT_BRIDGE_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
  uint8_t negative;
  uint64_t mantissa;
  int64_t exponent;
} lean_vault_number;

typedef struct {
  uint8_t numeric_tag;
  uint64_t mantissa;
  int64_t exponent;
  uint8_t negative;
} lean_vault_amount;

typedef struct {
  lean_vault_number total;
  lean_vault_number available;
  lean_vault_number shares;
  lean_vault_number loss;
  lean_vault_number maximum;
  uint64_t maximum_present;
  uint64_t numeric_tag;
  uint64_t scale;
} lean_vault_fields;

int lean_vault_initialize(void);
int lean_vault_fields_projection(uint64_t total, uint64_t available, uint64_t shares,
                                 uint64_t loss, lean_vault_fields *out);
int lean_vault_fields_projection_full(uint64_t total, uint64_t available,
                                      uint64_t maximum_present, uint64_t maximum,
                                      uint8_t numeric_tag, uint8_t scale,
                                      uint64_t shares, uint64_t loss,
                                      lean_vault_fields *out);
int lean_vault_insolvent_projection(uint64_t total, uint64_t shares);
int lean_vault_complete_adapter(void);
int lean_vault_smoke(void);
int lean_vault_withdraw_projection(uint64_t total, uint64_t loss, uint64_t shares_total,
                                   uint64_t shares, uint8_t waive,
                                   lean_vault_amount *out);

int lean_vault_wire_invoke(uint32_t operation, const uint8_t *input, size_t input_len,
                           uint8_t **out, size_t *out_len);
void lean_vault_wire_free(uint8_t *out);

#endif
