#ifndef STAMOUNT_BRIDGE_H
#define STAMOUNT_BRIDGE_H
#include <stdint.h>
typedef struct { uint8_t type; uint64_t mantissa; int64_t offset; uint8_t negative; } lean_stamount;
typedef struct { uint8_t negative; uint64_t mantissa; int64_t exponent; } lean_stnumber;
void lean_st_access(lean_stamount, lean_stamount*);
uint8_t lean_st_comparable(lean_stamount, lean_stamount);
int lean_st_int(lean_stamount, int64_t*, uint8_t*);
int lean_st_iou(lean_stamount, uint8_t, int64_t*, int64_t*, uint8_t*);
int lean_st_number(lean_stamount, uint8_t, lean_stnumber*, uint8_t*);
int lean_st_construct(uint8_t, lean_stamount, int64_t, lean_stnumber, uint8_t, lean_stamount*, uint8_t*);
uint8_t lean_st_eq(uint8_t, lean_stamount, lean_stamount);
int lean_st_compare(uint8_t, lean_stamount, lean_stamount, uint8_t*, uint8_t*);
void lean_st_neg(lean_stamount, lean_stamount*);
int lean_st_binary(uint8_t, lean_stamount, lean_stamount, uint8_t, uint8_t, uint8_t, lean_stamount*, uint8_t*);
int lean_st_can(uint8_t, lean_stamount, lean_stamount, uint8_t, uint8_t*, uint8_t*);
int lean_st_round(lean_stamount, int64_t, uint8_t, lean_stamount*, uint8_t*);
uint64_t lean_st_rate(lean_stamount, lean_stamount, uint8_t);
#endif
