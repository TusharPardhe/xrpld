# Lending transition parity manifest

**Created:** 2026-09-12. This is the initial, absolute-path ownership and schema map for genuine LWAB transition parity. It records the actual baseline: 34 Lean exports; seven scalar Lean↔Quaxar comparisons; 16 raw and 11 terminal routes currently ABI/Lean-codec checked only.

## Authoritative paths

- Lean repository: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification`
- Lean formal root: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification`
- Wire schema and route definitions: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/FFI/Lending/Wire/Transitions.lean`
- Request/response schemas: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/FFI/Lending/Wire/{LoanState,VaultBroker}.lean`
- Quaxar lossless core: `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpld/ledger/src/domain/lending_adapter/{model,core,operations}.rs`
- Quaxar LWAB target (not yet present): `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpld/ledger/src/domain/lending_adapter/lwab.rs`
- Bridge: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke/src/{lending,lending_wire,lending_manifest}.rs`

## Shared request schemas

| Schema | Exact fields |
|---|---|
| `CreateRequest` | `VaultIdentity, LoanIdentity, Vault, LoanBroker, Number principal, LoanRates, LoanFees, LoanSchedule, Bool allowsOverpayment, Bool pending` |
| `LoanVaultRequest` | `Loan, Vault` |
| `BrokerRequest` | `Loan, Vault, LoanBroker` |
| `PaymentRequest` | `BrokerRequest, LoanPaymentType, Number amount, UInt32 now` |
| `AmountRequest` | `BrokerRequest, Number amount, UInt32 now` |
| `DefaultRequest` | `BrokerRequest, Bool impaired` |
| `BrokerCreateRequest` | `BrokerIdentity, Option Number debtMaximum, Option UInt16 managementFeeRate, Option UInt32 coverRateMinimum, Option UInt32 coverRateLiquidation` |
| `BrokerUpdateRequest` | `LoanBroker, Option Number debtMaximum` |
| `CoverRequest` | `LoanBroker, NumericType, STAmount` |
| `CoverValidateRequest` | `NumericType, Number coverAvailable, STAmount` |

Responses are always LWAB v1 response tag `128 + request tag`, outer decode-error-or-value frame, and then the full typed model result: `LendingState` (1–3, 6–8, 17–19, 22–24), `LoanVault` (4,20), `BrokerVault` (5,11,21,27), `Vault` (9,10,25,26), `LoanBroker` (12,13), TER (14), or cover result (15,16).

## Exact transition routes and ownership

| Tag | Lean export | Request | Raw operation / terminal form | Quaxar group |
|---:|---|---|---|---|
| 1 | `lean_lending_raw_create_wire` | Create | `Loan.create` | raw 1–8 |
| 2 | `lean_lending_raw_create_pending_wire` | Create | `Loan.createPending` | raw 1–8 |
| 3 | `lean_lending_raw_create_immediate_wire` | Create | `Loan.createImmediate` | raw 1–8 |
| 4 | `lean_lending_raw_accept_wire` | LoanVault | `Loan.accept` | raw 1–8 |
| 5 | `lean_lending_raw_delete_wire` | Broker | `Loan.delete` | raw 1–8 |
| 6 | `lean_lending_raw_regular_payment_wire` | Payment | `Loan.regularPayment` | raw 1–8 |
| 7 | `lean_lending_raw_late_payment_wire` | Amount | `Loan.latePayment` | raw 1–8 |
| 8 | `lean_lending_raw_full_payment_wire` | Amount | `Loan.fullPayment` | raw 1–8 |
| 9 | `lean_lending_raw_manage_impair_wire` | LoanVault | `Loan.manageImpair` | raw 9–16 |
| 10 | `lean_lending_raw_manage_unimpair_wire` | LoanVault | `Loan.manageUnimpaired` | raw 9–16 |
| 11 | `lean_lending_raw_manage_default_wire` | Default | `Loan.manageDefault` | raw 9–16 |
| 12 | `lean_lending_raw_broker_create_wire` | BrokerCreate | `LoanBroker.create` | raw 9–16 |
| 13 | `lean_lending_raw_broker_update_wire` | BrokerUpdate | `LoanBroker.update` | raw 9–16 |
| 14 | `lean_lending_raw_cover_validate_wire` | CoverValidate | `canApplyToBrokerCover` | raw 9–16 |
| 15 | `lean_lending_raw_cover_deposit_wire` | Cover | `LoanBroker.coverDeposit` | raw 9–16 |
| 16 | `lean_lending_raw_cover_withdraw_wire` | Cover | `LoanBroker.coverWithdraw` | raw 9–16 |
| 17–27 | `lean_lending_terminal_*_wire` | same as 1–11 | matching raw operation, then exactly one Vault association | terminal 17–27 |

## Non-negotiable integration checks

1. Quaxar must decode the canonical request bytes into its `ledger::lending_adapter::lossless` full `NumberParts`, `STAmount`, `Vault`, `Loan`, `Broker`, and `LendingState` records—not local `i64` projections or bridge-only records.
2. The dispatcher must encode every full success, `LoanResult`/TER rejection, and model error into the same bytes as Lean. Malformed input remains codec-only and must not increase semantic coverage.
3. Terminal routes must apply the raw semantic result first and then perform exactly one association atomically; raw rejection or association overflow leaves the raw state uncommitted.
4. Bridge vectors must invoke both Lean C and Quaxar with the identical canonical request bytes and compare exact response bytes plus decoded full material fields.

## Current evidence

`cargo run --quiet` in `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke` completed on 2026-09-12 with `LENDING COUNTS | source_exports=34 | applicable_exports=7 | abi_invoked_exports=34 | semantic_compared_exports=7 | unavailable_exports=27 | divergences=0`. This is a baseline only; it does **not** establish route parity for tags 1–27.
