# Lending LWAB route manifest

**Authoritative sources:** Lean schema `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/FFI/Lending/Wire/{Primitive,VaultBroker,LoanState,Transitions}.lean`; Quaxar target `/Users/tusharpardhe/Documents/xrpl/quaxar/xrpld/ledger/src/domain/lending_adapter`; bridge `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/quaxar-lean-number-smoke`.

`LWAB/v1`: request tag `t`, response tag `128+t`. Every semantic vector sends the same canonical bytes to Lean C and Quaxar. Decoder-failure vectors are codec-only and do not contribute to semantic IDs.

| Stable ID | Request tag | Response tag | Lean export | Request schema | Response material | Owner |
|---|---:|---:|---|---|---|---|
| L01 | — | — | `lean_lending_has_expired` | `u32,u32,bool` | bool | scalar |
| L02–L07 | — | — | `lean_lending_schedule_*` | `u32,u32,u32,u32,u32,bool` | schedule fields/TER | scalar |
| L08 | 1 | 129 | `raw_create` | Create | Lifecycle<LendingState> | raw 1–8 |
| L09 | 2 | 130 | `raw_create_pending` | Create | Lifecycle<LendingState> | raw 1–8 |
| L10 | 3 | 131 | `raw_create_immediate` | Create | Lifecycle<LendingState> | raw 1–8 |
| L11 | 4 | 132 | `raw_accept` | LoanVault | Lifecycle<LoanVault> | raw 1–8 |
| L12 | 5 | 133 | `raw_delete` | Broker | Lifecycle<BrokerVault> | raw 1–8 |
| L13 | 6 | 134 | `raw_regular_payment` | Payment | Lifecycle<LendingState> | raw 1–8 |
| L14 | 7 | 135 | `raw_late_payment` | Amount | Lifecycle<LendingState> | raw 1–8 |
| L15 | 8 | 136 | `raw_full_payment` | Amount | Lifecycle<LendingState> | raw 1–8 |
| L16 | 9 | 137 | `raw_manage_impair` | LoanVault | Lifecycle<Vault> | raw 9–16 |
| L17 | 10 | 138 | `raw_manage_unimpair` | LoanVault | Lifecycle<Vault> | raw 9–16 |
| L18 | 11 | 139 | `raw_manage_default` | Default | Lifecycle<BrokerVault> | raw 9–16 |
| L19 | 12 | 140 | `raw_broker_create` | BrokerCreate | LoanBroker | raw 9–16 |
| L20 | 13 | 141 | `raw_broker_update` | BrokerUpdate | LoanBroker | raw 9–16 |
| L21 | 14 | 142 | `raw_cover_validate` | CoverValidate | Result<TER,Error> | raw 9–16 |
| L22 | 15 | 143 | `raw_cover_deposit` | Cover | Result<CoverResult,Error> | raw 9–16 |
| L23 | 16 | 144 | `raw_cover_withdraw` | Cover | Result<CoverResult,Error> | raw 9–16 |
| L24 | 17 | 145 | `terminal_create` | Create | Lifecycle<LendingState> | terminal 17–27 |
| L25 | 18 | 146 | `terminal_create_pending` | Create | Lifecycle<LendingState> | terminal 17–27 |
| L26 | 19 | 147 | `terminal_create_immediate` | Create | Lifecycle<LendingState> | terminal 17–27 |
| L27 | 20 | 148 | `terminal_accept` | LoanVault | Lifecycle<LoanVault> | terminal 17–27 |
| L28 | 21 | 149 | `terminal_delete` | Broker | Lifecycle<BrokerVault> | terminal 17–27 |
| L29 | 22 | 150 | `terminal_regular_payment` | Payment | Lifecycle<LendingState> | terminal 17–27 |
| L30 | 23 | 151 | `terminal_late_payment` | Amount | Lifecycle<LendingState> | terminal 17–27 |
| L31 | 24 | 152 | `terminal_full_payment` | Amount | Lifecycle<LendingState> | terminal 17–27 |
| L32 | 25 | 153 | `terminal_manage_impair` | LoanVault | Lifecycle<Vault> | terminal 17–27 |
| L33 | 26 | 154 | `terminal_manage_unimpair` | LoanVault | Lifecycle<Vault> | terminal 17–27 |
| L34 | 27 | 155 | `terminal_manage_default` | Default | Lifecycle<BrokerVault> | terminal 17–27 |

## Exact schemas

- `Number = bool negative, u64 mantissa, i64 exponent`; `STAmount = NumericType,u64 mantissa,i64 exponent,bool negative`; `NumericType = fractional | integral(u64 maximum,i64 offset,u64 sqrt,u64 shift)`.
- `VaultIdentity = ObjectId vault,u64 owner,u64 account,IssueId,LendingConfig(bool,bool,u32),TransactionMetadata(ObjectId,u32,u32)`; `BrokerIdentity = ObjectId broker,ObjectId vault,u64 owner,u64 account`; `LoanIdentity = ObjectId loan,ObjectId broker,u64 borrower,u64 counterparty,IssueId,CredentialAuth(bool,bool,bool),TransactionMetadata`.
- `Vault = Number total,available,reserved,Option<Number> maximum,NumericType,u8 scale,Number shares,loss`; `LoanBroker = BrokerIdentity,u16 managementFee,u32 coverMinimum,u32 coverLiquidation,Number debtTotal,debtMaximum,coverAvailable,u32 loanCount`.
- `Loan = LoanIdentity,VaultIdentity,LoanRates(5×u32),LoanFees(4×Number),LoanSchedule(4×u32),u32 remaining,Number periodic,principal,total,management,i64 scale,u32 previous,next,4×bool`.
- `Create = VaultIdentity,LoanIdentity,Vault,LoanBroker,Number principal,LoanRates,LoanFees,LoanSchedule,bool allowsOverpayment,bool pending`; `LoanVault = Loan,Vault`; `Broker = Loan,Vault,LoanBroker`; `Payment = Broker,PaymentType,Number,u32`; `Amount = Broker,Number,u32`; `Default = Broker,bool`; `BrokerCreate = BrokerIdentity,Option<Number>,Option<u16>,Option<u32>,Option<u32>`; `BrokerUpdate = LoanBroker,Option<Number>`; `Cover = LoanBroker,NumericType,STAmount`; `CoverValidate = NumericType,Number,STAmount`.

Terminal rule for L24–L34: execute its matching raw transition once; on a successful `LoanResult` only, call Vault association once. A raw rejection is returned unchanged. An association failure is an atomic `Error`, so no partially associated output is encoded.

## Executed semantic proof

`L08` / `lean_lending_raw_create_wire` is semantic only after execution: the bridge registers this exact export ID after it sends canonical tag-1 requests to both Lean and `ledger::lending_lwab::dispatch_route(1, input)`. The executed vectors cover immediate and pending success, nonzero-interest amortization, `temINVALID`, both insufficient-funds guards, debt limit, and precision loss. Each compares the complete tag-129 bytes, decoded `Lifecycle<LendingState>` fields, and a repeated Quaxar invocation. It also compares exact decoder-error bytes for malformed magic, version, tag, truncated, oversized length, trailing, boolean, option, numeric-type, and noncanonical inputs. The runtime ID set derives `semantic=8` and `unavailable=26`; malformed cases never add IDs.

## Superseding raw-create execution evidence (2026-09-12)

This supersedes the earlier tag-1-only raw-create note. The bridge executed `L08` tag 1/response 129, `L09` tag 2/response 130, and `L10` tag 3/response 131 in both debug and release. Each tag compared complete Lean/Quaxar bytes, decoded `Lifecycle<LendingState>`, and repeatability for request-pending and request-immediate successes, nonzero interest, invalid identity, both insufficient-funds guards, debt limit, precision loss, malformed magic/version/wrong-tag/truncation/length/trailing frames, and boolean/option/numeric-type/noncanonical decoder errors. Full frame equality preserves each DecodeError offset. Tags 2 and 3 decode the Create `pending` boolean but respectively force `Loan.createPending` (`true`) and `Loan.createImmediate` (`false`); tag 1 retains it. Export IDs were registered only after execution. Observed runtime counts: `semantic=10`, `unavailable=24`, `divergences=0`, `bounded_executable_checks=381`.

Validation used only focused scopes: `cargo test -p ledger lending_lwab --lib` and `--release` (one focused test each), then `cargo run --quiet` and `cargo run --release --quiet` for the bridge. All four commands passed; warnings were pre-existing unused Lending helpers/bridge projections.
