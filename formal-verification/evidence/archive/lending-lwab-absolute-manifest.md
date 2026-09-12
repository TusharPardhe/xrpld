# Lending LWAB absolute-path manifest

**Generated from authoritative sources:**

- Wire schema and route functions: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/FFI/Lending/Wire/Transitions.lean`
- Raw/terminal aliases: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/FFI/Lending/Transitions.lean`
- Raw 9–11 model: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Lending/Loan/LoanManage.lean`
- Raw 12–13 model: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Lending/LoanBroker/LoanBrokerSet.lean`
- Raw 14–16 model: `/Users/tusharpardhe/.kiro/crew/scratch/runtime-52c7dd05/rippled-formal-verification/formal_verification/XRPL/Model/Lending/LoanBroker/{BrokerCover,LoanBrokerCoverDeposit,LoanBrokerCoverWithdraw}.lean`

`LWAB` v1 request envelope is `magic[4]="LWAB" | version:u8=1 | tag:u8 | payloadLength:u32le | payload`; the response tag is `128 + tag`. A response payload begins `0` + operation result, or `1` + exact `DecodeError`. `N` is canonical `Number`; `A` is complete `STAmount`; `V`, `L`, `B`, `S`, `BV`, and `LV` are complete Vault, Loan, LoanBroker, LendingState, BrokerVault, and LoanVault records.

| Tag | Lean export | Request schema | Raw result schema | Terminal counterpart |
|---:|---|---|---|---|
| 1 | `raw_create` | `Create(VI,LI,V,B,N,Rates,Fees,Schedule,bool,bool)` | `LoanResult<S>` | 17, same request → `LoanResult<S>` then one association |
| 2 | `raw_create_pending` | `Create(...)` | `LoanResult<S>` | 18, same request → terminal state |
| 3 | `raw_create_immediate` | `Create(...)` | `LoanResult<S>` | 19, same request → terminal state |
| 4 | `raw_accept` | `LV(L,V)` | `LoanResult<LV>` | 20, same request → terminal loan/vault |
| 5 | `raw_delete` | `BrokerRequest(L,V,B)` | `LoanResult<BV>` | 21, same request → terminal broker/vault |
| 6 | `raw_regular_payment` | `Payment(L,V,B,paymentType,N,now)` | `LoanResult<S>` | 22, same request → terminal state |
| 7 | `raw_late_payment` | `Amount(L,V,B,N,now)` | `LoanResult<S>` | 23, same request → terminal state |
| 8 | `raw_full_payment` | `Amount(L,V,B,N,now)` | `LoanResult<S>` | 24, same request → terminal state |
| 9 | `raw_manage_impair` | `LV(L,V)` | `LoanResult<V>` | 25, same request → raw then exactly one Vault association |
| 10 | `raw_manage_unimpair` | `LV(L,V)` | `LoanResult<V>` | 26, same request → raw then exactly one Vault association |
| 11 | `raw_manage_default` | `Default(L,V,B,impaired:bool)` | `LoanResult<BV>` | 27, same request → raw then exactly one Vault association |
| 12 | `raw_broker_create` | `BrokerCreate(BI,Option<N>,Option<u16>,Option<u32>,Option<u32>)` | `B` | — |
| 13 | `raw_broker_update` | `BrokerUpdate(B,Option<N>)` | `B` | — |
| 14 | `raw_cover_validate` | `CoverValidate(NumericType,N,A)` | `Except<Error,TER>` | — |
| 15 | `raw_cover_deposit` | `Cover(B,NumericType,A)` | `Except<Error,CoverResult(status:A/B fields)>` | — |
| 16 | `raw_cover_withdraw` | `Cover(B,NumericType,A)` | `Except<Error,CoverResult(status:A/B fields)>` | — |
| 17–27 | terminal forms | exact tag 1–11 request schemas | exact corresponding result schema | apply raw transition; on success run one `Vault.associateAsset`; failure is atomic |

## Exact 9–16 semantic notes

- **9 impair:** add `loan.principalOutstanding` to `vault.lossUnrealized` with `adjustImpreciseNumber`; reject `tecLIMIT_EXCEEDED` if this exceeds `assetsTotal-assetsAvailable`; construct a lawful Vault.
- **10 unimpair:** reject `tefBAD_LEDGER` if loss is below outstanding principal; otherwise subtract with `adjustImpreciseNumber` and construct a lawful Vault.
- **11 default:** calculate cover through `tenthBipsOfValue`, upward asset rounding, and `min`; debit debt and cover, adjust totals/availability and (when impaired) unrealized loss; retain dust adjustment and all Lean errors.
- **12/13:** default optional values exactly as Lean (`0` on create; current debt maximum on absent update). Validation is a distinct model predicate and must not be invented by the raw transform.
- **14:** reject zero or cover-scale-rounding-to-zero input as `tecPRECISION_LOSS`; otherwise `tesSUCCESS`.
- **15/16:** first round downward to cover scale; an unroundable movement returns a successful cover-result tagged `tecINTERNAL` with zero amount and unchanged broker. Withdraw itself is the raw debit transform; do not substitute an independent balance guard.

## Required ownership

- Raw 1–8: separate dispatcher/operation and bridge vectors.
- **Raw 9–16: separate dispatcher/operation and bridge vectors.**
- Terminal 17–27: separate dispatcher/operation and bridge vectors.
- Only the integrator may update common module declarations, aggregate registry, Cargo metadata, counters, or final evidence after all three groups pass.
