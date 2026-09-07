# Ledger divergence evidence

This register contains explicit `Not validating incompatible consensus child`
diagnostics, not state-transition counts. The retained journal contains 33
confirmed incompatible children from 2–4 September 2026. In every case the
local child shares the canonical parent and uses the same transaction-ID set.

## Immutable offer-quality parity (6 September)

Three retained incompatible children from the current deployment were reduced
to the first transaction whose serialized metadata differs from the canonical
Testnet ledger:

| Ledger | Exact transaction | Canonical difference |
| ---: | --- | --- |
| 20,517,622 | `B978DA5848B8EF60C3602C027550E2ED4775D4768DCAF02E77F3E84925A1DC1F` | A second partial fill consumes 3,333,334 drops and leaves 3,333,332; Quaxar consumed 3,333,333 and left 3,333,333. |
| 20,517,766 | `3AEA384FC7AAB1EF80C910B0D2094F87DDC46D5A424BB57C616904D3911B6A0E` | Quaxar stopped the same-quality stream early and failed to delete four canonical consumed offers. |
| 20,518,045 | `2455ADF9919863BC60BA514CF39C627EC429BBD835252C12577A14252A82EF04` | The same one-drop partial-fill mismatch as ledger 20,517,622. |

The preceding transactions in each candidate have metadata identical to the
canonical ledger, including the sequence-zero/Batch transactions. The common
defect was in book iteration. `rippled::BookTip` extracts quality from the
quality-directory root and passes it into `TOffer`, whose quality never changes
for the offer's lifetime. Quaxar discarded that value and recomputed quality
from the remaining `TakerPays`/`TakerGets` after every partial fill. That both
changed consensus-significant rounding by one drop and made offers from one
directory appear to have different qualities. Quaxar's scan also read only the
root page of each quality directory, whereas `rippled::dirFirst/dirNext` follows
all `sfIndexNext` overflow pages.

The correction carries the immutable directory quality through CLOB/AMM tip
selection, quality gates, and every `limitIn`/`limitOut` operation, and walks
the complete linked directory. Regressions cover the exact one-drop rounding,
repeated partial fills, immutable same-directory quality, and overflow-page
enumeration.

## OfferCreate flow-result parity (5 September)

Four later incompatible children shared the canonical parent and candidate
transaction set, but omitted one canonical successful `OfferCreate` from the
locally built transaction map:

| Ledger | Omitted transaction | Quaxar crossing result | Canonical result |
| ---: | --- | --- | --- |
| 20,496,487 | `711C83C47F6FBC2DB6F37947492F9B1D45BB924A2FA015FA7098AB8D9883694A` | Retry after the IOU crossing strands failed validation | `tesSUCCESS`, unchanged residual offer placed |
| 20,499,545 | `035CEE565F07B9160E12B39306559727C724EE7F37DE9B417D91F3C1E0E38E58` | Retry after the IOU crossing strands failed validation | `tesSUCCESS`, unchanged residual offer placed |
| 20,500,630 | `5E177243080CDE7E4636FB091A2537F87619265131868D1B4098B55B88018AE2` | `temBAD_PATH_LOOP` (`-290`) | `tesSUCCESS`, unchanged residual passive offer placed |
| 20,500,732 | `171024C5CE9B97462FE834D25FFDD5A406786E7BE510AC3C76123CFBA55BB789` | `temBAD_PATH_LOOP` (`-290`) | `tesSUCCESS`, unchanged residual passive offer placed |

The common root cause was above the individual strand validators. rippled's
`OfferCreate::flowCross` propagates only the initial unfunded-account check.
If `flow()` cannot construct or execute a crossing path, `flowCross` treats the
cross as dry, preserves any stale-offer cleanup, and returns `tesSUCCESS` with
the original offer amounts. Quaxar instead returned the internal Flow TER from
`do_offer_create`, causing consensus application to retry and ultimately omit
the otherwise valid offer.

The correction implements that complete control-flow contract rather than
special-casing either transaction shape. It also constructs rippled's explicit
XRP bridge path as `TypeCurrency` instead of `TypeNone`, and validates serialized
path elements before normalization as `PaySteps.cpp::toStrand` does. Regression
fixtures cover both low/high NoRipple trust-line orientations and the passive
same-currency, self-issued destination shape from the four live incidents.

## Exact transaction divergences

Canonical binary metadata was compared byte-for-byte with serialized local
metadata. These are direct divergences, not merely later cascade transactions.

| Ledger | Exact transaction | Type | Difference |
| ---: | --- | --- | --- |
| 20,427,665 | `E205A52F3792D6B989518C2711A4BCC3AF3C525783364ADE0D9460E00BD71B07` | OfferCreate | Metadata differs from canonical `tesSUCCESS` at index 0. |
| 20,432,308 | `0ADFCD9BF10A1AA78E3EF5EF1E252D9CBCEA9476925C28CD584461A1094016EC` | OfferCreate | Metadata differs from canonical `tesSUCCESS` at index 0. |
| 20,444,445 | `FEE61A1E57BE02A23D2C19B0108058C0CF2C68E91492266E57B45845A4F793D8` | OfferCreate | Quaxar `tecKILLED` (TER 150); canonical `tesSUCCESS`. |
| 20,444,720 | `537BA2842A8EC1560E278BF841626F39D3BBFBF3A462B8289F61596DD32EE16D` | OfferCreate | Quaxar `tecKILLED` (TER 150); canonical `tesSUCCESS`. |
| 20,445,411 | `E8924A8A6CA7235E1F5BC80487380C2EF3A5F9430EF6DD2A1F312AEE355D05FC` | OfferCreate | Quaxar `tecKILLED` (TER 150); canonical `tesSUCCESS`. |
| 20,445,903 | `7B34F8E0B1B656F03AEFF214D447278D1492854EFC88E7F82865595B815533A0` | OfferCreate | Metadata differs from canonical `tesSUCCESS` at index 1. |
| 20,461,475 | `E4085471993AF2524C02261D8D70EFD4A54321BEE52FD2FB4077D5A0C39B4F9C` | OfferCreate | Canonical `tesSUCCESS` transaction missing from Quaxar's built transaction map. |
| 20,465,335 | `C44A4FCA32B0C1C44136F039CE3C1993E56A1F3DF8039BD86A75860E76BAEEBA` | OfferCreate | Quaxar `tecKILLED` (TER 150); canonical `tesSUCCESS`. |
| 20,469,322 | `EC3479FB90416165E63CA80A426F78EB3A27EA0B4C5A5124B098D7C178B5B7B1` | OfferCreate | Quaxar `tecKILLED` (TER 150); canonical `tesSUCCESS`. |
| 20,469,585 | `E143D01D444E21DEDCA3EB64A8647CFD261C4DF64D3BBE6FB37FF1611A2B371C` | OfferCreate | Quaxar `tecKILLED` (TER 150); canonical `tesSUCCESS`. |
| 20,473,059 | `0EDE3CA3040D9DD1E71ADC19C7FE0328CF219BBFBE20272D8140DC92519D5314` | Payment | Both report `tecUNFUNDED_PAYMENT`, but metadata differs at index 1. |
| 20,473,059 | `BF253E73523E712871AFF2D789680152E00D3B6693CF0BDF9EA89E1AC686A78B` | OfferCreate | Canonical `tesSUCCESS` transaction missing; likely downstream of the preceding Payment. |
| 20,477,952 | `3126B8056E9310C7BC21211F8D3D8C16540A4DDAE8826341110A11156D9C6FD8` | OfferCreate | Canonical `tesSUCCESS` transaction missing from Quaxar's built transaction map. |
| 20,478,303 | `3EA1971A2870C741AB7047A460F47A2DAE735873855EB1A425059B4A66A3DEB9` | OfferCreate | Canonical `tesSUCCESS` transaction missing from Quaxar's built transaction map. |
| 20,478,525 | `8F92783AFEDD17307213E8B31FF5C3663FF8F93D290B264B01139C8EC92EDC06` | OfferCreate | Canonical `tesSUCCESS` transaction missing from Quaxar's built transaction map. |

## Retained September root causes

The later 19 incidents were re-compared transaction-by-transaction. The earlier
description of them as “root-only” was incorrect: each candidate has a direct
metadata or TER mismatch. They reduce to three independent execution defects,
plus downstream transaction-index/threading changes after the first defect:

| Root cause | Ledgers with direct evidence | rippled parity correction |
| --- | --- | --- |
| OfferCreate flow | `20447062`, `20449243`, `20454056`, `20459481`, `20460021`, `20462138`, `20462497`, `20462526`, `20477342`, `20478560`, `20481587`, `20485432`, `20485479` | Apply StrandFlow's execution-time quality gate even when ActiveStrands has only one candidate. Use DirectIOfferCrossingStep semantics: ignore trust-line quality fields, and let the final issuer-to-taker step exceed or create the taker's trust line. |
| Holder-to-holder IOU Payment | `20453341`, `20460519`, `20481678`, `20485171` | Remove the non-rippled endpoint-wide freeze shortcut. Freeze is checked directionally by each DirectStep, so a frozen holding cannot be spent but may still receive. |
| MPT EscrowFinish | `20462448`, `20485226` | Permit EscrowFinish's destination MPToken creation after the amendment-gated MPT authorization checks, exactly where ValidMPTIssuance does in rippled. |

The retained exact Payment at `20473059` has the same
`tecUNFUNDED_PAYMENT` result; its different transaction index and owner thread
follow the preceding OfferCreate execution difference. It is not a fourth
Payment arithmetic defect.

These corrections have focused regression coverage, including the exact
`20453341` parent leaves and transaction, an absent-line issuer-to-taker offer
crossing, and an MPTokensV2 EscrowFinish that previously reproduced
`tecINVARIANT_FAILED`. Deployment and canonical-child replay remain required
before marking the incidents operationally closed.

## Earlier evidence

| Status | Ledger | Transaction | Evidence |
| --- | ---: | --- | --- |
| Confirmed | 20,296,265 | `31201568C685271B19B75DD840F3D529130768BCD1EBBD5CD97696A94660E3A5` | MPT Payment: canonical `tecNO_AUTH`; former Quaxar candidate accepted it. |
| Incomplete evidence | 20,285,668 | Unknown | Per-transaction diagnostics were not retained. |
| Incomplete evidence | 20,288,630 | Unknown | Same. |
| Incomplete evidence | 20,293,100 | Unknown | Same. |
| Incomplete evidence | 20,293,241 | Unknown | Same. |

## Evidence rule

An incident must retain child/parent hashes, canonical child hash, candidate
state and transaction roots, transaction set, IDs, TERs, indexes, and serialized
metadata. Startup, catch-up, storage stalls, and peer rotation are excluded.
