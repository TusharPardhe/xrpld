# Verification claim vocabulary

Use these terms exactly in code review, CI, and evidence.

| Claim | Meaning |
|---|---|
| `source-traced` | The behavior maps to named rippled source/declarations/tests or an amendment rule. |
| `modeled` | A Lean executable definition represents the behavior. |
| `proved` | Lean's kernel accepted a theorem under its explicit premises with the project proof-hygiene rules. |
| `abi-reachable` | The external harness successfully invoked the declared Lean export. |
| `applicable` | A concrete Quaxar operation exists for meaningful comparison. |
| `bounded-parity` | Lean and Quaxar returned equal material results for catalogued executed vectors. |
| `codec-only` | Encoding/decoding behavior was checked; it does not count as operation semantics. |
| `unavailable` | No meaningful executable Quaxar counterpart was invoked. |
| `divergent` | Material Lean and Quaxar outcomes differ for an executed vector. |

`source`, `manifest`, `ABI`, `applicable`, and `semantic` counters are independent and must reconcile explicitly. ABI reachability is not semantic parity. Malformed codec cases are excluded from semantic export counts.

A universal Lean theorem does not automatically apply to Rust. Transferring it would require a universal refinement proof from Quaxar semantics to the Lean model. Current Lean↔Quaxar results are bounded executable cross-validation, even when every export has at least one semantic comparison.
