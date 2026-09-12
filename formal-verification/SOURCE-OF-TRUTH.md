# Source-of-truth policy

Quaxar targets behavioral compatibility with rippled. The primary authority is the pinned rippled implementation and declarations, interpreted with XRPL amendment documentation and corroborated by rippled tests.

The model is not a blind textual translation. For every disagreement, classify the observation:

1. **Quaxar semantic defect:** a reachable Quaxar value/error conflicts with defined rippled behavior—fix Quaxar.
2. **Lean/model defect:** the model or public FFI represents the wrong rippled abstraction—fix Lean/FFI.
3. **Representation-only mismatch:** both reject or accept equivalently but expose different private details—stabilize the public boundary.
4. **Missing API:** rippled/Lean behavior has no Quaxar projection—add a production API separately.
5. **Undefined or implementation-defined C++:** do not invent a portable rippled result; document and select an explicit deterministic contract.
6. **False requested property:** retain the counterexample and weaken the theorem only to a true, useful statement.

Lean is authoritative for what its definitions and theorems state, not automatically for deployed rippled or Quaxar. Quaxar is the production implementation under comparison. The bridge supplies bounded evidence that the two agree on executed inputs.

Pinned revisions and schema versions live in `versions.toml`; every promoted evidence baseline must cite them.
