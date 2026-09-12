# Proof guide

A theorem must say exactly what is universal and expose every required premise. Separate representation `WF`, business `Valid`, combined `Lawful`, and mathematical `Exact` layers. Prove conversion/equivalence lemmas such as `valid_iff_exact` before large transition theorems.

Universal proof modules must not use `sorry`, `admit`, new axioms, `native_decide`, or `unsafe`. Executable examples may support discovery but do not replace a universal proof.

Use `Common` only for precisely named facts reused by multiple operations—for example zero-loss pricing-prefix reduction or normalized subtraction totality. Avoid generic `Utils`/`Misc` files.

When Lean rejects a theorem, investigate the statement before adding assumptions. Preserve executable counterexamples to false claims and replace them with the strongest true theorem whose premises reflect the protocol.

A successful `lake build` proves the Lean theorem was kernel-checked. It does not by itself prove that rippled or Quaxar implements the Lean definition; source traceability and bounded comparison are separate obligations.
