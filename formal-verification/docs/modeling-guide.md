# Modeling guide

A Lean model represents observable rippled semantics: branch order, guards, rounding points, overflow, tagged errors, identity, and complete state changes. Prefer pure functions returning `Except Error Result` so all outcomes are explicit.

For every operation:

- cite exact rippled declarations/implementations and relevant amendment or test;
- distinguish internal helpers from public constructors;
- model raw and terminal transitions separately;
- preserve full-width identities and Issues;
- document undefined or implementation-defined C++ rather than copying it;
- keep mathematical `Exact` views separate from finite executable representations;
- add a counterexample when a desired property is false.

Do not make the model match Quaxar merely to eliminate a divergence. Classify whether rippled, Lean/FFI, Quaxar, the boundary representation, or the requested theorem owns the discrepancy.
