# Source traceability

Every coverage target must identify:

- rippled repository revision and C++ symbol/path;
- relevant amendment/documentation/test;
- Lean model definition;
- Lean theorem modules and their assumptions;
- Lean FFI export and stable ABI/route ID;
- Quaxar production API or dispatcher;
- executable vector IDs and class;
- current claim status.

Traceability is many-to-many: one mathematical theorem may cover several implementation files, and one production file may support several properties. Do not force a one-file mirror. Store mappings in `coverage/*.toml`, not comments alone.

When authority is ambiguous, record the disagreement and owner rather than silently selecting whichever implementation makes a test pass.
