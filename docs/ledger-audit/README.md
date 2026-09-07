# Offline ledger audit

`quaxar ledger-audit` captures an immutable, canonical replay fixture without
reading the running node's NuDB. It is intended for investigating a suspected
consensus divergence after the fact.

```bash
quaxar ledger-audit \
  --network testnet \
  --ledger 20296265 \
  --output /var/tmp/quaxar-audit-20296265
```

The command resolves the requested child ledger, verifies its direct parent,
and follows every opaque `ledger_data` pagination marker for each state tree.
The output directory contains:

| File | Contents |
| --- | --- |
| `parent-ledger.json` | Canonical parent header |
| `parent-state.jsonl` | Every binary parent state leaf, streamed page by page |
| `child-ledger.json` | Canonical child header and expanded binary transactions |
| `child-state.jsonl` | Every binary resulting state leaf, streamed page by page |
| `parent-nodestore/` | Locally rebuilt, content-addressed SHAMap wire nodes |
| `manifest.json` | Network, hashes, counts, and fixture format |

This layout intentionally keeps capture data outside the repository and audit
implementation under `xrpld/cli/src/ledger_audit/`. Removing the audit feature
later is limited to that module, this document, the `LedgerAudit` CLI variant,
and its one dispatch arm; it has no production consensus or storage call path.

During capture, Quaxar imports parent leaves into `parent-nodestore/`. It
flushes canonical wire nodes to disk every 1,024 leaves, reloads only required
hash-linked branches, and rejects the fixture unless the rebuilt root exactly
matches the canonical parent `account_hash`. Public XRPL JSON-RPC servers expose
leaves, not NuDB files or authenticated internal SHAMap nodes; the local import
is therefore a verification boundary, not a byte-for-byte NuDB copy.

The final replay stage is still deliberately separate: it must execute the
child transaction set through Quaxar's production application path, then compare
the resulting state and transaction roots with `child-ledger.json`. Capture and
parent-root verification alone are never presented as a consensus verdict.
