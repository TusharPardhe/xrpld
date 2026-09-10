# Configuration Reference

This file explains the runtime configuration used by `quaxar`. Keep `quaxar.cfg`
focused on actual values; use this document for operational guidance.

## Loading A Config

Run with an explicit config path:

```bash
quaxar --conf /etc/quaxar/quaxar.cfg
```

Docker Compose mounts the container-specific `infra/docker/quaxar.cfg` to
`/etc/quaxar/quaxar.cfg`. The root `quaxar.cfg` is the safe bare-metal example
and binds administration to host loopback.

The Docker config permits admin requests from its Compose network because host
port forwarding does not originate at container loopback. Keep that network
private to trusted Quaxar components; do not attach untrusted containers or
publish the admin ports on a non-loopback host address.

The runtime does not implicitly load an old `xrpld.cfg`. Upgrade tooling may
migrate a legacy file, but operators should verify the final
`/etc/quaxar/quaxar.cfg` path and its protected validator credentials before
starting the service.

### Diagnostic environment

Set `QUAXAR_ACQUISITION_SHADOW=1` to enable the bounded, read-only acquisition
shadow on the serialized coordinator owner. It compares typed events, exact
session/timer identities, effects, and derived phase decisions without becoming
a second lifecycle authority. The shadow is disabled by default and should be
enabled temporarily when auditing acquisition parity or mode transitions.

## Core Sections

### `[server]`

Lists enabled server port sections. Each line should be the name of a
`[port_*]` section.

```ini
[server]
port_rpc_admin_local
port_peer
```

### `[port_*]`

Configures one listening port.

| Key | Meaning |
|-----|---------|
| `port` | TCP port to bind. |
| `ip` | Bind address, for example `127.0.0.1` or `0.0.0.0`. |
| `protocol` | Comma-separated protocols, commonly `http`, `ws`, or `peer`. |
| `limit` | Optional connection limit; values below `256` still reserve at least 256 file descriptors for the listener. |
| `admin` | Admin access scope, typically `127.0.0.1` for local-only admin RPC. |
| `secure_gateway` | Trusted proxy/gateway IP for forwarded client metadata. |
| `user`, `password` | Optional basic-auth credentials for ordinary requests. |
| `admin_user`, `admin_password` | Optional basic-auth credentials for admin requests. |
| `ssl_key`, `ssl_cert`, `ssl_chain`, `ssl_ciphers` | TLS listener material and cipher configuration. |

Port defaults may be placed in `[server]` and are inherited by each named port
section. `admin` and `secure_gateway` accept IPv4 or IPv6 addresses and CIDR
ranges. The runtime does not apply the parsed `send_queue_limit`; it has therefore
been removed from the packaged examples rather than presented as an effective
WebSocket control.

### `[node_size]`

Selects the resource profile. This is the recommended primary tuning knob.

```ini
[node_size]
medium
```

Profiles currently map to these NodeFamily and history defaults:

| Size | Tree-node target | Node age | Sweep | Adjacent history | Intended use |
|------|-----------------:|---------:|------:|-----------------:|--------------|
| `tiny` | 262,144 | 30s | 10s | 2 | Small/dev machines. |
| `small` | 524,288 | 60s | 30s | 3 | Light nodes. |
| `medium` | 2,097,152 | 90s | 60s | 4 | Default balanced profile. |
| `large` | 4,194,304 | 120s | 90s | 5 | Stronger machines. |
| `huge` | 8,388,608 | 900s | 120s | 8 | High-throughput machines with ample memory and fast disk. |

The profile also influences SHAMap tree-cache size and age, sweep cadence, the
adjacent history-fetch window, and selected JobQueue defaults. Prefer changing
`node_size` before using expert overrides.

The tree-node target is an entry target, not a byte or hard-RSS limit. One
application-owned NodeFamily supplies the same tree-node and FullBelow caches
to every inbound acquisition. Verified nodes survive per-hash session expiry
and remain reusable until ordinary cache policy or online deletion removes
them; execution-scheduler limits do not resize this cache.
The FullBelow cache target is 524,288 entries with a 600-second expiration for
all profiles.

Cache profile and RAM use affect retention and performance, not preferred-LCL
correctness. Do not increase `node_size` to mask repeated mode transitions or
growing local-closed versus validated-ledger lag.

### `[sweep_interval]`

Optional cache-maintenance interval in seconds. Accepted values are 10 through
600. When omitted, the selected `[node_size]` supplies the interval.

### `[node_db]`

Persistent network nodes should set `fast_load = 1`. On restart, this selects
the rippled-compatible `Load` startup path and restores the newest complete
ledger from SQL and NodeStore. If local durable state is absent or incomplete,
`fast_load` falls back to genesis/network bootstrap; omit it only when that
genesis startup is intentional.

Configures persistent ledger object storage.

| Key | Meaning |
|-----|---------|
| `type` | Storage backend, commonly `NuDB` or `RocksDB`. |
| `path` | Filesystem path for the node database. |
| `nudb_block_size` | Optional NuDB block size. |
| `online_delete` | Retention interval; `0` disables online deletion. Minimum `256` on a networked node and `8` in standalone mode. |
| `advisory_delete` | When enabled, deletion waits for the advisory `can_delete` boundary. |
| `delete_batch` | Relational cleanup batch size; default `100`. |
| `back_off_milliseconds` | Delay between relational cleanup batches; default `100`. Legacy key `backOff` is also accepted. |
| `age_threshold_seconds` | Maximum validated-ledger age allowed before a rotation waits; default `60`. |
| `recovery_wait_seconds` | Retry delay after a rotation health gate blocks; default `5`. |

When nonzero, `online_delete` must be at least the selected numeric
`ledger_history`. Online-delete rotation freshens cache generations and clears
prior-ledger and FullBelow state; it is separate from normal age/size sweeps.
Rotating NodeStores intentionally bypass the encoded `NodeObject` cache, matching
`rippled`: reads go directly to the writable and archive backends so cached
archive objects cannot hide copy-forward work during rotation. Cache-size and
cache-age settings apply only to non-rotating NodeStores.

### `[database_path]`

Directory for relational metadata databases.

### `[ledger_history]`

Desired validated-ledger acquisition/history depth. Use a number, `none` (`0`),
or `full` (`u32::MAX`). Full history requires `online_delete = 0`. When online
deletion is enabled, a numeric history depth cannot exceed its interval.

### `[validation_seed]`

Secret family seed for this server's validator identity. Keep the containing
file restricted to the service account. See [VALIDATORS.md](VALIDATORS.md).

### `[validator_token]`

Multi-line validator-token input. The section is accepted by bootstrap, but
Quaxar's token generation and rotation workflow is still experimental. Prefer
`[validation_seed]` for current operator deployments.

### `[validators]`

Static trusted validator public keys, one per line. Public networks should
normally use signed validator lists rather than hand-maintaining a large set.

### `[validators_file]`

Path to a validator-list config file. Relative paths are resolved from the
directory containing `quaxar.cfg`.

### `[validator_list_sites]`

Validator list publisher URLs.

### `[validator_list_keys]`

Validator list publisher public keys.

### `[validator_list_threshold]`

Optional number of configured publisher lists required. Omitted or `0` selects
the computed default. A nonzero value must not exceed the number of entries in
`[validator_list_keys]`.

### `[validator_key_revocation]`

Advanced multi-line base64 revocation-manifest input. Bootstrap rejects a
payload that is malformed, not a revocation, or invalid for the manifest cache.

### `[ips]` and `[ips_fixed]`

Outbound peer endpoints.

```ini
[ips]
s1.ripple.com 51235
s2.ripple.com 51235
```

`[ips]` seeds ordinary outbound discovery. `[ips_fixed]` configures fixed peer
relationships that PeerFinder keeps trying to maintain.

### `[peer_private]`

One boolean value. When enabled, the node does not advertise for incoming
peers and does not automatically dial the ordinary boot cache; configured
`[ips_fixed]` peers remain active.

### `[network_id]`

Optional network selector. Accepted values are `main` (`0`), `testnet` (`1`),
`devnet` (`2`), or an unsigned numeric network ID.

### `[peers_max]`

Maximum peer slots. An omitted or zero value uses the reference default of 21.
Any nonzero value below `10` has an effective floor of `10`.
When present, this legacy total takes precedence over the directional limits
below, including when its value is zero.

### `[peers_in_max]` and `[peers_out_max]`

Optional directional peer limits. Configure both sections together and omit
`[peers_max]` when using them. The inbound limit may be `0..1000`; the outbound
limit must be `10..1000`. Supplying only one section, or placing more than one
value in either section, fails startup validation.

### `[network_quorum]`

The minimum number of peers required before NetworkOps treats the network as
present. The default is `1`. It must be one unsigned value and may not exceed
legacy `[peers_max]`; when `[peers_max]` is omitted or zero, the reference
default maximum of `21` is used. Falling below this threshold publishes
`disconnected` even when some peers remain connected and usable for ledger
acquisition; satisfying it again returns the node to `connected` before normal
synchronization/readiness promotion.

```ini
[network_quorum]
1
```

### `[overlay]`

Peer overlay settings.

| Key | Meaning |
|-----|---------|
| `public_ip` | Advertised public endpoint IP. |
| `ip_limit` | Incoming peer limit per public IP. |
| `verify_endpoints` | Validate advertised endpoints before using them. |

### `[crawl]`

Controls peer crawl responses.

| Key | Meaning |
|-----|---------|
| section value | `1` enables crawl responses, `0` disables crawl responses. |
| `overlay` | Include overlay peer crawl data. |
| `server` | Include server info crawl data. |
| `counts` | Include server count crawl data. |
| `unl` | Include UNL crawl data. |

### `[vl]`

Validator-list runtime toggle.

| Key | Meaning |
|-----|---------|
| `enabled` | Enables validator-list fetching and processing. |

### `[sntp_servers]`

Built-in SNTP time synchronisation for environments where host NTP cannot be
configured (LXC containers, Docker, managed VPS). One server per line. When
configured, the node queries these servers in the background and applies the
computed clock offset. Disabled in standalone mode.

```ini
[sntp_servers]
time.windows.com
time.apple.com
time.nist.gov
pool.ntp.org
```

### `[reduce_relay]`

Controls validation and transaction relay reduction.

| Key | Meaning |
|-----|---------|
| `vp_base_squelch_enable` | Enables validation relay base squelch. |
| `vp_base_squelch_max_selected_peers` | Max selected validation relay peers. Must be at least `3`. |
| `tx_enable` | Enables transaction reduce relay. |
| `tx_min_peers` | Minimum peers before transaction reduce relay is active. Must be at least `10`. |
| `tx_relay_percentage` | Transaction relay percentage. Valid range: `10..100`. |

### `[transaction_queue]`

Optional transaction-queue overrides. Supported keys are
`ledgers_in_queue`, `minimum_queue_size`, `retry_sequence_percent`,
`minimum_txn_in_ledger`, `minimum_txn_in_ledger_standalone`,
`target_txn_in_ledger`, `maximum_txn_in_ledger`,
`normal_consensus_increase_percent`, `slow_consensus_decrease_percent`,
`maximum_txn_per_account`, and `minimum_last_ledger_buffer`. Omitted keys use
runtime defaults; unknown keys are logged and ignored.

### Runtime worker and path-search sections

The following single-value sections expose advanced runtime sizing. Defaults
are normally preferable; measure the target workload before overriding them.

| Section | Meaning |
|---------|---------|
| `[io_workers]` | I/O runtime worker count. |
| `[workers]` | JobQueue worker count; `0` selects the node-size-derived default. |
| `[path_search_old]` | Search level used for old path requests; default `2`. |
| `[path_search]` | Normal path-search level; default `2`. |
| `[path_search_fast]` | Fast path-search level; default `2`. |
| `[path_search_max]` | Maximum path-search level. When omitted it defaults to `0` on a validating node and `3` otherwise. |

Malformed worker/path values currently fall back to their defaults in the
bootstrap parser rather than failing configuration validation. Do not depend
on that fallback: use unsigned integers and verify the effective bootstrap log.

### `[relay_validations]` and `[relay_proposals]`

Control relaying of untrusted consensus messages. Each section accepts one of
`all`, `trusted`, or `drop_untrusted` (case-insensitive). Defaults are `all`
for validations and `trusted` for proposals. `all` processes and permits relay
of untrusted messages; `trusted` may process untrusted messages locally but
does not relay them; `drop_untrusted` discards them before local processing.
These settings do not make an untrusted validator trusted or give its messages
consensus weight.

### `[cluster_nodes]`

Optional trusted cluster peers, one XRPL node-public key per line followed by
an optional display name. Invalid entries fail bootstrap. Cluster membership
changes overlay load-reporting behavior and should be configured only between
servers under the same operator's control.

### `[debug_logfile]`

Compatibility placeholder accepted by the parser but omitted from packaged
configs. The current runtime does not open this path; logs are emitted through
`tracing` to stdout/stderr and should be collected by systemd, Docker, or the
process supervisor.

### `[rpc_startup]`

Compatibility placeholder for startup JSON-RPC commands, omitted from packaged
configs. The current runtime parses the section as configuration text but does
not execute these commands. Set `RUST_LOG` in the service environment or use
`quaxar log-level` after startup instead.

```ini
[rpc_startup]
{ "command": "log_level", "severity": "warning" }
```

### `[ssl_verify]`

Accepted by configuration validation for compatibility and omitted from
packaged configs, but it is not wired to runtime HTTP clients. Do not rely on
this setting to weaken or strengthen certificate verification.

### `[features]` and `[amendments]`

Feature names or amendment IDs used when creating a fresh private network with
`--start`. They do not override the amendment set of an existing public
network.

## Recommended Examples

Balanced default:

```ini
[node_size]
medium
```

High-throughput machine:

```ini
[node_size]
large
```

Validator identity (secret placeholder):

```ini
[validation_seed]
<family-seed>
```
