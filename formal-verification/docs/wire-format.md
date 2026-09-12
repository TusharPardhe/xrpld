# Verification wire format

Vault and Lending comparisons use versioned LWAB envelopes carrying complete requests and tagged responses. A codec must define magic, version, route tag, body length, little-endian integer encoding, canonical Boolean/Option tags, identity widths, NumericType/Number/STAmount representation, exact-end rejection, and stable decode/model/TER error tags.

The Lean FFI and Rust verification-wire/production adapter must independently encode or decode the same schema. The harness compares complete bytes and then complete typed values; projections or echoed input are insufficient.

Malformed magic, version, route, length, truncation, trailing bytes, noncanonical Booleans, and invalid bodies are codec-only observations. They must never increase semantic operation/export coverage.

Schema changes require a new version and retained old fixtures. Do not reinterpret bytes under an existing version.
