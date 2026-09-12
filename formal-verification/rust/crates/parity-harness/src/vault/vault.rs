//! Direct predicate vectors supplementing the complete material LWAB registry.

use crate::vault_abi;

/// `isInsolvent` is the only exported predicate not serialized as a standalone
/// route result. These are genuine state predicates, not reachability probes.
pub fn run() -> usize {
    assert_eq!(vault_abi::initialize(), 1, "initialize Vault Lean ABI");
    let cases = [(100, 100, false), (0, 0, false), (0, 1, true)];
    for (total, shares, expected) in cases {
        let lean = vault_abi::insolvent(total, shares);
        let quaxar = total == 0 && shares != 0;
        assert_eq!(lean, expected, "Lean insolvency boundary");
        assert_eq!(lean, quaxar, "Lean and Quaxar insolvency predicate");
    }
    cases.len()
}
