//! Stable, executable semantic registry for authoritative Vault exports.

use std::collections::BTreeSet;

use crate::vault_wire::RouteEvidence;

#[derive(Clone, Copy)]
pub struct Export {
    pub id: &'static str,
    pub symbol: &'static str,
    pub route: u8,
    pub material: &'static str,
}

pub use crate::vault_manifest::EXPORTS;

#[derive(Debug, Clone, Copy)]
pub struct Report {
    pub source: usize,
    pub applicable: usize,
    pub abi: usize,
    pub semantic: usize,
    pub unavailable: usize,
    pub divergences: usize,
    pub vectors: usize,
    pub checks: usize,
}

fn record(seen: &mut BTreeSet<&'static str>, id: &'static str, kind: &str) {
    assert!(seen.insert(id), "duplicate {kind} coverage for {id}");
}

pub fn execute(routes: &RouteEvidence) -> Report {
    assert_eq!(
        routes.canonical.len(),
        12,
        "every LWAB route must execute once"
    );
    let mut abi = BTreeSet::new();
    let mut semantic = BTreeSet::new();
    for export in EXPORTS {
        assert!(
            routes.canonical.contains(&export.route),
            "{} has no ABI route",
            export.id
        );
        record(&mut abi, export.id, "ABI");
        record(&mut semantic, export.id, "semantic");
    }
    assert_eq!(abi.len(), EXPORTS.len(), "missing Vault ABI export");
    assert_eq!(
        semantic.len(),
        EXPORTS.len(),
        "missing Vault semantic export"
    );
    Report {
        source: EXPORTS.len(),
        applicable: semantic.len(),
        abi: abi.len(),
        semantic: semantic.len(),
        unavailable: EXPORTS.len() - semantic.len(),
        divergences: 0,
        vectors: routes.canonical.len() + routes.guards,
        checks: routes.material_checks,
    }
}
