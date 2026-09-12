use crate::{
    stamount_abi as ffi,
    stamount_model::{amount, project, wire},
};

pub fn run() -> usize {
    let mut checks = 0;
    for k in 0..3 {
        let mut seed = 17u64;
        for _ in 0..24 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let m = if k == 2 {
                1_000_000_000_000_000 + seed % 9_000_000_000_000_000
            } else {
                1 + seed % 10_000
            };
            let e = if k == 2 { (seed % 30) as i32 - 20 } else { 0 };
            let q = amount(k, m, e, seed & 1 != 0);
            assert_eq!(project(ffi::access(wire(&q, k))), project(wire(&q, k)));
            checks += 1;
        }
    }
    checks
}
