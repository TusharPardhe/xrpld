use std::{env, path::PathBuf, process::Command};

fn lean_prefix() -> PathBuf {
    if let Some(prefix) = env::var_os("LEAN_PREFIX") {
        return PathBuf::from(prefix);
    }
    let output = Command::new("lean")
        .arg("--print-prefix")
        .output()
        .expect("set LEAN_PREFIX or place the pinned `lean` executable on PATH");
    assert!(output.status.success(), "`lean --print-prefix` failed");
    PathBuf::from(
        String::from_utf8(output.stdout)
            .expect("Lean prefix is UTF-8")
            .trim(),
    )
}

fn main() {
    println!("cargo:rerun-if-env-changed=LEAN_PREFIX");
    let runtime = lean_prefix().join("lib/lean");
    println!("cargo:rustc-link-search=native={}", runtime.display());
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", runtime.display());
}
