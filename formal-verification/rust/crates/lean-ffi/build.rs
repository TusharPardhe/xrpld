use std::{env, path::PathBuf, process::Command};

fn run(command: &mut Command) {
    assert!(
        command
            .status()
            .expect("failed to execute native build command")
            .success(),
        "native build command failed: {command:?}"
    );
}

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
    for name in ["LEAN_PREFIX", "LEAN_MODEL_LIB", "LEAN_DEPS_LIB"] {
        println!("cargo:rerun-if-env-changed={name}");
    }

    let manifest = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("Cargo manifest dir"));
    let verification_root = manifest.join("../../..");
    let lean_root = verification_root.join("lean");
    let prefix = lean_prefix();
    let model_lib = env::var_os("LEAN_MODEL_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| lean_root.join(".lake/build/lib"));
    let dependency_lib = env::var_os("LEAN_DEPS_LIB").map(PathBuf::from);
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo output dir"));
    let archive = out.join("liblean_bridge_shim.a");
    let profile = env::var("PROFILE").expect("Cargo profile");
    let optimization = if profile == "release" { "-O3" } else { "-O0" };
    let debug = if profile == "release" {
        "-DNDEBUG"
    } else {
        "-g"
    };

    let sources = [
        "lean_bridge_shim.c",
        "iou_bridge.c",
        "int_bridge.c",
        "stamount_bridge.c",
        "vault_bridge.c",
        "vault_bridge_ops.c",
        "vault_wire_bridge.c",
        "lending_bridge.c",
    ];
    let objects: Vec<_> = sources
        .iter()
        .map(|name| {
            let source = manifest.join("native").join(name);
            let object = out.join(format!("{name}.o"));
            let mut command = Command::new("clang");
            command
                .args([
                    "-std=c11",
                    optimization,
                    debug,
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                ])
                .arg(format!("-I{}", prefix.join("include").display()))
                .arg("-c")
                .arg(&source)
                .arg("-o")
                .arg(&object);
            run(&mut command);
            println!("cargo:rerun-if-changed={}", source.display());
            object
        })
        .collect();

    let mut archive_command = Command::new("libtool");
    archive_command
        .arg("-static")
        .arg("-o")
        .arg(&archive)
        .args(&objects);
    run(&mut archive_command);

    for header in [
        "iou_bridge.h",
        "int_bridge.h",
        "stamount_bridge.h",
        "vault_bridge.h",
        "lending_bridge.h",
    ] {
        println!(
            "cargo:rerun-if-changed={}",
            manifest.join("native").join(header).display()
        );
    }
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-search=native={}", model_lib.display());
    println!(
        "cargo:rustc-link-search=native={}",
        prefix.join("lib/lean").display()
    );
    println!("cargo:rustc-link-lib=static=lean_bridge_shim");
    println!("cargo:rustc-link-lib=static=XRPL_XRPLModel");
    if let Some(path) = dependency_lib {
        println!("cargo:rustc-link-search=native={}", path.display());
        println!("cargo:rustc-link-lib=static=LeanDeps");
        println!("cargo:rustc-link-lib=static=Lake");
    } else {
        println!(
            "cargo:warning=LEAN_DEPS_LIB is unset; set it when the model archive requires the prebuilt Lean dependency bundle"
        );
    }
    println!("cargo:rustc-link-lib=dylib=leanshared");
    println!(
        "cargo:rustc-link-arg=-Wl,-rpath,{}",
        prefix.join("lib/lean").display()
    );
}
