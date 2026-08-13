// Detect the rustc_private MonoItem path exposed by the selected rustc.

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=RUSTC");
    println!("cargo:rerun-if-env-changed=RUSTFLAGS");
    println!("cargo:rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    println!("cargo:rustc-check-cfg=cfg(rustc_middle_mir_mono)");

    if probe_mir_mono_path() {
        println!("cargo:rustc-cfg=rustc_middle_mir_mono");
    }

    emit_hidden_rlib_symbols();
}

/// Stop re-exporting every upstream rlib symbol from the backend dylib.
///
/// rustc loads this crate with `dlopen` and looks up exactly ONE symbol,
/// `__rustc_codegen_backend`. But `crate-type = ["dylib"]` is a *Rust* dylib,
/// so rustc's generated version script exports the public symbols of every
/// statically linked rlib as well — measured here: 11,914 exported dynamic
/// symbols, a 1.45 MB `.dynstr`, and 6,438 symbolic relocations that the
/// dynamic linker must resolve on EVERY rustc invocation.
///
/// `--exclude-libs,ALL` makes symbols pulled from archive members (all our
/// rlibs) local. `__rustc_codegen_backend` lives in this crate's own object,
/// not an archive, so it stays exported and `dlsym` still finds it.
///
/// Measured on aarch64 (Cortex-X925, min-of-25 / 41 paired rounds):
///   exported dynsyms  11,914 -> 109
///   .dynstr           1,453,689 -> 68,926 bytes
///   symbolic relocs   6,438 -> 795   (total 25,804 -> 20,667)
///   loader-touched metadata  2,467,573 -> 585,892 bytes (602 -> 143 pages)
///   dlopen            0.86 ms -> 0.19 ms
///   in-rustc load     1.59 ms -> ~0.03 ms  (faster in 41/41 paired rounds)
/// Emitted code is byte-identical: verified by sha256 of the same benchmark
/// compiled to the same output path at -Copt-level 0/1/2/3
/// (`scripts/dylib_codegen_identity.sh`).
///
/// ELF-only: `--exclude-libs` is a GNU ld / lld flag. Mach-O's ld64 has no
/// equivalent and errors on it, so gate on the target OS.
fn emit_hidden_rlib_symbols() {
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();
    let elf = !matches!(target_os.as_str(), "macos" | "ios" | "windows") && target_env != "msvc";
    if elf {
        println!("cargo:rustc-link-arg=-Wl,--exclude-libs,ALL");
    }
}

fn probe_mir_mono_path() -> bool {
    let rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR is set by cargo"));
    let probe = out_dir.join("probe_mir_mono.rs");
    let output = out_dir.join("probe_mir_mono.rmeta");

    fs::write(
        &probe,
        r#"
#![feature(rustc_private)]
extern crate rustc_middle;

use rustc_middle::mir::mono::MonoItem;

fn probe<'tcx>() {
    let _ = core::mem::size_of::<Option<MonoItem<'tcx>>>();
}
"#,
    )
    .expect("write rustc_middle::mir::mono probe");

    let mut command = Command::new(rustc);
    command
        .arg("--crate-name")
        .arg("rustc_codegen_trust_cg_probe_mir_mono")
        .arg("--crate-type=rlib")
        .arg("--emit=metadata")
        .arg(&probe)
        .arg("-o")
        .arg(&output);

    add_rustflags(&mut command);

    command.status().is_ok_and(|status| status.success())
}

fn add_rustflags(command: &mut Command) {
    if let Some(encoded) = env::var_os("CARGO_ENCODED_RUSTFLAGS") {
        for flag in encoded.to_string_lossy().split('\x1f') {
            if !flag.is_empty() {
                command.arg(flag);
            }
        }
        return;
    }

    if let Some(flags) = env::var_os("RUSTFLAGS") {
        for flag in flags.to_string_lossy().split_whitespace() {
            command.arg(flag);
        }
    }
}
