#[path = "support/target_dir.rs"]
mod target_dir_support;

// E2E (aarch64-apple-darwin): a `MonoItem::Static` lowered to its own object.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// This pins the plain-data `MonoItem::Static` cases end-to-end on aarch64. The
// immutable lane checks exact scalar / byte-array initializer bytes in exported
// read-only globals. The mutable lane checks that one canonical writable global
// is shared by Rust reader/writer objects and a C driver. Together they cover
// definition, import, section writability, relocation, linkage, and run-time
// state identity (without the static arm, the symbols are undefined at link).
//
// PROOF GATE: compiled with `TCG_NO_PROOF_CERTS=1`. Per-instruction mappings
// exist, but the final Mach-O object emits compact-unwind and global-data
// `ARM64_RELOC_UNSIGNED` rows. The complete production-surface inventory exposes
// those still-unproven rows, so these runtime checks must not claim
// certification or exact-object binding.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            let Some((_, value)) = raw_channel.split_once('=') else {
                continue;
            };
            return value.trim().trim_matches('"').to_owned();
        }
    }
    panic!("rust-toolchain.toml did not contain a channel");
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run static-data test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn aarch64_std_available() -> bool {
    let output = Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output();
    match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line.trim() == TARGET),
        Err(_) => false,
    }
}

fn host_is_aarch64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_sd_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// The static-only crate: immutable, plain scalar / byte-array statics with NO
/// internal pointers — the simplest sound `MonoItem::Static` shape the bridge
/// admits. `#[no_mangle]` so the C driver can name the symbols directly.
const STATIC_CRATE: &str = "\
#![no_std]\n\
#![no_main]\n\
#[no_mangle]\npub static AY_STATIC_N: u32 = 0xDEAD_BEEF;\n\
#[no_mangle]\npub static AY_STATIC_BYTES: [u8; 4] = [0x42, 0x43, 0x00, 0x44];\n\
#[no_mangle]\npub static AY_STATIC_W: u64 = 0x0102_0304_0506_0708;\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

/// C driver: reads each static through its `extern` symbol and returns 0 only if
/// every byte matches. A wrong byte / layout / section silently miscompiles the
/// read, surfacing as a nonzero exit.
const DRIVER_C: &str = "\
#include <stdint.h>\n\
extern const uint32_t AY_STATIC_N;\n\
extern const uint8_t  AY_STATIC_BYTES[4];\n\
extern const uint64_t AY_STATIC_W;\n\
int main(void){\n\
    if (AY_STATIC_N != 0xDEADBEEFu) return 1;\n\
    if (AY_STATIC_BYTES[0] != 0x42) return 2;\n\
    if (AY_STATIC_BYTES[1] != 0x43) return 3;\n\
    if (AY_STATIC_BYTES[2] != 0x00) return 4;\n\
    if (AY_STATIC_BYTES[3] != 0x44) return 5;\n\
    if (AY_STATIC_W != 0x0102030405060708ull) return 6;\n\
    return 0;\n\
}\n";

#[test]
fn immutable_statics_emit_correct_bytes_and_link_runs_aarch64() {
    if !host_is_aarch64_macos() {
        eprintln!("skipping: requires an aarch64-apple-darwin host");
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }

    let dylib = ensure_dylib_built();
    let dir = workdir("immutable");

    // 1. Compile the static-only crate THROUGH THE BRIDGE to an object.
    let src_path = dir.join("statics.rs");
    std::fs::write(&src_path, STATIC_CRATE).expect("write source");
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let obj_out = dir.join("statics");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .env("TCG_NO_PROOF_CERTS", "1")
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bridge failed to compile the static-only crate. stderr: <<<{stderr}>>>"
    );

    // rustc places each `static` in its own CGU, so the bridge emits one object
    // PER static. Collect them ALL — the static symbols are spread across them.
    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(
        !objs.is_empty(),
        "bridge produced no object file. stderr: <<<{stderr}>>>"
    );

    // Each static symbol must be DEFINED (as a GLOBAL symbol) in some object —
    // the whole point of the `MonoItem::Static` arm. `nm` prints a defined data
    // symbol with an uppercase section letter (e.g. `S`); a `U` is undefined and
    // a lowercase letter is local (not exported), neither of which links from a C
    // driver.
    let nm_all: String = objs
        .iter()
        .map(|o| {
            String::from_utf8_lossy(&Command::new("nm").arg(o).output().expect("nm").stdout)
                .into_owned()
        })
        .collect();
    for sym in ["_AY_STATIC_N", "_AY_STATIC_BYTES", "_AY_STATIC_W"] {
        assert!(
            nm_all.lines().any(|l| {
                let mut it = l.split_whitespace();
                let kind = it.nth(1);
                let name = it.next();
                // Exported defined symbol: a non-`U`, UPPERCASE section letter.
                name == Some(sym)
                    && kind
                        .map(|k| k != "U" && k.chars().all(|c| c.is_ascii_uppercase()))
                        .unwrap_or(false)
            }),
            "static symbol {sym} is not DEFINED+EXPORTED in any bridge object.\nnm:\n{nm_all}"
        );
    }

    // 2. Link ALL bridge objects with a C driver that reads the statics.
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, DRIVER_C).expect("write driver.c");
    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin).arg(&driver_path);
    for o in &objs {
        link.arg(o);
    }
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed (the static symbols must be defined+exported). stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    // 3. RUN: exit 0 iff every static byte read back correctly.
    let run = Command::new(&bin).output().expect("run linked binary");
    let code = run.status.code().expect("process terminated by signal");
    assert_eq!(
        code, 0,
        "static-read driver returned {code} (nonzero == a wrong byte/layout/section for some \
         static; exit code identifies which check failed)"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A mutable static is one canonical writable global. Its defining object owns
/// the initialized bytes; Rust functions in other objects import that symbol;
/// and foreign code can read and write the same storage. Exercising both
/// directions catches a read-only-section mistake, a per-object copy, a missing
/// undefined-external relocation, or a non-exported definition.
#[test]
fn mutable_static_is_shared_writable_and_link_runs_aarch64() {
    if !host_is_aarch64_macos() || !aarch64_std_available() {
        eprintln!("skipping: requires an aarch64-apple-darwin host with rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("mutable");
    let src = "\
#![no_std]\n#![no_main]\n\
#[no_mangle]\npub static mut AY_STATIC_MUT: u32 = 7;\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_static_get() -> u32 { AY_STATIC_MUT }\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_static_set(value: u32) { AY_STATIC_MUT = value; }\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";
    let src_path = dir.join("mut.rs");
    std::fs::write(&src_path, src).expect("write source");
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let obj_out = dir.join("mut");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .env("TCG_NO_PROOF_CERTS", "1")
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bridge failed to compile the mutable-static crate. stderr: <<<{stderr}>>>"
    );

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(
        !objs.is_empty(),
        "bridge produced no object file. stderr: <<<{stderr}>>>"
    );

    let nm_all: String = objs
        .iter()
        .map(|o| {
            String::from_utf8_lossy(&Command::new("nm").arg(o).output().expect("nm").stdout)
                .into_owned()
        })
        .collect();
    let definitions = nm_all
        .lines()
        .filter(|line| {
            let mut fields = line.split_whitespace();
            let kind = fields.nth(1);
            let name = fields.next();
            name == Some("_AY_STATIC_MUT")
                && kind
                    .map(|kind| kind != "U" && kind.chars().all(|c| c.is_ascii_uppercase()))
                    .unwrap_or(false)
        })
        .count();
    assert_eq!(
        definitions, 1,
        "mutable static must have exactly one exported definition. nm:\n{nm_all}"
    );

    let driver = "\
#include <stdint.h>\n\
extern uint32_t AY_STATIC_MUT;\n\
extern uint32_t ay_static_get(void);\n\
extern void ay_static_set(uint32_t);\n\
int main(void) {\n\
    if (AY_STATIC_MUT != 7u) return 1;\n\
    if (ay_static_get() != 7u) return 2;\n\
    AY_STATIC_MUT = 19u;\n\
    if (ay_static_get() != 19u) return 3;\n\
    ay_static_set(42u);\n\
    if (AY_STATIC_MUT != 42u) return 4;\n\
    return 0;\n\
}\n";
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, driver).expect("write driver.c");
    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin).arg(&driver_path);
    for obj in &objs {
        link.arg(obj);
    }
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed (mutable definition/imports must resolve once). stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin).output().expect("run linked binary");
    let code = run.status.code().expect("process terminated by signal");
    assert_eq!(
        code, 0,
        "mutable-static driver returned {code}; the exit code identifies which shared-state \
         observation failed"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
