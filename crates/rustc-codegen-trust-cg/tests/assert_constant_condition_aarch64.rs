// Compiled only on an aarch64-apple-darwin host: another host builds this
// target with no test in it, never one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// A MIR `Assert` whose condition is a compile-time constant equal to its
// expected value emits no panic path, as rustc's own codegen does.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `codegen_assert_terminator` skips the panic block when the condition is a
// known constant ("Don't codegen the panic block if success known"). A constant
// array index at -O0 leaves exactly that shape — `_5 = Lt(const 0_usize, const
// 2_usize); assert(move _5, ..)` — and LLVM's IR builder folds the compare, so
// rustc's object names no `panic_bounds_check`. Once every failed assert raises
// rustc's exact panic entry, the bridge must make the same call: a `no_std`
// object a C driver links without `core` otherwise fails with an undefined
// `panic_bounds_check`. The control keeps the reference where the index is
// not a constant, so the fold cannot be satisfied by dropping every check.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

const SRC: &str = "\
#![no_std]\n#![no_main]\n\
static TABLE: [u32; 2] = [7, 11];\n\
#[no_mangle]\npub extern \"C\" fn ay_const_index() -> u32 {\n\
    let t = core::hint::black_box(TABLE);\n\
    t[0].wrapping_mul(3).wrapping_add(t[1])\n\
}\n\
#[no_mangle]\npub extern \"C\" fn ay_const_index_signed() -> i32 {\n\
    let t: [i32; 3] = core::hint::black_box([-4, 5, 6]);\n\
    t[2] - t[0]\n\
}\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

const CONTROL_SRC: &str = "\
#![no_std]\n#![no_main]\n\
#[no_mangle]\npub extern \"C\" fn ay_dynamic_index(i: usize) -> u32 {\n\
    let t: [u32; 2] = core::hint::black_box([7, 11]);\n\
    t[i]\n\
}\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

const DRIVER_C: &str = "\
#include <stdint.h>\n\
extern uint32_t ay_const_index(void);\n\
extern int32_t ay_const_index_signed(void);\n\
int main(void) {\n\
    if (ay_const_index() != 7u * 3u + 11u) return 1;\n\
    if (ay_const_index_signed() != 10) return 2;\n\
    return 0;\n\
}\n";

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_acc_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` to objects in `dir` at `-Copt-level=0`, with the bridge when
/// `bridge` is set and with LLVM otherwise. Returns the object paths.
fn compile_objects(dir: &Path, src: &str, bridge: bool) -> Vec<PathBuf> {
    let src_path = dir.join("lib.rs");
    std::fs::write(&src_path, src).expect("write source");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "staticlib", "--crate-name", "acc"]);
    if bridge {
        let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
        backend.push(backend_artifact_support::current_test_backend());
        cmd.arg(backend)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let output = cmd
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Cdebug-assertions=off",
        ])
        .args(["-Copt-level=0", "-Ccodegen-units=1", "--emit=obj", "-o"])
        .arg(dir.join("acc"))
        .arg(&src_path)
        .output()
        .expect("spawn rustc");
    assert!(
        output.status.success(),
        "{} compile failed: {}",
        if bridge { "bridge" } else { "LLVM" },
        String::from_utf8_lossy(&output.stderr)
    );
    let mut objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    // One codegen unit through LLVM is written to the `-o` path itself.
    if objects.is_empty() && dir.join("acc").is_file() {
        objects.push(dir.join("acc"));
    }
    assert!(!objects.is_empty(), "no object in {}", dir.display());
    objects
}

/// Whether any of `objects` has an undefined reference to a symbol whose name
/// contains `panic_bounds_check`.
fn references_panic_bounds_check(objects: &[PathBuf]) -> bool {
    objects.iter().any(|object| {
        let out = Command::new("nm")
            .arg("-u")
            .arg(object)
            .output()
            .expect("spawn nm");
        assert!(out.status.success(), "nm -u {} failed", object.display());
        String::from_utf8_lossy(&out.stdout).contains("panic_bounds_check")
    })
}

#[test]
fn constant_condition_assert_emits_no_panic_path_aarch64() {
    darwin_native::require("assert_constant_condition_aarch64", &["cc", "nm"]);

    for bridge in [false, true] {
        let tag = if bridge { "bridge" } else { "llvm" };
        let dir = workdir(&format!("const_{tag}"));
        let objects = compile_objects(&dir, SRC, bridge);
        assert!(
            !references_panic_bounds_check(&objects),
            "{tag}: a constant in-bounds index must not reference panic_bounds_check"
        );
        let bin = dir.join("bin");
        let driver = dir.join("driver.c");
        std::fs::write(&driver, DRIVER_C).expect("write driver");
        let link = Command::new("cc")
            .arg("-o")
            .arg(&bin)
            .arg(&driver)
            .args(&objects)
            .output()
            .expect("spawn cc");
        assert!(
            link.status.success(),
            "{tag}: link without core failed: {}",
            String::from_utf8_lossy(&link.stderr)
        );
        let run = Command::new(&bin).output().expect("run");
        assert_eq!(
            run.status.code(),
            Some(0),
            "{tag}: driver exit {:?}",
            run.status
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    // Control: a run-time index keeps its check, and its failure edge raises.
    for bridge in [false, true] {
        let tag = if bridge { "bridge" } else { "llvm" };
        let dir = workdir(&format!("dyn_{tag}"));
        let objects = compile_objects(&dir, CONTROL_SRC, bridge);
        assert!(
            references_panic_bounds_check(&objects),
            "{tag}: a run-time index must keep its panic_bounds_check raise"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
    println!("ASSERT_CONSTANT_CONDITION const_index=folded dynamic_index=raises");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
