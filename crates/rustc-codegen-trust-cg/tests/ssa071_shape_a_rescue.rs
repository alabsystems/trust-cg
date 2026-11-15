#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// SSA-071 phase-2 bridge regression: a dead same-typed loop node may be
// rescued only when the value is positively attributable to MIR locals that
// are all write-only. These compile-only cases exercise the real
// MIR -> trust-ir -> ssa_loop_complete gate, not a duplicate of its predicate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::path::{Path, PathBuf};

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trustcg_ssa071_shape_a_{stem}_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create test workdir");
    dir
}

fn compile_object(stem: &str, source: &str, dylib: &Path) -> (bool, String) {
    let dir = workdir(stem);
    let source_path = dir.join("probe.rs");
    std::fs::write(&source_path, source).expect("write probe source");

    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    // The knobs go on the TRACKED `-Ztrust-ir-cg-args` option: trustc refuses
    // every `TCG_*`/`TRUST_CG_*` variable as an untracked semantic/codegen
    // control, so the environment spellings these used to use now fail the
    // compile before the backend loads.
    //
    // The two `env_remove`s are KEPT, and matter more than before: an ambient
    // `TCG_P3C_REFINE`/`TCG_REFINE` in the developer's shell would not merely
    // change the lane, it would make every compile below refuse. Not passing the
    // corresponding knob is what selects the fast lane; removing the variables
    // is what keeps the child reachable at all.
    let output = toolchain_support::rustc_command()
        .arg(toolchain_support::backend_knobs_arg(&[
            "refine-trace",
            "no-proof-certs",
            "refine-solver=0",
        ]))
        .env_remove("TCG_P3C_REFINE")
        .env_remove("TCG_REFINE")
        .arg(backend_arg)
        .args([
            "--crate-type=lib",
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
            "-Copt-level=0",
            "--emit=obj",
            "--out-dir",
        ])
        .arg(&dir)
        .arg(&source_path)
        .output()
        .expect("failed to invoke rustc");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let produced_object = std::fs::read_dir(&dir)
        .expect("read test workdir")
        .filter_map(Result::ok)
        .any(|entry| entry.path().extension().is_some_and(|ext| ext == "o"));
    let _ = std::fs::remove_dir_all(&dir);
    (output.status.success() && produced_object, stderr)
}

const DEAD_WRITE_ONLY: &str = r#"
#![no_std]

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn dead_write_only(p2: u64, n: u64) -> u64 {
    let mut i0 = 0u64;
    while i0 < n {
        let _a0 = i0 & p2;
        i0 = i0.wrapping_add(1);
    }
    p2
}
"#;

const MIR_READ: &str = r#"
#![no_std]

struct Pair {
    a: u64,
    b: u64,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn mir_read(p2: u64, n: u64) -> u64 {
    let mut i0 = 0u64;
    while i0 < n {
        let a0 = i0 & p2;
        let _reads_a0 = Pair { a: a0, b: 0 };
        i0 = i0.wrapping_add(1);
    }
    p2
}
"#;

const MIR_BORROW: &str = r#"
#![no_std]

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn mir_borrow(p2: u64, n: u64) -> u64 {
    let mut i0 = 0u64;
    while i0 < n {
        let a0 = i0 & p2;
        let _borrow = &a0;
        i0 = i0.wrapping_add(1);
    }
    p2
}
"#;

const MISSING_SCALAR_BIRTH: &str = r#"
#![no_std]

struct Pair {
    a: u64,
    b: u64,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn missing_scalar_birth(p2: u64, n: u64) -> u64 {
    let mut i0 = 0u64;
    while i0 < n {
        let mut pair = Pair { a: 0, b: 0 };
        pair.a = i0 & p2;
        i0 = i0.wrapping_add(1);
    }
    p2
}
"#;

const MIXED_RESCUED_AND_UNATTRIBUTED: &str = r#"
#![no_std]

struct Pair {
    a: u64,
    b: u64,
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn mixed(p2: u64, n: u64) -> u64 {
    let mut i0 = 0u64;
    while i0 < n {
        let _rescuable = i0 & p2;
        let mut pair = Pair { a: 0, b: 0 };
        pair.a = i0 ^ p2;
        i0 = i0.wrapping_add(1);
    }
    p2
}
"#;

const SLOT_MISTHREADED_POSTURE: &str = r#"
#![no_std]

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn slot_misthreaded_posture(p0: u64, n: u64) -> u64 {
    let mut a = 0u64;
    let mut i = 0u64;
    while i < n {
        a = i.wrapping_add(p0);
        i = i.wrapping_add(1);
    }
    a
}
"#;

fn assert_ssa071_decline(stem: &str, source: &str, dylib: &Path) -> String {
    let (ok, stderr) = compile_object(stem, source, dylib);
    assert!(!ok, "{stem} must fail closed, but it compiled:\n{stderr}");
    assert!(
        stderr.contains("[TCG-SSA-071]"),
        "{stem} declined for an unrelated reason:\n{stderr}"
    );
    stderr
}

#[test]
fn dead_write_only_value_is_rescued_at_the_real_bridge_gate() {
    // These compiles pass backend knobs on `-Ztrust-ir-cg-args`; their former
    // `TCG_*` environment spellings are refused outright, so a compiler without
    // that option cannot run this test at all. Skip honestly.
    if toolchain_support::skip_without_backend_knobs("ssa071_shape_a_rescue") {
        return;
    }
    let dylib = ensure_dylib_built();
    let (ok, stderr) = compile_object("positive", DEAD_WRITE_ONLY, &dylib);
    assert!(ok, "dead write-only shape must compile:\n{stderr}");
    assert!(
        stderr.contains("dead write-only not-threaded violation(s) rescued"),
        "compile succeeded without exercising the shape-A rescue:\n{stderr}"
    );
}

#[test]
fn mir_read_prevents_shape_a_rescue() {
    // These compiles pass backend knobs on `-Ztrust-ir-cg-args`; their former
    // `TCG_*` environment spellings are refused outright, so a compiler without
    // that option cannot run this test at all. Skip honestly.
    if toolchain_support::skip_without_backend_knobs("ssa071_shape_a_rescue") {
        return;
    }
    let dylib = ensure_dylib_built();
    let stderr = assert_ssa071_decline("read", MIR_READ, &dylib);
    assert!(!stderr.contains("dead write-only not-threaded violation(s) rescued"));
}

#[test]
fn mir_borrow_prevents_shape_a_rescue() {
    // These compiles pass backend knobs on `-Ztrust-ir-cg-args`; their former
    // `TCG_*` environment spellings are refused outright, so a compiler without
    // that option cannot run this test at all. Skip honestly.
    if toolchain_support::skip_without_backend_knobs("ssa071_shape_a_rescue") {
        return;
    }
    let dylib = ensure_dylib_built();
    let stderr = assert_ssa071_decline("borrow", MIR_BORROW, &dylib);
    assert!(!stderr.contains("dead write-only not-threaded violation(s) rescued"));
}

#[test]
fn scalarized_field_without_a_scalar_birth_stays_fail_closed() {
    // These compiles pass backend knobs on `-Ztrust-ir-cg-args`; their former
    // `TCG_*` environment spellings are refused outright, so a compiler without
    // that option cannot run this test at all. Skip honestly.
    if toolchain_support::skip_without_backend_knobs("ssa071_shape_a_rescue") {
        return;
    }
    let dylib = ensure_dylib_built();
    let stderr = assert_ssa071_decline("missing_birth", MISSING_SCALAR_BIRTH, &dylib);
    assert!(!stderr.contains("dead write-only not-threaded violation(s) rescued"));
}

#[test]
fn one_unattributed_violation_suppresses_mixed_rescues() {
    // These compiles pass backend knobs on `-Ztrust-ir-cg-args`; their former
    // `TCG_*` environment spellings are refused outright, so a compiler without
    // that option cannot run this test at all. Skip honestly.
    if toolchain_support::skip_without_backend_knobs("ssa071_shape_a_rescue") {
        return;
    }
    let dylib = ensure_dylib_built();
    let stderr = assert_ssa071_decline("mixed", MIXED_RESCUED_AND_UNATTRIBUTED, &dylib);
    assert!(!stderr.contains("dead write-only not-threaded violation(s) rescued"));
}

#[test]
fn slot_misthreading_keeps_its_existing_semantic_vc_posture() {
    // These compiles pass backend knobs on `-Ztrust-ir-cg-args`; their former
    // `TCG_*` environment spellings are refused outright, so a compiler without
    // that option cannot run this test at all. Skip honestly.
    if toolchain_support::skip_without_backend_knobs("ssa071_shape_a_rescue") {
        return;
    }
    let dylib = ensure_dylib_built();
    let (ok, stderr) = compile_object("slot", SLOT_MISTHREADED_POSTURE, &dylib);
    assert!(
        ok,
        "the existing semantic VC must keep admitting this correct structural-misthread shape:\n{stderr}"
    );
    assert!(
        stderr
            .contains("back-edge threading PROVEN (structural misthread admitted via semantic VC)"),
        "the structural-misthread shape compiled without exercising its existing semantic VC:\n{stderr}"
    );
    assert!(!stderr.contains("dead write-only not-threaded violation(s) rescued"));
}
