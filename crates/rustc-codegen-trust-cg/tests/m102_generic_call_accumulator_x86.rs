// Differential regression test for MISCOMPILE #102: a loop-carried accumulator
// reassigned by a GENERIC TRAIT-METHOD `Call` rvalue was dropped at -O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. `s = s + x` where `+` is a generic trait method (`<i32 as Add>::add`,
// also Mul/Sub/a custom trait) lowers to a `Call` TERMINATOR whose `destination`
// is `s` — a genuine reassignment of the loop-carried accumulator. But the bridge's
// `compute_loop_header_params` derived its scalar def-sites from STATEMENTS only
// (`statement_scalar_def`), never from a `Call` terminator's destination. So a `s`
// updated ONLY by a call was treated as loop-INVARIANT: no loop-header phi was
// created for it, the call result was never threaded across the loop back-edge, and
// `s` kept its ENTRY value (`init`). At -O0 the register allocator happened to
// coalesce the call-result register and the accumulator's register into the same
// chain, so it accidentally worked (returned the right value); at -O3 coalescing
// separated them, exposing the dropped result — `sumv(&[40], 5)` returned 5 (the
// init) instead of 45. (A non-generic `s = s + x` is a primitive `BinaryOp`
// STATEMENT, already caught; a generic INDEX loop `s = s + v[i]` likewise; only the
// loop-carried accumulator whose SOLE in-loop def is a trait-method Call was lost.)
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs).
//   * `terminator_scalar_def`: a `Call` terminator's unprojected destination local
//     is a scalar def-site.
//   * `compute_loop_header_params` counts it, so a call-updated loop-carried
//     accumulator becomes a header phi and the result is threaded on the back-edge.
//   * `block_upward_uses_and_defs` also registers it as a def, so the call-result
//     TEMP's liveness is killed at its def block (otherwise it propagated backward
//     as spuriously live across the loop header and became a bogus header param
//     with no value on the entry edge — a fail-closed regression at -O0).
//
// SOUNDNESS BACKSTOP (regalloc translation validator). The fix also makes the
// accumulator recurrence VREG-VISIBLE (the call result now flows into the
// accumulator through a vreg block-arg/copy rather than only a physical result
// register). The validator's value-flow therefore now DETECTS a wrong back-edge
// that drops the call result (spec CONFLICT vs POST DEFINITE init) — see the
// `phi_free_loop_call_result_accumulator_wrong_latch_rejected` unit test in
// `regalloc_validator.rs`. A silent miscompile of this class can no longer pass.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 0 and 3. The invariant is MATCH-OR-FAIL-CLOSED: trust-cg
// must either return the LLVM value or fail closed (compile/link error), NEVER a
// different value.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";

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
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m102 test");
    let built = target_dir
        .join("release")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn x86_64_std_available() -> bool {
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

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m102_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Build panic stubs for every undefined `*panic*` symbol so a no_std binary links.
fn write_panic_stubs(dir: &Path, objs: &[PathBuf]) -> PathBuf {
    let mut stubs = String::from("#include <stdlib.h>\n");
    let mut seen = std::collections::BTreeSet::new();
    for obj in objs {
        let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
        for line in String::from_utf8_lossy(&nm.stdout).lines() {
            let sym = line.trim().trim_start_matches('U').trim();
            if sym.contains("panic") && seen.insert(sym.to_owned()) {
                let c = sym.strip_prefix('_').unwrap_or(sym);
                stubs.push_str(&format!(
                    "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
                ));
            }
        }
    }
    let stubs_path = dir.join("stubs.c");
    std::fs::write(&stubs_path, stubs).expect("write stubs");
    stubs_path
}

/// Compile + link + run; returns `Some(exit_code)` on success or `None` when the
/// trust-cg backend FAILED CLOSED (a compile or link error). A `None` from the
/// trust path is an ACCEPTABLE outcome (a safe coverage gap); a `None` from the
/// LLVM oracle is a test bug.
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> Option<i32> {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    if !output.status.success() {
        // The trust-cg backend is allowed to fail CLOSED (e.g. an unsupported MIR
        // shape skipped, so a required symbol is missing). That is match-or-fail-
        // closed-compliant. The LLVM oracle must always compile.
        if dylib.is_some() {
            let _ = std::fs::remove_dir_all(&dir);
            return None;
        }
        panic!(
            "{stem} (opt={opt}, LLVM): failed to compile. stderr: <<<{}>>>",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    if objs.is_empty() {
        let _ = std::fs::remove_dir_all(&dir);
        // No object: a fail-closed skip on the trust path is acceptable.
        return if dylib.is_some() { None } else { panic!("{stem} (opt={opt}, LLVM): no object") };
    }

    let stubs_path = write_panic_stubs(&dir, &objs);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    if !link.status.success() {
        let _ = std::fs::remove_dir_all(&dir);
        // A link failure on the trust path (e.g. a skipped fail-closed function
        // left an undefined symbol) is an acceptable fail-closed outcome.
        if dylib.is_some() {
            return None;
        }
        panic!(
            "{stem} (opt={opt}, LLVM): link failed. stderr: <<<{}>>>",
            String::from_utf8_lossy(&link.stderr)
        );
    }

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    Some(run.status.code().expect("process terminated by signal"))
}

/// MATCH-OR-FAIL-CLOSED differential at O0 AND O3: trust-cg must return the LLVM
/// value or fail closed, NEVER a different value.
fn differential_program(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n{body}\n"
    );
    for opt in ["0", "3"] {
        let llvm = compile_link_run(stem, &src, opt, None)
            .expect("LLVM oracle must compile and run");
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        match compile_link_run(stem, &src, opt, Some(&dylib)) {
            Some(trust) => assert_eq!(
                trust, llvm,
                "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} \
                 (SILENT MISCOMPILE — the m102 class)"
            ),
            None => eprintln!(
                "{stem} (opt={opt}): trust-cg failed CLOSED (acceptable: match-or-fail-closed)"
            ),
        }
    }
}

const SUMV: &str =
    "use core::ops::Add;\n\
     #[inline(never)] fn sumv<T: Add<Output=T> + Copy>(v:&[T], init:T)->T{ \
        let mut s=init; for &x in v { s = s + x; } s }\n";
const PRODV: &str =
    "use core::ops::Mul;\n\
     #[inline(never)] fn prodv<T: Mul<Output=T> + Copy>(v:&[T], init:T)->T{ \
        let mut s=init; for &x in v { s = s * x; } s }\n";
const SUBV: &str =
    "use core::ops::Sub;\n\
     #[inline(never)] fn subv<T: Sub<Output=T> + Copy>(v:&[T], init:T)->T{ \
        let mut s=init; for &x in v { s = s - x; } s }\n";
// A user-defined trait (not a std operator) — same loop-carried-via-Call shape.
const COMBV: &str =
    "trait Combine { fn comb(self, o:Self)->Self; }\n\
     impl Combine for i32 { #[inline(never)] fn comb(self,o:i32)->i32 { \
        self.wrapping_mul(2).wrapping_add(o) } }\n\
     #[inline(never)] fn combv<T: Combine + Copy>(v:&[T], init:T)->T{ \
        let mut s=init; for &x in v { s = s.comb(x); } s }\n";

/// The minimized repro: `sumv(&[40], 5)` => 40 + 5 = 45 (was 5 at O3).
#[test]
fn m102_generic_add_single_element_matches_llvm() {
    differential_program(
        "add_single",
        &format!("{SUMV}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            (sumv(&[40i32], 5) % 120) as i32 }}"),
        45,
    );
}

/// Multi-element generic Add accumulator with a non-zero init.
#[test]
fn m102_generic_add_multi_element_matches_llvm() {
    differential_program(
        "add_multi",
        &format!("{SUMV}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            sumv(&[1i32,2,3,4,5], 100) }}"),
        // 100 + 1+2+3+4+5 = 115
        115,
    );
}

/// Generic Mul accumulator (`prodv`).
#[test]
fn m102_generic_mul_accumulator_matches_llvm() {
    differential_program(
        "mul_acc",
        &format!("{PRODV}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            prodv(&[2i32,3,4], 1) }}"),
        // 1 * 2*3*4 = 24
        24,
    );
}

/// Generic Sub accumulator (`subv`) — order-sensitive, so a dropped update shows.
#[test]
fn m102_generic_sub_accumulator_matches_llvm() {
    differential_program(
        "sub_acc",
        &format!("{SUBV}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            subv(&[1i32,2,3], 100) }}"),
        // 100 - 1 - 2 - 3 = 94
        94,
    );
}

/// A USER-DEFINED trait method as the accumulator update (not a std operator).
#[test]
fn m102_custom_trait_accumulator_matches_llvm() {
    differential_program(
        "custom_trait",
        &format!("{COMBV}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            combv(&[1i32,2,3], 0) }}"),
        // ((0*2+1)*2+2)*2+3 = (1)*2+2=4; 4*2+3 = 11
        11,
    );
}

/// Wider element type (i64 accumulator) folded to i32 at the boundary.
#[test]
fn m102_generic_add_i64_accumulator_matches_llvm() {
    differential_program(
        "add_i64",
        &format!("{SUMV}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            sumv(&[10i64,20,30], 0i64) as i32 }}"),
        // 0 + 10+20+30 = 60
        60,
    );
}

/// Empty slice: the accumulator must keep exactly its init (no iterations).
#[test]
fn m102_generic_add_empty_slice_keeps_init_matches_llvm() {
    differential_program(
        "add_empty",
        &format!("{SUMV}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            sumv(&[] as &[i32], 7) }}"),
        7,
    );
}
