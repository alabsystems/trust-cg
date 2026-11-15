#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// crates/rustc-codegen-trust-cg/tests/mir_lane_valid_trust_ir.rs
//
// WS7.3-pre: the in-process MIR lane must emit VALID trust-ir.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WS7.3 makes every trust-cg ingestion entry refuse what trust-ir's validator
// refuses. Measured 2026-10-07 (the WS7.3 salvage probe, the two functions
// below): this lane's output for ordinary Rust was refused, because the lane
//
//   * read slot fields with an `ExtractField` whose aggregate operand is the
//     slot POINTER (`FieldAccessInvalid`, and every use of the result then
//     mistyped: `CastOperandTypeMismatch inttoptr operand [ty.3 x 2]`);
//   * passed a slot address where the callee declares the aggregate
//     (`CallArgTypeMismatch expected [ty.3 x 1], got ptr` on `Option::map`'s
//     `FnOnce::call_once`) or a reference (`expected &[ty.3 x 3], got ptr` on
//     `core::slice::from_raw_parts`'s `#[track_caller]` location), and
//     returned a slot address where the signature names the aggregate.
//
// THE GATE: the probe compiles through the backend (proof certificates off —
// this is a lowering check, not proof evidence) with `dump-trust-ir`, and EVERY
// module the backend handed to trust-cg passes `trust_ir_build::validate_module`
// at the pinned trust-ir. A refusal fails the test too: an IR the lane cannot
// emit cannot be validated. The run-twin below builds the same functions into
// an executable and compares it with LLVM, so the migrated reads and edges are
// also held to the values they compute.
//
// HOST-NATIVE: no `--target`.

use std::path::{Path, PathBuf};
use std::process::Command;

const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

/// The WS7.3 salvage probe (`mir-lane-probe.rs`): a slice sum through
/// `core::slice::from_raw_parts` and the slice iterator, and `Option::map` over
/// a fn item.
const PROBE_LIB: &str = r#"#![crate_type = "lib"]
#[no_mangle]
pub extern "C" fn sum(xs: *const u64, n: usize) -> u64 {
    let s: &[u64] = unsafe { core::slice::from_raw_parts(xs, n) };
    let mut t = 0u64;
    for x in s {
        t = t.wrapping_add(*x);
    }
    t
}
#[no_mangle]
pub extern "C" fn neg_opt(v: u64, some: bool) -> u64 {
    let o = if some { Some(v) } else { None };
    o.map(u64::wrapping_neg).unwrap_or(7)
}
"#;

/// The same two functions in an executable whose exit code is their results.
const PROBE_BIN: &str = r#"
#[inline(never)]
fn sum(xs: *const u64, n: usize) -> u64 {
    let s: &[u64] = unsafe { core::slice::from_raw_parts(xs, n) };
    let mut t = 0u64;
    for x in s {
        t = t.wrapping_add(*x);
    }
    t
}
#[inline(never)]
fn neg_opt(v: u64, some: bool) -> u64 {
    let o = if some { Some(v) } else { None };
    o.map(u64::wrapping_neg).unwrap_or(7)
}
fn main() {
    let xs = std::hint::black_box([3u64, 5, 11, 13]);
    let n = std::hint::black_box(xs.len());
    let a = sum(xs.as_ptr(), n); // 32
    let b = neg_opt(std::hint::black_box(9), std::hint::black_box(true)); // -9
    let c = neg_opt(std::hint::black_box(9), std::hint::black_box(false)); // 7
    let code = a.wrapping_add(b).wrapping_add(c); // 30
    std::process::exit((code & 0x7f) as i32);
}
"#;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_ws73pre_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
    arg.push(dylib);
    arg
}

/// The `.trust_irbin` modules `dump-trust-ir` wrote into `dir`.
fn dumped_modules(dir: &Path) -> Vec<PathBuf> {
    let mut modules: Vec<PathBuf> = std::fs::read_dir(dir)
        .map(|entries| {
            entries
                .filter_map(Result::ok)
                .map(|entry| entry.path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
                .collect()
        })
        .unwrap_or_default();
    modules.sort();
    modules
}

/// Every module the backend compiled for the probe library passes trust-ir's
/// validator, at -O0 and -O2.
#[test]
fn mir_lane_probe_modules_validate() {
    if toolchain_support::skip_without_backend_knobs("mir_lane_probe_modules_validate") {
        return;
    }
    let backend = backend_artifact_support::current_test_backend();
    let mut failures = Vec::new();
    let mut validated = 0usize;
    for opt in OPT_LEVELS {
        let dir = workdir(&format!("lib_{}", opt.replace('=', "_")));
        let dump = dir.join("dump");
        let src = dir.join("probe.rs");
        std::fs::write(&src, PROBE_LIB).expect("write probe");
        let knobs = toolchain_support::backend_knobs_arg(&[
            "no-proof-certs",
            &format!("dump-trust-ir={}", dump.display()),
        ]);
        let output = toolchain_support::rustc_command()
            .args(["-Cpanic=abort", "-Ccodegen-units=1"])
            .arg(opt)
            .arg(backend_arg(&backend))
            .arg(knobs)
            .arg("-o")
            .arg(dir.join("libprobe.rlib"))
            .arg(&src)
            .output()
            .expect("spawn the compiler");
        if !output.status.success() {
            failures.push(format!(
                "{opt}: the backend refused the probe (it must compile):\n{}",
                String::from_utf8_lossy(&output.stderr)
            ));
            continue;
        }
        let modules = dumped_modules(&dump);
        let mut functions = Vec::new();
        for path in &modules {
            let bytes = std::fs::read(path).expect("read dumped module");
            let module = match trust_ir::binary::deserialize_module(&bytes) {
                Ok(module) => module,
                Err(err) => {
                    failures.push(format!(
                        "{opt}: {}: does not decode: {err:?}",
                        path.display()
                    ));
                    continue;
                }
            };
            functions.extend(module.functions.iter().map(|f| f.name.clone()));
            let errors = trust_ir_build::validate_module(&module);
            validated += 1;
            if !errors.is_empty() {
                failures.push(format!(
                    "{opt}: module `{}` is not valid trust-ir ({} finding(s)):\n  {}",
                    module.name,
                    errors.len(),
                    errors
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join("\n  ")
                ));
            }
        }
        for symbol in ["sum", "neg_opt"] {
            if !functions.iter().any(|name| name == symbol) {
                failures.push(format!(
                    "{opt}: no dumped module defines `{symbol}` (functions: {functions:?}) — \
                     the check would be vacuous"
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    println!("WS73PRE_VALID modules={validated} opts=0,2");
    positive_evidence::record(
        positive_evidence::Evidence::Compiled,
        positive_evidence::Certs::Off,
    );
}

/// The probe's functions, built into an executable by the backend, compute
/// what LLVM's build computes.
#[test]
fn mir_lane_probe_matches_llvm() {
    if toolchain_support::skip_without_backend_knobs("mir_lane_probe_matches_llvm") {
        return;
    }
    let backend = backend_artifact_support::current_test_backend();
    let mut failures = Vec::new();
    for opt in OPT_LEVELS {
        let dir = workdir(&format!("bin_{}", opt.replace('=', "_")));
        let src = dir.join("probe.rs");
        std::fs::write(&src, PROBE_BIN).expect("write probe");
        let mut runs = Vec::new();
        for side in ["llvm", "cg"] {
            let bin = dir.join(side);
            let mut cmd = toolchain_support::rustc_command();
            cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"])
                .arg(opt);
            if side == "cg" {
                cmd.arg(backend_arg(&backend))
                    .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
            }
            let output = cmd
                .arg("-o")
                .arg(&bin)
                .arg(&src)
                .output()
                .expect("spawn the compiler");
            if !output.status.success() {
                failures.push(format!(
                    "{opt} {side}: compile failed:\n{}",
                    String::from_utf8_lossy(&output.stderr)
                ));
                break;
            }
            let run = Command::new(&bin).output().expect("run the probe");
            runs.push(run.status.code());
        }
        if let [llvm, cg] = runs.as_slice() {
            if *llvm != Some(30) {
                failures.push(format!("{opt}: the LLVM oracle exited {llvm:?}, not 30"));
            } else if cg != llvm {
                failures.push(format!(
                    "{opt}: MISCOMPILE: backend exited {cg:?}, LLVM {llvm:?}"
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
