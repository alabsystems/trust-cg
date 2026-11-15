#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// crates/rustc-codegen-trust-cg/tests/dom_bounds_refutation_x86.rs
//
// BOUNDS-CHECK RETENTION PINS — dominated shapes that must still TRAP.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A wrongly-dropped bounds check is a SILENT out-of-bounds write, so these
// shapes get bridge-only behavioral pins (they go OUT OF BOUNDS at runtime, so
// they cannot live in the differential corpus: the LLVM oracle's bounds panic
// aborts while the kept trust-cg check traps — both die, but the outcome shapes
// differ structurally).
//
// Each adversarial program has a dominating compare that does NOT establish
// the checked property, so the check must be KEPT and must TRAP at q = 64:
//
//   1. OFF-BY-ONE: guard `q <= 64` over `[u8; 64]`.
//   2. WEAKER FACT: guard `q < 128` over `[u8; 64]`.
//   3. MUTATED INDEX: `q += 1` between the guard `q < 64` and the check.
//
// The positive control (the exact sieve marking-loop shape, all accesses in
// bounds) must run to completion with the right exit code.
//
// History: these began as the refusal legs of the OPT-6b dominating-compare
// elimination, with trace assertions (`TCG-BCE-DOM fired` / `refused
// (solver)`) gated on the probe having fired. Main's `9c523812f` ("preserve
// canonical runtime bounds assertions") retired that probe, so the gate could
// never open again; the dead trace assertions and the `bce-trace` knob are
// gone, and what the pins protect — every check kept, every OOB write trapped —
// is asserted unconditionally. Compiled on the census default lane
// (`no-proof-certs`): with certificates on, E0.2 refuses these bodies outright.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_dombce_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

enum Outcome {
    Exited(i32),
    Signalled,
}

/// Compile `src` as a `--crate-type bin` with the trust-cg backend, run it, and
/// return the outcome plus the compile stderr.
fn compile_run_traced(stem: &str, src: &str, opt: &str, dylib: &Path) -> (Outcome, String) {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join("bin");

    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    let output = toolchain_support::rustc_command()
        .env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET)
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args(["--crate-type", "bin"])
        .arg(&backend_arg)
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "{stem} (opt={opt}): trust-cg compile failed: {stderr}"
    );

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    let outcome = match run.status.code() {
        Some(code) => Outcome::Exited(code),
        None => Outcome::Signalled,
    };
    (outcome, stderr)
}

/// The exact sieve marking-loop shape, ALL accesses in bounds. Exit code:
/// marks 4,7,..,61 (20 entries) -> 64 - 20 = 44 zeros.
const POSITIVE_SRC: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let mut comp = [0u8; 64];
    let p = bb(3usize);
    let mut q = bb(4usize);
    while q < 64 { comp[q] = 1; q += p; }
    let mut zeros = 0i32;
    let mut i = bb(0usize);
    while i < 64 { if comp[i] == 0 { zeros += 1; } i += 1; }
    std::process::exit(zeros);
}
"#;

/// OFF-BY-ONE: `q <= 64` reaches q == 64 -> the KEPT check must trap.
const OFF_BY_ONE_SRC: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let mut comp = [0u8; 64];
    let p = bb(1usize);
    let mut q = bb(0usize);
    while q <= 64 { comp[q] = 1; q += p; }
    std::process::exit(comp[bb(5usize)] as i32);
}
"#;

/// WEAKER FACT: `q < 128` over a [u8; 64] reaches q == 64 -> must trap.
const WEAK_GUARD_SRC: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let mut comp = [0u8; 64];
    let mut q = bb(0usize);
    while q < 128 { comp[q] = 1; q += 1; }
    std::process::exit(comp[bb(5usize)] as i32);
}
"#;

/// MUTATED INDEX: `q += 1` between guard and check reaches comp[64] -> trap.
const MUTATED_INDEX_SRC: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let mut comp = [0u8; 64];
    let mut q = bb(0usize);
    while q < 64 { q += 1; comp[q] = 1; }
    std::process::exit(comp[bb(5usize)] as i32);
}
"#;

#[test]
fn dominated_adversarials_keep_their_bounds_checks_and_trap() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();

    for opt in ["2", "3"] {
        // POSITIVE CONTROL: in-bounds dominated checks run clean with the
        // right answer.
        let (outcome, _stderr) = compile_run_traced("positive", POSITIVE_SRC, opt, &dylib);
        match outcome {
            Outcome::Exited(code) => assert_eq!(
                code, 44,
                "positive control (opt={opt}) exited with the wrong count — \
                 the elimination (or the kept check) broke in-bounds behavior"
            ),
            Outcome::Signalled => {
                panic!("positive control (opt={opt}) TRAPPED on an in-bounds access")
            }
        }

        // OFF-BY-ONE `<=`: check kept; OOB write traps.
        let (outcome, _stderr) = compile_run_traced("off_by_one", OFF_BY_ONE_SRC, opt, &dylib);
        assert!(
            matches!(outcome, Outcome::Signalled),
            "off-by-one <= guard (opt={opt}): the OOB write at q == 64 must \
             TRAP — a clean exit means the bounds check was DROPPED (silent \
             out-of-bounds write)"
        );

        // WEAKER fact: check kept; traps.
        let (outcome, _stderr) = compile_run_traced("weak_guard", WEAK_GUARD_SRC, opt, &dylib);
        assert!(
            matches!(outcome, Outcome::Signalled),
            "weak guard (opt={opt}): the OOB write at q == 64 must TRAP"
        );

        // MUTATED index: check kept; traps.
        let (outcome, _stderr) =
            compile_run_traced("mutated_index", MUTATED_INDEX_SRC, opt, &dylib);
        assert!(
            matches!(outcome, Outcome::Signalled),
            "mutated-index shape (opt={opt}): the OOB write at q == 64 must TRAP"
        );
    }
}
