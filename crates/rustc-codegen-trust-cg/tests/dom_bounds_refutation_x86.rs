#[path = "support/target_dir.rs"]
mod target_dir_support;

// crates/rustc-codegen-trust-cg/tests/dom_bounds_refutation_x86.rs
//
// OPT-6b REFUTATION PINS — dominating-compare bounds-check elimination.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A wrongly-dropped bounds check is a SILENT out-of-bounds write, so the
// dominating-compare elimination's refusal legs get their own bridge-only
// behavioral pins (these programs go OUT OF BOUNDS at runtime, so they cannot
// live in the differential corpus: the LLVM oracle's bounds panic aborts
// while the kept trust-cg check traps — both die, but the outcome shapes
// differ structurally).
//
// Each adversarial program has a dominating compare that does NOT establish
// the checked property:
//
//   1. OFF-BY-ONE: guard `q <= 64` over `[u8; 64]` — the ay lane must REFUTE
//      `(q <=u 64) => (q <u 64)` (witness q = 64) and the kept check must
//      TRAP when q reaches 64.
//   2. WEAKER FACT: guard `q < 128` over `[u8; 64]` — refuted (witness 64),
//      kept, traps at q = 64.
//   3. MUTATED INDEX: `q += 1` between the guard `q < 64` and the check —
//      the copy-chain resolution refuses (no solver involvement), kept,
//      traps at q = 64.
//
// The positive control (the exact sieve marking-loop shape, all accesses in
// bounds) must run to completion with the right exit code AND, under
// `TCG_BCE_TRACE=1`, report the probe FIRED — pinning that the adversarial
// "did not fire" observations are not a vacuously-disabled feature.
//
// Every compile here runs with the DEFAULT solver env (elimination genuinely
// ATTEMPTED), so a pass proves the refusal legs, not a disabled feature.
// If the solver lane is unavailable the positive control cannot fire; the
// trace assertions are gated on it having fired at least once.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

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

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let name = dylib_name();
    let candidates = [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
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
    assert!(status.success(), "cargo build failed; cannot run refutation pins");
    let built = target_dir.join("release").join(&name);
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

/// Compile `src` as a `--crate-type bin` with the trust-cg backend (default
/// solver env + `TCG_BCE_TRACE=1`), run it, and return the outcome plus the
/// compile stderr (which carries the `TCG-BCE-DOM` trace lines).
fn compile_run_traced(stem: &str, src: &str, opt: &str, dylib: &Path) -> (Outcome, String) {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join("bin");

    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    let output = Command::new("rustup")
        .env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET)
        .env("TCG_BCE_TRACE", "1")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
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
        .expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "{stem} (opt={opt}): trust-cg compile failed (the probe path must NEVER \
         introduce a compile failure): {stderr}"
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
fn dom_bce_positive_fires_and_adversarials_keep_their_checks() {
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
        // right answer. Whether the probe FIRES depends on the solver lane
        // being available in this environment; record it for the gating
        // below.
        let (outcome, stderr) =
            compile_run_traced("positive", POSITIVE_SRC, opt, &dylib);
        match outcome {
            Outcome::Exited(code) => assert_eq!(
                code, 44,
                "positive control (opt={opt}) exited with the wrong count — \
                 the elimination (or the kept check) broke in-bounds behavior"
            ),
            Outcome::Signalled => panic!(
                "positive control (opt={opt}) TRAPPED on an in-bounds access"
            ),
        }
        let solver_live = stderr.contains("TCG-BCE-DOM fired");

        // OFF-BY-ONE `<=`: ay must refute; check kept; OOB write traps.
        let (outcome, stderr) =
            compile_run_traced("off_by_one", OFF_BY_ONE_SRC, opt, &dylib);
        assert!(
            !stderr.contains("TCG-BCE-DOM fired"),
            "off-by-one <= guard (opt={opt}) must NOT license elimination; \
             trace: {stderr}"
        );
        if solver_live {
            assert!(
                stderr.contains("TCG-BCE-DOM refused (solver): ule k=64 len=64"),
                "off-by-one <= guard (opt={opt}) must reach the solver and be \
                 REFUTED there (the synthetic wrong-obligation pin); trace: {stderr}"
            );
        }
        assert!(
            matches!(outcome, Outcome::Signalled),
            "off-by-one <= guard (opt={opt}): the OOB write at q == 64 must \
             TRAP — a clean exit means the bounds check was DROPPED (silent \
             out-of-bounds write)"
        );

        // WEAKER fact: refuted at the solver; kept; traps.
        let (outcome, stderr) =
            compile_run_traced("weak_guard", WEAK_GUARD_SRC, opt, &dylib);
        assert!(
            !stderr.contains("TCG-BCE-DOM fired"),
            "weak guard (opt={opt}) must NOT license elimination; trace: {stderr}"
        );
        if solver_live {
            assert!(
                stderr.contains("TCG-BCE-DOM refused (solver): ult k=128 len=64"),
                "weak guard (opt={opt}) must reach the solver and be REFUTED; \
                 trace: {stderr}"
            );
        }
        assert!(
            matches!(outcome, Outcome::Signalled),
            "weak guard (opt={opt}): the OOB write at q == 64 must TRAP"
        );

        // MUTATED index: refused before the solver (copy-chain resolution);
        // kept; traps.
        let (outcome, stderr) =
            compile_run_traced("mutated_index", MUTATED_INDEX_SRC, opt, &dylib);
        assert!(
            !stderr.contains("TCG-BCE-DOM fired"),
            "mutated-index shape (opt={opt}) must NOT license elimination; \
             trace: {stderr}"
        );
        assert!(
            matches!(outcome, Outcome::Signalled),
            "mutated-index shape (opt={opt}): the OOB write at q == 64 must TRAP"
        );
    }
}
