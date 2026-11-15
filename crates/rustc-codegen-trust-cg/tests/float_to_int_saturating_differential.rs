#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/float_int_saturation.rs"]
mod float_int_saturation;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// crates/rustc-codegen-trust-cg/tests/float_to_int_saturating_differential.rs
//
// Rust's float -> integer conversions must reach trust-ir with Rust's meaning.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `x as {iN,uN}` saturates: NaN -> 0, out of range -> MIN/MAX, otherwise toward
// zero. trust-ir's raw `fptosi`/`fptoui` are UNDEFINED for NaN and for values
// outside the destination (docs/ub-numerics-policy.md §2 at the pinned
// trust-ir; its reference interpreter refuses them). The bridge used to emit
// the raw op and lean on the x86 selector's saturating sequence. That is not a
// refinement of the source: an optimizer, another backend or a verifier reading
// trust-ir may treat the out-of-range case as UB the Rust program does not have.
// Measured before the fix (reports/2026-10-26-bridge-saturating-float-cast):
//
//   * every `as` cast reached trust-ir as `fptosi`/`fptoui` (`f as i8` as
//     `fptosi f -> i64` plus an integer clamp), and the reference interpreter
//     reported UB on NaN, the infinities and every out-of-range input;
//   * `f as i128`/`u128` lowered to a bare `__fix{s,d}fti`/`__fixuns{s,d}fti`
//     call. Linked by the C compiler driver against the platform runtime, the
//     x86-64 Darwin build returned i128::MAX for `f64::NAN as i128` and i128::MIN
//     for `2^127 as i128`;
//   * `to_int_unchecked` also took the raw op, whose UB band is WIDER than
//     Rust's: core documents `(-128.9f32).to_int_unchecked::<i8>() == i8::MIN`,
//     which trust-ir's `fptosi` leaves undefined (`value < -2^7`).
//
// THE GATE. casts.rs exports one `as_*` and one `unchecked_*` function for each
// of f32/f64 x i8..i128, isize, u8..u128, usize.
//
//   * `as_casts_reach_trust_ir_as_the_saturating_op` (O0-O3): every float ->
//     integer cast in the dumped modules is `fptosi.sat`/`fptoui.sat`, and
//     trust-ir's reference interpreter, run on every exported function and
//     every input of spec.rs (NaNs, infinities, signed zeros, subnormals, both
//     neighbours of every 2^(N-1) and 2^N, the sub-minimum fractional band,
//     in-range values), returns Rust's result.
//   * `conversions_match_llvm_and_rusts_semantics` (O0-O3): the same functions
//     built by trust-cg and by LLVM, linked into one LLVM-built Rust driver,
//     print identical results on every input, and both match spec.rs, which
//     computes Rust's conversions from the IEEE encoding alone. A C driver
//     linked against the platform runtime checks the 128-bit rows.
//
// Proof certificates are off (`no-proof-certs`): this is lowering and native
// testing evidence, not proof credit. HOST-NATIVE: no `--target`.

use std::path::PathBuf;
use std::process::Command;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_fcast_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_command(knobs: &[&str]) -> Command {
    let backend = backend_artifact_support::current_test_backend();
    let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
    arg.push(backend);
    let mut command = toolchain_support::rustc_command();
    command
        .arg(arg)
        .arg(toolchain_support::backend_knobs_arg(knobs));
    command
}

#[test]
fn as_casts_reach_trust_ir_as_the_saturating_op() {
    if toolchain_support::skip_without_backend_knobs("as_casts_reach_trust_ir_as_the_saturating_op")
    {
        return;
    }
    let root = workdir("tir");
    let mut failures = Vec::new();
    for opt in float_int_saturation::OPT_LEVELS {
        let dir = root.join(format!("O{opt}"));
        let dump = dir.join("dump");
        let dump_knob = format!("dump-trust-ir={}", dump.display());
        let compiled = float_int_saturation::compile_casts(
            backend_command(&["no-proof-certs", &dump_knob]),
            &dir,
            opt,
        );
        if let Err(stderr) = compiled {
            failures.push(format!("O{opt}: the backend refused casts.rs:\n{stderr}"));
            continue;
        }
        let modules = match float_int_saturation::dumped_modules(&dump) {
            Ok(modules) => modules,
            Err(error) => {
                failures.push(format!("O{opt}: {error}"));
                continue;
            }
        };
        let findings = float_int_saturation::check_trust_ir(&modules);
        println!(
            "FCAST_TRUST_IR O{opt} saturating_casts={} interpreted_calls={} findings={}",
            findings.saturating_casts,
            findings.interpreted_calls,
            findings.failures.len()
        );
        if findings.saturating_casts < float_int_saturation::conversions().len() {
            failures.push(format!(
                "O{opt}: only {} saturating casts for {} `as` conversions — the check would be vacuous",
                findings.saturating_casts,
                float_int_saturation::conversions().len()
            ));
        }
        failures.extend(
            findings
                .failures
                .into_iter()
                .map(|failure| format!("O{opt}: {failure}")),
        );
    }
    let _ = std::fs::remove_dir_all(&root);
    assert!(
        failures.is_empty(),
        "{} finding(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    positive_evidence::record(
        positive_evidence::Evidence::Compiled,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn conversions_match_llvm_and_rusts_semantics() {
    if toolchain_support::skip_without_backend_knobs("conversions_match_llvm_and_rusts_semantics") {
        return;
    }
    let root = workdir("native");
    let mut failures = Vec::new();
    for opt in float_int_saturation::OPT_LEVELS {
        match float_int_saturation::native_differential(
            &toolchain_support::rustc_command,
            &|| backend_command(&["no-proof-certs"]),
            &root,
            opt,
        ) {
            Ok(report) => println!("{report}"),
            Err(found) => failures.extend(found),
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    assert!(
        failures.is_empty(),
        "{} finding(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
