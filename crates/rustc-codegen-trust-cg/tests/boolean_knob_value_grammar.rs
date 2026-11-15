#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a BOOLEAN backend knob's value must be read, not merely its
// PRESENCE — end to end, through the real compiler.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS, and what it caught. `BackendKnobs::parse` stored any
// `key=value` verbatim and `no-proof-certs` was read as
// `knobs::raw(NO_PROOF_CERTS).is_none()`, so ANY value counted as "set".
// `-Ztrust-ir-cg-args=no-proof-certs=0` — which an operator writes to mean KEEP
// the certificates — switched the per-compile proof-certificate gate OFF.
// Measured on this backend before the fix, on the program below:
//
//     (no knob)            certs=19 / 26 / 138
//     no-proof-certs       certs=0  /  0 /   0
//     no-proof-certs=0     certs=0  /  0 /   0     <- the defect
//     no-proof-certs=false certs=0  /  0 /   0     <- the defect
//     no-proof-certs=nope  certs=0  /  0 /   0     <- silently ignored
//
// The counts come from the backend's own `time` knob, which prints
// `TCG_TIME cgu=<name> ... certs=<N>` per CGU: `N > 0` is the certificates
// being produced and re-checked, `N == 0` is the gate off. That is the
// observable this test reads — no count is hard-coded, because the number
// depends on the emitted instruction stream; what is asserted is the ONE
// distinction the knob controls.
//
// HOST-NATIVE: no `--target`, so this runs wherever the crate is built.

use std::path::{Path, PathBuf};

/// A tiny program with a real (non-inlined) call and a loop, so every lane
/// emits enough instructions for the certificate walk to have something to
/// certify.
const PROGRAM: &str = r#"
#[inline(never)]
fn add(a: i64, b: i64) -> i64 { a + b }

fn main() {
    let mut sum = 0i64;
    let mut i = 0i64;
    while i < 5 {
        sum = add(sum, i);
        i += 1;
    }
    std::process::exit((sum & 7) as i32);
}
"#;

/// The backend sibling of this Cargo test executable, not another profile or
/// whichever cached library happens to have the newest modification time.
fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

/// Compile `PROGRAM` with `knobs` and return the per-CGU certificate counts the
/// backend reports. `Err` carries the compiler's stderr tail — a REFUSAL, which
/// for a knob outside the value grammar is the correct outcome.
fn certificate_counts(dir: &Path, dylib: &Path, knobs: &[&str]) -> Result<Vec<u64>, String> {
    let source = dir.join("knob_probe.rs");
    std::fs::write(&source, PROGRAM).expect("write source");
    let binary = dir.join(format!("knob_probe_{}", knobs.len()));

    let mut command = toolchain_support::rustc_command();
    command.args([
        "--crate-type",
        "bin",
        "-Cpanic=abort",
        "-Ccodegen-units=1",
        "-Copt-level=0",
    ]);
    let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
    backend.push(dylib);
    command.arg(backend);
    command.arg(toolchain_support::backend_knobs_arg(knobs));
    command.arg("-o").arg(&binary).arg(&source);

    let output = command.output().expect("spawn the compiler");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    if !output.status.success() {
        return Err(stderr);
    }
    // `TCG_TIME cgu=<name> ... certs=<N> ...` — one line per CGU.
    let counts: Vec<u64> = stderr
        .lines()
        .filter(|line| line.starts_with("TCG_TIME cgu="))
        .filter_map(|line| {
            line.split_whitespace()
                .find_map(|field| field.strip_prefix("certs="))
                .and_then(|value| value.parse().ok())
        })
        .collect();
    assert!(
        !counts.is_empty(),
        "the `time` knob must report at least one CGU; stderr was:\n{stderr}"
    );
    Ok(counts)
}

#[test]
fn a_boolean_knob_reads_its_value_and_not_its_presence() {
    if toolchain_support::skip_without_backend_knobs(
        "a_boolean_knob_reads_its_value_and_not_its_presence",
    ) {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = std::env::temp_dir().join(format!("tcg_knob_grammar_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");

    // The default lane: certificates are produced.
    let default = certificate_counts(&dir, &dylib, &["time"]).expect("the default lane compiles");
    assert!(
        default.iter().all(|count| *count > 0),
        "with no knob, every CGU must carry certificates; got {default:?}"
    );

    // The knob ON, in both of its spellings: certificates are skipped. This is
    // the knob doing its job, and it is what makes the assertion below a real
    // distinction rather than a constant.
    for knobs in [
        &["time", "no-proof-certs"][..],
        &["time", "no-proof-certs=1"][..],
    ] {
        let off = certificate_counts(&dir, &dylib, knobs).expect("compiles");
        assert!(
            off.iter().all(|count| *count == 0),
            "{knobs:?} must skip the certificates; got {off:?}"
        );
    }

    // THE FIX: the knob explicitly turned OFF must keep the certificates —
    // every OFF spelling, because an operator who reaches for `false` means the
    // same thing as one who reaches for `0`.
    for spelling in [
        "no-proof-certs=0",
        "no-proof-certs=false",
        "no-proof-certs=off",
        "no-proof-certs=no",
    ] {
        let kept = certificate_counts(&dir, &dylib, &["time", spelling]).expect("compiles");
        assert_eq!(
            kept, default,
            "`{spelling}` means KEEP the certificates, so the counts must match the \
             default lane exactly; got {kept:?} against {default:?}"
        );
    }

    // And a value the grammar does not accept is a REFUSAL that names the way
    // out — never a silently ignored argument, which is how the defect read.
    let error = certificate_counts(&dir, &dylib, &["time", "no-proof-certs=nope"])
        .expect_err("a value outside the boolean table must fail the compile");
    assert!(
        error.contains("knob `no-proof-certs` was given the value `nope`"),
        "the refusal must name the knob and the value; got:\n{error}"
    );
    assert!(
        error.contains("`1`, `true`, `on` or `yes`")
            && error.contains("`0`, `false`, `off` or `no`"),
        "the refusal must name the accepted spellings; got:\n{error}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
