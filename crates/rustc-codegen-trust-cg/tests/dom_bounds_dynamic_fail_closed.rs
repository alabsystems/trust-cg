//! Every MIR bounds assertion survives a dynamic-guard shape — silent-OOB canaries.
//!
//! Main's `9c523812f` ("preserve canonical runtime bounds assertions") retired
//! the backend's dominated bounds-check-elimination probe (OPT-6b) and its
//! dynamic lane; the backend now keeps every MIR bounds assertion. The probe's
//! trace assertions this file used to make (`TCG-BCE-DOM fact: ..`,
//! `TCG-BCE-DYN refused: ..`) could no longer pass and are gone with its
//! `bce-trace` knob. What remains is what they were protecting: each
//! adversarial below shrinks a `Vec` after a dynamic guard but before indexing
//! at the old last element. Keeping the check aborts; deleting it reads
//! still-allocated capacity and exits cleanly — a crisp silent-OOB canary. The
//! two in-bounds controls must still run to their exact exit code.
//!
//! Compiled on the census default lane (`no-proof-certs`): with certificates
//! on, E0.2 refuses these bodies outright and the canary would never run.

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::{Path, PathBuf};
use std::process::Command;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_dyn_bce_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create dynamic BCE workdir");
    dir
}

enum Outcome {
    Exited(i32),
    Signalled,
}

fn compile_run_traced(stem: &str, source: &str, dylib: &Path) -> (Outcome, String) {
    let dir = workdir(stem);
    let source_path = dir.join("prog.rs");
    std::fs::write(&source_path, source).expect("write dynamic BCE source");
    let binary = dir.join("prog");
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    let output = toolchain_support::rustc_command()
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args([
            "--crate-type",
            "bin",
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
            "-Copt-level=2",
        ])
        .arg(&backend_arg)
        .arg("-o")
        .arg(&binary)
        .arg(&source_path)
        .output()
        .expect("spawn rustc for dynamic BCE canary");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "{stem}: backend compile failed: {stderr}"
    );

    let run = Command::new(&binary)
        .output()
        .expect("run dynamic BCE canary");
    let outcome = match run.status.code() {
        Some(code) => Outcome::Exited(code),
        None => Outcome::Signalled,
    };
    let _ = std::fs::remove_dir_all(&dir);
    (outcome, stderr)
}

const CONSTANT_CONTROL: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let mut a = [0u8; 64];
    let mut i = bb(0usize);
    while i < 64 { a[i] = 1; i += 1; }
    std::process::exit(a.iter().map(|&x| x as i32).sum::<i32>());
}
"#;

// This is the exact h1 shape the dynamic recognizer was introduced for. It
// must still be recognized, but recognition now terminates at the explicit
// authority refusal rather than deleting the bounds check by identity.
const DYNAMIC_RECOGNIZED_CONTROL: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let n = bb(8usize);
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < n { v.push((i + 1) as u64); i += 1; }
    let mut acc = 0u64;
    let mut k = 0usize;
    while k < v.len() { acc = acc.wrapping_add(v[k]); k += 1; }
    std::process::exit(acc as i32);
}
"#;

// The length write is deliberately sequenced after the guard value is formed
// but before its branch, targeting the old guard-endpoint scan exemption.
const GUARD_ENDPOINT_WRITE: &str = r#"
use std::hint::black_box as bb;
#[inline(always)] unsafe fn shrink(v: &mut Vec<u8>, n: usize) { unsafe { v.set_len(bb(n)); } }
fn main() {
    let mut v = vec![9u8; bb(8usize)];
    let i = bb(7usize);
    let guarded = i < v.len();
    unsafe { shrink(&mut v, i); }
    if guarded { bb(v[i]); }
    std::process::exit(0);
}
"#;

// The inlined shrink sits on the true-edge/check side, targeting the old
// assert-endpoint scan exemption.
const ASSERT_ENDPOINT_WRITE: &str = r#"
use std::hint::black_box as bb;
#[inline(always)] unsafe fn shrink(v: &mut Vec<u8>, n: usize) { unsafe { v.set_len(bb(n)); } }
fn main() {
    let mut v = vec![11u8; bb(8usize)];
    let i = bb(7usize);
    if i < v.len() {
        unsafe { shrink(&mut v, i); }
        bb(v[i]);
    }
    std::process::exit(0);
}
"#;

// The mutable alias is created before the guard. A scan limited to
// address-taking inside guard..use cannot establish its provenance. This uses
// a supported reference shape rather than `&raw`, which the bridge correctly
// rejects before bounds analysis.
const PREEXISTING_MUT_ALIAS: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let mut v = vec![13u8; bb(8usize)];
    let alias: &mut Vec<u8> = &mut v;
    let i = bb(7usize);
    if i < alias.len() {
        unsafe { alias.set_len(bb(i)); }
        bb(alias[i]);
    }
    std::process::exit(0);
}
"#;

#[test]
fn retained_bounds_checks_abort_on_dynamic_guard_hazards() {
    // The bridge compiles below pass a backend knob on `-Ztrust-ir-cg-args`;
    // the knob's former `TCG_*` environment spelling is refused outright, so on
    // a compiler without that option the test cannot run at all. Skip honestly.
    if toolchain_support::skip_without_backend_knobs("dom_bounds_dynamic_fail_closed") {
        return;
    }
    if !matches!(std::env::consts::ARCH, "aarch64" | "x86_64") {
        eprintln!("skipping: trust-cg host backend is not available for this architecture");
        return;
    }
    let dylib = ensure_dylib_built();

    let (outcome, _stderr) = compile_run_traced("constant_control", CONSTANT_CONTROL, &dylib);
    assert!(matches!(outcome, Outcome::Exited(64)));

    let (outcome, _stderr) = compile_run_traced(
        "dynamic_recognized_control",
        DYNAMIC_RECOGNIZED_CONTROL,
        &dylib,
    );
    assert!(matches!(outcome, Outcome::Exited(36)));

    for (stem, source) in [
        ("guard_endpoint_write", GUARD_ENDPOINT_WRITE),
        ("assert_endpoint_write", ASSERT_ENDPOINT_WRITE),
    ] {
        let (outcome, _stderr) = compile_run_traced(stem, source, &dylib);
        assert!(
            matches!(outcome, Outcome::Signalled),
            "{stem}: retained bounds check must abort after the Vec shrinks"
        );
    }

    let (outcome, _stderr) =
        compile_run_traced("preexisting_mut_alias", PREEXISTING_MUT_ALIAS, &dylib);
    assert!(
        matches!(outcome, Outcome::Signalled),
        "preexisting alias: retained bounds check must abort after the Vec shrinks"
    );
}
