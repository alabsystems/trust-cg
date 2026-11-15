#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a request for retag CALLS fails closed through the bridge.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// HAZARD PINNED. On the stock nightly this bridge used to pin, retag semantics
// reached codegen as `StatementKind::Retag`, which `lower_statement` refused by
// name. The Trust rustc has no such statement (the backend's move to it,
// trust-cg `0d8cb948a`): a retag rides on `Rvalue::Use(_, WithRetag)`, which
// the bridge lowers as the plain copy/move rustc_codegen_ssa emits when retag
// emission is off, and the only remaining request for retag semantics is
// `-Zcodegen-emit-retag` (rustc_codegen_ssa `retag_mem`/`retag_reg` calls).
// The bridge has no retag emitter, and it used to accept that option and
// silently drop the calls. It now refuses the compile with `[TCG-EMIT-RETAG]`.
//
// Both directions are pinned on the host target:
//   * with `-Zcodegen-emit-retag` (bare and with a sub-option) the default-lane
//     compile fails with the exact diagnostic and writes no object, while the
//     LLVM backend compiles the same crate with the option (so the refusal is
//     the bridge's, not rustc's option parser) and a metadata-only compile with
//     the option succeeds (rustc never calls the backend's `codegen_crate`);
//   * the same crate without the option compiles to an object, so the refusal
//     does not over-fire. That control runs with the `no-proof-certs` knob:
//     in the default lane a function with a frame prologue is refused by the
//     AArch64 proof wall (`[TCG-PROOF-465]`, no proof mapping for
//     `StpPreIndex`/`LdpPostIndex`), which says nothing about retag. The
//     refused compile with the same knob is checked too, so the knob is not
//     what separates the two outcomes.

use std::path::{Path, PathBuf};
use std::process::Output;

/// The bridge's exact refusal, as `codegen_crate` emits it.
const REFUSAL: &str = "[TCG-EMIT-RETAG] rustc_codegen_trust_cg: `-Zcodegen-emit-retag` requests \
     retag calls (Rust provenance/alias retag semantics), which this backend does not emit; \
     failing closed rather than silently dropping them";

/// A crate whose function moves references, i.e. exactly the uses a retag
/// emitter would instrument.
const PROGRAM: &str = r#"
#[inline(never)]
#[no_mangle]
pub extern "C" fn retag_probe(slot: &mut i64, delta: &i64) -> i64 {
    let target = slot;
    let amount = delta;
    *target += *amount;
    *target
}
"#;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_emit_retag_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `PROGRAM` as a library with `extra` arguments; `backend` selects the
/// bridge, `None` the compiler's own (LLVM) backend.
fn compile(
    dir: &Path,
    tag: &str,
    backend: Option<&Path>,
    emit: &str,
    extra: &[String],
) -> (Output, PathBuf) {
    let source = dir.join("retag_probe.rs");
    std::fs::write(&source, PROGRAM).expect("write source");
    let out_dir = dir.join(tag);
    std::fs::create_dir_all(&out_dir).expect("create output dir");
    let mut command = toolchain_support::rustc_command();
    command.args([
        "--crate-type",
        "lib",
        "--crate-name",
        "retag_probe",
        "-Ccodegen-units=1",
        "-Copt-level=0",
    ]);
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        command.arg(arg);
    }
    command
        .args(extra)
        .arg(format!("--emit={emit}"))
        .arg("--out-dir")
        .arg(&out_dir)
        .arg(&source);
    let output = command.output().expect("spawn the compiler");
    (output, out_dir)
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn objects_in(dir: &Path) -> Vec<PathBuf> {
    let mut objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read output dir")
        .map(|entry| entry.expect("output dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    objects.sort();
    objects
}

fn assert_refused(dir: &Path, dylib: &Path, tag: &str, args: &[String]) {
    let (output, out_dir) = compile(dir, tag, Some(dylib), "obj", args);
    let text = stderr(&output);
    assert!(!output.status.success(), "{args:?}: compiled: {text}");
    assert!(text.contains(REFUSAL), "{args:?}: {text}");
    assert!(
        objects_in(&out_dir).is_empty(),
        "{args:?}: object written after the refusal: {:?}",
        objects_in(&out_dir)
    );
}

#[test]
fn codegen_emit_retag_is_refused_by_name() {
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("refused");
    let option = |value: &str| vec![value.to_owned()];

    // Control: the option and the program are valid for this compiler.
    let (llvm, llvm_out) = compile(&dir, "llvm", None, "obj", &option("-Zcodegen-emit-retag"));
    assert!(
        llvm.status.success(),
        "the LLVM backend must compile the probe with -Zcodegen-emit-retag: {}",
        stderr(&llvm)
    );
    assert!(!objects_in(&llvm_out).is_empty(), "LLVM wrote no object");

    // The refusal, in the default lane, for the bare option and a sub-option.
    assert_refused(&dir, &dylib, "bare", &option("-Zcodegen-emit-retag"));
    assert_refused(
        &dir,
        &dylib,
        "suboption",
        &option("-Zcodegen-emit-retag=no-precise-im"),
    );

    // Metadata only: rustc does not call the backend's `codegen_crate`, so the
    // option is not refused where no code is generated.
    let (metadata, _) = compile(
        &dir,
        "metadata",
        Some(&dylib),
        "metadata",
        &option("-Zcodegen-emit-retag"),
    );
    let text = stderr(&metadata);
    assert!(metadata.status.success(), "metadata only: {text}");
    assert!(!text.contains("[TCG-EMIT-RETAG]"), "metadata only: {text}");

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn the_same_crate_compiles_without_the_option() {
    if toolchain_support::skip_without_backend_knobs("the_same_crate_compiles_without_the_option") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("control");
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);

    let (plain, plain_out) = compile(&dir, "plain", Some(&dylib), "obj", &[knobs.clone()]);
    let text = stderr(&plain);
    assert!(plain.status.success(), "no option: {text}");
    assert!(!text.contains("[TCG-EMIT-RETAG]"), "no option: {text}");
    assert!(!objects_in(&plain_out).is_empty(), "no option: no object");

    // The same knob with the option is still refused: the option, not the
    // knob, decides the outcome.
    assert_refused(
        &dir,
        &dylib,
        "knob_refused",
        &[knobs, "-Zcodegen-emit-retag".to_owned()],
    );

    let _ = std::fs::remove_dir_all(&dir);
}
