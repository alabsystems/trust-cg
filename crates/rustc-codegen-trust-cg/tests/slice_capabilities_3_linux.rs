#![cfg(all(
    target_os = "linux",
    any(target_arch = "x86_64", target_arch = "aarch64")
))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the two capabilities of the third Clean-slice round
// (2026-11-16), each compiled by the bridge for the HOST and RUN at -O0..-O3
// and compared with rustc's LLVM backend at the same level on stdout bytes,
// stderr bytes and exit status. It runs on x86-64 Linux (where it was
// measured) and on AArch64 Linux (on the authoring host the AArch64 leg is
// written, compiled, not executed; `tests/slice_parity_cross_targets.rs`
// compiles its objects).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// 1. A CAPTURING closure handed to an intercepted iterator terminal
//    (`terminal_capturing_closure_target`): the drive calls a private copy of
//    the closure environment (`terminal_closure_env`), so an FnMut's state
//    is the callee's copy, exactly as std moves `f` into the terminal. FnOnce
//    and a constant closure without a plain byte image are refused; a
//    drop-carrying capture keeps its refusal. Core's `<[T]>::contains` over a
//    non-integer element steps aside to core's own body.
// 2. A Vec/String FIELD held inline by a memory-backed aggregate
//    (`collection_field_image_target`, `collection_field_header_ty`): the
//    field is the checked 24-byte rustc header image. A borrow binds the
//    field's address, a store copies the source header's bytes, a projected
//    drop frees the buffer at the field's address, and every aggregate that
//    holds one is memory-backed and addressed through the rustc-layout walker
//    (`aggregate_holds_inline_collection_header`). An element that needs drop
//    is not admitted.
//
// EVIDENCE BOUNDARY: a differential test on fixed inputs, proofs-off lane
// (`-Ztrust-verify=off`, `no-proof-certs`); not proof evidence.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = if cfg!(target_arch = "aarch64") {
    host_target_support::AARCH64_TARGET
} else {
    host_target_support::X86_64_TARGET
};
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_slicecap3_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

#[derive(Debug, PartialEq, Eq)]
struct RunResult {
    stdout: String,
    stderr: String,
    code: Option<i32>,
    signal: Option<i32>,
}

fn run_bin(bin: &Path) -> RunResult {
    use std::os::unix::process::ExitStatusExt;
    let out = Command::new(bin).output().expect("run binary");
    RunResult {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        code: out.status.code(),
        signal: out.status.signal(),
    }
}

enum Outcome {
    Ran(RunResult),
    Refused(String),
}

/// The fixture with its `main` renamed `fixture_main` and the live-allocation
/// counter (`support/slice_capabilities_3/live_alloc_counter.rs`) appended, so
/// both arms print the allocations still live at exit: a leaked or doubly
/// freed buffer is a different output, not a silent pass.
fn leak_checked(stem: &str, src: &str) -> String {
    assert_eq!(
        src.matches("fn main()").count(),
        1,
        "`{stem}`: the leak check needs exactly one `fn main()`"
    );
    format!(
        "{}\n{LIVE_ALLOC_COUNTER}",
        src.replacen("fn main()", "fn fixture_main()", 1)
    )
}

fn compile(dir: &Path, dylib: Option<&Path>, stem: &str, src: &str, opt: &str) -> Outcome {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, leak_checked(stem, src)).expect("write source");
    let arm = if dylib.is_some() { "cg" } else { "llvm" };
    let bin = dir.join(format!("{stem}_{arm}_O{opt}"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "--target", TARGET])
        .arg("-Cpanic=abort")
        .arg(format!("-Copt-level={opt}"))
        .args(["-Coverflow-checks=off", "-Ccodegen-units=1", "-Awarnings"]);
    if let Some(dylib) = dylib {
        let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
        backend.push(dylib);
        cmd.arg(backend)
            .arg("-Ztrust-ir-cg-args=no-proof-certs")
            .arg("-Ztrust-ir-cg-args=refine-solver=0");
    }
    let output = cmd
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc");
    if !output.status.success() {
        return Outcome::Refused(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Outcome::Ran(run_bin(&bin))
}

fn llvm(dir: &Path, stem: &str, src: &str, opt: &str) -> RunResult {
    match compile(dir, None, stem, src, opt) {
        Outcome::Ran(result) => result,
        Outcome::Refused(stderr) => panic!("LLVM failed to compile `{stem}`: {stderr}"),
    }
}

/// Every case must compile under the bridge and equal LLVM at each listed level.
fn require_match_at(test: &str, cases: &[(&str, &str)], levels: &[&str]) {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir(test);
    for (stem, src) in cases {
        for opt in levels {
            let want = llvm(&dir, stem, src, opt);
            match compile(&dir, Some(&dylib), stem, src, opt) {
                Outcome::Ran(got) => {
                    assert_eq!(
                        got, want,
                        "`{stem}` at -O{opt}: bridge output differs from LLVM"
                    )
                }
                Outcome::Refused(stderr) => {
                    panic!("`{stem}` refused at -O{opt}, expected to compile: {stderr}")
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Each case must either compile and equal LLVM, or refuse by name; a wrong
/// value never passes.
fn require_match_or_named_refusal(test: &str, cases: &[(&str, &str)]) {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir(test);
    for (stem, src) in cases {
        for opt in OPT_LEVELS {
            let want = llvm(&dir, stem, src, opt);
            match compile(&dir, Some(&dylib), stem, src, opt) {
                Outcome::Ran(got) => assert_eq!(got, want, "`{stem}` at -O{opt}: WRONG output"),
                Outcome::Refused(stderr) => assert!(
                    stderr.contains("[TCG-MIR-UNSUPPORTED]"),
                    "`{stem}` at -O{opt}: refusal is not a named fail-closed: {stderr}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// The case must refuse at every level, naming `text`.
fn require_refusal(test: &str, stem: &str, src: &str, text: &str) {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir(test);
    for opt in OPT_LEVELS {
        let _ = llvm(&dir, stem, src, opt);
        match compile(&dir, Some(&dylib), stem, src, opt) {
            Outcome::Refused(stderr) => assert!(
                stderr.contains("[TCG-MIR-UNSUPPORTED]") && stderr.contains(text),
                "`{stem}` at -O{opt}: expected a refusal naming {text:?}: {stderr}"
            ),
            Outcome::Ran(got) => {
                panic!("`{stem}` at -O{opt}: compiled ({got:?}); pinned as refused")
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

fn skip() -> bool {
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return true;
    }
    false
}

const LIVE_ALLOC_COUNTER: &str = include_str!("support/slice_capabilities_3/live_alloc_counter.rs");
const TERMINAL_CAPTURE: &str = include_str!("support/slice_capabilities_3/terminal_capture.rs");
const TERMINAL_CAPTURE_COPY: &str =
    include_str!("support/slice_capabilities_3/terminal_capture_copy.rs");
const TERMINAL_CAPTURE_BYKEY: &str =
    include_str!("support/slice_capabilities_3/terminal_capture_bykey.rs");
const TERMINAL_CAPTURE_OTHER: &str =
    include_str!("support/slice_capabilities_3/terminal_capture_other.rs");
const TERMINAL_CAPTURE_DROP: &str =
    include_str!("support/slice_capabilities_3/terminal_capture_drop.rs");
const TERMINAL_CAPTURE_DROP_GUARD: &str =
    include_str!("support/slice_capabilities_3/terminal_capture_drop_guard.rs");
const COLLECTION_FIELD: &str = include_str!("support/slice_capabilities_3/collection_field.rs");
const COLLECTION_FIELD_LOCAL: &str =
    include_str!("support/slice_capabilities_3/collection_field_local.rs");
const COLLECTION_FIELD_DROP_ELEM: &str =
    include_str!("support/slice_capabilities_3/collection_field_drop_elem.rs");
const CLOSURE_ENV_VEC: &str = include_str!("support/slice_capabilities_3/closure_env_vec.rs");
const CLOSURE_ENV_HOLDER: &str = include_str!("support/slice_capabilities_3/closure_env_holder.rs");

/// `any`/`all`/`find`/`position` with by-reference, by-value, several, `&mut`
/// counting, `move` FnMut-state, generic, ZST-item and `u128` captures over
/// empty, one-element and 10 000-element slices; a borrowed iterator resumed
/// after the terminal; core's `contains` over `char` and a user struct. At
/// -O0/-O1 these reach the interception with the capturing closure.
#[test]
fn capturing_terminal_closures_match_llvm() {
    require_match_at(
        "terminal",
        &[("terminal_capture", TERMINAL_CAPTURE)],
        &OPT_LEVELS,
    );
}

/// One `Copy` FnMut closure handed to `any` twice and then called through a
/// wrapper: each terminal mutates its own copy, so the second `any` starts
/// from the caller's state, over empty, two-element and twenty-element input.
#[test]
fn terminal_closure_environment_is_a_private_copy() {
    require_match_at(
        "terminal_copy",
        &[("terminal_capture_copy", TERMINAL_CAPTURE_COPY)],
        &OPT_LEVELS,
    );
}

/// `min_by_key`/`min_by`/`max_by` with capturing closures. -O0/-O1 reach the
/// interception; -O2/-O3 inline them into `map(..).reduce(..)` over
/// `KeyAndValue`, which is not this capability: match or named refusal.
#[test]
fn capturing_by_key_terminals_match_llvm_or_refuse_by_name() {
    require_match_at(
        "bykey",
        &[("terminal_capture_bykey", TERMINAL_CAPTURE_BYKEY)],
        &["0", "1"],
    );
    require_match_or_named_refusal(
        "bykey_all",
        &[("terminal_capture_bykey", TERMINAL_CAPTURE_BYKEY)],
    );
}

/// Shapes beside the admission (an integer `contains` of a register scalar,
/// `try_fold` with a by-value capturing check closure): match or named refusal.
#[test]
fn neighbouring_terminal_shapes_match_llvm_or_refuse_by_name() {
    require_match_or_named_refusal(
        "other",
        &[("terminal_capture_other", TERMINAL_CAPTURE_OTHER)],
    );
}

/// A terminal closure owning a `String` capture is not admitted. Its
/// environment owns a collection header, which the closure-environment route
/// refuses (`[TCG-COLLECTION-IMAGE]`, as on the base tree; record
/// SLICE-CAP3-GATE-SCOPE), before the drive's own owned-drop check
/// (`[TCG-INTERCEPT-OWNED-DROP]`) is reached.
#[test]
fn drop_carrying_terminal_capture_keeps_its_refusal() {
    require_refusal(
        "terminal_drop",
        "terminal_capture_drop",
        TERMINAL_CAPTURE_DROP,
        "[TCG-COLLECTION-IMAGE]",
    );
}

/// A terminal closure owning a user `Drop` value (no collection). On x86-64
/// Linux the drive runs rustc's drop glue for the environment
/// (`owned_closure_drop_plan`), so the destructor's output and the
/// live-allocation count equal LLVM's. On AArch64 Linux the same program is
/// refused by `[TCG-INTERCEPT-OWNED-DROP]` at O0-O3 (measured by object
/// emission on the x86-64 host), which this test pins there.
#[test]
fn drop_glue_terminal_capture_matches_llvm() {
    if cfg!(target_arch = "aarch64") {
        require_refusal(
            "terminal_drop_guard",
            "terminal_capture_drop_guard",
            TERMINAL_CAPTURE_DROP_GUARD,
            "[TCG-INTERCEPT-OWNED-DROP]",
        );
        return;
    }
    require_match_at(
        "terminal_drop_guard",
        &[("terminal_capture_drop_guard", TERMINAL_CAPTURE_DROP_GUARD)],
        &OPT_LEVELS,
    );
}

/// Vec/String fields: construction, push through `&mut s.v`, reads through
/// `&S`, by-value passing, a move out of a field, reassignment, nested and
/// generic containers, an enum payload, `Vec<()>`, and empty / one / 1000
/// element buffers, all dropped; non-escaping holding locals with a field
/// moved out and a field reassigned from another local.
#[test]
fn collection_fields_match_llvm() {
    require_match_at(
        "coll_field",
        &[
            ("collection_field", COLLECTION_FIELD),
            ("collection_field_local", COLLECTION_FIELD_LOCAL),
        ],
        &OPT_LEVELS,
    );
}

/// A `Vec<String>` field (element needs drop) is outside the admission; the
/// shape compiled before it on its own route (measured on the base tree):
/// match or named refusal.
#[test]
fn drop_element_collection_field_is_not_admitted_here() {
    require_match_or_named_refusal(
        "coll_drop_elem",
        &[("collection_field_drop_elem", COLLECTION_FIELD_DROP_ELEM)],
    );
}

/// The inline-header admission is reached only from
/// `memory_aggregate_layout_uncached`: a closure environment owning a `Vec`
/// by value, or a struct holding one, keeps `[TCG-COLLECTION-IMAGE]` at every
/// level (record SLICE-CAP3-GATE-SCOPE). Before that restriction both
/// compiled through the shared leaf validator (the `FnOnce` one ran).
#[test]
fn closure_environment_collection_keeps_its_refusal() {
    require_refusal(
        "closure_env_vec",
        "closure_env_vec",
        CLOSURE_ENV_VEC,
        "[TCG-COLLECTION-IMAGE]",
    );
    require_refusal(
        "closure_env_holder",
        "closure_env_holder",
        CLOSURE_ENV_HOLDER,
        "[TCG-COLLECTION-IMAGE]",
    );
}
