#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: host-native programs whose calls reach the bridge's call
// models, its `#[track_caller]` ABI and its typing of reference values,
// compiled BY THE BRIDGE and BY LLVM at the same optimization level, run, and
// compared (stdout and exit code).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS.
// * A call model replaces a call only when the callee IS the std item it
//   models. A user `fn new(x) -> Box<T>` and a user `fn new_uninit() ->
//   Box<T>` have the same name, arity and result type as the `Box`
//   constructors the bridge synthesizes; each must run its own body.
// * The `Iterator::max`/`min` model compares items as integers only when the
//   item type's `Ord` is that integer order; `Reverse<u32>` and a user `Ord`
//   newtype are ordered by their own `cmp`.
// * rustc's `FnAbi` gives every `#[track_caller]` instance a hidden trailing
//   `&'static Location` parameter. The program prints which of the
//   `Location` addresses it observes are equal — a pattern rustc's semantics
//   fix, and which a definition missing the parameter or a call missing the
//   argument breaks (see `bridge_corpus/track_caller_abi.rs`).
// * A reference carried by a loop header and a reference to a reference whose
//   referent is an aggregate or a scalar newtype lower to well-typed, fully
//   defined trust-ir, which the native adapter checks and refuses otherwise.
//
// The `std`-using programs cannot run on the wasm32 corpus (whose sysroot has
// only `core`); `tests/support/wasm32_differential/r6-bridge-frontend.rs`
// covers the `core` shapes of the same fixes on wasm32.
//
// PROOF GATE: compiled with `no-proof-certs`; this is an execution
// differential, not a certified-object claim.

use std::path::{Path, PathBuf};
use std::process::Command;

const O0_O2: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_callid_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code and stdout; `Err` carries the compiler's stderr tail.
fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    opt: &str,
    backend: Option<&Path>,
) -> Result<Run, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr)
            .lines()
            .rev()
            .take(10)
            .collect::<Vec<_>>()
            .join(" | "));
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    let code = run
        .status
        .code()
        .expect("compiled program exited via signal, not an exit code");
    Ok(Run {
        code,
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

struct Case {
    name: &'static str,
    what: &'static str,
    src: &'static str,
    opts: &'static [&'static str],
    /// The named refusal this program must get from the bridge on an x86-64
    /// host instead of agreeing with LLVM (a lane not yet qualified there).
    x86_64_refusal: Option<&'static str>,
}

fn corpus() -> Vec<Case> {
    vec![
        Case {
            name: "call_model_user_box_new",
            what: "a user `new(x) -> Box<u32>` and `W::new_uninit() -> Box<u64>` beside the \
                   genuine `Box::new` (the `Box` constructor models must key on the callee's \
                   identity, not its name)",
            src: include_str!("bridge_corpus/call_model_user_box_new.rs"),
            opts: O0_O2,
            x86_64_refusal: None,
        },
        Case {
            name: "iterator_minmax_item_ord",
            what: "`Iterator::max`/`min` over `Reverse<u32>` and a user `Ord` newtype beside \
                   primitive and `Ordering` items (the integer-compare model must follow the \
                   item type's `Ord`)",
            src: include_str!("bridge_corpus/iterator_minmax_item_ord.rs"),
            // At -Copt-level=0 the body of `Iterator::max` (`max_by(Ord::cmp)`) is
            // refused on every target.
            opts: &["-Copt-level=2"],
            x86_64_refusal: None,
        },
        Case {
            name: "track_caller_abi",
            what: "`#[track_caller]` definitions and calls carrying rustc's hidden \
                   `&'static Location` parameter",
            src: include_str!("bridge_corpus/track_caller_abi.rs"),
            opts: O0_O2,
            // `call_dyn(&dyn Tc)` reaches a `#[track_caller]` TRAIT method
            // through its vtable; x86-64 keeps that lane refused by name.
            x86_64_refusal: Some("[TCG-ABI-TRACKCALLER-VIRTUAL]"),
        },
        Case {
            name: "reference_values",
            what: "loop-carried references and references to references (the trust-ir the \
                   bridge emits for them must be well typed and fully defined)",
            src: include_str!("bridge_corpus/reference_values.rs"),
            opts: O0_O2,
            x86_64_refusal: None,
        },
    ]
}

#[test]
fn call_identity_and_track_caller_programs_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("call_identity_native") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    for case in corpus() {
        for opt in case.opts {
            let level = opt.trim_start_matches("-Copt-level=");
            let dir = workdir(&format!("{}_O{level}", case.name));
            if let (true, Some(code)) = (cfg!(target_arch = "x86_64"), case.x86_64_refusal) {
                match compile_and_run(&dir, case.name, case.src, opt, Some(&dylib)) {
                    Err(e) => assert!(
                        e.contains(code),
                        "{} ({opt}): expected the {code} refusal on x86-64, got <<<{e}>>>",
                        case.name
                    ),
                    Ok(_) => panic!(
                        "{} ({opt}): x86-64 compiled a program this lane refuses by {code}; \
                         qualify it against LLVM and drop the expected refusal",
                        case.name
                    ),
                }
                let _ = std::fs::remove_dir_all(&dir);
                continue;
            }
            let oracle = compile_and_run(&dir, case.name, case.src, opt, None)
                .unwrap_or_else(|e| panic!("{} ({opt}): LLVM oracle failed: <<<{e}>>>", case.name));
            let bridge = compile_and_run(&dir, case.name, case.src, opt, Some(&dylib))
                .unwrap_or_else(|e| {
                    panic!(
                        "{} ({opt}): trust-cg REFUSED or failed to compile {}: <<<{e}>>>",
                        case.name, case.what
                    )
                });
            assert_eq!(
                bridge.stdout, oracle.stdout,
                "{} ({opt}): STDOUT differs from LLVM for {}",
                case.name, case.what
            );
            assert_eq!(
                bridge.code, oracle.code,
                "{} ({opt}): exit code differs from LLVM for {}",
                case.name, case.what
            );
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
}
