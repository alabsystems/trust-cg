#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a BY-VALUE AGGREGATE RETURN THROUGH AN INDIRECT CALL —
// a vtable slot (`&dyn Trait` method, the `Box<dyn Fn>` blanket dispatch) and a
// `fn(..)` POINTER — bound into a memory-backed destination.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. Three lanes carried the same coarse refusal: a call through a
// vtable slot or a fn pointer whose result is an aggregate landing in a whole,
// memory-backed destination local was rejected outright, even though the DIRECT
// path has relocated exactly that result into exactly that slot since
// `lower_memory_aggregate_call` landed. Measured 2026-09-14 on a `library/core`
// census, the virtual-call spelling alone was the sole refusal of 18 roots —
// every one of them `core::fmt`, and every one of them returning a ONE-BYTE
// `fmt::Result`.
//
// What the direct path reads and an indirect lane cannot is `ctx.sret_returns` /
// `ctx.scalar_pair_returns` / `ctx.aapcs64_hfa_abis`: all keyed by callee SYMBOL,
// and a vtable slot has none. The placement therefore comes from rustc's own
// `FnAbi` for the trait-method / fn-pointer signature instead, and
// `check_return_abi_for_output` re-checks it — so this battery covers BOTH the
// values (rows 1-3) and the refusals that must survive (row 4).
//
// ROW 4 IS A CONTROL, NOT A GAP. A `PassMode::Indirect` return — the hidden `x8`
// caller buffer — is still NOT lowered on an indirect lane, because the selector
// marker that places the buffer pointer in the target's indirect-result register
// is keyed by callee symbol. The control asserts that such a program still fails
// closed AND that its refusal names an ABI gate, which is what stops the
// destination widening above from quietly swallowing it.
//
// WHY STDOUT AND EXIT CODE ONLY: panic text legitimately differs between the two
// backends, so the comparison is restricted to what a correct program prints and
// the status it exits with.
//
// HOST-NATIVE: no `--target` is passed, so this runs on whatever host builds the
// crate. A single codegen unit keeps every function in one object.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Every case is run at BOTH of these. `-O0` exercises the un-inlined shape (a
/// real vtable load, a real indirect call, a real aggregate destination slot);
/// `-O2` exercises it after rustc's inliner has folded the aggregates, which is
/// where a lane written at the wrong offset usually surfaces.
const OPT_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

/// The compiler the differential drives.
///
/// `BUILD_COMPILER` is the compiler that BUILT the dylib, which is the right
/// default whenever the backend is built by the same driver that loads it. It is
/// NOT the same driver in a bootstrap layout: a codegen backend is a
/// rustc-private TOOL, compiled by the stage0 compiler against the stage-N
/// `rustc_driver` it then links and is loaded into. Name that driver here when
/// the two differ; the variable is read for the trust-cg side and the LLVM oracle
/// alike, so the differential stays apples-to-apples either way.
const COMPILER_ENV: &str = "TCG_DIFFERENTIAL_COMPILER";

fn compiler_command() -> Command {
    match std::env::var_os(COMPILER_ENV) {
        Some(path) => {
            let mut cmd = Command::new(path);
            cmd.arg("--edition=2021");
            // The Trust frontend verifies every crate by default and fails
            // closed on unproved obligations. These are codegen differentials,
            // not verification runs — the same off-switch `rustc_command`
            // applies on the trust channel, applied to BOTH sides.
            cmd.arg("-Ztrust-verify=off");
            cmd
        }
        None => toolchain_support::rustc_command(),
    }
}

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_vcallagg_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// Compile `src` (with the bridge when `backend` is `Some`), run it, and return
/// its exit code + stdout. `Err` carries the compiler's stderr tail.
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

    let mut cmd = compiler_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
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
}

fn corpus() -> Vec<Case> {
    vec![
        Case {
            name: "fix_virtual_call_unit_result",
            what: "a VIRTUAL call returning `Result<(), Sink>` — the one-byte \
                   `core::fmt::Result` shape all 18 census roots returned — into a \
                   memory-backed destination, with every returned value checked at \
                   runtime",
            src: include_str!("bridge_corpus/fix_virtual_call_unit_result.rs"),
        },
        Case {
            name: "fix_virtual_call_pair_return",
            what: "a VIRTUAL call returning a TWO-REGISTER `PassMode::Pair` \
                   aggregate — `(i64, i64)` and `&'static str` — whose lanes must \
                   be stored at rustc's own offsets; every field and every byte is \
                   checked",
            src: include_str!("bridge_corpus/fix_virtual_call_pair_return.rs"),
        },
        Case {
            name: "fix_fn_pointer_pair_return",
            what: "the `lower_indirect_call_terminator` sibling: \
                   `fn f(g: fn() -> (i64, i64)) -> i64 { let (a, b) = g(); a + b }` \
                   and its `-> &'static str` twin, through a fn pointer chosen at \
                   runtime",
            src: include_str!("bridge_corpus/fix_fn_pointer_pair_return.rs"),
        },
    ]
}

#[test]
fn indirect_aggregate_returns_match_llvm() {
    let dylib = ensure_dylib_built();
    for case in corpus() {
        for opt in OPT_LEVELS {
            let dir = workdir(&format!("{}_{}", case.name, opt.len()));
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

/// CONTROL: a `PassMode::Indirect` (hidden `x8` buffer) return through a vtable
/// slot must STILL fail closed, and the refusal must NAME an ABI gate.
///
/// This is the half of the hidden-buffer convention an indirect lane cannot
/// lower, and the destination widening above must not silently start emitting
/// it. The assertion is deliberately on the DIAGNOSTIC and not merely on the
/// non-zero exit: a refusal for some unrelated reason would pass a bare
/// "did not compile" check while proving nothing about the ABI.
#[test]
fn indirect_return_through_a_vtable_still_fails_closed() {
    let dylib = ensure_dylib_built();
    let src = include_str!("bridge_corpus/fix_virtual_call_indirect_return_control.rs");
    for opt in OPT_LEVELS {
        let dir = workdir(&format!("control_{}", opt.len()));
        // The oracle must still compile and run it — the program is valid Rust;
        // only trust-cg's indirect lanes decline the convention.
        compile_and_run(&dir, "control", src, opt, None)
            .unwrap_or_else(|e| panic!("({opt}) LLVM oracle failed on the control: <<<{e}>>>"));
        let err = match compile_and_run(&dir, "control", src, opt, Some(&dylib)) {
            Err(stderr) => stderr,
            Ok(_) => panic!(
                "({opt}) trust-cg COMPILED a `PassMode::Indirect` return through a vtable \
                 slot. The hidden return-buffer pointer is placed by a selector marker \
                 keyed by callee SYMBOL, and a vtable slot has none, so emitting this \
                 call leaves the buffer address in the wrong register. It must fail \
                 closed."
            ),
        };
        assert!(
            err.contains("[TCG-RET-ABI]")
                || err.contains("[TCG-SRET-ABI]")
                || err.contains("[TCG-INDIRECT-AGGREGATE-RET]"),
            "({opt}) the control failed closed, but for an UNNAMED reason — the refusal \
             must name the ABI gate that decided it, or this control proves nothing \
             about the return convention. stderr was: <<<{err}>>>"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
