#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: VALUE-LEVEL uses of a WIDE pointer whose bridge value type
// is its data half alone.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. `rust_ty_to_trust_ir_ty` types a `&[T]` / `&str` /
// `*const [T]` / `&CStr` / `*const dyn Trait` value as ONE pointer: its data
// half. A lowering that loads, passes, stores or compares a wide pointer as that
// one value drops its metadata. Two such lowerings are pinned here:
//
//  * `<[T; N]>::map` / `core::array::from_fn` with a wide element: the
//    intercepted element loop must pass the element's `{ data, len }` slot to
//    the closure (`fix_array_map_wide_element`) and store both lanes of a wide
//    result (`fix_array_map_wide_result`);
//  * a comparison operator on wide raw pointers: `==` / `!=` / `<` / `<=` /
//    `>` / `>=` compare the `(data, metadata)` pairs, which also decides
//    `std::ptr::eq` (`fix_wide_pointer_compare`; operands reached through
//    derived impls, `Option`, generics, loops, joins and aggregate elements in
//    `fix_wide_pointer_compare_shapes`; for a vtable metadata
//    `fix_wide_pointer_compare_dyn`).
//
// Each program is compiled BY THE BRIDGE and BY LLVM at the SAME optimization
// level, run, and compared on STDOUT and EXIT CODE (panic text legitimately
// differs between the backends, so it is not compared). A dropped length or
// vtable lane prints a different value; a forged data lane reads or writes
// another object. A bridge refusal fails the test: these are the shapes the
// two lowerings admit.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
//
// WHY THE BRIDGE SIDE PASSES `no-proof-certs`. With proof certificates on, the
// bridge refuses AArch64 objects at proof promotion (`[TCG-PROOF-465]`, an
// opcode-inventory fact unrelated to these lowerings), which would stop every
// row after lowering succeeded. The knob is applied to the bridge side only, so
// the compared values are the two backends' answers to the same program.

use std::path::{Path, PathBuf};
use std::process::Command;

/// `-O0` keeps `<[T; N]>::map` and `std::ptr::eq` as calls (the intercepted
/// element loop, real wide-pointer parameters); `-O2` inlines them into the
/// caller, where the comparison operands are reborrow temporaries.
const BOTH_LEVELS: &[&str] = &["-Copt-level=0", "-Copt-level=2"];

/// `-O0` only: at `-O2` rustc inlines `map` / `from_fn` and the wide-result
/// rows stop at a different, unrelated refusal (the inlined body's
/// aggregate-element array assignment), so they pin nothing about this
/// intercept there.
const INTERCEPT_LEVEL: &[&str] = &["-Copt-level=0"];

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_wideptr_{stem}_{}", std::process::id()));
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
}

fn corpus() -> Vec<Case> {
    vec![
        Case {
            name: "fix_array_map_wide_element",
            what: "`<[T; N]>::map` over `&str`, `&[T]`, `&mut [u8]`, `*const [u8]` and \
                   `&CStr` elements: each element must cross the \
                   hand-built closure call as both lanes, not as its data half loaded \
                   at a 16-byte stride (which hands the closure the pointee's first 16 \
                   bytes as its `{ data, len }`)",
            src: include_str!("bridge_corpus/fix_array_map_wide_element.rs"),
            opts: BOTH_LEVELS,
        },
        Case {
            name: "fix_array_map_wide_result",
            what: "`<[T; N]>::map` / `array::from_fn` producing `[&[u8]; N]` / \
                   `[&str; N]`, and `map` over `NonNull<[u8]>`: the closure's two-value \
                   `PassMode::Pair` return must land as both lanes of the destination \
                   element, and a carrier source crosses as its `{ data, len }` slot",
            src: include_str!("bridge_corpus/fix_array_map_wide_result.rs"),
            opts: INTERCEPT_LEVEL,
        },
        Case {
            name: "fix_wide_pointer_compare",
            what: "`==` / `!=` / `<` / `<=` / `>` / `>=` and `std::ptr::eq` on \
                   `*const [T]`, `*const str`, `*const CStr` and `NonNull<[u8]>`: the \
                   `(data, length)` pairs are compared, so two pointers with one \
                   address and different lengths are not equal",
            src: include_str!("bridge_corpus/fix_wide_pointer_compare.rs"),
            opts: BOTH_LEVELS,
        },
        Case {
            name: "fix_wide_pointer_compare_shapes",
            what: "wide raw-pointer comparisons whose operands come from a derived \
                   `PartialEq` / `PartialOrd`, an `Option` payload, a generic `*const T` \
                   with an unsized `T`, a local written through `&mut`, a loop-carried \
                   value, a tuple / enum / array element, a `match` join, the `Ord` \
                   methods, a closure-captured local and a `Cell`'s value: each must \
                   read both lanes of each operand",
            src: include_str!("bridge_corpus/fix_wide_pointer_compare_shapes.rs"),
            opts: BOTH_LEVELS,
        },
        Case {
            name: "fix_wide_pointer_compare_dyn",
            what: "`==` / `!=` / `<` on `*const dyn Debug`: the `(data, vtable)` \
                   pairs are compared, so a struct and its first field (one address, \
                   two vtables) are not equal",
            src: include_str!("bridge_corpus/fix_wide_pointer_compare_dyn.rs"),
            opts: BOTH_LEVELS,
        },
    ]
}

#[test]
fn wide_pointer_value_lanes_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("wide_pointer_value_lanes_match_llvm") {
        return;
    }
    let dylib = ensure_dylib_built();
    for case in corpus() {
        for opt in case.opts {
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
