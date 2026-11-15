#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: on a native target, a call to a function rustc marked
// `#[inline(never)]` or `#[cold]` stays a call in the bridge's object, as
// rustc's own backend keeps every `#[inline(never)]` call.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. The bridge names both kinds of function to every native
// module compile as `CompilerConfig::never_inline`, which the native inliner
// (OPT-4) honours. Before that, only the wasm lane read the set, and the
// x86-64 bridge spliced both callees into `main` at `-Copt-level=2`
// (measured 2026-11-07 on the bridge of `b30110fcd`: no call left in `main`;
// at `-Copt-level=0`, where no inliner runs, both calls).
//
// NON-VACUITY. The program also calls an unmarked twin of the
// `#[inline(never)]` function, the same body under another name. Every compile
// passes `-Zinline-mir=no`: rustc's MIR inliner, which runs at
// `-Copt-level=2` before the bridge reads any MIR, splices the twin itself, so
// without the flag the twin is gone whether or not the backend inliner ran
// (measured on x86-64 with the backend held at O0 by `opt-level=0`: no call to
// the twin, the marked calls kept). With it the twin reaches the bridge as its
// own function, and only OPT-4 can splice it. On x86-64, where it was
// measured, the twin's call must be gone at `-Copt-level=2`: OPT-4 ran in this
// compile and would have spliced the marked function too, but for its
// attribute (with the backend held at O0 the twin's call stays, and this
// assertion fails). On AArch64 only the kept calls and the run are asserted
// at `-Copt-level=2`. At `-Copt-level=0` all three calls must be present.
//
// WHERE IT ASSERTS. Only on Mach-O (Apple x86-64 and AArch64), where a
// CGU-private name keeps rustc's symbol (`__trust_cg_private.<cgu>.<index>.
// <symbol>`), so `main`'s listing names each callee. Elsewhere the test
// skips, saying why: on AArch64 ELF the private name is
// `__trust_cg_private.<cgu>.<index>` alone, so the listing cannot tell the
// three callees apart (the set's ELF names are pinned by the `wasm32_linkage`
// unit test `native_never_inline_set_follows_the_cgu_private_names`), and on
// every other native target the bridge refuses the program's `Internal`
// definitions (ruling OD-BRIDGE-UNSPELLED-BINDING-20261024).
//
// The objects also run: each, linked into a program, must exit as LLVM's
// object of the same source does.
//
// PROOF GATE: compiled with `no-proof-certs`. A compile that makes a proof
// claim runs no inliner at O1 and above (ruling OD-225), so there the set
// changes no code; this is a code-shape and execution test, not a
// certified-object claim.

use std::path::{Path, PathBuf};
use std::process::Command;

const PROGRAM: &str = r#"
#![no_std]
#![no_main]

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[inline(never)]
fn kept_never(mut n: u64) -> u64 {
    let mut c = 0u64;
    while n != 1 {
        n = if n & 1 == 0 { n / 2 } else { 3 * n + 1 };
        c += 1;
    }
    c
}

// The same body as `kept_never`, unmarked: the control.
fn spliced_twin(mut n: u64) -> u64 {
    let mut c = 0u64;
    while n != 1 {
        n = if n & 1 == 0 { n / 2 } else { 3 * n + 1 };
        c += 1;
    }
    c
}

#[cold]
fn kept_cold(n: u64) -> u64 {
    (n ^ 0x5a) | 1
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut r: u32 = 0;
    while r < 50 {
        acc = acc.wrapping_add(kept_never(27 + r as u64));
        acc = acc.wrapping_add(spliced_twin(7 + r as u64));
        r += 1;
    }
    if acc & 0xff == 0x34 {
        acc = kept_cold(acc);
    }
    ((acc ^ 0x11) & 0x7f) as i32
}
"#;

const MARKED: [&str; 2] = ["kept_never", "kept_cold"];
const CONTROL: &str = "spliced_twin";
/// Whether the control's splice at `-Copt-level=2` was measured on this
/// target (x86_64-apple-darwin, 2026-11-08, with `-Zinline-mir=no`).
const CONTROL_MEASURED: bool = cfg!(all(target_vendor = "apple", target_arch = "x86_64"));
/// Whether a CGU-private name keeps rustc's symbol on this target (Mach-O),
/// so `main`'s listing names each callee.
const PRIVATE_NAMES_CARRY_THE_SYMBOL: bool = cfg!(target_vendor = "apple");

fn workdir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_never_inline_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `PROGRAM` to one object at `opt` (with the bridge when `backend`
/// is `Some`, else with LLVM), rustc's MIR inliner off (see NON-VACUITY).
fn compile_object(dir: &Path, stem: &str, opt: &str, backend: Option<&Path>) -> PathBuf {
    let src = dir.join("prog.rs");
    std::fs::write(&src, PROGRAM).expect("write source");
    let object = dir.join(format!("{stem}.o"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args([
        "--crate-type",
        "bin",
        "--crate-name",
        "prog",
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
        "-Zinline-mir=no",
        "--emit=obj",
    ]);
    cmd.arg(opt);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&object).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    assert!(
        output.status.success(),
        "{stem}: compile failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    object
}

/// The sysroot's `llvm-objdump` (the Trust package ships the LLVM tools).
fn objdump() -> PathBuf {
    let query = |args: &[&str]| {
        let output = toolchain_support::rustc_driver_command()
            .args(args)
            .output()
            .expect("query the compiler");
        String::from_utf8_lossy(&output.stdout).into_owned()
    };
    let sysroot = query(&["--print", "sysroot"]).trim().to_owned();
    let host = query(&["-vV"])
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(str::to_owned))
        .expect("the compiler names its host");
    let tool = PathBuf::from(sysroot)
        .join("lib/rustlib")
        .join(host)
        .join("bin/llvm-objdump");
    assert!(
        tool.is_file(),
        "no llvm-objdump at {tool:?}: the Trust package's LLVM tools are required"
    );
    tool
}

/// The disassembly of `main` in `object`, relocation lines included: a call
/// to a symbol names it either in its own `<symbol>` annotation or in the
/// relocation line under it, on ELF and Mach-O alike.
fn main_listing(objdump: &Path, object: &Path) -> String {
    let output = Command::new(objdump)
        .args(["-d", "-r", "--no-show-raw-insn"])
        .arg(object)
        .output()
        .expect("run llvm-objdump");
    assert!(output.status.success(), "llvm-objdump {object:?} failed");
    let listing = String::from_utf8_lossy(&output.stdout).into_owned();
    let mut body = String::new();
    let mut inside = false;
    for line in listing.lines() {
        // A symbol header: `0000000000000040 <_main>:`.
        if line.ends_with(">:") {
            inside = line.ends_with("<main>:") || line.ends_with("<_main>:");
            continue;
        }
        if inside {
            body.push_str(line);
            body.push('\n');
        }
    }
    assert!(!body.is_empty(), "no `main` in {object:?}:\n{listing}");
    body
}

/// Link `object` into a program and return its exit code.
fn run_object(dir: &Path, stem: &str, object: &Path) -> i32 {
    let stubs = toolchain_support::write_abort_stubs(dir, &[object]);
    let bin = dir.join(stem);
    let link = Command::new("cc")
        .arg("-o")
        .arg(&bin)
        .arg(object)
        .arg(&stubs)
        .output()
        .expect("spawn cc");
    assert!(
        link.status.success(),
        "{stem}: link failed: {}",
        String::from_utf8_lossy(&link.stderr)
    );
    Command::new(&bin)
        .status()
        .expect("run the linked program")
        .code()
        .expect("the program exited by a signal")
}

#[test]
fn never_inline_and_cold_calls_stay_calls_on_the_native_target() {
    let test = "never_inline_and_cold_calls_stay_calls_on_the_native_target";
    if !PRIVATE_NAMES_CARRY_THE_SYMBOL {
        eprintln!(
            "{test}: SKIPPED — this target's codegen-unit-private names do not carry rustc's \
             symbol (AArch64 ELF), or the bridge refuses this program's `Internal` definitions \
             (ruling OD-BRIDGE-UNSPELLED-BINDING-20261024), so `main`'s listing cannot name the \
             callees; the assertions run on Mach-O (Apple x86-64 and AArch64)."
        );
        return;
    }
    if toolchain_support::skip_without_backend_knobs(test) {
        return;
    }
    let backend = backend_artifact_support::current_test_backend();
    let dir = workdir();
    let objdump = objdump();
    let reference = run_object(
        &dir,
        "llvm-O2",
        &compile_object(&dir, "llvm-O2", "-Copt-level=2", None),
    );
    for (opt, control_called) in [("-Copt-level=0", true), ("-Copt-level=2", false)] {
        let stem = format!("bridge{opt}");
        let object = compile_object(&dir, &stem, opt, Some(&backend));
        let main = main_listing(&objdump, &object);
        for marked in MARKED {
            assert!(
                main.contains(marked),
                "{opt}: `main` must still call `{marked}`:\n{main}"
            );
        }
        if control_called || CONTROL_MEASURED {
            assert_eq!(
                main.contains(CONTROL),
                control_called,
                "{opt}: the unmarked twin `{CONTROL}` must be {} (the inliner {} here):\n{main}",
                if control_called { "called" } else { "spliced" },
                if control_called {
                    "does not run"
                } else {
                    "runs"
                },
            );
        }
        assert_eq!(
            run_object(&dir, &stem, &object),
            reference,
            "{opt}: the bridge's program must exit as LLVM's does"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
