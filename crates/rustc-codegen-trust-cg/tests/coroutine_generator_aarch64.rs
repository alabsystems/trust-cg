// E2E (aarch64-apple-darwin): a REAL Rust `#[coroutine]` generator compiled
// THROUGH THE BRIDGE, linked, and RUN — asserting the yielded sequence is correct.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS: a 2-yield generator (`yield 10; yield 20; return 30`) driven by
// `Pin::new(&mut g).resume(())` in a loop. rustc's `StateTransform` lowers the
// coroutine into a state machine BEFORE the bridge sees it (`tcx.instance_mir` is
// post-transform — there is no `TerminatorKind::Yield`), so this exercises the
// rustc-native coroutine lowering the bridge gained:
//   * `AggregateKind::Coroutine`  — construct the frame (the Unresumed state) in
//     a memory slot at the rustc-computed layout (`coroutine_memory_layout`).
//   * `discriminant((*frame))`     — read the resume STATE through the frame ptr.
//   * `switchInt` over the state   — dispatch to the right resume arm.
//   * `SetDiscriminant((*frame))`  — advance the resume state in place.
//   * `CoroutineState::Yielded/Complete` construct + the caller's `match` on it.
//   * the `resume` call (a `ty::Coroutine`-bodied callee returning `CoroutineState`
//     by value) + `Pin::new`, the coroutine frame `Drop` (a no-op here — no
//     drop-needing cross-suspend state), and the `ResumedAfterReturn` assert.
//
// The driver packs the observed sequence into one i64 so the C `main` verifies
// BOTH the VALUES and their ORDER: `first*1_000_000 + second*1_000 + ret`. A
// correct run yields 10 then 20 then returns 30 => 10*1_000_000 + 20*1_000 + 30 =
// 10_020_030. Any wrong value, wrong order, or skipped/extra yield changes it.
//
// PROOF GATE: compiled with `TCG_NO_PROOF_CERTS=1`. Per-instruction AArch64
// mappings exist, but the final Mach-O object also emits compact-unwind
// `ARM64_RELOC_UNSIGNED` rows. Those object-side rows are now inventoried
// fail-closed and are not yet backed by a relocation proof, so this semantic
// runtime lane must not claim certified-object authority.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

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

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run coroutine test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn aarch64_std_available() -> bool {
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

fn host_is_aarch64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_coro_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// A REAL `#[coroutine]` closure (`yield 10; yield 20; return 30`) driven by
/// `Pin::new(&mut g).resume(())` in a loop. The observed sequence is packed into
/// one i64 so a wrong value / order / count is detectable from the return alone.
const GEN_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]\n\
\n\
use std::ops::{Coroutine, CoroutineState};\n\
use std::pin::Pin;\n\
\n\
#[no_mangle]\n\
pub extern \"C\" fn ay_gen_seq() -> i64 {\n\
    let mut g = #[coroutine] || {\n\
        yield 10i64;\n\
        yield 20i64;\n\
        30i64\n\
    };\n\
    let mut packed: i64 = 0;\n\
    let mut step: i64 = 0;\n\
    loop {\n\
        match Pin::new(&mut g).resume(()) {\n\
            CoroutineState::Yielded(v) => {\n\
                if step == 0 { packed += v * 1_000_000; } else { packed += v * 1_000; }\n\
                step += 1;\n\
            }\n\
            CoroutineState::Complete(r) => { packed += r; break; }\n\
        }\n\
    }\n\
    packed\n\
}\n";

/// The C driver: call the exported generator-driver and verify the packed
/// sequence is exactly `10*1_000_000 + 20*1_000 + 30 == 10_020_030`.
const DRIVER_C: &str = "\
#include <stdio.h>\n\
extern long ay_gen_seq(void);\n\
int main(void) {\n\
    long packed = ay_gen_seq();\n\
    printf(\"packed=%ld\\n\", packed);\n\
    if (packed != 10020030L) return 1;\n\
    return 0;\n\
}\n";

/// The defined (`T`/`t`) text symbol names of an object.
fn defined_text_symbols(obj: &Path) -> Vec<String> {
    let nm = String::from_utf8_lossy(&Command::new("nm").arg(obj).output().expect("nm").stdout)
        .into_owned();
    nm.lines()
        .filter_map(|l| {
            let mut it = l.split_whitespace();
            let _addr = it.next();
            match it.next() {
                Some("T") | Some("t") => it.next().map(|s| s.to_owned()),
                _ => None,
            }
        })
        .collect()
}

/// Whether `obj` is part of the PROGRAM-REACHABLE closure of the generator driver:
/// it defines the `ay_gen_seq` driver, the coroutine resume body / its `Pin::new`
/// (every `ay_gen_seq`-derived symbol), and nothing else. The bridge also emits a
/// dead default-allocator shim (referencing `#[rustc_std_internal_symbol]`
/// `__rdl_*` entry points) and dead `__trustcg_*` runtime helpers; this generator
/// allocates nothing, so those are unreachable and MUST be excluded from the link
/// (pulling the shim in would surface its undefined `__rdl_*` references). Selection
/// is by DEFINED symbol, never by filename — exactly as drop_heap_aarch64.rs.
fn is_reachable_from_driver(obj: &Path) -> bool {
    defined_text_symbols(obj).iter().any(|name| {
        name == "_ay_gen_seq"
            // The coroutine resume body, its `Pin::new`, and any other
            // `ay_gen_seq`-mangled item the driver calls.
            || name.contains("ay_gen_seq")
    })
}

#[test]
fn coroutine_generator_yields_in_order_and_links_runs_aarch64() {
    if !host_is_aarch64_macos() {
        eprintln!("skipping: requires an aarch64-apple-darwin host");
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !has_cc() {
        eprintln!("skipping: cc not available");
        return;
    }

    let dylib = ensure_dylib_built();
    let dir = workdir("seq");

    // 0. The generator MIR must actually carry the rustc-native coroutine state
    //    machine (`AggregateKind::Coroutine` + `SetDiscriminant`), not a `Yield`
    //    terminator — that is the lowering this test pins.
    let src_path = dir.join("gen_seq.rs");
    std::fs::write(&src_path, GEN_CRATE).expect("write source");
    let mir = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib", "-Copt-level=0", "-Zmir-opt-level=0"])
        .args(["--emit=mir", "-o"])
        .arg(dir.join("gen_seq.mir"))
        .arg(&src_path)
        .output()
        .expect("emit MIR");
    assert!(mir.status.success(), "MIR emission failed");
    let mir_text = std::fs::read_to_string(dir.join("gen_seq.mir")).expect("read MIR");
    assert!(
        mir_text.contains("{coroutine@") && mir_text.contains("(#0)}"),
        "generator MIR did not contain an `AggregateKind::Coroutine` frame construct"
    );
    assert!(
        mir_text.contains("discriminant((*_") && mir_text.contains(") = "),
        "generator MIR did not contain a `SetDiscriminant` on the coroutine frame"
    );
    assert!(
        !mir_text.contains("yield ") && !mir_text.contains("-> [resume:"),
        "generator MIR still contained a raw `Yield` terminator (not post-StateTransform)"
    );

    // 1. Compile the generator crate THROUGH THE BRIDGE to objects.
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let obj_out = dir.join("gen_seq");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .env("TCG_NO_PROOF_CERTS", "1")
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bridge failed to compile the coroutine crate. stderr: <<<{stderr}>>>"
    );

    // rustc places each function in its own CGU, so the bridge emits one object per
    // function (the `ay_gen_seq` driver, the coroutine `resume` body, `Pin::new`)
    // plus the dead allocator shim / runtime helpers. Collect every object that
    // defines code; the linker drops the unreferenced ones. The coroutine's
    // `drop_in_place` glue is legitimately SKIPPED (the frame holds no drop-needing
    // state, so the caller's `drop(g)` is a no-op) and must be unreachable — which
    // it is, since nothing references that symbol.
    let all_objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .filter(|p| is_reachable_from_driver(p))
        .collect();
    assert!(
        !all_objs.is_empty(),
        "bridge produced no code object. stderr: <<<{stderr}>>>"
    );
    // The driver AND the coroutine resume body must both be present (the resume
    // body is the actual post-StateTransform coroutine the bridge now lowers).
    let has_driver = all_objs.iter().any(|o| {
        String::from_utf8_lossy(&Command::new("nm").arg(o).output().expect("nm").stdout)
            .contains("_ay_gen_seq")
    });
    let has_resume_body = all_objs.iter().any(|o| {
        let nm = String::from_utf8_lossy(
            &Command::new("nm").arg(o).output().expect("nm").stdout,
        )
        .into_owned();
        // The coroutine resume body is the `{closure#0}` of `ay_gen_seq`.
        nm.lines().any(|l| l.contains("ay_gen_seq0") && !l.contains("_ay_gen_seq"))
    });
    assert!(
        has_driver && has_resume_body,
        "expected both the `ay_gen_seq` driver AND the coroutine resume body objects; \
         objects: {all_objs:?}"
    );

    // 2. Link all code objects with the C driver and RUN under a 10s timeout.
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, DRIVER_C).expect("write driver.c");
    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin).arg(&driver_path);
    for o in &all_objs {
        link.arg(o);
    }
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed (the resume body / Pin::new symbols must resolve). stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    // 3. RUN natively on aarch64 under a timeout. Exit 0 iff the generator yielded
    //    10 then 20 then returned 30 (packed == 10_020_030).
    let run = Command::new("timeout")
        .arg("10")
        .arg(&bin)
        .output()
        .or_else(|_| Command::new(&bin).output())
        .expect("run linked binary");
    let stdout = String::from_utf8_lossy(&run.stdout);
    let code = run.status.code().expect("process terminated by signal");
    assert_eq!(
        code, 0,
        "coroutine driver returned {code} (expected 0). The yielded sequence / order \
         was wrong. stdout: {stdout:?}"
    );
    assert!(
        stdout.contains("packed=10020030"),
        "expected the packed yielded sequence 10020030 (yield 10, yield 20, return 30); \
         got stdout: {stdout:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
