// Integration test (FUZZ-7): PANIC=UNWIND raise semantics on x86_64 — whole
// std binaries compiled via the rustc_codegen_trust_cg bridge, RUN, and their
// exit codes checked against the default LLVM backend AND the expected value.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS — the FUZZ-7 EH differential-fuzz miscompile classes, all
// found the day EH went default-on, all fixed together:
// ----------------------------------------------------------------------------
//  1. [TCG-EH-RAISE] A REACHABLE diverging panic block under `panic=unwind`
//     was trapped whole (`ud2`) instead of RAISING: the process died with
//     SIGILL (exit 132), no message, no unwind, EVERY cleanup Drop skipped,
//     no libstd catch/exit(101). Fixed by `emit_unwinding_panic_raise`: a
//     genuine `core::panicking::panic(msg, len, &Location)` call honoring the
//     block's unwind edge (`Invoke` into the cleanup pad / plain call for
//     `Continue`). `drop_exits` observes the Drop DURING unwind via
//     `process::exit(47)` from the guard's `Drop`; `multiframe_order` encodes
//     the innermost-first Drop ORDER across three frames (exit 18 = ((0*3+1)*3
//     +2)*3+3 — any skipped/reordered Drop yields a different code).
//  2. [TCG-EH-WALK] Phase-1 unwinding died with `_URC_END_OF_STACK` ("failed
//     to initiate panic, error 5" abort, exit 134): x86-64 Mach-O objects only
//     carried FDEs for EH/dynamic-alloc functions (plain frames — `main`, the
//     `lang_start` shims — were unwalkable), and ld64's `__eh_frame`-only
//     reader mis-associated FDEs in multi-function objects. Fixed by emitting
//     clang's exact shape: a `__LD,__compact_unwind` DWARF-mode entry per
//     function (section-based UNSIGNED reloc against `__text`) plus a zPLR FDE
//     for EVERY function — non-EH functions get a synthetic ALL-FILLER LSDA
//     ("no handler here, continue"). `passthrough` unwinds through a no-drop
//     frame; `plain_panic`/`oob_no_guard` end in libstd's `lang_start` catch
//     (message + exit 101).
//  3. [TCG-EH-DIVERGE-INVOKE] A DIVERGING callee with a cleanup edge
//     (`main`-with-a-live-guard calls `process::exit`) failed closed on
//     "Invoke call without a normal successor" — fixed with a synthetic
//     `Unreachable` continuation (`closure_panic`, the guard programs).
//  4. [TCG-EH-ASSERT-RAISE] `Assert` failure edges (bounds check / div-by-zero
//     / overflow at O0) branched to the reserved ud2 trap block under
//     `panic=unwind` — same skipped-Drops SIGILL class. Fixed by routing the
//     failure edge to a synthetic raise block honoring the assert's unwind
//     edge (`assert_oob_guard` exit 37, `div_zero_guard` exit 59).
//  4b. [TCG-EH-INTERCEPT-RAISE] (X1 follow-up) The bounds checks EMITTED BY
//     INTERCEPTED call lowerings themselves — the `&arr[a..b]` array-range
//     subslice index and `<[T]>::split_at` interceptions synthesize their own
//     compare + branch (no MIR `Assert`) — still branched to the reserved ud2
//     trap under `panic=unwind`: same skipped-Drops SIGILL class. Fixed by
//     routing the failure edge through `intercepted_bounds_check_fail_target`
//     (raise honoring the intercepted call's unwind edge; trap kept for
//     abort/nounwind). `subslice_oob_guard` exit 47 / `split_at_oob_guard`
//     exit 53, no-guard variants exit 101, in-bounds controls.
//  5. [TCG-TRACK-CALLER-DIVERGE] A diverging call to a PRECOMPILED std
//     `#[track_caller]` panic helper OUTSIDE `core::panicking`
//     (`core::option::unwrap_failed`) passed GARBAGE in the hidden trailing
//     `&'static Location` register — the entry dereferenced it and died with
//     SIGSEGV (exit 139) instead of panicking. PRE-EXISTING under BOTH panic
//     strategies; fixed by lowering such calls as the synthesized raise
//     (`unwrap_none`, `expect_err` — exit 101).
//
// The panic message TEXT for synthesized raises is the long-accepted cosmetic
// deviation; what these programs pin is the VALUE-OBSERVABLE raise semantics:
// Drop execution + order across unwind, the libstd catch, and exit codes.
// `run_exit_code` insists on a REAL exit code — a SIGILL/SIGSEGV/SIGABRT
// regression fails the test loudly.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";

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
    assert!(
        status.success(),
        "cargo build failed; cannot run panic-unwind test"
    );
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn x86_64_std_available() -> bool {
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

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_ehraise_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the given backend (None = default LLVM) at `opt` under
/// `-Cpanic=unwind`, returning the linked binary path.
fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("{name}_{opt}{}", if backend.is_some() { "_tcg" } else { "_llvm" }));

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=unwind"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    assert!(
        output.status.success(),
        "compile of `{name}` (O{opt}) failed ({} backend). stderr: <<<{}>>>",
        if backend.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

/// Run and demand a REAL exit code: a signal death (the SIGILL-trap /
/// SIGSEGV-garbage-Location / SIGABRT-failed-to-initiate regressions this test
/// pins) fails the assertion loudly.
fn run_exit_code(bin: &Path) -> i32 {
    let output = Command::new(bin).output().expect("run binary");
    output.status.code().unwrap_or_else(|| {
        panic!(
            "`{}` died via a signal ({:?}) instead of exiting — the unwind-raise \
             regression this test pins",
            bin.display(),
            output.status
        )
    })
}

/// Every panic=unwind shape × O0/O2/O3: trust-cg exit == LLVM exit == expected.
#[test]
fn panic_unwind_raise_shapes_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("shapes");

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        // [TCG-EH-RAISE] Drop DURING unwind, observable via exit(47) from the
        // guard's Drop. Was: SIGILL 132, Drop skipped.
        (
            "drop_exits",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn inner(n: i32) -> i32 { let _g = G(47); if n > 1 { panic!(\"die\"); } 5 }\n\
             fn main() { let n = black_box(7i32); let v = inner(n); std::process::exit(v); }\n",
            47,
        ),
        // [TCG-EH-RAISE] Innermost-first Drop ORDER across three unwound
        // frames, encoded as acc = acc*3 + tag; outermost Drop exits.
        (
            "multiframe_order",
            "use std::hint::black_box;\n\
             static mut ACC: i32 = 0;\n\
             struct G(i32, bool);\n\
             impl Drop for G {\n\
                 fn drop(&mut self) { unsafe {\n\
                     ACC = ACC * 3 + self.0;\n\
                     if self.1 { std::process::exit(ACC & 0xff); }\n\
                 } }\n\
             }\n\
             fn f3(n: i32) { let _g = G(1, false); if n > 0 { panic!(\"x\"); } }\n\
             fn f2(n: i32) { let _g = G(2, false); f3(n); }\n\
             fn f1(n: i32) { let _g = G(3, true); f2(n); }\n\
             fn main() { let n = black_box(4i32); f1(n); std::process::exit(200); }\n",
            18,
        ),
        // [TCG-EH-WALK] Unwind THROUGH a no-drop pass-through frame; both
        // guards' Drops run (17 + 25 = 42). Was: "failed to initiate panic,
        // error 5" abort.
        (
            "passthrough",
            "use std::hint::black_box;\n\
             static mut ACC: i32 = 0;\n\
             struct G(i32, bool);\n\
             impl Drop for G {\n\
                 fn drop(&mut self) { unsafe {\n\
                     ACC += self.0;\n\
                     if self.1 { std::process::exit(ACC); }\n\
                 } }\n\
             }\n\
             fn deep(n: i32) -> i32 { if n > 2 { panic!(\"d\"); } n }\n\
             fn mid(n: i32) -> i32 { deep(n) + 1 }\n\
             fn outer(n: i32) -> i32 { let _g = G(17, false); mid(n) }\n\
             fn main() { let n = black_box(6i32); let _e = G(25, true); \
                         let v = outer(n); std::process::exit(v); }\n",
            42,
        ),
        // [TCG-EH-DIVERGE-INVOKE] Panic inside a generic-applied closure;
        // caller + main guards both drop (11 + 20 = 31). Also pins the
        // diverging `process::exit`-under-a-live-guard Invoke shape in main.
        (
            "closure_panic",
            "use std::hint::black_box;\n\
             static mut ACC: i32 = 0;\n\
             struct G(i32, bool);\n\
             impl Drop for G {\n\
                 fn drop(&mut self) { unsafe {\n\
                     ACC += self.0;\n\
                     if self.1 { std::process::exit(ACC); }\n\
                 } }\n\
             }\n\
             fn apply<F: FnOnce(i32) -> i32>(f: F, v: i32) -> i32 { f(v) }\n\
             fn work(n: i32) -> i32 {\n\
                 let _g = G(11, false);\n\
                 apply(|x| { if x > 2 { panic!(\"cl\"); } x + 1 }, n)\n\
             }\n\
             fn main() { let n = black_box(5i32); let _e = G(20, true); \
                         let v = work(n); std::process::exit(v); }\n",
            31,
        ),
        // [TCG-EH-ASSERT-RAISE] Index OOB (Assert terminator) raises through
        // the guards (7 + 30 = 37). Was: SIGILL 132 via the assert trap block.
        (
            "assert_oob_guard",
            "use std::hint::black_box;\n\
             static mut ACC: i32 = 0;\n\
             struct G(i32, bool);\n\
             impl Drop for G {\n\
                 fn drop(&mut self) { unsafe {\n\
                     ACC += self.0;\n\
                     if self.1 { std::process::exit(ACC); }\n\
                 } }\n\
             }\n\
             fn pick(a: &[i32; 4], i: usize) -> i32 { let _g = G(7, false); a[i] }\n\
             fn main() { let i = black_box(9usize); let _e = G(30, true); \
                         let arr = [1, 2, 3, 4]; let v = pick(&arr, i); \
                         std::process::exit(v); }\n",
            37,
        ),
        // [TCG-EH-ASSERT-RAISE] Division by zero raises through the guards
        // (9 + 50 = 59).
        (
            "div_zero_guard",
            "use std::hint::black_box;\n\
             static mut ACC: i32 = 0;\n\
             struct G(i32, bool);\n\
             impl Drop for G {\n\
                 fn drop(&mut self) { unsafe {\n\
                     ACC += self.0;\n\
                     if self.1 { std::process::exit(ACC); }\n\
                 } }\n\
             }\n\
             fn dv(a: i32, b: i32) -> i32 { let _g = G(9, false); a / b }\n\
             fn main() { let z = black_box(0i32); let _e = G(50, true); \
                         let v = dv(100, z); std::process::exit(v); }\n",
            59,
        ),
        // [TCG-EH-RAISE]+[TCG-EH-WALK] Plain panic, no guards: unwinds to
        // libstd's `lang_start` catch — message + exit 101.
        (
            "plain_panic",
            "use std::hint::black_box;\n\
             fn main() { let n = black_box(3i32); if n > 2 { panic!(\"plain\"); } \
                         std::process::exit(7); }\n",
            101,
        ),
        // [TCG-EH-ASSERT-RAISE] Runtime index OOB with no guards: exit 101.
        (
            "oob_no_guard",
            "use std::hint::black_box;\n\
             fn main() { let i = black_box(9usize); let a = [1i32, 2, 3, 4]; \
                         std::process::exit(a[i]); }\n",
            101,
        ),
        // [TCG-TRACK-CALLER-DIVERGE] `Option::unwrap()` on `None`: the
        // diverging `core::option::unwrap_failed` `#[track_caller]` call.
        // Was: SIGSEGV 139 (garbage hidden `&Location` argument).
        (
            "unwrap_none",
            "use std::hint::black_box;\n\
             fn main() { let n = black_box(3i32); \
                         let o: Option<i32> = if n > 2 { None } else { Some(n) }; \
                         let v = o.unwrap(); std::process::exit(v); }\n",
            101,
        ),
        // [TCG-TRACK-CALLER-DIVERGE] `Result::expect` on `Err` (the
        // `expect_failed` entry).
        (
            "expect_err",
            "use std::hint::black_box;\n\
             fn main() { let n = black_box(3i32); \
                         let r: Result<i32, i32> = if n > 2 { Err(n) } else { Ok(n) }; \
                         let v = r.expect(\"wanted ok\"); std::process::exit(v); }\n",
            101,
        ),
        // [TCG-EH-INTERCEPT-RAISE] Bounds-check failure edge of an INTERCEPTED
        // call lowering — `&arr[a..b]` array-range subslice index
        // (`lower_local_array_subslice_index_call` emits its OWN bounds check,
        // not a MIR `Assert`) — raises through the live guard. Was: SIGILL 132
        // via the reserved trap block (Drop skipped).
        (
            "subslice_oob_guard",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(47); let arr = [1i64, 2, 3, 4]; \
                         let s = &arr[1..black_box(7usize)]; \
                         black_box(s.len()); std::process::exit(9); }\n",
            47,
        ),
        // [TCG-EH-INTERCEPT-RAISE] `<[T]>::split_at` interception's `mid <= len`
        // bounds check raises through the live guard. Was: SIGILL 132.
        (
            "split_at_oob_guard",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(53); let v = [1i64, 2, 3]; \
                         let s: &[i64] = &v; \
                         let (a, b) = s.split_at(black_box(5usize)); \
                         black_box(a.len() + b.len()); std::process::exit(9); }\n",
            53,
        ),
        // [TCG-EH-INTERCEPT-RAISE] Same two shapes with NO guard: the raise
        // unwinds to libstd's `lang_start` catch — message + exit 101.
        (
            "subslice_oob_no_guard",
            "use std::hint::black_box;\n\
             fn main() { let arr = [1i64, 2, 3, 4]; \
                         let s = &arr[1..black_box(7usize)]; \
                         black_box(s.len()); std::process::exit(9); }\n",
            101,
        ),
        (
            "split_at_oob_no_guard",
            "use std::hint::black_box;\n\
             fn main() { let v = [1i64, 2, 3]; let s: &[i64] = &v; \
                         let (a, b) = s.split_at(black_box(5usize)); \
                         black_box(a.len() + b.len()); std::process::exit(9); }\n",
            101,
        ),
        // IN-BOUNDS control for the intercepted checks: the raise block must
        // not perturb the success path (subslice len 2 -> 12; split 2/1 -> 41).
        (
            "subslice_ok_path",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(90 + self.0); } }\n\
             fn main() { let _g = G(black_box(2)); let arr = [1i64, 2, 3, 4]; \
                         let s = &arr[1..black_box(3usize)]; \
                         std::process::exit(10 + s.len() as i32); }\n",
            12,
        ),
        (
            "split_at_ok_path",
            "use std::hint::black_box;\n\
             fn main() { let v = [1i64, 2, 3]; let s: &[i64] = &v; \
                         let (a, b) = s.split_at(black_box(2usize)); \
                         std::process::exit(20 + (a.len() * 10 + b.len()) as i32); }\n",
            41,
        ),
        // NO-panic control: the EH structure must not perturb the normal path
        // (guard drops on return; 42 + 21 = 63).
        (
            "ok_path",
            "use std::hint::black_box;\n\
             static mut ACC: i32 = 0;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { unsafe { ACC += self.0; } } }\n\
             fn work(n: i32) -> i32 { let _g = G(n); n * 2 }\n\
             fn main() { let n = black_box(21i32); let v = work(n); \
                         std::process::exit(v + unsafe { ACC }); }\n",
            63,
        ),
        // [TCG-EH-INTERCEPT-CLEANUP] (FUZZ-8) — a panic inside a payload closure
        // invoked by an INTERCEPTED iterator drive loop must honor the
        // intercepted call terminator's cleanup edge: the frame's live guard
        // Drop runs during unwind (exit 73). Was: the drive emitted a plain
        // `Inst::Call`, the unwinder walked PAST the frame (walk-past LSDA), the
        // guard was SKIPPED and libstd's catch exited 101 — a live wrong-exit
        // miscompile at EVERY opt level. Fixed by stashing the terminator's pad
        // (`intercept_unwind_pad`) and emitting payload calls as `Inst::Invoke`
        // + continuation split (`push_unwindable_intercept_call`).
        (
            "iter_map_panic_guard",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(73); let n = black_box(20u64); \
                         let s: u64 = (0..n).map(|i| { if i == 7 { panic!(\"im\"); } i * 2 }).sum(); \
                         std::process::exit((s % 251) as i32); }\n",
            73,
        ),
        // Same class through the FILTER predicate payload.
        (
            "iter_filter_panic_guard",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(79); let n = black_box(30u64); \
                         let s: u64 = (0..n).filter(|&i| { if i == 13 { panic!(\"if\"); } i % 2 == 0 }).sum(); \
                         std::process::exit((s % 251) as i32); }\n",
            79,
        ),
        // Same class through the FOLD payload (the direct fold-closure call
        // site in the drive, distinct from the Map/Filter adapter site).
        (
            "iter_fold_panic_guard",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(61); let n = black_box(20u64); \
                         let s = (0..n).fold(0u64, |a, i| { if i == 5 { panic!(\"fo\"); } a + i }); \
                         std::process::exit((s % 251) as i32); }\n",
            61,
        ),
        // Same class through the TRY_FOLD driver's check payload
        // (`position`'s ControlFlow closure — the third payload call site).
        (
            "iter_position_panic_guard",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(63); let n = black_box(20u64); \
                         let p = (0..n).position(|i| { if i == 9 { panic!(\"po\"); } i == 15 }); \
                         std::process::exit(p.map(|v| v as i32).unwrap_or(200)); }\n",
            63,
        ),
        // Two frames: the panic in the drive payload unwinds through the
        // driving frame's guard AND main's guard (11 + 20 = 31).
        (
            "iter_nested_guard",
            "use std::hint::black_box;\n\
             static mut ACC: i32 = 0;\n\
             struct G(i32, bool);\n\
             impl Drop for G {\n\
                 fn drop(&mut self) { unsafe {\n\
                     ACC += self.0;\n\
                     if self.1 { std::process::exit(ACC); }\n\
                 } }\n\
             }\n\
             fn work(n: u64) -> u64 {\n\
                 let _g = G(11, false);\n\
                 (0..n).map(|i| { if i == 3 { panic!(\"x\"); } i }).sum()\n\
             }\n\
             fn main() { let _e = G(20, true); let v = work(black_box(9u64)); \
                         std::process::exit((v % 251) as i32); }\n",
            31,
        ),
        // IN-BOUNDS control: the Invoke + continuation split on the payload
        // call must not perturb the drive's normal path (sum 3*0..30 = 1305,
        // % 251 = 50; the guard's exit(90) must NOT fire before main's exit).
        (
            "iter_sum_guard_ok",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(90); let n = black_box(30u64); \
                         let s: u64 = (0..n).map(|i| i * 3).sum(); \
                         std::process::exit((s % 251) as i32); }\n",
            50,
        ),
        // [TCG-EH-DROP-GLUE-UNWIND] (FUZZ-8) — the Slice-1 user-`Drop` glue call
        // must honor its MIR CLEANUP edge: a Drop that panics on the NORMAL
        // path with ANOTHER guard live runs that guard's Drop during unwind
        // (exit 55). Was: plain `Inst::Call` dropped the edge, the second
        // guard was SKIPPED, libstd's catch exited 101 — live at every opt
        // level. (The `Terminate` half of the same fix — double panic aborts,
        // SIGABRT — is pinned by `double_panic_aborts_like_llvm` below.)
        (
            "drop_panic_second_guard",
            "use std::hint::black_box;\n\
             struct P(u64);\n\
             impl Drop for P { fn drop(&mut self) { if self.0 == 7 { panic!(\"dp\"); } } }\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(55); let _p = P(black_box(7u64)); }\n",
            55,
        ),
    ];

    for (name, src, expected) in shapes {
        for opt in ["0", "2", "3"] {
            let llvm_bin = compile(&dir, name, src, None, opt);
            let tcg_bin = compile(&dir, name, src, Some(&dylib), opt);
            let llvm_code = run_exit_code(&llvm_bin);
            let tcg_code = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_code, *expected,
                "`{name}` (O{opt}): LLVM exit {llvm_code} != expected {expected} (harness bug?)"
            );
            assert_eq!(
                tcg_code, llvm_code,
                "`{name}` (O{opt}): trust-cg exit {tcg_code} != LLVM exit {llvm_code} — \
                 panic=unwind raise semantics diverged"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// [TCG-EH-TERMINATE] (FUZZ-8) — a DOUBLE PANIC (a guard's `Drop` panicking
/// while ALREADY unwinding) must ABORT, exactly like rustc: the cleanup pad's
/// drop-glue call carries `UnwindAction::Terminate(InCleanup)`, whose codegen
/// is an invoke into a terminate pad calling
/// `core::panicking::panic_cannot_unwind()` ("panic in a destructor during
/// cleanup" + non-unwinding-panic SIGABRT). The bridge lowered that glue call
/// as a plain `Inst::Call` with the synthesized walk-past LSDA, so the second
/// panic CONTINUED unwinding to libstd's catch and the process exited 101
/// while LLVM's aborted with SIGABRT (134 in a shell) — a live exit divergence
/// found by the FUZZ-8 differential. Fixed by `terminate_pad_block` +
/// honoring the Drop terminator's unwind action in `lower_drop_terminator`.
///
/// Pinned at O0 only: at O2/O3 the shape currently FAILS CLOSED (sound).
/// Unlike `run_exit_code`, this runner accepts signal death — SIGABRT is
/// exactly what it demands of BOTH backends.
#[test]
fn double_panic_aborts_like_llvm() {
    use std::os::unix::process::ExitStatusExt;
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("dblpanic");
    let src = "use std::hint::black_box;\n\
               struct D(u64);\n\
               impl Drop for D { fn drop(&mut self) { if self.0 == 7 { panic!(\"drop panic\"); } } }\n\
               fn main() { let _d = D(black_box(7u64)); panic!(\"first\"); }\n";
    let llvm_bin = compile(&dir, "dblpanic", src, None, "0");
    let tcg_bin = compile(&dir, "dblpanic", src, Some(&dylib), "0");
    let llvm_status = Command::new(&llvm_bin).output().expect("run llvm binary").status;
    let tcg_status = Command::new(&tcg_bin).output().expect("run tcg binary").status;
    assert_eq!(
        llvm_status.signal(),
        Some(libc_sigabrt()),
        "LLVM double panic did not die via SIGABRT (harness assumption): {llvm_status:?}"
    );
    assert_eq!(
        tcg_status.signal(),
        llvm_status.signal(),
        "trust-cg double panic did not abort like LLVM (tcg {tcg_status:?} vs llvm \
         {llvm_status:?}) — the [TCG-EH-TERMINATE] regression this test pins \
         (the second panic must hit the terminate pad, not unwind to the catch)"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

fn libc_sigabrt() -> i32 {
    6
}

/// [TCG-EH-LITERAL-MSG] (FUZZ-8 cosmetic follow-up) — EXACT panic message for
/// LITERAL panics. On this nightly `panic!("literal")` / `assert!(cond,
/// "literal")` lower via `panic_fmt(Arguments::from_str(const "…"))` (O0) /
/// the MIR-inlined tagged-pointer `Arguments` struct literal (O2/O3), so the
/// direct-`panic(&str)` pass-through never fired and the raise printed the
/// synthesized "message not lowered by trust-cg" text. Now the `Arguments` is
/// decoded (`decode_pure_literal_fmt_arguments`) and the REAL literal is
/// raised: the message line must BYTE-MATCH LLVM's. Formatted panics stay
/// synthesized — pinned here as "never a WRONG/partial message" (the tcg
/// message must not be the bare format prefix) with unchanged exit codes.
#[test]
fn literal_panic_message_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("litmsg");

    // Extract the message body from a panic report: everything after the
    // first "panicked at …:\n" header line up to the trailing backtrace note
    // (the thread-name prefix / backtrace hint are runtime noise, the message
    // BYTES in between are the comparison target).
    fn panic_message(stderr: &str) -> Option<String> {
        let (_, rest) = stderr.split_once(":\n")?;
        let body = match rest.split_once("\nnote: run with `RUST_BACKTRACE=1`") {
            Some((body, _)) => body,
            None => rest.trim_end_matches('\n'),
        };
        Some(body.to_owned())
    }

    // (name, source, the exact literal LLVM prints, exact-match expected).
    let shapes: &[(&str, &str, &str, bool)] = &[
        (
            "lit_panic",
            "use std::hint::black_box;\n\
             fn main() { let n = black_box(3i32); \
                         if n > 2 { panic!(\"boom: the exact literal bytes\"); } \
                         std::process::exit(7); }\n",
            "boom: the exact literal bytes",
            true,
        ),
        (
            "lit_assert",
            "use std::hint::black_box;\n\
             fn main() { let n = black_box(3i32); \
                         assert!(n <= 2, \"assert literal message\"); \
                         std::process::exit(7); }\n",
            "assert literal message",
            true,
        ),
        // Escaped braces are a single literal piece post-unescaping.
        (
            "lit_braces",
            "use std::hint::black_box;\n\
             fn main() { let n = black_box(3i32); \
                         if n > 2 { panic!(\"braces {{}} stay literal\"); } \
                         std::process::exit(7); }\n",
            "braces {} stay literal",
            true,
        ),
        // `unreachable!()` goes through the direct `panic(&str)` lang-item arm
        // (already exact before this fix) — pinned so the panic_fmt arm never
        // regresses it.
        (
            "lit_unreachable",
            "use std::hint::black_box;\n\
             fn main() { let n = black_box(3i32); \
                         if n > 2 { unreachable!(); } \
                         std::process::exit(7); }\n",
            "internal error: entered unreachable code",
            true,
        ),
        // A FORMATTED panic (runtime placeholder): stays on the synthesized
        // path. What is pinned: the tcg message is never the WRONG/partial
        // literal (the bare "value " prefix), and the exit code matches.
        (
            "fmt_panic",
            "use std::hint::black_box;\n\
             fn main() { let n = black_box(3i32); \
                         if n > 2 { panic!(\"value {}\", n); } \
                         std::process::exit(7); }\n",
            "value 3",
            false,
        ),
    ];

    for (name, src, literal, must_match) in shapes {
        for opt in ["0", "2", "3"] {
            let llvm_bin = compile(&dir, name, src, None, opt);
            let tcg_bin = compile(&dir, name, src, Some(&dylib), opt);
            let llvm_out = Command::new(&llvm_bin).output().expect("run llvm binary");
            let tcg_out = Command::new(&tcg_bin).output().expect("run tcg binary");
            assert_eq!(
                tcg_out.status.code(),
                llvm_out.status.code(),
                "`{name}` (O{opt}): exit codes diverged"
            );
            let llvm_msg = panic_message(&String::from_utf8_lossy(&llvm_out.stderr))
                .unwrap_or_else(|| panic!("`{name}` (O{opt}): no LLVM panic message"));
            let tcg_msg = panic_message(&String::from_utf8_lossy(&tcg_out.stderr))
                .unwrap_or_else(|| panic!("`{name}` (O{opt}): no trust-cg panic message"));
            assert_eq!(
                llvm_msg, *literal,
                "`{name}` (O{opt}): LLVM message != expected literal (harness bug?)"
            );
            if *must_match {
                assert_eq!(
                    tcg_msg, llvm_msg,
                    "`{name}` (O{opt}): trust-cg literal panic message is not byte-exact"
                );
            } else {
                // Synthesized is accepted; a WRONG or PARTIAL message is not.
                assert_ne!(
                    tcg_msg, "value ",
                    "`{name}` (O{opt}): trust-cg printed a PARTIAL format template — \
                     worse than the synthesized message"
                );
                assert!(
                    tcg_msg == llvm_msg || tcg_msg.contains("message not lowered by trust-cg"),
                    "`{name}` (O{opt}): formatted panic message neither exact nor the \
                     synthesized text: <<<{tcg_msg}>>>"
                );
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// [TCG-TRACK-CALLER-RETURN] (X1 follow-up to FUZZ-7's class 5) — a RETURNING
/// `#[track_caller]` function in a PRECOMPILED (LLVM-built) dependency rlib.
/// Its real ABI carries a hidden trailing `&'static Location` the MIR call
/// args do not include; the bridge used to leave GARBAGE in that register,
/// which the callee dereferences on its panic path to format the message:
/// panicking calls died SIGSEGV (exit 139) instead of panicking (LLVM: message
/// + exit 101), while the non-panic path silently "worked" (register never
/// read) — a latent, reachable miscompile under BOTH panic strategies. Fixed
/// by widening the declared FuncTy (`func_ty_for_instance`) and appending the
/// const-eval'd call-site Location (`lower_direct_call_args` via
/// `callee_needs_extern_caller_location`) — exactly what rustc's codegen
/// passes when the caller is not itself `#[track_caller]`. Also covers a
/// DIVERGING track_caller fn OUTSIDE core/std/alloc (the FUZZ-7 raise
/// interception is std-crate-gated; the appended Location makes the real call
/// correct instead).
#[test]
fn returning_track_caller_extern_rlib_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("tcret");

    // The dependency rlib — ALWAYS compiled by the default LLVM backend (the
    // precompiled-object stand-in), so its `#[track_caller]` fns keep the real
    // hidden-Location ABI at the link boundary.
    let lib_src = "#[track_caller]\n\
                   pub fn checked_div(a: i64, b: i64) -> i64 {\n\
                       if b == 0 { panic!(\"ehlib: divide by zero\"); }\n\
                       a / b\n\
                   }\n\
                   #[track_caller]\n\
                   pub fn always_panics(code: i64) -> i64 {\n\
                       panic!(\"ehlib: always panics with {code}\");\n\
                   }\n";
    let lib_path = dir.join("ehlib.rs");
    std::fs::write(&lib_path, lib_src).expect("write lib source");
    let rlib = dir.join("libehlib.rlib");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "rlib", "--crate-name", "ehlib"])
        .args(["--target", TARGET, "-Cpanic=unwind", "-Copt-level=2"])
        .arg("-o")
        .arg(&rlib)
        .arg(&lib_path)
        .output()
        .expect("spawn rustc for rlib");
    assert!(
        output.status.success(),
        "rlib compile failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        // Panic path of the RETURNING track_caller extern: message + exit 101.
        // Was: SIGSEGV 139 (garbage Location dereferenced).
        (
            "tc_ret_panics",
            "use std::hint::black_box;\n\
             fn main() { let ok = ehlib::checked_div(black_box(84), black_box(2)); \
                         let v = ehlib::checked_div(black_box(10), black_box(0)); \
                         std::process::exit((ok + v) as i32); }\n",
            101,
        ),
        // Non-panic path: the appended Location must not perturb the value.
        (
            "tc_ret_ok",
            "use std::hint::black_box;\n\
             fn main() { let ok = ehlib::checked_div(black_box(84), black_box(2)); \
                         std::process::exit(ok as i32); }\n",
            42,
        ),
        // The raise unwinds THROUGH the precompiled frame and runs the caller's
        // guard Drop (exit 61 from the Drop during unwind).
        (
            "tc_ret_guard",
            "use std::hint::black_box;\n\
             struct G(i32);\n\
             impl Drop for G { fn drop(&mut self) { std::process::exit(self.0); } }\n\
             fn main() { let _g = G(61); \
                         let v = ehlib::checked_div(black_box(10), black_box(0)); \
                         std::process::exit(v as i32); }\n",
            61,
        ),
        // DIVERGING track_caller OUTSIDE core/std/alloc: not claimed by the
        // FUZZ-7 std-gated raise interception; the appended Location makes the
        // real call correct.
        (
            "tc_diverging_rlib",
            "use std::hint::black_box;\n\
             fn main() { let v = ehlib::always_panics(black_box(7)); \
                         std::process::exit(v as i32); }\n",
            101,
        ),
    ];

    for (name, src, expected) in shapes {
        for opt in ["0", "2", "3"] {
            let src_path = dir.join(format!("{name}.rs"));
            std::fs::write(&src_path, src).expect("write source");
            for backend in [None, Some(dylib.as_path())] {
                let bin = dir.join(format!(
                    "{name}_{opt}{}",
                    if backend.is_some() { "_tcg" } else { "_llvm" }
                ));
                let mut cmd = Command::new("rustup");
                cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
                    .args(["--crate-type", "bin"]);
                if let Some(dylib) = backend {
                    cmd.arg(backend_arg(dylib));
                }
                cmd.args(["--target", TARGET, "-Cpanic=unwind"])
                    .arg(format!("-Copt-level={opt}"))
                    .arg("--extern")
                    .arg(format!("ehlib={}", rlib.display()))
                    .arg("-o")
                    .arg(&bin)
                    .arg(&src_path);
                let output = cmd.output().expect("spawn rustc");
                assert!(
                    output.status.success(),
                    "compile of `{name}` (O{opt}, {} backend) failed. stderr: <<<{}>>>",
                    if backend.is_some() { "trust-cg" } else { "llvm" },
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            let llvm_code = run_exit_code(&dir.join(format!("{name}_{opt}_llvm")));
            let tcg_code = run_exit_code(&dir.join(format!("{name}_{opt}_tcg")));
            assert_eq!(
                llvm_code, *expected,
                "`{name}` (O{opt}): LLVM exit {llvm_code} != expected {expected} (harness bug?)"
            );
            assert_eq!(
                tcg_code, llvm_code,
                "`{name}` (O{opt}): trust-cg exit {tcg_code} != LLVM exit {llvm_code} — \
                 returning-track_caller hidden-Location ABI diverged"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}
