#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: x86 drop-glue Slice 3 (needs-drop ELEMENTS) — a `Box<T>` /
// `Vec<T>` whose element `T` has its own `Drop`. The drop glue runs `T`'s
// `drop_in_place` on each initialized element (in ascending order for a `Vec`),
// then frees the heap buffer. This is the per-element drop loop the drop-glue plan
// (docs/x86-dropglue-plan.md STEP 5) describes, composed with the Slice-1 user-Drop
// glue for the element `T`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Each program is compiled for x86_64 through the rustc_codegen_trust_cg bridge at
// -O0/-O2/-O3 alongside the default LLVM backend. The HARD INVARIANT (a wrong drop
// is a P0 miscompile — a wrong side effect / double-free / use-after-free / wrong
// order): trust-cg either FAILS CLOSED (refuses to compile) OR produces the EXACT
// SAME exit code as LLVM. A per-element `Drop` that records into a static counter
// must run EXACTLY ONCE per element, front-to-back.
//
// Coverage:
//   * POSITIVE (compile + match): `Box<Guard>` (single- and multi-field), a
//     `Vec<Guard>` of several elements (drop ORDER observed via a base-10 running
//     digit accumulator — a wrong order diverges), an EMPTY `Vec<Guard>` (no
//     element drops, buffer still freed), a `Vec<Guard>` with a RUNTIME element
//     count. These MUST compile and match (a missed drop, extra drop, double-free,
//     or wrong order would diverge from LLVM's exit code).
//   * STILL FAIL CLOSED (never a wrong value): an `enum` element with a `Drop` impl
//     (Slice 4), a `Vec` of a multi-field non-scalar element (a separate Vec-model
//     gap), and an explicit `drop(v)` (introduces an unmodeled Vec move). Each must
//     fail closed OR match.

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
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
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
    assert!(status.success(), "cargo build failed; cannot run test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m134_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
) -> (std::process::Output, PathBuf) {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    (output, bin)
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// THE CORE INVARIANT: trust-cg either fails closed OR matches LLVM — never a
/// wrong value. Runs at O0/O2/O3.
fn assert_failclosed_or_matches(dylib: &Path, dir: &Path, name: &str, src: &str) {
    for opt in ["0", "2", "3"] {
        let (lout, lbin) = try_compile(dir, &format!("{name}_l"), src, None, opt);
        assert!(
            lout.status.success(),
            "LLVM compile of `{name}` (opt={opt}) failed: {}",
            String::from_utf8_lossy(&lout.stderr)
        );
        let llvm = run_exit_code(&lbin);

        let (tout, tbin) = try_compile(dir, &format!("{name}_t"), src, Some(dylib), opt);
        if !tout.status.success() {
            continue; // fail-closed is SOUND
        }
        let tcg = run_exit_code(&tbin);
        assert_eq!(
            tcg, llvm,
            "[P0 MISCOMPILE] `{name}` (opt={opt}): trust-cg produced a WRONG value \
             tcg={tcg} vs llvm={llvm} (must fail closed OR match)"
        );
    }
}

/// A POSITIVE check: `src` MUST compile on trust-cg at every opt level and match
/// LLVM. Used for the Slice-3 needs-drop-element shapes that are now supported — a
/// wrong count, a missed/extra element drop, a double-free, or a wrong drop order
/// would diverge from LLVM's exit code.
fn assert_compiles_and_matches(dylib: &Path, dir: &Path, name: &str, src: &str) {
    for opt in ["0", "2", "3"] {
        let (lout, lbin) = try_compile(dir, &format!("{name}_l"), src, None, opt);
        assert!(lout.status.success(), "LLVM compile of `{name}` failed");
        let llvm = run_exit_code(&lbin);
        let (tout, tbin) = try_compile(dir, &format!("{name}_t"), src, Some(dylib), opt);
        assert!(
            tout.status.success(),
            "[SLICE-3 REGRESSION] trust-cg failed to compile `{name}` (opt={opt}) — the \
             needs-drop-element shape must lower: {}",
            String::from_utf8_lossy(&tout.stderr)
        );
        let tcg = run_exit_code(&tbin);
        assert_eq!(
            tcg, llvm,
            "[P0 MISCOMPILE] `{name}` (opt={opt}): tcg={tcg} vs llvm={llvm}"
        );
    }
}

// A drop recorder that encodes ORDER: `TOTAL = TOTAL*10 + n`, so the final value's
// decimal digits ARE the front-to-back drop order (a reversed / wrong order gives a
// different number). No atomics (unsupported), a `static mut` RMW gives the exact
// observable side effect.
const REC: &str = "use std::hint::black_box as bb;\n\
    static mut TOTAL: i64 = 0;\n\
    #[inline(never)] fn rec(x: i64) { unsafe { TOTAL = TOTAL*10 + x; } }\n\
    #[inline(never)] fn total() -> i64 { unsafe { TOTAL } }\n";

/// SLICE 3 POSITIVE: `Box<Guard>` (single- and multi-field) runs the element's
/// `Drop` exactly once and matches LLVM at O0/O2/O3.
#[test]
fn box_needs_drop_element_runs_once_and_matches() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("box");

    // Single-field Guard: Drop runs once -> 7.
    let single = format!(
        "{REC}struct Guard {{ n: i64 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ rec(self.n); }} }}\n\
         #[inline(never)] fn go() {{ let _b = Box::new(Guard {{ n: bb(7) }}); }}\n\
         fn main() {{ go(); std::process::exit(total() as i32); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "box_single", &single);

    // Multi Copy fields (i32 + i64 + u8); Drop reads all -> 1+20+3 = 24 once.
    let multi = format!(
        "{REC}struct G {{ a: i32, b: i64, c: u8 }}\n\
         impl Drop for G {{ fn drop(&mut self) {{ \
            rec(self.a as i64 + self.b + self.c as i64); }} }}\n\
         #[inline(never)] fn go() {{ let _b = Box::new(G {{ a: bb(1), b: bb(20), c: bb(3) }}); }}\n\
         fn main() {{ go(); std::process::exit(total() as i32); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "box_multi", &multi);
}

/// SLICE 3 POSITIVE: `Vec<Guard>` drops EACH element exactly once, front-to-back,
/// then frees the buffer — the ORDER is observed via the base-10 accumulator.
#[test]
fn vec_needs_drop_elements_order_and_count_match() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("vec");

    // Three elements, drop order front-to-back (1,2,3) -> 123.
    let three = format!(
        "{REC}struct Guard {{ n: i64 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ rec(self.n); }} }}\n\
         #[inline(never)] fn go() {{ let mut v: Vec<Guard> = Vec::new(); \
            v.push(Guard {{ n: bb(1) }}); v.push(Guard {{ n: bb(2) }}); \
            v.push(Guard {{ n: bb(3) }}); }}\n\
         fn main() {{ go(); std::process::exit(total() as i32); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "vec_three", &three);

    // EMPTY Vec: no element drops, buffer still freed cleanly -> 0.
    let empty = format!(
        "{REC}struct Guard {{ n: i64 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ rec(self.n); }} }}\n\
         #[inline(never)] fn go() {{ let _v: Vec<Guard> = Vec::new(); }}\n\
         fn main() {{ go(); std::process::exit(total() as i32); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "vec_empty", &empty);

    // RUNTIME element count (a while-push loop): each of n elements drops once,
    // front-to-back. n=4 -> digits 1,2,3,4 -> 1234, truncated to u8 exit == 210
    // (LLVM truncates identically, so the differential still pins the order/count).
    let dynamic = format!(
        "{REC}struct Guard {{ n: i64 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ rec(self.n); }} }}\n\
         #[inline(never)] fn go(n: i64) {{ let mut v: Vec<Guard> = Vec::new(); \
            let mut i = 0i64; while i < n {{ v.push(Guard {{ n: bb(i + 1) }}); i += 1; }} }}\n\
         fn main() {{ go(bb(4)); std::process::exit(total() as i32); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "vec_dynamic", &dynamic);
}

/// STILL FAIL CLOSED (never a wrong value): an `enum` element with a `Drop` impl
/// (Slice 4), a `Vec` of a multi-field non-scalar element (a separate Vec-model
/// gap), and an explicit `drop(v)` (an unmodeled whole-Vec move). Each must fail
/// closed OR match LLVM.
#[test]
fn enum_element_multifield_vec_and_explicit_drop_stay_fail_closed() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("fc");

    // Slice 4: enum element with a Drop impl behind a Box.
    let enum_elem = format!(
        "{REC}enum E {{ A(i64), B }}\n\
         impl Drop for E {{ fn drop(&mut self) {{ \
            if let E::A(x) = self {{ rec(*x); }} else {{ rec(1); }} }} }}\n\
         #[inline(never)] fn go() {{ let _b = Box::new(E::A(bb(8))); }}\n\
         fn main() {{ go(); std::process::exit(total() as i32); }}\n"
    );
    assert_failclosed_or_matches(&dylib, &dir, "box_enum_elem", &enum_elem);

    // A Vec of a MULTI-FIELD non-scalar element (Vec-model gap, not the drop).
    let multi_vec = format!(
        "{REC}struct G {{ a: i32, b: i64 }}\n\
         impl Drop for G {{ fn drop(&mut self) {{ rec(self.a as i64 + self.b); }} }}\n\
         #[inline(never)] fn go() {{ let mut v: Vec<G> = Vec::new(); \
            v.push(G {{ a: bb(1), b: bb(2) }}); }}\n\
         fn main() {{ go(); std::process::exit(total() as i32); }}\n"
    );
    assert_failclosed_or_matches(&dylib, &dir, "vec_multifield_elem", &multi_vec);

    // Explicit `drop(v)` introduces an unmodeled whole-Vec move.
    let explicit = format!(
        "{REC}struct Guard {{ n: i64 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ rec(self.n); }} }}\n\
         #[inline(never)] fn go() {{ let mut v: Vec<Guard> = Vec::new(); \
            v.push(Guard {{ n: bb(1) }}); v.push(Guard {{ n: bb(2) }}); drop(v); \
            rec(bb(9)); }}\n\
         fn main() {{ go(); std::process::exit(total() as i32); }}\n"
    );
    assert_failclosed_or_matches(&dylib, &dir, "explicit_drop_v", &explicit);
}

// ----------------------------------------------------------------------------
// FUZZ-8 residual [TCG-EH-ELEM-DROP]: element `Drop` PANICS under panic=unwind.
// ----------------------------------------------------------------------------
// rustc's own drop glue gives the element loop a NESTED cleanup: the panicked
// element counts as dropped, the REMAINING elements are still dropped, the heap
// buffer is freed, and the unwind then continues at the enclosing Drop's own
// unwind action (running the frame's guard Drops; a drop already running DURING
// an unwind aborts). The bridge's plain-`Call` element loop let the unwinder
// walk PAST the frame — live divergences at every opt level (guard skipped ->
// libstd catch 101; remaining element Drops skipped). Now the element glue call
// is an `Inst::Invoke` whose synthesized pad replicates the nested cleanup.
//
// The observable is the exit code: the `TOTAL` base-10 accumulator records the
// element-drop ORDER, and the guard's Drop (running mid-unwind) exits with
// `total()*10 + code` — a skipped guard, a skipped remaining-element drop, a
// wrong order, or a missing double-panic abort all diverge from LLVM.

fn try_compile_unwind(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
) -> (std::process::Output, PathBuf) {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

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
    (output, bin)
}

/// Exit status as the shell reports it: the exit code, or `128 + signal` for a
/// signal death (the double-panic SIGABRT -> 134). Both binaries are mapped
/// identically, so the differential still pins abort-vs-catch behavior.
fn run_status_code(bin: &Path) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    let status = Command::new(bin).output().expect("run binary").status;
    match status.code() {
        Some(code) => code,
        None => 128 + status.signal().expect("no exit code and no signal"),
    }
}

/// POSITIVE under panic=unwind: the element-panic shapes MUST compile on
/// trust-cg at every opt level and match LLVM's exit status exactly.
fn assert_unwind_compiles_and_matches(dylib: &Path, dir: &Path, name: &str, src: &str) {
    for opt in ["0", "2", "3"] {
        let (lout, lbin) = try_compile_unwind(dir, &format!("{name}_l"), src, None, opt);
        assert!(lout.status.success(), "LLVM compile of `{name}` failed");
        let llvm = run_status_code(&lbin);
        let (tout, tbin) = try_compile_unwind(dir, &format!("{name}_t"), src, Some(dylib), opt);
        assert!(
            tout.status.success(),
            "[TCG-EH-ELEM-DROP REGRESSION] trust-cg failed to compile `{name}` \
             (opt={opt}) — the element-panic shape must lower: {}",
            String::from_utf8_lossy(&tout.stderr)
        );
        let tcg = run_status_code(&tbin);
        assert_eq!(
            tcg, llvm,
            "[P0 MISCOMPILE] `{name}` (opt={opt}): tcg={tcg} vs llvm={llvm}"
        );
    }
}

const EH_REC: &str = "use std::hint::black_box as bb;\n\
    static mut TOTAL: i64 = 0;\n\
    #[inline(never)] fn rec(x: i64) { unsafe { TOTAL = TOTAL*10 + x; } }\n\
    #[inline(never)] fn total() -> i64 { unsafe { TOTAL } }\n\
    struct P { n: i64 }\n\
    impl Drop for P { fn drop(&mut self) { rec(self.n); \
        if self.n == 2 { panic!(\"elem boom\"); } } }\n\
    struct G { code: i64 }\n\
    impl Drop for G { fn drop(&mut self) { \
        std::process::exit((total()*10 + self.code) as i32); } }\n";

#[test]
fn element_drop_panic_unwind_matches_llvm() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("ehpanic");

    // (a) Vec element panics mid-loop with a LIVE GUARD in the same frame
    // (`Cleanup(pad)` action): LLVM drops P1, P2 (panics), then P3 in the
    // NESTED cleanup, frees the buffer, and the guard exits mid-unwind:
    // TOTAL=123 -> exit (1237 & 0xff) = 213. A skipped guard is 101; a skipped
    // remaining-drop is 127.
    let vec_guard = format!(
        "{EH_REC}#[inline(never)] fn go() {{ let _g = G {{ code: bb(7) }}; \
            let mut v: Vec<P> = Vec::new(); v.push(P {{ n: bb(1) }}); \
            v.push(P {{ n: bb(2) }}); v.push(P {{ n: bb(3) }}); }}\n\
         fn main() {{ go(); std::process::exit(0); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "eh_vec_guard", &vec_guard);

    // (b) Box element panics with a live guard: the box storage is freed in the
    // nested cleanup and the guard exits mid-unwind (27).
    let box_guard = format!(
        "{EH_REC}#[inline(never)] fn go() {{ let _g = G {{ code: bb(7) }}; \
            let _b = Box::new(P {{ n: bb(2) }}); }}\n\
         fn main() {{ go(); std::process::exit(0); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "eh_box_guard", &box_guard);

    // (c) DOUBLE PANIC: the Vec is dropped DURING an unwind (`Terminate`
    // action), so the element's panic must ABORT ("panic in a destructor
    // during cleanup", SIGABRT -> 134), not continue to libstd's catch (101).
    let double = format!(
        "{EH_REC}#[inline(never)] fn go() {{ let mut v: Vec<P> = Vec::new(); \
            v.push(P {{ n: bb(2) }}); panic!(\"first\"); }}\n\
         fn main() {{ go(); std::process::exit(0); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "eh_double_panic", &double);

    // (d) `Continue` action: no guard in the dropping frame — the nested
    // cleanup still drops the REMAINING elements + frees the buffer before the
    // unwind leaves the frame (a guard in `main` observes TOTAL=123 -> 213;
    // the walk-past bug observed 12 -> 127).
    let continue_action = format!(
        "{EH_REC}#[inline(never)] fn go() {{ let mut v: Vec<P> = Vec::new(); \
            v.push(P {{ n: bb(1) }}); v.push(P {{ n: bb(2) }}); \
            v.push(P {{ n: bb(3) }}); }}\n\
         fn main() {{ let _g = G {{ code: bb(7) }}; go(); std::process::exit(0); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "eh_vec_continue", &continue_action);

    // (e) TWO panicking elements: the SECOND panic fires inside the NESTED
    // remaining-elements cleanup — a double panic, abort (134), exactly like
    // rustc's `Terminate(InCleanup)` cleanup-path drops.
    let two_panics = format!(
        "use std::hint::black_box as bb;\n\
         static mut TOTAL: i64 = 0;\n\
         #[inline(never)] fn rec(x: i64) {{ unsafe {{ TOTAL = TOTAL*10 + x; }} }}\n\
         #[inline(never)] fn total() -> i64 {{ unsafe {{ TOTAL }} }}\n\
         struct P {{ n: i64 }}\n\
         impl Drop for P {{ fn drop(&mut self) {{ rec(self.n); \
            if self.n == 2 || self.n == 3 {{ panic!(\"elem boom\"); }} }} }}\n\
         struct G {{ code: i64 }}\n\
         impl Drop for G {{ fn drop(&mut self) {{ \
            std::process::exit((total()*10 + self.code) as i32); }} }}\n\
         #[inline(never)] fn go() {{ let _g = G {{ code: bb(7) }}; \
            let mut v: Vec<P> = Vec::new(); v.push(P {{ n: bb(2) }}); \
            v.push(P {{ n: bb(3) }}); v.push(P {{ n: bb(4) }}); }}\n\
         fn main() {{ go(); std::process::exit(0); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "eh_two_panics", &two_panics);
}

// ----------------------------------------------------------------------------
// FUZZ-9: adversarial re-fuzz of the nested-cleanup machinery (1578475). The
// full sweep (~50 programs x O0/O2/O3 x panic=unwind/abort) found ZERO live
// miscompiles; these pin the trickiest shapes it exercised, plus the one
// faithfulness fix it landed: the TERMINATE entry is now REASON-mapped
// (`Terminate(InCleanup)` -> `panic_in_cleanup`, "panic in a destructor during
// cleanup" — byte-identical to rustc; previously `panic_cannot_unwind` for
// both reasons, same abort/exit but different wording).
// ----------------------------------------------------------------------------

/// The trickiest FUZZ-9 nested-cleanup shapes, each pinned as
/// compile-and-match at O0/O2/O3 under panic=unwind.
#[test]
fn nested_cleanup_fuzz9_shapes_match_llvm() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("fuzz9");

    const REC9: &str = "use std::hint::black_box as bb;\n\
        static mut TOTAL: i64 = 0;\n\
        #[inline(never)] fn rec(x: i64) { unsafe { TOTAL = TOTAL*10 + x; } }\n\
        #[inline(never)] fn total() -> i64 { unsafe { TOTAL } }\n\
        struct G { code: i64 }\n\
        impl Drop for G { fn drop(&mut self) { \
            std::process::exit((total()*10 + self.code) as i32); } }\n\
        struct R { id: i64 }\n\
        impl Drop for R { fn drop(&mut self) { rec(self.id); } }\n";

    // (f) CLEANUP CHAIN: two rec-guards + a Vec whose middle element panics —
    // the elem-loop nested cleanup finishes into padB whose drop(_b) Invokes
    // with [return: padA] (the HEAD/BODY split + normal-edge redirect shape).
    // Drops: 1,2(panic),3 then _b(5), _a(4) mid-unwind; main guard exits.
    let chain = format!(
        "{REC9}struct P {{ n: i64 }}\n\
         impl Drop for P {{ fn drop(&mut self) {{ rec(self.n); \
            if self.n == 2 {{ panic!(\"elem boom\"); }} }} }}\n\
         #[inline(never)] fn go() {{ let _a = R {{ id: bb(4) }}; \
            let _b = R {{ id: bb(5) }}; let mut v: Vec<P> = Vec::new(); \
            v.push(P {{ n: bb(1) }}); v.push(P {{ n: bb(2) }}); \
            v.push(P {{ n: bb(3) }}); }}\n\
         fn main() {{ let _mg = G {{ code: bb(7) }}; go(); \
            std::process::exit(total() as i32); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "f9_chain", &chain);

    // (g) INTERLEAVED guards and TWO Vec<P>s: v2's element panics on the
    // normal path; v1's element loop then runs INSIDE the cleanup chain
    // (Terminate-action arm, no second panic) between the guard Drops.
    let interleaved = format!(
        "{REC9}struct P {{ n: i64 }}\n\
         impl Drop for P {{ fn drop(&mut self) {{ rec(self.n); \
            if self.n == 3 {{ panic!(\"elem boom\"); }} }} }}\n\
         #[inline(never)] fn go() {{ let _a = R {{ id: bb(5) }}; \
            let mut v1: Vec<P> = Vec::new(); v1.push(P {{ n: bb(1) }}); \
            v1.push(P {{ n: bb(2) }}); let _b = R {{ id: bb(6) }}; \
            let mut v2: Vec<P> = Vec::new(); v2.push(P {{ n: bb(3) }}); \
            v2.push(P {{ n: bb(4) }}); }}\n\
         fn main() {{ let _mg = G {{ code: bb(7) }}; go(); \
            std::process::exit(total() as i32); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "f9_interleaved", &interleaved);

    // (h) CROSS-VEC DOUBLE PANIC: v2's element panics normally, then v1's
    // element panics while ITS loop runs during the cleanup — the
    // Terminate(InCleanup) arm aborts (134).
    let cross_vec = format!(
        "{REC9}struct P {{ n: i64 }}\n\
         impl Drop for P {{ fn drop(&mut self) {{ rec(self.n); \
            if self.n == 2 || self.n == 3 {{ panic!(\"elem boom\"); }} }} }}\n\
         #[inline(never)] fn go() {{ let mut v1: Vec<P> = Vec::new(); \
            v1.push(P {{ n: bb(1) }}); v1.push(P {{ n: bb(2) }}); \
            let mut v2: Vec<P> = Vec::new(); v2.push(P {{ n: bb(3) }}); \
            v2.push(P {{ n: bb(4) }}); }}\n\
         fn main() {{ let _mg = G {{ code: bb(7) }}; go(); \
            std::process::exit(total() as i32); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "f9_cross_vec", &cross_vec);

    // (i) TWO BOXES, the panicking one dropped SECOND: the other box's element
    // drop then runs inside the cleanup (box glue under Terminate, no panic).
    let two_boxes = format!(
        "{REC9}struct P {{ n: i64 }}\n\
         impl Drop for P {{ fn drop(&mut self) {{ rec(self.n); \
            if self.n == 2 {{ panic!(\"elem boom\"); }} }} }}\n\
         #[inline(never)] fn go() {{ let _bok = Box::new(P {{ n: bb(5) }}); \
            let _bp = Box::new(P {{ n: bb(2) }}); }}\n\
         fn main() {{ let _mg = G {{ code: bb(7) }}; go(); \
            std::process::exit(total() as i32); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "f9_two_boxes", &two_boxes);

    // (j) VALUE-RETURNING frame: the panicking Vec drop sits in a `fn -> i64`
    // (Invoke normal edges carry a live return value past the pads).
    let value_frame = format!(
        "{REC9}struct P {{ n: i64 }}\n\
         impl Drop for P {{ fn drop(&mut self) {{ rec(self.n); \
            if self.n == 2 {{ panic!(\"elem boom\"); }} }} }}\n\
         #[inline(never)] fn go(k: i64) -> i64 {{ let mut v: Vec<P> = Vec::new(); \
            v.push(P {{ n: bb(1) }}); v.push(P {{ n: bb(2) }}); \
            v.push(P {{ n: bb(3) }}); k * 2 }}\n\
         fn main() {{ let _mg = G {{ code: bb(7) }}; let r = go(bb(21)); \
            std::process::exit((total() + r) as i32); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "f9_value_frame", &value_frame);

    // (k) Vec<P> in MAIN, no guards anywhere: the nested cleanup runs, then
    // the unwind reaches libstd's lang_start catch (message + exit 101).
    let in_main = "use std::hint::black_box as bb;\n\
        static mut TOTAL: i64 = 0;\n\
        #[inline(never)] fn rec(x: i64) { unsafe { TOTAL = TOTAL*10 + x; } }\n\
        struct P { n: i64 }\n\
        impl Drop for P { fn drop(&mut self) { rec(self.n); \
            if self.n == 2 { panic!(\"elem boom\"); } } }\n\
        fn main() { let mut v: Vec<P> = Vec::new(); v.push(P { n: bb(1) }); \
            v.push(P { n: bb(2) }); v.push(P { n: bb(3) }); }\n";
    assert_unwind_compiles_and_matches(&dylib, &dir, "f9_in_main", in_main);

    // (l) FUZZ-8 COMPOSITION: an intercepted iterator drive's payload panics
    // while a Vec<P> is live — the intercept pad and the element-loop cleanup
    // pads compose in one frame.
    let iter_payload = format!(
        "{REC9}struct P {{ n: i64 }}\n\
         impl Drop for P {{ fn drop(&mut self) {{ rec(self.n); \
            if self.n == 9 {{ panic!(\"elem boom\"); }} }} }}\n\
         #[inline(never)] fn go() {{ let mut v: Vec<P> = Vec::new(); \
            v.push(P {{ n: bb(1) }}); v.push(P {{ n: bb(3) }}); \
            let s: i64 = (0..bb(5i64)).map(|i| if i == 2 {{ panic!(\"payload\") }} \
            else {{ i }}).sum(); rec(s); }}\n\
         fn main() {{ let _mg = G {{ code: bb(7) }}; go(); \
            std::process::exit(total() as i32); }}\n"
    );
    assert_unwind_compiles_and_matches(&dylib, &dir, "f9_iter_payload", &iter_payload);
}

/// FUZZ-9 faithfulness fix pin: a DOUBLE PANIC at a cleanup-path drop aborts
/// with rustc's `Terminate(InCleanup)` entry `panic_in_cleanup` — the abort
/// reason line is byte-identical to LLVM's ("panic in a destructor during
/// cleanup", NOT the `Abi` reason's "panic in a function that cannot unwind").
#[test]
fn double_panic_abort_reason_wording_matches_llvm() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("fuzz9w");

    let two_panics = format!(
        "use std::hint::black_box as bb;\n\
         struct P {{ n: i64 }}\n\
         impl Drop for P {{ fn drop(&mut self) {{ \
            if self.n >= 2 {{ panic!(\"elem boom\"); }} }} }}\n\
         #[inline(never)] fn go() {{ let mut v: Vec<P> = Vec::new(); \
            v.push(P {{ n: bb(2) }}); v.push(P {{ n: bb(3) }}); }}\n\
         fn main() {{ go(); std::process::exit(0); }}\n"
    );
    for opt in ["0", "2", "3"] {
        let (tout, tbin) =
            try_compile_unwind(&dir, &format!("f9w_o{opt}_t"), &two_panics, Some(&dylib), opt);
        assert!(
            tout.status.success(),
            "trust-cg failed to compile the double-panic shape (opt={opt}): {}",
            String::from_utf8_lossy(&tout.stderr)
        );
        let run = Command::new(&tbin).output().expect("run binary");
        let stderr = String::from_utf8_lossy(&run.stderr);
        assert_eq!(run_status_code(&tbin), 134, "double panic must SIGABRT");
        assert!(
            stderr.contains("panic in a destructor during cleanup"),
            "opt={opt}: expected rustc's InCleanup terminate wording; got:\n{stderr}"
        );
        assert!(
            !stderr.contains("panic in a function that cannot unwind"),
            "opt={opt}: the Abi-reason entry leaked into an InCleanup terminate:\n{stderr}"
        );
    }
}
