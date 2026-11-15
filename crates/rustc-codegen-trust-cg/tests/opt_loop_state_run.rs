// Compiled only on an aarch64-apple-darwin host: the aarch64 rows run natively
// and the x86-64 rows under Rosetta (`support/x86_rosetta.rs`).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/loop_coverage_program.rs"]
mod loop_coverage;
#[path = "support/loop_state_program.rs"]
mod loop_state;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/x86_rosetta.rs"]
mod x86_rosetta_support;

// Integration test: the loop-state contract of trust-cg-opt's pre-loop
// rewrites, checked on whole aarch64-apple-darwin programs against the LLVM
// oracle.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The rows, the program and the performance controls are
// `support/loop_state_program.rs`. Before trust-cg-opt stated the rule once
// (`src/loop_contract.rs`) and routed every such rewrite through it, whole
// programs came out wrong at O2/O3. Measured 2026-09-30 through this bridge,
// LLVM as the oracle, at trust-cg `47f63ec1d` and again at `c84d39e93`: fill
// and zero-fill with a carried accumulator (`neon_fill`), the count-if arm that
// also runs `t += i` (`neon_bytesum`), and byte-sum, byte-count, popcount, fill
// and zero-fill whose only extra register is `last = i`, at N a multiple of the
// vector block (the vector loop takes every iteration, so the scalar remainder
// that writes `last` never runs): 21 of 144 rows wrong at each of O2 and O3.
//
// The second test runs the same program for x86_64-apple-darwin under Rosetta,
// against an x86-64 `core` built from the compiler's own library source
// (`support/x86_rosetta.rs`, the helper the cross-backend signature tests
// share). Measured at the same commits: byte-sum, byte-count, popcount-sum,
// fill, zero-fill, i32-sum and the count-if arm with a second carried register
// came out wrong (`x86_vectorize`), 37 of 144 rows at each of O2 and O3. On
// Apple silicon the Rosetta route always exists, so a missing route or library
// source FAILS the test; it never skips.
//
// `aarch64_benchmark_loops_stay_vectorized` keeps the programs the NEON passes
// exist for vectorized: `p7_sieve` and `v3_popcount` from benchmarks/beat-llvm
// keep their NEON ops in `main` and agree with LLVM.
//
// The program's early-exit rows (`EXIT_KERNELS`) and
// `pre_loop_rewrites_never_run_past_an_exit` judge the contract's CONTROL
// clause: a rewrite must not run past a `break`, a `return` or a bounds check
// its scalar loop would have taken. Before it, on aarch64 at O2 and O3,
// `neon_fill` filled past a `break` (wrong values) and past a slice's end
// before its bounds-check panic, and `strided_store_unroll` admitted any exit
// into a panicking block, so its unrolled stores ran past a short slice
// (SIGSEGV).
//
// `aarch64_real_program_corpus_runs_agree_with_llvm` is the RUN lane the
// shared real-program corpus lacked:
// `real_program_corpus_a64` compiles its guests with proof certificates on, so
// every row is refused `[TCG-PROOF-465]` and none is ever linked or run. That
// is why `p09_sieve`, the guest this defect was found in, was invisible: its
// count-if arm over `[bool]` exited 192 against LLVM's 198 at O2/O3 until a
// bool-load change stopped the matcher firing on it. Here every guest is
// compiled, linked and run at O0, O2 and O3 and must exit as LLVM's build does.
//
// Every test builds with the backend's no-proof-certs knob: they judge
// codegen, not proof promotion. This is test-rung evidence; nothing here is a
// proof.

use loop_state::{
    Bridge, OPTS, Target, compile, compile_with_panic, disassembly_of, run, vector_ops, workdir,
};
use std::path::Path;

include!("real_program_corpus/corpus_guests.rs");

#[test]
fn aarch64_pre_loop_rewrites_keep_every_register_the_loop_leaves() {
    darwin_native::require("opt_loop_state_run rows", &["objdump"]);
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let failures = loop_state::check_target(
        Target::Aarch64,
        Bridge {
            dylib: &dylib,
            knobs: &knobs,
        },
    );
    assert!(
        failures.is_empty(),
        "{} aarch64 row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn x86_64_pre_loop_rewrites_keep_every_register_the_loop_leaves() {
    if let x86_rosetta_support::X86Exec::Unavailable(reason) =
        x86_rosetta_support::x86_execution(OPTS[0])
    {
        panic!("x86-64 rows: this Apple-silicon host has no x86-64 execution route: {reason}");
    }
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let failures = loop_state::check_target(
        Target::X86_64,
        Bridge {
            dylib: &dylib,
            knobs: &knobs,
        },
    );
    assert!(
        failures.is_empty(),
        "{} x86-64 row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The ITERATION-COVERAGE rows (`support/loop_coverage_program.rs`): every
/// loop kernel over run-time `(start, bound)` pairs in nine loop forms, and
/// over constant ones, must print what LLVM's build prints, at O2 and O3. A
/// rewrite that runs new code in place of scalar iterations and, with the
/// scalar remainder, runs any other set of iterations changes the line.
/// `controls` must keep vector code, so the rows are not bought by
/// vectorizing nothing.
fn coverage_rows(target: Target, controls: &[&str]) {
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let failures = loop_coverage::check_target(
        target,
        Bridge {
            dylib: &dylib,
            knobs: &knobs,
        },
        controls,
    );
    assert!(
        failures.is_empty(),
        "{} {target:?} coverage row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn aarch64_rewrites_run_exactly_the_iterations_they_replace() {
    darwin_native::require("opt_loop_state_run coverage rows", &["objdump"]);
    coverage_rows(Target::Aarch64, loop_coverage::AARCH64_CONTROLS);
}

#[test]
fn x86_64_rewrites_run_exactly_the_iterations_they_replace() {
    if let x86_rosetta_support::X86Exec::Unavailable(reason) =
        x86_rosetta_support::x86_execution(OPTS[0])
    {
        panic!(
            "x86-64 coverage rows: this Apple-silicon host has no x86-64 execution route: {reason}"
        );
    }
    coverage_rows(Target::X86_64, loop_coverage::X86_64_CONTROLS);
}

/// UB-free raw pointers: the loop's trip bound is 1000 but its `break` stops it
/// at 64, the end of a 64-byte buffer a 1024-byte canary follows. Exit 10 means
/// the call returned 64 with the canary intact.
const RAW_CANARY: &str = r#"#![no_std]
#![no_main]
extern "C" {
    fn abort() -> !;
}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe { abort() }
}
#[repr(C)]
struct S {
    buf: [u8; 64],
    canary: [u8; 1024],
}
static mut G: S = S { buf: [0; 64], canary: [0x55; 1024] };

#[inline(never)]
unsafe fn fill_raw(p: *mut u8, cap: usize, stop: usize) -> usize {
    let mut i = 0;
    while i < cap {
        if i == stop {
            break;
        }
        unsafe { *p.add(i) = 7 };
        i += 1;
    }
    i
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let cap = core::hint::black_box(1000);
    let stop = core::hint::black_box(64);
    let p = unsafe { core::ptr::addr_of_mut!(G.buf) } as *mut u8;
    let i = unsafe { fill_raw(p, cap, stop) };
    let canary = unsafe { &*core::ptr::addr_of!(G.canary) };
    let mut clobbered = 0usize;
    let mut k = 0;
    while k < 1024 {
        if canary[k] != 0x55 {
            clobbered += 1;
        }
        k += 1;
    }
    if clobbered == 0 && i == 64 { 10 } else { 20 + (clobbered / 16) as i32 + (i != 64) as i32 }
}
"#;

/// Safe Rust whose loop bound exceeds its 64-byte slice, a 1024-byte canary
/// right after it: the bounds check must panic at the first index past the
/// slice, before anything past it is written. The panic hook exits `100 +
/// (changed canary bytes) / 8`. `{LOOP}` is the loop.
const SLICE_CANARY: &str = r#"#[repr(C)]
struct S {
    buf: [u8; 64],
    canary: [u8; 1024],
}
static mut G: S = S { buf: [0; 64], canary: [0x55; 1024] };

#[inline(never)]
fn kernel(a: &mut [u8], n: usize) {
    {LOOP}
}

fn hook(_: &std::panic::PanicHookInfo<'_>) {
    let canary = unsafe { &*core::ptr::addr_of!(G.canary) };
    let mut clobbered = 0usize;
    let mut k = 0;
    while k < 1024 {
        if canary[k] != 0x55 {
            clobbered += 1;
        }
        k += 1;
    }
    std::process::exit((clobbered / 8) as i32 + 100);
}

fn main() {
    std::panic::set_hook(Box::new(hook));
    let n = std::hint::black_box(1000);
    let buf = unsafe { &mut *core::ptr::addr_of_mut!(G.buf) };
    kernel(&mut buf[..], n);
    std::process::exit(0);
}
"#;

/// The loops [`SLICE_CANARY`] runs: a unit-stride fill (`neon_fill`) and a
/// stride-3 marking loop under a constant bound (`strided_store_unroll`).
const SLICE_LOOPS: &[(&str, &str)] = &[
    (
        "fill_past_slice",
        "let mut i = 0; while i < n { a[i] = 7; i += 1; }",
    ),
    (
        "strided_past_slice",
        "let p = std::hint::black_box(3usize); let mut q = 0usize; \
         while q < 1024 { a[q] = 1; q += p; } let _ = n;",
    ),
];

/// A pre-loop rewrite must not run past an exit its scalar loop would have
/// taken: a `break` (raw pointers) or a bounds-check panic (safe Rust over a
/// slice shorter than the loop bound, with `std`, whose panic hook observes
/// the memory written before it). These are the aarch64 rows; the x86-64
/// `break` rows are [`x86_64_pre_loop_rewrites_never_run_past_an_exit`], so a
/// host without an x86-64 route still runs these.
///
/// Measured 2026-09-30 with the loop-state contract's register clause alone
/// (`neon_fill` and `strided_store_unroll` deciding exits privately), and the
/// same at `c84d39e93`: the raw row exited 79 on aarch64 at O2 and O3 (928 to
/// 943 canary bytes written, the call returned 1000), the fill row 212 (896 to
/// 903 bytes), and the strided row died of SIGSEGV (139) at O2 and O3, where
/// LLVM exits 10, 100 and 100. With the contract's control clause every row
/// agrees. x86-64 was already right.
#[test]
fn pre_loop_rewrites_never_run_past_an_exit() {
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let bridge = Bridge {
        dylib: &dylib,
        knobs: &knobs,
    };
    let mut failures = raw_canary_rows(Target::Aarch64, bridge);
    for &(name, body) in SLICE_LOOPS {
        let src = SLICE_CANARY.replace("{LOOP}", body);
        for &opt in OPTS {
            let dir = workdir(&format!("{name}_O{opt}"));
            let unwind = |backend| {
                compile_with_panic(
                    &dir,
                    name,
                    &src,
                    Target::Aarch64,
                    opt,
                    backend,
                    false,
                    "unwind",
                )
            };
            let oracle =
                unwind(None).unwrap_or_else(|e| panic!("{name} O{opt}: LLVM failed:\n{e}"));
            let label = format!("{name} aarch64 O{opt}");
            match unwind(Some(bridge)) {
                Ok(built) => failures.extend(exit_mismatch(
                    label,
                    run(&oracle, Target::Aarch64, opt).0,
                    run(&built, Target::Aarch64, opt).0,
                    100,
                )),
                Err(e) => failures.push(format!("{label}: the bridge failed:\n{e}")),
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    assert!(
        failures.is_empty(),
        "{} early-exit row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The raw-pointer `break` rows of
/// [`pre_loop_rewrites_never_run_past_an_exit`] on x86-64, under Rosetta.
#[test]
fn x86_64_pre_loop_rewrites_never_run_past_an_exit() {
    if let x86_rosetta_support::X86Exec::Unavailable(reason) =
        x86_rosetta_support::x86_execution(OPTS[0])
    {
        panic!("x86-64 rows: this Apple-silicon host has no x86-64 execution route: {reason}");
    }
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let failures = raw_canary_rows(
        Target::X86_64,
        Bridge {
            dylib: &dylib,
            knobs: &knobs,
        },
    );
    assert!(
        failures.is_empty(),
        "{} early-exit row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The raw-pointer `break` canary on `target` at every level, bridge against
/// LLVM; each failure is one line.
fn raw_canary_rows(target: Target, bridge: Bridge) -> Vec<String> {
    let mut failures = Vec::new();
    for &opt in OPTS {
        let dir = workdir(&format!("raw_canary_{target:?}_O{opt}"));
        let oracle = compile(&dir, "raw_canary", RAW_CANARY, target, opt, None, true)
            .unwrap_or_else(|e| panic!("raw canary {target:?} O{opt}: LLVM failed:\n{e}"));
        let label = format!("raw canary {target:?} O{opt}");
        match compile(
            &dir,
            "raw_canary",
            RAW_CANARY,
            target,
            opt,
            Some(bridge),
            true,
        ) {
            Ok(built) => failures.extend(exit_mismatch(
                label,
                run(&oracle, target, opt).0,
                run(&built, target, opt).0,
                10,
            )),
            Err(e) => failures.push(format!("{label}: the bridge failed:\n{e}")),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    failures
}

/// A row's failure when the LLVM oracle did not exit `want`, or the bridge's
/// exit differs from the oracle's.
fn exit_mismatch(
    label: String,
    oracle: Option<i32>,
    got: Option<i32>,
    want: i32,
) -> Option<String> {
    eprintln!("{label}: exit llvm={oracle:?} tcg={got:?}");
    if oracle != Some(want) {
        Some(format!(
            "{label}: the LLVM oracle exited {oracle:?}, not {want}"
        ))
    } else if got != oracle {
        Some(format!("{label}: WRONG exit {got:?}, LLVM {oracle:?}"))
    } else {
        None
    }
}

/// The beat-llvm programs the two aarch64 NEON passes exist for keep their
/// NEON code in `main` and agree with LLVM: the gate must not buy the rows
/// above by vectorizing nothing.
#[test]
fn aarch64_benchmark_loops_stay_vectorized() {
    darwin_native::require("opt_loop_state_run benchmarks", &["objdump"]);
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let bridge = Bridge {
        dylib: &dylib,
        knobs: &knobs,
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/beat-llvm/progs");
    let programs: Vec<(&str, String)> = ["p7_sieve", "v3_popcount"]
        .into_iter()
        .map(|program| {
            let src = std::fs::read_to_string(root.join(format!("{program}.rs")))
                .unwrap_or_else(|e| panic!("read {program}.rs: {e}"));
            (program, src)
        })
        .collect();
    let mut failures = Vec::new();
    for (program, src) in &programs {
        for &opt in OPTS {
            let dir = workdir(&format!("{program}_O{opt}"));
            let oracle = compile(&dir, program, src, Target::Aarch64, opt, None, false)
                .unwrap_or_else(|e| panic!("{program} O{opt}: LLVM failed:\n{e}"));
            let built = match compile(
                &dir,
                program,
                src,
                Target::Aarch64,
                opt,
                Some(bridge),
                false,
            ) {
                Ok(bin) => bin,
                Err(e) => {
                    failures.push(format!("{program} O{opt}: bridge failed:\n{e}"));
                    continue;
                }
            };
            let (expected, _) = run(&oracle, Target::Aarch64, opt);
            let (got, _) = run(&built, Target::Aarch64, opt);
            let Some(asm) = disassembly_of(&built, "4main") else {
                failures.push(format!(
                    "{program} O{opt}: no `main` symbol in the bridge binary"
                ));
                continue;
            };
            let ops = vector_ops(&asm, Target::Aarch64);
            eprintln!(
                "{program} O{opt}: exit llvm={expected:?} tcg={got:?}, main vector ops {ops}"
            );
            if got != expected {
                failures.push(format!("{program} O{opt}: exit {got:?}, LLVM {expected:?}"));
            }
            if ops == 0 {
                failures.push(format!("{program} O{opt}: main lost its NEON code"));
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    assert!(
        failures.is_empty(),
        "{} benchmark row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The kernels of [`constant_bound_program`]: `(name, element, accumulator,
/// initial element, loop body over a, acc, i)`, in the shapes of the AArch64
/// NEON fill, byte-sum, count-if and i32-sum loops. Measured 2026-10-01 at
/// O2 and O3: the proven fill and i32-sum rows vectorize (`neon_fill`,
/// `neon_array`); the byte-sum and count-if rows stay scalar in this program
/// (no `neon_bytesum` code), so they check the fold alone.
const CHECK_KERNELS: &[(&str, &str, &str, &str, &str)] = &[
    ("fill", "u8", "u64", "0", "a[i] = 7;"),
    ("bsum", "u8", "u64", "3", "acc += a[i] as u64;"),
    ("count", "u8", "u64", "0", "if a[i] == 0 { acc += 1; }"),
    ("isum", "i32", "i32", "5", "acc = acc.wrapping_add(a[i]);"),
];

/// `(N, L, start)`: `while i < N { .. a[i] .. }` from `i = start` over a
/// `[_; L]` array that a 64-byte canary follows. `N <= L` never panics, and
/// the guard's constant proves the check; `N > L` must panic exactly where
/// the scalar loop does: at the FIRST iteration (`start = L`), in the MIDDLE
/// (`L = N / 2`), at the LAST (`L = N - 1`), after exactly the writes before
/// it.
const CHECK_ROWS: &[(usize, usize, usize)] = &[
    (1024, 1024, 0),
    (1000, 1024, 0),
    (1024, 512, 512),
    (1024, 512, 0),
    (1024, 1023, 0),
];

/// One `std` program holding every (kernel, row), the row chosen at run time
/// by `CB_ROW` (libc `getenv`: the bridge refuses `std::env::args`' `OsString`
/// drop glue). `CB_ROW = r` installs a hook that prints the row's observable
/// memory (array elements written, canary bytes clobbered) and the panic's
/// line and column; `r + 1000` keeps std's default hook, whose stderr carries
/// the panic message with the index and the length. Returns the source and the
/// row count.
fn constant_bound_program() -> (String, usize) {
    let mut src = String::from(
        "use std::hint::black_box;\n\
         use std::sync::atomic::{AtomicUsize, Ordering};\n\
         static ROW: AtomicUsize = AtomicUsize::new(usize::MAX);\n",
    );
    let mut state_arms = String::new();
    let mut run_arms = String::new();
    let mut row = 0usize;
    for &(name, elem, acc, init, body) in CHECK_KERNELS {
        src.push_str(&format!(
            "#[inline(never)]\n\
             fn {name}<const N: usize, const L: usize>(a: &mut [{elem}; L], start: usize) -> u64 {{\n\
             \x20   let mut acc: {acc} = 0;\n    let mut i = start;\n\
             \x20   while i < N {{ {body} i += 1; }}\n\
             \x20   let _ = &mut acc;\n    acc as u64\n}}\n"
        ));
        for &(n, l, start) in CHECK_ROWS {
            src.push_str(&format!(
                "#[repr(C)]\nstruct S{row} {{ buf: [{elem}; {l}], canary: [u8; 64] }}\n\
                 static mut G{row}: S{row} = S{row} {{ buf: [{init}; {l}], canary: [0x55; 64] }};\n"
            ));
            state_arms.push_str(&format!(
                "        {row} => {{ let g = &*core::ptr::addr_of!(G{row}); \
                 let (mut w, mut c, mut k) = (0usize, 0usize, 0usize); \
                 while k < {l} {{ if g.buf[k] == 7 {{ w += 1; }} k += 1; }} \
                 k = 0; while k < 64 {{ if g.canary[k] != 0x55 {{ c += 1; }} k += 1; }} (w, c) }}\n"
            ));
            run_arms.push_str(&format!(
                "        {row} => {name}::<{n}, {l}>(&mut *core::ptr::addr_of_mut!(G{row}.buf), black_box({start})),\n"
            ));
            row += 1;
        }
    }
    src.push_str(&format!(
        "fn state(row: usize) -> (usize, usize) {{\n    unsafe {{ match row {{\n{state_arms}\
         \x20       _ => (usize::MAX, usize::MAX),\n    }} }}\n}}\n\
         fn run(row: usize) -> u64 {{\n    unsafe {{ match row {{\n{run_arms}\
         \x20       _ => 0,\n    }} }}\n}}\n"
    ));
    src.push_str(
        "extern \"C\" {\n    fn getenv(name: *const u8) -> *const u8;\n}\n\
         fn row_from_env() -> usize {\n\
         \x20   let p = unsafe { getenv(b\"CB_ROW\\0\".as_ptr()) };\n\
         \x20   if p.is_null() { return 0; }\n\
         \x20   let (mut v, mut k) = (0usize, 0usize);\n\
         \x20   loop {\n\
         \x20       let c = unsafe { *p.add(k) };\n\
         \x20       if c < b'0' || c > b'9' { break; }\n\
         \x20       v = v * 10 + (c - b'0') as usize;\n\
         \x20       k += 1;\n\
         \x20   }\n\
         \x20   v\n}\n\
         fn main() {\n\
         \x20   let row = row_from_env();\n\
         \x20   if row < 1000 {\n\
         \x20       std::panic::set_hook(Box::new(|info| {\n\
         \x20           let row = ROW.load(Ordering::SeqCst);\n\
         \x20           let (w, c) = state(row);\n\
         \x20           let (line, col) = match info.location() { Some(l) => (l.line(), l.column()), None => (0, 0) };\n\
         \x20           println!(\"hook row={row} written={w} canary={c} at {line}:{col}\");\n\
         \x20       }));\n\
         \x20   }\n\
         \x20   let row = row % 1000;\n\
         \x20   ROW.store(row, Ordering::SeqCst);\n\
         \x20   go(black_box(row));\n}\n\
         #[inline(never)]\n\
         fn go(row: usize) {\n\
         \x20   let v = run(row);\n\
         \x20   let (w, c) = state(row);\n\
         \x20   println!(\"done row={row} value={v} written={w} canary={c}\");\n}\n",
    );
    (src, row)
}

/// The AArch64 bounds-check eliminator folds an explicit check against a
/// CONSTANT bound when a dominating unsigned guard against a constant proves
/// it (`while i < N { .. a[i] .. }` over `[_; N]`), which is what lets the NEON
/// passes vectorize the loop again. A check the guard does NOT prove must keep
/// panicking exactly where LLVM's binary does, with the same writes before it,
/// under `panic=abort` and `panic=unwind`, at O2 and O3: every row's exit
/// status, stdout and stderr (std's default hook prints the index and length)
/// must equal LLVM's, and each row is first held to its intent on the oracle.
/// The proven rows must leave NEON code in the bridge binary, so the
/// comparison is not won by folding nothing.
///
/// Mutant, measured 2026-10-01: with the eliminator's implication (`K' <= K`,
/// `K' < K`) forced true, the `N > L` rows lost their check and this test
/// failed 96 of its 160 row runs, every run of an `N > L` row: exit 0 with no
/// panic, the fill rows having written past the array into the canary (all 64
/// bytes at `L = 512`), the read rows having returned sums read past it.
/// Before the constant-bound rule existed the program had no NEON code in
/// its own functions (0 vector instructions at O2 and O3); with it, 32.
#[test]
fn aarch64_constant_bound_checks_panic_where_the_scalar_loop_does() {
    darwin_native::require("opt_loop_state_run constant-bound checks", &["objdump"]);
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let bridge = Bridge {
        dylib: &dylib,
        knobs: &knobs,
    };
    let (src, rows) = constant_bound_program();
    let normalize = |stderr: &[u8]| {
        // std names the thread with its OS id: `thread 'main' (12345) panicked`.
        let text = String::from_utf8_lossy(stderr).into_owned();
        match (text.find("thread 'main' ("), text.find(") panicked")) {
            (Some(open), Some(close)) if open < close => {
                format!("{}thread 'main'{}", &text[..open], &text[close + 1..])
            }
            _ => text,
        }
    };
    let run_row = |bin: &Path, row: usize| {
        let output = std::process::Command::new(bin)
            .env("CB_ROW", row.to_string())
            .output()
            .expect("run the program");
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            normalize(&output.stderr),
        )
    };
    let mut failures = Vec::new();
    let mut compared = 0usize;
    for panic in ["abort", "unwind"] {
        for &opt in OPTS {
            let dir = workdir(&format!("cbchk_{panic}_O{opt}"));
            let build = |backend| {
                compile_with_panic(
                    &dir,
                    "cbchk",
                    &src,
                    Target::Aarch64,
                    opt,
                    backend,
                    false,
                    panic,
                )
            };
            let oracle =
                build(None).unwrap_or_else(|e| panic!("cbchk {panic} O{opt}: LLVM failed:\n{e}"));
            let built = match build(Some(bridge)) {
                Ok(bin) => bin,
                Err(e) => {
                    failures.push(format!("cbchk {panic} O{opt}: the bridge failed:\n{e}"));
                    continue;
                }
            };
            for row in 0..rows {
                let (n, l, _) = CHECK_ROWS[row % CHECK_ROWS.len()];
                let panics = n > l;
                for hook in [0, 1000] {
                    let label = format!("cbchk {panic} O{opt} row {row} hook {hook}");
                    let want = run_row(&oracle, row + hook);
                    let oracle_ok = if panics {
                        want.0 != Some(0)
                            && (hook != 0 || want.1.starts_with(&format!("hook row={row} ")))
                            && (hook == 0 || want.2.contains("index out of bounds"))
                    } else {
                        want.0 == Some(0) && want.1.starts_with(&format!("done row={row} "))
                    };
                    if !oracle_ok {
                        failures.push(format!(
                            "{label}: the LLVM oracle does not show the row's intent: {want:?}"
                        ));
                        continue;
                    }
                    let got = run_row(&built, row + hook);
                    compared += 1;
                    if got != want {
                        failures.push(format!("{label}: WRONG {got:?}, LLVM {want:?}"));
                    }
                }
            }
            match disassembly_of(&built, "5cbchk") {
                Some(asm) => {
                    let ops = vector_ops(&asm, Target::Aarch64);
                    eprintln!("cbchk {panic} O{opt}: crate-local vector ops {ops}");
                    if ops == 0 {
                        failures.push(format!(
                            "cbchk {panic} O{opt}: no NEON code: the proven rows were not vectorized"
                        ));
                    }
                }
                None => failures.push(format!("cbchk {panic} O{opt}: no crate symbol")),
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    eprintln!("cbchk: {compared} row runs compared against LLVM");
    assert!(
        failures.is_empty(),
        "{} constant-bound row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The corpus rows the bridge refuses BY NAME today with proofs off: (guest,
/// opt level, the diagnostic it must still print). Shrink-only: a listed row
/// that compiles fails the test until its line is deleted, and a refusal not
/// listed here fails it too. Empty since 2026-10-03: the last rows,
/// `p13_sort_std` at O2 and O3 (measured 2026-09-30 at trust-cg `c84d39e93`),
/// were `core::slice::sort`'s `&raw (*v)[k of n]` borrows (`heapsort`,
/// `find_existing_run`), which the bridge now addresses as `data + k * stride`;
/// every row links, runs and agrees with LLVM.
const CORPUS_REFUSALS: &[(&str, &str, &str)] = &[];

/// The shared real-program corpus (`real_program_corpus/corpus_guests.rs`,
/// the same 13 guests the x86 and aarch64 corpus rows compile), compiled
/// whole by LLVM and by the bridge at O0, O2 and O3, linked and run: every
/// bridge binary must exit as LLVM's does.
#[test]
fn aarch64_real_program_corpus_runs_agree_with_llvm() {
    darwin_native::require("opt_loop_state_run corpus", &[]);
    let dylib = backend_artifact_support::current_test_backend();
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let bridge = Bridge {
        dylib: &dylib,
        knobs: &knobs,
    };
    let guests = corpus();
    let mut failures = Vec::new();
    let mut agreed = 0usize;
    let mut refused = 0usize;
    for guest in &guests {
        for opt in ["0", "2", "3"] {
            let dir = workdir(&format!("corpus_{}_O{opt}", guest.name));
            let listed = CORPUS_REFUSALS
                .iter()
                .find(|(name, level, _)| *name == guest.name && *level == opt);
            let oracle = compile(
                &dir,
                guest.name,
                guest.src,
                Target::Aarch64,
                opt,
                None,
                false,
            )
            .unwrap_or_else(|e| panic!("{} O{opt}: LLVM failed:\n{e}", guest.name));
            match compile(
                &dir,
                guest.name,
                guest.src,
                Target::Aarch64,
                opt,
                Some(bridge),
                false,
            ) {
                Ok(built) => {
                    if let Some((_, _, code)) = listed {
                        failures.push(format!(
                            "{} O{opt}: compiles now; delete its CORPUS_REFUSALS row ({code})",
                            guest.name
                        ));
                    }
                    let (expected, _) = run(&oracle, Target::Aarch64, opt);
                    let (got, _) = run(&built, Target::Aarch64, opt);
                    eprintln!("{} O{opt}: exit llvm={expected:?} tcg={got:?}", guest.name);
                    if got == expected {
                        agreed += 1;
                    } else {
                        failures.push(format!(
                            "{} O{opt} ({}): WRONG exit {got:?}, LLVM {expected:?}",
                            guest.name, guest.what
                        ));
                    }
                }
                Err(stderr) => match listed {
                    Some((_, _, code)) if stderr.contains(code) => {
                        eprintln!("{} O{opt}: refused by name ({code})", guest.name);
                        refused += 1;
                    }
                    _ => failures.push(format!(
                        "{} O{opt}: the bridge refused:\n{stderr}",
                        guest.name
                    )),
                },
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    eprintln!(
        "corpus: {agreed} of {} rows agree with LLVM, {refused} refused by name",
        guests.len() * 3
    );
    assert!(
        failures.is_empty(),
        "{} corpus row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
