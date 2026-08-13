// Integration test: CLOSURE environment captures of upvars with DIFFERING
// alignment, compiled for x86_64 via the rustc_codegen_trust_cg bridge —
// COMPILED, LINKED, and RUN at BOTH `-Copt-level=0` and `-Copt-level=3`, with
// exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Regression for bug #54: a closure capturing upvars of DIFFERING alignment
// (e.g. a `u8` and a `u32`) read them from the WRONG offsets. rustc lays out the
// closure environment with ALIGNMENT-DRIVEN field reordering (the `u32` lands at
// offset 0, the `u8` at offset 4), and the env-construct side stored the upvars
// at those real layout offsets. But the closure BODY read each upvar `(*env).N`
// through the scalarized `aggregate_field_memory_access` ExtractField path, whose
// declaration-ORDER trust-ir tuple layout (u8@0, u32@4) disagreed — so `a` read
// `b`'s low byte and vice versa.
//
// The fix routes a `&closure` upvar read through the byte-offset addressing path
// (rustc `layout_of` offsets), matching the construct side exactly. These
// programs are differential against LLVM at both opt levels; at O3 the closure is
// fully inlined/folded (so it accidentally matched before), so O0 is the
// load-bearing check and O3 guards the inlined path.

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
    assert!(status.success(), "cargo build failed; cannot run closure-capture test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_closcap_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
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
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend, -Copt-level={opt}). stderr: <<<{}>>>",
        if backend.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr),
    );
    bin
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The full differential: each closure-capture `fn main` is compiled by trust-cg
/// AND LLVM at `-Copt-level=0` and `-Copt-level=3`, run, and the exit codes must
/// match each other and the expected value.
#[test]
fn closure_differing_alignment_captures_run_and_match_llvm() {
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

    // (name, source, expected exit code). Each captures upvars of DIFFERING
    // alignment, so rustc reorders the closure env fields and the body must read
    // each upvar at its real layout offset.
    let shapes: &[(&str, &str, i32)] = &[
        // The keystone: capture a u8 and a u32 by move; compute a*10+b.
        (
            "u8_u32_nullary",
            "fn main(){ let a: u8 = 3; let b: u32 = 5; \
             let g = move || (a as u32) * 10 + b; \
             std::process::exit((g() & 0xFF) as i32); }",
            35,
        ),
        // A captured u8 and i16 with a closure ARGUMENT: (x+a)*b.
        (
            "u8_i16_arg",
            "fn main(){ let a: u8 = 3; let b: i16 = 5; \
             let g = move |x: u32| x.wrapping_add(a as u32).wrapping_mul(b as u32); \
             let r = g(2); std::process::exit((r & 0xFF) as i32); }",
            25,
        ),
        // A high-alignment pad upvar (i16) masked to 0, so only `a` (u8) matters —
        // confirms the body reads `a` from its real offset, not the pad's slot.
        (
            "u8_i16_pad",
            "fn main(){ let a: u8 = 7; let pad: i16 = 999; \
             let g = move |x: u32| x.wrapping_add(a as u32).wrapping_add((pad as i32 as u32) & 0); \
             let r = g(0); std::process::exit((r & 0xFF) as i32); }",
            7,
        ),
        // Three upvars of mixed alignment (u8, u64, u16): every offset must line up.
        (
            "u8_u64_u16",
            "fn main(){ let a: u8 = 1; let b: u64 = 2; let c: u16 = 3; \
             let g = move || (a as u64) + b * 10 + (c as u64) * 100; \
             std::process::exit((g() & 0xFF) as i32); }",
            // 1 + 2*10 + 3*100 = 321; 321 & 0xFF = 65
            65,
        ),
        // Reverse declaration order (wide first, narrow last) — rustc still places
        // by alignment, so the body offsets must be layout-driven either way.
        (
            "u64_u8",
            "fn main(){ let big: u64 = 1000; let small: u8 = 7; \
             let g = move || big.wrapping_add(small as u64); \
             std::process::exit((g() & 0xFF) as i32); }",
            // 1007 & 0xFF = 239
            239,
        ),
    ];

    for opt in ["0", "3"] {
        for (name, src, expected) in shapes {
            let llvm_bin = compile(&dir, &format!("{name}_llvm_o{opt}"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_tcg_o{opt}"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` (-Copt-level={opt}) was {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit for `{name}` (-Copt-level={opt}) was {tcg_exit}, LLVM was {llvm_exit}"
            );
        }
    }
}

/// Regression for bug #54 (BY-REFERENCE captures): a closure capturing an upvar
/// BY REFERENCE (a `&T` / `&mut T` whose env field is a POINTER to the captured
/// local) read the WRONG location. The env correctly held the pointer, but the
/// captured LOCAL's value was never stored into its address-taken "cell" on the
/// call/cast/binary-op definition paths (only on a whole-local statement assign),
/// so the closure dereferenced the cell pointer and read uninitialized memory.
/// The fix stores a scalar-cell local's value through every definition form
/// (`finish_assign_target`), so a by-ref upvar reads the live value.
///
/// Covers single/multi/mixed-alignment, `Fn` and `FnMut`, and a generic-fn
/// boundary (`call_it<F: Fn()>` / `run<F: FnMut()>`, which forces the closure to
/// be passed by value with its by-ref pointers intact). Differential vs LLVM at
/// BOTH opt levels: O0 exercises the by-ref read directly; O3 (where the closure
/// inlines and the by-ref loop carries the result through a header phi) guards the
/// loop-liveness and wide-switch-constant paths the same fix touched.
#[test]
fn closure_by_reference_captures_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("byref");

    let shapes: &[(&str, &str, i32)] = &[
        // (a) Single by-ref u64 capture, direct `Fn` call.
        (
            "single_u64_byref",
            "fn main(){ let b:u64=std::hint::black_box(42); let f=|| b; \
             std::process::exit(f() as i32); }",
            42,
        ),
        // (b) Mixed-alignment u8 + u64 by-ref behind a generic `Fn` boundary.
        (
            "u8_u64_byref_generic",
            "#[inline(never)] fn call_it<F:Fn()->u64>(f:F)->u64 { f() } \
             fn main(){ let a:u8=std::hint::black_box(0xAB); \
             let b:u64=std::hint::black_box(0x0123456789ABCDEF); \
             let f=|| (a as u64).wrapping_add(b); \
             let r=call_it(f); std::process::exit((r & 0xFF) as i32); }",
            // (0xEF + 0xAB) & 0xFF = 0x9A = 154
            154,
        ),
        // (c) FnMut by-ref over a u8 counter + u64 accumulator across a generic
        // boundary with a loop (exercises the loop-carried-result header phi).
        (
            "fnmut_u8_u64_byref_loop",
            "#[inline(never)] fn run<F:FnMut()->u64>(mut f:F)->u64 \
             { let mut s=0u64; for _ in 0..3 { s=f(); } s } \
             fn main(){ let mut cnt:u8=std::hint::black_box(0u8); \
             let mut acc:u64=std::hint::black_box(0u64); \
             let f=|| { cnt=cnt.wrapping_add(1); acc=acc.wrapping_add(20); \
             (cnt as u64).wrapping_add(acc) }; \
             let r=run(f); std::process::exit((r & 0xFF) as i32); }",
            // after 3 iters: cnt=3, acc=60, 3+60 = 63
            63,
        ),
        // (d) bool + i64 by-ref (mixed align, negative value -> wide switch const).
        (
            "bool_i64_byref",
            "fn main(){ let flag=std::hint::black_box(true); \
             let v:i64=std::hint::black_box(-0x0102030405060708); \
             let f=|| if flag {v} else {0}; \
             std::process::exit((f() & 0xFF) as i32); }",
            // (-0x0102030405060708) & 0xFF = 0xF8 = 248
            248,
        ),
        // Multi-capture by-ref `Fn` (u8 + u64 + u16), direct call.
        (
            "triple_byref_direct",
            "fn main(){ let a:u8=std::hint::black_box(0xAB); \
             let b:u64=std::hint::black_box(0x0102030405060708); \
             let c:u16=std::hint::black_box(0x1234); \
             let f=|| (a as u64).wrapping_add(b).wrapping_add(c as u64); \
             std::process::exit((f() & 0xFF) as i32); }",
            // (0xAB + 0x08 + 0x34) & 0xFF = 0xE7 = 231
            231,
        ),
        // FnMut by-ref, single u64, direct (unrolled) calls.
        (
            "fnmut_single_byref_direct",
            "fn main(){ let mut x:u64=std::hint::black_box(10); \
             let mut f=|| { x=x.wrapping_add(5); x }; \
             let _=f(); let _=f(); let r=f(); \
             std::process::exit((r & 0xFF) as i32); }",
            25,
        ),
    ];

    for opt in ["0", "3"] {
        for (name, src, expected) in shapes {
            let llvm_bin = compile(&dir, &format!("{name}_llvm_o{opt}"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_tcg_o{opt}"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` (-Copt-level={opt}) was {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit for `{name}` (-Copt-level={opt}) was {tcg_exit}, LLVM was {llvm_exit}"
            );
        }
    }
}

/// Regression for bug #56: a NESTED by-move closure whose inner body uses a std
/// arithmetic method (`u64::wrapping_shl`) emitted an UNDEFINED external symbol,
/// yielding an unlinkable binary. The inner closure body referenced `wrapping_shl`
/// as an external symbol, but `wrapping_shl`'s own body failed to lower (it uses
/// `Operand::RuntimeChecks(UbChecks)` and a divering `precondition_check` panic
/// block built from `&raw const` / fat-pointer `Transmute` rvalues) and was
/// SILENTLY DROPPED as "unreachable" — leaving the symbol undefined.
///
/// The fix (1) resolves `Operand::RuntimeChecks` to its compile-time boolean
/// (so the precondition branch folds) and (2) traps a diverging panic block whole
/// rather than failing to lower it, so the reachable std helper is emitted. A
/// reachable function is now NEVER silently skipped. Differential vs LLVM at both
/// opt levels (O0 was the link error; O3 exercises the fully-inlined wide-switch
/// comparison against the expected sum).
#[test]
fn nested_by_move_closure_wrapping_shl_links_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("nested");

    let shapes: &[(&str, &str, i32)] = &[
        // The keystone #56 repro: outer u64 by-move + nested closure capturing an
        // inner u8 by-move, whose body calls `u64::wrapping_shl`.
        (
            "nested_wrapping_shl",
            "fn main(){ let outer:u64=std::hint::black_box(0x77778888_9999AAAA); \
             let inner:u8=std::hint::black_box(0x5A); \
             let f = move || -> u64 { \
                 let g = move || -> u64 { (inner as u64).wrapping_shl(8) }; \
                 outer.wrapping_add(g()) }; \
             std::process::exit(if f()==(0x77778888_9999AAAAu64)\
                 .wrapping_add((0x5Au64)<<8) {31} else {107}); }",
            31,
        ),
        // A single `wrapping_shl` whose result is compared against a wide (>i32)
        // 64-bit constant via a `switchInt(u64)` at O3 — guards the wide-switch
        // case-value materialization (must compare the full 64-bit pattern).
        (
            "wrapping_shl_wide_switch",
            "fn main(){ let inner:u8 = std::hint::black_box(90u8); \
             let outer:u64 = std::hint::black_box(0x77778888_9999AAAAu64); \
             let v = outer.wrapping_add((inner as u64).wrapping_shl(8)); \
             let expected = 0x77778888_9999AAAAu64.wrapping_add(90u64<<8); \
             std::process::exit(if v == expected {31} else {107}); }",
            31,
        ),
        // A switch on a u64 with the HIGH bit set (case value outside i64 range)
        // must reinterpret to the i64 bit pattern, not be rejected/truncated.
        (
            "high_bit_switch_const",
            "fn main(){ let v:u64 = std::hint::black_box(0xFFFFFFFF_00000000u64); \
             std::process::exit(if v == 0xFFFFFFFF_00000000u64 {31} else {107}); }",
            31,
        ),
    ];

    for opt in ["0", "3"] {
        for (name, src, expected) in shapes {
            let llvm_bin = compile(&dir, &format!("{name}_llvm_o{opt}"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_tcg_o{opt}"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` (-Copt-level={opt}) was {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit for `{name}` (-Copt-level={opt}) was {tcg_exit}, LLVM was {llvm_exit}"
            );
        }
    }
}
