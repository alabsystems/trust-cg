#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: `RangeInclusive` (`a..=b` / `1..=n`) as a `for`-loop source
// AND an iterator-chain source, compiled for x86_64 via the
// rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS — `RangeInclusive<scalar int>` (`start..=end`) support.
//
// A `RangeInclusive<T>` is a THREE-field struct `{ start, end, exhausted: bool }`
// (unlike a `Range<T>`'s two fields). Its iteration yields `start..=end`
// INCLUSIVELY: the final element `end` is produced exactly once, even at
// `end == T::MAX` (the `exhausted` flag is what avoids the `MAX + 1` overflow).
//
// A `for i in a..=b { .. }` desugars (at -O0) to
//
//     let mut it = IntoIterator::into_iter(RangeInclusive::new(a, b));
//     loop { match Iterator::next(&mut it) { Some(i) => body, None => break } }
//
// and at -O3 to an inlined `RangeInclusive { start, end, exhausted: false }`
// aggregate + a copy + `RangeInclusiveIteratorImpl::spec_next`. The bridge
// intercepts all of these (`RangeInclusive::new`, `into_iter`, `next`/`spec_next`)
// and synthesizes them BRANCHLESSLY against a memory-backed 3-field slot, with
// the std `spec_next` semantics:
//
//     if exhausted || !(start <= end) { None }
//     else { let v = start;
//            if start < end { start += 1 } else { exhausted = true }
//            Some(v) }
//
// The `start += 1` is computed unconditionally but DISCARDED (via `Select`) when
// `start == end`, so it never traps at `start == end == T::MAX`. The same source
// logic drives the iterator-chain path (`emit_source_next`), so `(a..=b).sum()`,
// `.map(..).sum()`, `.filter(..).count()`, and `(a..=b).collect::<Vec<_>>()`
// compose with the existing adapter chain.
//
// SCOPE: a `RangeInclusive<T>` for a scalar INTEGER index `T` (signed / unsigned,
// runtime bounds). A non-integer / char range, or `.rev()` over a
// `RangeInclusive` (a backward walk with its own exhausted bookkeeping), is NOT
// modeled and fails closed (no binary, never a wrong value).
//
// Each program is compiled with BOTH backends and run at -O0 AND -O3; the
// trust-cg exit code must equal the LLVM exit code (and the expected value). The
// inclusive FINAL element and the `T::MAX` boundary (`1u8..=255`) are the
// critical correctness points an off-by-one would diverge on.

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
    assert!(
        status.success(),
        "cargo build failed; cannot run range-inclusive test"
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
    let dir = std::env::temp_dir().join(format!("rcl2_m105_{stem}_{}", std::process::id()));
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
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    (output, bin)
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
    let (output, bin) = try_compile(dir, name, src, backend, opt);
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend, -Copt-level={opt}). stderr: <<<{}>>>",
        if backend.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr)
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

/// The full differential: each inclusive-range program is compiled by trust-cg
/// AND LLVM, run at -O0 AND -O3, and the exit codes must match each other and the
/// expected value. An off-by-one (the inclusive final element) or a `T::MAX`
/// boundary wrap would diverge from LLVM, so equal exit codes are the assertion.
#[test]
fn range_inclusive_programs_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("run");

    // `black_box` keeps the bound RUNTIME (not const-folded), so the real
    // inclusive iteration / chain runs. (name, source, expected exit code). These
    // all run AND MATCH LLVM at BOTH -O0 and -O3 (the `for`-loop desugar at -O0 is
    // `new` + `into_iter` + `next`; at -O3 it is an inlined aggregate + a copy +
    // `spec_next` — both intercepted).
    let bb = "std::hint::black_box";
    let shapes: Vec<(&str, String, i32)> = vec![
        // `for i in 1..=n { s += i }` == n(n+1)/2 == 15 for n = 5.
        (
            "forloop_sum",
            format!("fn main(){{let mut s=0i64; for i in 1..={bb}(5i64){{s+=i;}} std::process::exit(s as i32);}}"),
            15,
        ),
        // `(1..=n).sum()` == 15 (chain consumer over the inclusive source).
        (
            "chain_sum",
            format!("fn main(){{let s:i64=(1..={bb}(5i64)).sum(); std::process::exit(s as i32);}}"),
            15,
        ),
        // `(1..=n).filter(|x| x%2==0).count()` == |{2,4}| == 2 (a closure-carrying
        // FILTER adapter over the inclusive source; works at -O0 AND -O3).
        (
            "chain_filter_count",
            format!("fn main(){{let c=(1..={bb}(5i64)).filter(|x|x%2==0).count(); std::process::exit(c as i32);}}"),
            2,
        ),
        // `(0..=n).collect::<Vec<_>>()` length == n+1 == 6.
        (
            "collect_len",
            format!("fn main(){{let v:Vec<i64>=(0..={bb}(5i64)).collect(); std::process::exit(v.len() as i32);}}"),
            6,
        ),
        // `(0..=n).collect::<Vec<_>>()` index [3] == 3 (the inclusive sequence is 0..=5).
        (
            "collect_index",
            format!("fn main(){{let v:Vec<i64>=(0..={bb}(5i64)).collect(); std::process::exit(v[3] as i32);}}"),
            3,
        ),
        // Nested `for i in 1..=a { for j in 1..=b { s += i+j } }`. a=3,b=2 ->
        // sum over (i,j) of (i+j) = (2+3)+(3+4)+(4+5) = 21.
        (
            "nested",
            format!("fn main(){{let mut s=0i64; for i in 1..={bb}(3i64){{for j in 1..={bb}(2i64){{s+=i+j;}}}} std::process::exit(s as i32);}}"),
            21,
        ),
        // Runtime bounds `a..=b` (a=4,b=8): 4+5+6+7+8 = 30.
        (
            "runtime_bounds",
            format!("fn main(){{let a={bb}(4i64);let b={bb}(8i64);let mut s=0i64;for i in a..=b{{s+=i;}} std::process::exit(s as i32);}}"),
            30,
        ),
        // `a..=a` (a == b): exactly ONE element (the inclusive endpoint). s = 7.
        (
            "single_element",
            format!("fn main(){{let a={bb}(7i64);let mut s=0i64;for i in a..=a{{s+=i;}} std::process::exit(s as i32);}}"),
            7,
        ),
        // `a..=b` with a > b: EMPTY (zero iterations). count = 0.
        (
            "empty_a_gt_b",
            format!("fn main(){{let a={bb}(9i64);let b={bb}(4i64);let mut c=0i64;for _ in a..=b{{c+=1;}} std::process::exit(c as i32);}}"),
            0,
        ),
        // u8 `1..=255` — the `T::MAX` boundary: the LAST element is 255, then the
        // loop STOPS (no `255 + 1` overflow wrap). Final element == 255.
        (
            "u8_max_last",
            format!("fn main(){{let mut last=0u8;for i in 1u8..={bb}(255u8){{last=i;}} std::process::exit(last as i32);}}"),
            255,
        ),
        // u8 `1..=255` element COUNT == 255 (it terminates — an off-by-one /
        // overflow would loop forever or under-count).
        (
            "u8_max_count",
            format!("fn main(){{let mut c=0i32;for _ in 1u8..={bb}(255u8){{c+=1;}} std::process::exit(c);}}"),
            255,
        ),
        // Signed crossing zero `-3..=3`: sum of squares = 9+4+1+0+1+4+9 = 28.
        (
            "signed_neg_pos",
            format!("fn main(){{let mut s=0i64;for i in {bb}(-3i64)..=3i64{{s+=i*i;}} std::process::exit(s as i32);}}"),
            28,
        ),
        // Signed i8 `-24..=24` count == 49 (inclusive both ends).
        (
            "i8_neg_pos_count",
            format!("fn main(){{let mut c=0i32;for _ in {bb}(-24i8)..=24i8{{c+=1;}} std::process::exit(c);}}"),
            49,
        ),
        // === RangeInclusive short-circuit / find / try_fold family (the SIGILL-gap
        // regression). At -O3 `.filter()`/`.find()`/`.any()`/`.all()`/`.position()`
        // over an inclusive source inline down to
        // `RangeInclusiveIteratorImpl::spec_try_fold`, which the bridge intercepts and
        // drives through the SAME exhausted-flag model as `.sum()`; previously
        // `spec_try_fold` was un-intercepted and reached a `ud2` stub at RUNTIME
        // (SIGILL / exit 132). These run AND MATCH LLVM at BOTH -O0 and -O3. ===
        //
        // `for x in (0..=n).filter(p)` — the exact SIGILL repro. Odds in 0..=9 = 25.
        (
            "filter_forloop_shortcircuit",
            format!("fn main(){{let mut s=0i64; for x in (0..={bb}(9i64)).filter(|v|v%2==1){{s+=x;}} std::process::exit(s as i32);}}"),
            25,
        ),
        // `(0..=n).find(p)` — first x with x*x>30 is 6.
        (
            "find_predicate",
            format!("fn main(){{let r=(0..={bb}(9i64)).find(|&x|x*x>30); std::process::exit(r.unwrap_or(-1) as i32);}}"),
            6,
        ),
        // `(0..=n).any(p)` — 7 is in 0..=9 -> true.
        (
            "any_predicate",
            format!("fn main(){{let b=(0..={bb}(9i64)).any(|x|x==7); std::process::exit(if b {{1}} else {{0}});}}"),
            1,
        ),
        // `(0..=n).all(p)` — every element < 100 -> true (exercises the Continue /
        // exhaustion arm, the classic inclusive-final-element case).
        (
            "all_predicate",
            format!("fn main(){{let b=(0..={bb}(9i64)).all(|x|x<100); std::process::exit(if b {{1}} else {{0}});}}"),
            1,
        ),
        // `(0..=n).position(p)` — index of the first `== 3` is 3 (non-ZST usize
        // accumulator + `&mut acc` reference capture in the check).
        (
            "position_predicate",
            format!("fn main(){{let p=(0..={bb}(9i64)).position(|x|x==3); std::process::exit(p.map(|v|v as i32).unwrap_or(-1));}}"),
            3,
        ),
    ];

    for (name, src, expected) in &shapes {
        for opt in ["0", "3"] {
            let llvm_bin = compile(&dir, &format!("{name}_o{opt}_llvm"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_o{opt}_tcg"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit code for `{name}` (-O{opt}) is {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{name}` (-O{opt}) is {tcg_exit}, LLVM is {llvm_exit} \
                 (must match — an off-by-one / MAX-boundary miscompile would diverge)"
            );
        }
    }

    // A `.map(closure)` chain over the inclusive source runs AND MATCHES at BOTH
    // -O0 and -O3. (The former -O3 `.map(closure).sum()` gap — the -O3-inlined
    // reduction inlines the inner `RangeInclusive::try_fold` down to
    // `RangeInclusiveIteratorImpl::spec_try_fold`, which used to reach a trapped
    // dead body — is closed by the `spec_try_fold` interception: `lower_iter_try_fold`
    // recognizes the reduction's non-`ControlFlow` (`NeverShortCircuit`) result and
    // fails that internal body closed, leaving the sum to the intercepted `spec_fold`
    // consumer. Verified bit-identical to LLVM across a broad bound/closure fuzz.)
    let map_shapes: Vec<(&str, String, i32)> = vec![
        // `(1..=n).map(|x| x*x).sum()` == 1+4+9+16+25 == 55.
        (
            "chain_map_sum",
            format!("fn main(){{let s:i64=(1..={bb}(5i64)).map(|x|x*x).sum(); std::process::exit(s as i32);}}"),
            55,
        ),
        // u8 chain `1..=127` widened sum = 127*128/2 = 8128; 8128 % 256 = 192.
        (
            "u8_chain_map_sum",
            format!("fn main(){{let s:u32=(1u8..={bb}(127u8)).map(|x|x as u32).sum(); std::process::exit((s%256) as i32);}}"),
            192,
        ),
        // `(0..=n).map(|x| x*2).collect()` index [4] == 8.
        (
            "chain_map_collect",
            format!("fn main(){{let v:Vec<i64>=(0..={bb}(5i64)).map(|x|x*2).collect(); std::process::exit(v[4] as i32);}}"),
            8,
        ),
    ];
    for (name, src, expected) in &map_shapes {
        for opt in ["0", "3"] {
            let llvm_bin = compile(&dir, &format!("{name}_o{opt}_llvm"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_o{opt}_tcg"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit code for `{name}` (-O{opt}) is {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{name}` (-O{opt}) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// A `.map(closure)` iterator chain reduction over a `RangeInclusive` now RUNS and
/// MATCHES LLVM at -O3 (regression guard for the former fail-closed gap). At -O3 the
/// reduction inlines the inner `RangeInclusive::try_fold` down to
/// `RangeInclusiveIteratorImpl::spec_try_fold`; the `spec_try_fold` interception
/// drives that through the same exhausted-flag model as `.sum()` (and fails the
/// reduction's non-`ControlFlow` internal body closed so the intercepted `spec_fold`
/// consumer computes the sum). Previously this whole compile failed closed.
#[test]
fn range_inclusive_map_closure_chain_runs_o3() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("mapfc");
    let bb = "std::hint::black_box";

    let src = format!(
        "fn main(){{let s:i64=(1..={bb}(5i64)).map(|x|x*x).sum(); std::process::exit(s as i32);}}"
    );
    let llvm = compile(&dir, "mapfc_llvm", &src, None, "3");
    assert_eq!(run_exit_code(&llvm), 55, "LLVM map-closure inclusive sum -O3 should be 55");

    let tcg = compile(&dir, "mapfc_o3_tcg", &src, Some(&dylib), "3");
    assert_eq!(
        run_exit_code(&tcg),
        55,
        "trust-cg `.map(|x| x*x).sum()` over a RangeInclusive at -O3 must run and match LLVM (55)"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A `RangeInclusive` short-circuit consumer (`.all()`/`.any()`) whose predicate
/// CAPTURES a runtime value BY VALUE (`|x| x >= lo`) must FAIL CLOSED (no binary)
/// at BOTH -O0 and -O3 — never a wrong value. At -O3 it inlines to
/// `spec_try_fold(_, all::check(pred))` where the `check` closure holds the
/// capturing predicate's environment INLINE (a non-reference by-value upvar); the
/// bridge's `try_fold` engine hands the check env off BY POINTER, which is correct
/// only for a REFERENCE-captured predicate (`find::check(&mut p)`, the un-gated
/// `.filter(p)` loop) — a by-value capture would MISCOMPILE, so it is refused. LLVM
/// compiles and runs it, so this is a deliberate soundness gate, not a bug. (The
/// SAME limitation applies to an exclusive `Range`, where it is caught one level
/// up in `lower_iter_terminal`.)
#[test]
fn range_inclusive_capturing_shortcircuit_fails_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("capsc");
    let bb = "std::hint::black_box";

    // `(0..=n).all(|x| x >= lo)` with a runtime-captured `lo`: LLVM runs it
    // (every element >= 0 >= lo? here lo=2, so `all` is FALSE), the point is only
    // that the program is well-formed. trust-cg must refuse it (no binary).
    let src = format!(
        "fn main(){{let lo={bb}(2i64);let b=(0..={bb}(9i64)).all(|x|x>=lo); \
         std::process::exit(if b {{1}} else {{0}});}}"
    );
    let llvm = compile(&dir, "capsc_llvm", &src, None, "3");
    let _ = run_exit_code(&llvm); // well-formed under LLVM

    for opt in ["0", "3"] {
        let (output, bin) =
            try_compile(&dir, &format!("capsc_o{opt}_tcg"), &src, Some(&dylib), opt);
        assert!(
            !output.status.success() && !bin.exists(),
            "trust-cg unexpectedly produced a binary for `(0..=n).all(capturing predicate)` \
             (-O{opt}); a by-value capturing check closure is not modeled and must FAIL \
             CLOSED rather than miscompile. stderr: <<<{}>>>",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// `.rev()` over a `RangeInclusive` (a backward `end..=start` walk with its own
/// exhausted-flag bookkeeping) is NOT modeled — it must FAIL CLOSED (no binary)
/// at BOTH -O0 and -O3, never produce a wrong value. (A plain `Range` reverses
/// fine; only the inclusive form is gated.) LLVM compiles and runs it, so this
/// is a deliberate coverage gap, not a correctness bug.
#[test]
fn range_inclusive_rev_fails_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("rev");
    let bb = "std::hint::black_box";

    let rev_src = format!(
        "fn main(){{let s:i64=(1..={bb}(5i64)).rev().sum(); std::process::exit(s as i32);}}"
    );
    // LLVM still runs it (1+2+3+4+5 = 15) — confirm the program is well-formed.
    let llvm = compile(&dir, "rev_llvm", &rev_src, None, "0");
    assert_eq!(run_exit_code(&llvm), 15, "LLVM rev-inclusive sum should be 15");

    for opt in ["0", "3"] {
        let (output, bin) = try_compile(&dir, &format!("rev_o{opt}_tcg"), &rev_src, Some(&dylib), opt);
        assert!(
            !output.status.success() && !bin.exists(),
            "trust-cg unexpectedly produced a binary for `.rev()` over a RangeInclusive \
             (-O{opt}); a reversed inclusive range is not modeled and must FAIL CLOSED. \
             stderr: <<<{}>>>",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
