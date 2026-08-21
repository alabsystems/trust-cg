#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: idiomatic ITERATOR ADAPTERS and terminal consumers
// (`.map` / `.filter` / `.sum` / `.fold` / `.count`) over `Range` and slices
// compiled for x86_64 via the rustc_codegen_trust_cg bridge — COMPILED, LINKED,
// and RUN, with exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: lazy adapters `.map(f)` / `.filter(p)` and terminal consumers
// `.sum()` / `.fold(init, f)` / `.count()` over `Range<T>` and
// `core::slice::Iter<T>` (and `.map`/`.filter` chains of them) RUN on x86_64.
//
// A chain such as `(0..n).filter(|x| x % 2 == 0).map(|x| x * 3).sum()` builds, in
// MIR, a `Filter`/`Map` adapter value wrapping the inner iterator + a (ZST,
// non-capturing) closure, then a terminal `Iterator::sum`/`fold`/`count` call
// that DRIVES the chain. The real std bodies inline to `Iterator::fold` ->
// `Range/slice/Map/Filter::next` -> `spec_next` / `try_fold` / the `cold_path`
// intrinsic / a `NonNull` union representation this backend cannot lower. So —
// exactly as `Box::new`, the `Vec<T>` methods, and the bare `for`-loop iterators
// are intercepted — the bridge intercepts the adapter constructors and the
// terminal consumers and synthesizes them directly against a memory-backed
// iterator-chain slot:
//
//   * `.map(f)` / `.filter(p)` copy the inner iterator's state into the adapter
//     slot (the ZST closure carries no upvars), leaving the slot as the chain's
//     runtime state;
//   * `.sum()` / `.fold(init, f)` / `.count()` synthesize the driving loop — a
//     real multi-block loop whose carried state (the iterator chain slot + the
//     accumulator) is MEMORY-BACKED (no phi nodes). Each iteration advances the
//     source (Range `start < end`, slice `ptr != end`), threads the element
//     through each adapter (a `Map` calls its closure; a `Filter` calls its
//     predicate and loops on rejection), and folds the survivor into the
//     accumulator (`+` for `sum`, `+1` for `count`, the user closure for `fold`).
//     The closure is called through its compiled closure-body symbol.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A miscompiled adapter
// (a wrong element, a skipped/duplicated item, a bad fold) would diverge from
// LLVM, so equal exit codes are the differential we assert.

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
    assert!(status.success(), "cargo build failed; cannot run iter-adapter test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_iter_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
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
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend). stderr: <<<{}>>>",
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

/// The full differential: each iterator-adapter program is compiled by trust-cg
/// AND LLVM, run, and the exit codes must match each other and the expected
/// value. A divergence is a miscompiled adapter / consumer.
#[test]
fn iter_adapter_programs_run_and_match_llvm() {
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

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        // `(0..10).sum()` -> 0+..+9 = 45 (the canonical terminal consumer).
        (
            "range_sum_0_10",
            "fn main() { let s: i64 = (0..10i64).sum(); std::process::exit(s as i32); }",
            45,
        ),
        // `(0..n).map(|x| x*2).sum()` -> 2*(0+..+4) = 20.
        (
            "range_map_sum",
            "fn main() { let n: i64 = 5; let s: i64 = (0..n).map(|x| x * 2).sum(); \
             std::process::exit(s as i32); }",
            20,
        ),
        // `(0..n).filter(|x| x%2==0).sum()` -> 0+2+4+6+8 = 20.
        (
            "range_filter_sum",
            "fn main() { let n: i64 = 10; let s: i64 = (0..n).filter(|x| x % 2 == 0).sum(); \
             std::process::exit(s as i32); }",
            20,
        ),
        // `(0..n).filter(|x| x%2==0).count()` -> {0,2,4,6,8} = 5.
        (
            "range_filter_count",
            "fn main() { let n: i64 = 10; let c: usize = (0..n).filter(|x| x % 2 == 0).count(); \
             std::process::exit(c as i32); }",
            5,
        ),
        // `(0..n).fold(0, |a,x| a+x)` -> 0+..+9 = 45.
        (
            "range_fold_add",
            "fn main() { let n: i64 = 10; let r: i64 = (0..n).fold(0i64, |a, x| a + x); \
             std::process::exit(r as i32); }",
            45,
        ),
        // `.skip_while(p)` RE-ENTER semantic: once the predicate first goes false,
        // ALL later elements yield even if the predicate becomes true again
        // ([1,2,10,3,1] skip<5 -> yield 10,3,1 = 14). The distinction from filter.
        (
            "skip_while_reenter",
            "fn main() { let v = [1i32, 2, 10, 3, 1]; \
             let s: i32 = v.iter().skip_while(|x| **x < 5).sum(); std::process::exit(s); }",
            14,
        ),
        // `.skip_while(p)` that skips NOTHING (first element already fails p) -> all.
        (
            "skip_while_none",
            "fn main() { let v = [9i32, 1, 2]; \
             let s: i32 = v.iter().skip_while(|x| **x < 5).sum(); std::process::exit(s); }",
            12,
        ),
        // `.skip_while(p).map(..).sum()` -> skip 1,2; map*2 over 10,3 = 26.
        (
            "skip_while_map",
            "fn main() { let v = [1i32, 2, 10, 3]; \
             let s: i32 = v.iter().skip_while(|x| **x < 5).map(|x| x * 2).sum(); \
             std::process::exit(s); }",
            26,
        ),
        // The predicate is called only through the first false (1,2,10 => three
        // calls), never for the yielded tail. The assert would abort if the
        // completed-state fast path called it again.
        (
            "skip_while_predicate_short_circuits",
            "static mut CALLS: i32 = 0; fn main() { let v=[1i32,2,10,3,1]; \
             let s:i32=v.iter().skip_while(|x| { let c=unsafe { CALLS+=1; CALLS }; \
             assert!(c<=3, \"predicate called after first false\"); **x<5 }).sum(); \
             let c=unsafe { CALLS }; std::process::exit(s+c*20); }",
            74,
        ),
        // Each reference-taking adapter needs its own exact-typed preheader slot:
        // map changes i64 -> u8 before the first filter, then u8 -> i128 before the
        // second. A shared I64 slot is both mistyped and too small for the latter.
        (
            "map_width_change_between_filters",
            "fn main() { let s:i128=(0i64..6).map(|x| x as u8)\
             .filter(|x| *x%2==0).map(|x| x as i128)\
             .filter(|x| *x>=2).sum(); std::process::exit(s as i32); }",
            6,
        ),
        // `.min_by(cmp)` / `.max_by(cmp)` with a REVERSED comparator (min_by(rev) is
        // a MAX). A def-path-only recognizer once flattened this to plain min
        // (miscompile). min_by(|a,b| b.cmp(a)) over [3,1,2] -> 3.
        (
            "min_by_reversed",
            "fn main() { let v = [3i32, 1, 2]; \
             let m = v.iter().copied().min_by(|a, b| b.cmp(a)).unwrap(); std::process::exit(m); }",
            3,
        ),
        // `.max_by(cmp)` tie-break keeps the LAST maximum: |x| by abs over [10,-10]
        // (both |.|=10) keeps -10 (& 0xFF = 246).
        (
            "max_by_tie_last",
            "fn main() { let v = [10i32, -10]; \
             let m = v.iter().copied().max_by(|a, b| a.abs().cmp(&b.abs())).unwrap(); \
             std::process::exit(m & 0xFF); }",
            246,
        ),
        // `.min_by(cmp)` over a REFERENCE item (`v.iter()`, comparator `&&i32`): the
        // first-element `&best` must not deref a wild pointer (was a segfault).
        (
            "min_by_reference_item",
            "fn main() { let v = [3i32, 1, 2]; \
             let m = *v.iter().min_by(|a, b| a.cmp(b)).unwrap(); std::process::exit(m); }",
            1,
        ),
        // `(&arr).iter().map(|x| x*x).sum()` over a STACK array -> 1+4+9+16 = 30.
        (
            "slice_map_square_sum",
            "fn main() { let arr: [i64; 4] = [1, 2, 3, 4]; \
             let s: i64 = (&arr).iter().map(|x| x * x).sum(); std::process::exit(s as i32); }",
            30,
        ),
        // A `.filter().map().sum()` chain: keep evens of 0..10 {0,2,4,6,8}, *3 ->
        // {0,6,12,18,24} -> 60.
        (
            "range_filter_map_sum",
            "fn main() { let n: i64 = 10; \
             let s: i64 = (0..n).filter(|x| x % 2 == 0).map(|x| x * 3).sum(); \
             std::process::exit(s as i32); }",
            60,
        ),
        // `count()` over a `map` (the consumer ignores the element) -> 7 items.
        (
            "range_map_count",
            "fn main() { let c: usize = (0..7i64).map(|x| x * x).count(); \
             std::process::exit(c as i32); }",
            7,
        ),
        // `fold` over a `map`: sum of {0,2,4,6,8} = 20.
        (
            "range_map_fold",
            "fn main() { let r: i64 = (0..5i64).map(|x| x * 2).fold(0i64, |a, x| a + x); \
             std::process::exit(r as i32); }",
            20,
        ),
        // Chained `map`s: ((0..5)+1)*10 summed = (1+2+3+4+5)*10 = 150.
        (
            "range_map_map_sum",
            "fn main() { let s: i64 = (0..5i64).map(|x| x + 1).map(|y| y * 10).sum(); \
             std::process::exit(s as i32); }",
            150,
        ),
        // An UNSIGNED Range (`usize`) through `map().sum()`: 2*(0+1+2+3+4+5+6) = 42.
        (
            "range_usize_map_sum",
            "fn main() { let n: usize = 7; let s: usize = (0..n).map(|x| x * 2).sum(); \
             std::process::exit(s as i32); }",
            42,
        ),
        // A slice `.iter().filter(...).sum()` (the filter predicate sees `&&T`):
        // elements > 2 in [1,2,3,4,5] are {3,4,5} = 12.
        (
            "slice_filter_sum",
            "fn main() { let arr: [i64; 5] = [1, 2, 3, 4, 5]; \
             let s: i64 = arr.iter().filter(|x| **x > 2).sum(); std::process::exit(s as i32); }",
            12,
        ),
        // An EMPTY range consumer yields the identity (0).
        (
            "empty_range_sum",
            "fn main() { let s: i64 = (5..5i64).map(|x| x * 9).sum(); std::process::exit(s as i32); }",
            0,
        ),
        // A by-value CONSTANT `Range<i64>` argument: a user fn taking the Range by
        // value, called with a const Range literal (`span(3..10)`). This is the
        // const-folded shape rustc's inlined adapter chains pass into the first
        // iterator call (`Range::zip(const Range {..}, ..)`), so it exercises the
        // by-value const-aggregate call-argument lowering directly. 10 - 3 = 7.
        (
            "byval_const_range_arg",
            "#[inline(never)] fn span(r: std::ops::Range<i64>) -> i64 { r.end - r.start } \
             fn main() { std::process::exit(span(3..10) as i32); }",
            7,
        ),
        // A by-value CONSTANT struct argument (MEMORY-class, 24 B on the stack):
        // a user fn taking a `{i64,i64,i64}` by value, called with a const literal.
        // 10 + 20 + 11 = 41.
        (
            "byval_const_struct_arg",
            "#[derive(Clone, Copy)] struct Big { a: i64, b: i64, c: i64 } \
             #[inline(never)] fn tot(p: Big) -> i64 { p.a + p.b + p.c } \
             fn main() { const Q: Big = Big { a: 10, b: 20, c: 11 }; \
             std::process::exit(tot(Q) as i32); }",
            41,
        ),
        // A by-value CONSTANT `Range<i64>` consumed by an in-fn `for` loop: the
        // const Range flows into the loop's `into_iter`/`next` adapter calls by
        // value. Sum 0..10 = 45.
        (
            "byval_const_range_forloop",
            "#[inline(never)] fn consume(r: std::ops::Range<i64>) -> i64 { \
             let mut s = 0; for x in r { s += x; } s } \
             fn main() { std::process::exit(consume(0..10) as i32); }",
            45,
        ),
        // chain() over two SLICE sub-sources (`a.iter().chain(b.iter())`) driven by a
        // terminal. Previously only Range sub-sources were modeled: a slice's
        // `Option<slice::Iter>` is NICHE-encoded (its NonNull ptr is the niche), so
        // `option_direct_payload_offset` failed closed. Now the ctor skips the
        // (absent) Some-tag write for the niche Option and the Concat `next` drives
        // each slice via `emit_slice_next_guarded`. 1+2+3+4+5+6 = 21.
        (
            "slice_chain_sum",
            "fn main() { let a = [1i64, 2, 3]; let b = [4i64, 5, 6]; \
             let s: i64 = a.iter().chain(b.iter()).sum(); std::process::exit(s as i32); }",
            21,
        ),
        // chain() of two slices via `fold`: 1*2*3*4*5 = 120.
        (
            "slice_chain_fold",
            "fn main() { let a = [1i64, 2, 3]; let b = [4i64, 5]; \
             let p: i64 = a.iter().chain(b.iter()).fold(1i64, |acc, &x| acc * x); \
             std::process::exit(p as i32); }",
            120,
        ),
        // chain() of two slices via `count`: 3 + 4 = 7 elements.
        (
            "slice_chain_count",
            "fn main() { let a = [1i64, 2, 3]; let b = [4i64, 5, 6, 7]; \
             let c: usize = a.iter().chain(b.iter()).count(); std::process::exit(c as i32); }",
            7,
        ),
        // chain() where the FIRST sub-slice is RUNTIME-empty (`a[..0]`): the driver
        // must skip the exhausted first source and yield the whole second. 1+..+5 = 15.
        (
            "slice_chain_empty_first",
            "fn main() { let a = [1i64, 2, 3, 4, 5]; let n = std::hint::black_box(0usize); \
             let s: i64 = a[..n].iter().chain(a[n..].iter()).sum(); \
             std::process::exit(s as i32); }",
            15,
        ),
        // chain() of two slices with a `.copied()` adapter before the terminal. 21.
        (
            "slice_chain_copied_sum",
            "fn main() { let a = [1i64, 2, 3]; let b = [4i64, 5, 6]; \
             let s: i64 = a.iter().chain(b.iter()).copied().sum(); std::process::exit(s as i32); }",
            21,
        ),
        // `.map_while(f)`: the closure returns `Option<U>` (like filter_map) but a
        // `None` STOPS the iterator (like take_while). Modeled by an emit_chain_next
        // arm identical to FilterMap except `None` -> terminate (not_found) instead
        // of re-pull. Stops at the first non-positive: 1+2+3 = 6.
        (
            "map_while_sum",
            "fn main() { let v = [1i64, 2, 3, -1, 5]; \
             let s: i64 = v.iter().map_while(|&x| if x > 0 { Some(x) } else { None }).sum(); \
             std::process::exit(s as i32); }",
            6,
        ),
        // map_while whose closure NEVER returns None (behaves like map): (1+2+3)*2 = 12.
        (
            "map_while_all_pass",
            "fn main() { let v = [1i64, 2, 3]; \
             let s: i64 = v.iter().map_while(|&x| Some(x * 2)).sum(); \
             std::process::exit(s as i32); }",
            12,
        ),
        // map_while over a RANGE source, stopping at 5: 1+2+3+4 = 10.
        (
            "map_while_range",
            "fn main() { let s: i64 = (1i64..10).map_while(|x| if x < 5 { Some(x) } else { None }).sum(); \
             std::process::exit(s as i32); }",
            10,
        ),
        // map_while via `count`: stops at the first odd -> {2,4,6} = 3 elements.
        (
            "map_while_count",
            "fn main() { let v = [2i64, 4, 6, 7, 8]; \
             let c: usize = v.iter().map_while(|&x| if x % 2 == 0 { Some(x) } else { None }).count(); \
             std::process::exit(c as i32); }",
            3,
        ),
        // map_while whose FIRST element fails -> empty -> identity 0 (+7 sentinel).
        (
            "map_while_first_fail",
            "fn main() { let v = [-1i64, 2, 3]; \
             let s: i64 = v.iter().map_while(|&x| if x > 0 { Some(x) } else { None }).sum(); \
             std::process::exit((s + 7) as i32); }",
            7,
        ),
        // `s.bytes()` = `Copied<slice::Iter<u8>>` over the str's UTF-8 bytes. Modeled
        // by building the same `{ ptr, end }` slice-iter state a `&[u8]` into_iter
        // would (a `&str` shares the `{data,len}` fat-ptr repr), + a resolve peel of
        // `str::Bytes` -> its inner `Copied<slice::Iter<u8>>`. 'A'+'B'+'C' = 198.
        (
            "str_bytes_sum",
            "fn main() { let x: u32 = \"ABC\".bytes().map(|b| b as u32).sum(); \
             std::process::exit(x as i32); }",
            198,
        ),
        // str.bytes().count() -> 5 bytes.
        (
            "str_bytes_count",
            "fn main() { let c = \"hello\".bytes().count(); std::process::exit(c as i32); }",
            5,
        ),
        // str.bytes().filter(...).count(): two 'o' bytes in \"hello world\".
        (
            "str_bytes_filter_count",
            "fn main() { let c = \"hello world\".bytes().filter(|&b| b == b'o').count(); \
             std::process::exit(c as i32); }",
            2,
        ),
        // A `for b in s.bytes()` bare-next loop (the Bytes iterator drives directly).
        // 'A'+'B'+'C' = 198.
        (
            "str_bytes_forloop",
            "fn main() { let mut x = 0u32; for b in \"ABC\".bytes() { x += b as u32; } \
             std::process::exit(x as i32); }",
            198,
        ),
        // str.bytes().position(p): the first 'l' in \"hello\" is at index 2.
        (
            "str_bytes_position",
            "fn main() { let p = \"hello\".bytes().position(|b| b == b'l').unwrap(); \
             std::process::exit(p as i32); }",
            2,
        ),
        // `.inspect(f)`: a transparent pass-through -- calls `f(&item) -> ()` for its
        // side effect, yields the item UNCHANGED, always proceeds. Modeled by an
        // emit_chain_next arm that emits a VOID closure call (no result binding) and
        // an unconditional Br. 1+2+3 = 6.
        (
            "inspect_sum",
            "fn main() { let v = [1i64, 2, 3]; \
             let s: i64 = v.iter().inspect(|_| {}).sum(); std::process::exit(s as i32); }",
            6,
        ),
        // inspect before a `map` (the item passes through unchanged): (1+2+3)*2 = 12.
        (
            "inspect_map",
            "fn main() { let v = [1i64, 2, 3]; \
             let s: i64 = v.iter().inspect(|_| {}).map(|&x| x * 2).sum(); \
             std::process::exit(s as i32); }",
            12,
        ),
        // inspect AFTER a filter (only kept items are inspected): {3,4} = 7.
        (
            "inspect_after_filter",
            "fn main() { let v = [1i64, 2, 3, 4]; \
             let s: i64 = v.iter().filter(|&&x| x > 2).inspect(|_| {}).sum(); \
             std::process::exit(s as i32); }",
            7,
        ),
        // A CAPTURING, SIDE-EFFECTING inspect closure: `count` must be mutated once
        // per element (the side effect is preserved, not dropped). sum=10, count=4 ->
        // 10*10 + 4 = 104.
        (
            "inspect_side_effect",
            "fn main() { let v = [1i64, 2, 3, 4]; let mut count = 0i64; \
             let s: i64 = v.iter().inspect(|_| count += 1).sum(); \
             std::process::exit((s * 10 + count) as i32); }",
            104,
        ),
        // inspect via `count` (the item is ignored but the closure still fires): 5.
        (
            "inspect_count",
            "fn main() { let v = [1i64, 2, 3, 4, 5]; \
             let c = v.iter().inspect(|_| {}).count(); std::process::exit(c as i32); }",
            5,
        ),
        // A BY-VALUE array iterator chain: `[..].into_iter().sum()` — the array's
        // `into_iter` yields `T` by value; the chain resolver models it as the same
        // `{ptr,end}` slice cursor + an implicit `Copied` (like `vec::IntoIter`). 15.
        (
            "array_into_iter_sum",
            "fn main() { let s: i32 = [1i32, 2, 3, 4, 5].into_iter().sum(); \
             std::process::exit(s); }",
            15,
        ),
        // `[..].into_iter().map(..).sum()` — a by-value array source under an adapter. 12.
        (
            "array_into_iter_map_sum",
            "fn main() { let s: i32 = [1i32, 2, 3].into_iter().map(|x| x * 2).sum(); \
             std::process::exit(s); }",
            12,
        ),
        // `[..].into_iter().filter(..).count()` — by-value array + filter + count. 3.
        (
            "array_into_iter_filter_count",
            "fn main() { let n = [1i32, 2, 3, 4, 5].into_iter().filter(|&x| x > 2).count(); \
             std::process::exit(n as i32); }",
            3,
        ),
        // `<[T; N]>::map(f)` — the fixed-size array map (NOT `Iterator::map`). Applies `f`
        // to each element by value, producing `[U; N]`. `[1,2,3,4].map(|x| x*x)` = [1,4,9,16];
        // a position-weighted sum (`v[0] + 2*v[1] + 3*v[2] + 4*v[3]`) = 1+8+27+64 = 100
        // catches a misplaced/mis-ordered element.
        (
            "array_map_square",
            "fn main() { let a = [1i32, 2, 3, 4].map(|x| x * x); \
             std::process::exit(a[0] + a[1] * 2 + a[2] * 3 + a[3] * 4); }",
            100,
        ),
        // `array::map` with a STATEFUL `FnMut` — the closure is called left-to-right, so
        // the counter yields 1,2,3 in order. `[0;3].map(|_|{c+=1;c})` = [1,2,3]; the
        // order-sensitive checksum `v[0]*100 + v[1]*10 + v[2]` = 123 (reverse would be 321).
        (
            "array_map_ordered_fnmut",
            "fn main() { let mut c = 0i32; let a = [0i32, 0, 0].map(|_| { c += 1; c }); \
             std::process::exit(a[0] * 100 + a[1] * 10 + a[2]); }",
            123,
        ),
        // `array::map` that CHANGES the element type/width (i32 -> i64). [3,4,5] -> [6,8,10]. 24.
        (
            "array_map_widen",
            "fn main() { let a = [3i32, 4, 5].map(|x| (x as i64) * 2); \
             std::process::exit((a[0] + a[1] + a[2]) as i32); }",
            24,
        ),
        // `core::array::from_fn(|i| ..)` — build `[T; N]` by calling the closure with each
        // INDEX in order (not an element). `from_fn(|i| i*2)` for [i32;4] = [0,2,4,6], sum 12.
        (
            "array_from_fn_double",
            "fn main() { let a: [i32; 4] = std::array::from_fn(|i| i as i32 * 2); \
             std::process::exit(a[0] + a[1] + a[2] + a[3]); }",
            12,
        ),
        // `array::from_fn` order-sensitivity: identity `|i| i` yields [0,1,2,3]; the
        // position-weighted checksum `a[0]*1000 + a[1]*100 + a[2]*10 + a[3]` = 123.
        (
            "array_from_fn_order",
            "fn main() { let a: [i32; 4] = std::array::from_fn(|i| i as i32); \
             std::process::exit(a[0] * 1000 + a[1] * 100 + a[2] * 10 + a[3]); }",
            123,
        ),
        // `array::from_fn` with a STATEFUL FnMut (called left-to-right): c goes 101,102,103;
        // a[0]-a[2]+200 = 101-103+200 = 198.
        (
            "array_from_fn_stateful",
            "fn main() { let mut c = 100i32; \
             let a: [i32; 3] = std::array::from_fn(|_| { c += 1; c }); \
             std::process::exit(a[0] - a[2] + 200); }",
            198,
        ),
        // `<[i128; N]>::map` over 16-byte elements — the `<< 40 >> 40` round-trip
        // exercises bits BEYOND i64, so a truncated (8-byte) load/store would diverge.
        // [1<<40, 1<<41] -> [1, 2], sum 3.
        (
            "array_map_i128",
            "fn main() { let a: [i128; 2] = [1i128 << 40, 1i128 << 41]; \
             let b = a.map(|x| x >> 40); std::process::exit((b[0] + b[1]) as i32); }",
            3,
        ),
        // `array::from_fn` over i128 (16-byte): a[i] = i<<40; a[2]>>40 = 2.
        (
            "array_from_fn_i128",
            "fn main() { let a: [i128; 3] = std::array::from_fn(|i| (i as i128) << 40); \
             std::process::exit((a[2] >> 40) as i32); }",
            2,
        ),
        // `.for_each(f)` — a SIDE-EFFECT terminal driving the chain and calling `f` per
        // element (mutable-captured accumulator, the common form). Slice `&T` item: sum
        // 1+2+3+4 = 10.
        (
            "for_each_slice",
            "fn main() { let v = vec![1i32, 2, 3, 4]; let mut s = 0; \
             v.iter().for_each(|x| s += *x); std::process::exit(s); }",
            10,
        ),
        // `.for_each` over a `.filter()` chain — only odd elements fire the closure. 5,7,9
        // -> counted 3.
        (
            "for_each_filter_count",
            "fn main() { let v = vec![5i32, 6, 7, 8, 9]; let mut c = 0; \
             v.iter().filter(|&&x| x % 2 == 1).for_each(|_| c += 1); std::process::exit(c); }",
            3,
        ),
        // `.for_each` ORDER-sensitivity: `acc = acc*10 + x` over [1,2,3] left-to-right = 123.
        (
            "for_each_order",
            "fn main() { let v = vec![1i32, 2, 3]; let mut acc = 0; \
             v.iter().for_each(|x| acc = acc * 10 + *x); std::process::exit(acc); }",
            123,
        ),
        // `.enumerate().for_each(|(i, x)| ..)` — a TUPLE item, materialized like
        // `.map()`/`.inspect()` over a tuple. `sum(i * x)` over [10,20,30] = 0+20+60 = 80.
        (
            "for_each_enumerate",
            "fn main() { let v = vec![10i32, 20, 30]; let mut s = 0; \
             v.iter().enumerate().for_each(|(i, x)| s += i as i32 * *x); std::process::exit(s); }",
            80,
        ),
        // `.zip(..).for_each(|(x, y)| ..)` — a two-source tuple item. `sum(x*y)` over
        // [1,2,3] . [10,20,30] = 10+40+90 = 140.
        (
            "for_each_zip",
            "fn main() { let a = vec![1i32, 2, 3]; let b = vec![10i32, 20, 30]; let mut s = 0; \
             a.iter().zip(b.iter()).for_each(|(x, y)| s += x * y); std::process::exit(s & 0xFF); }",
            140,
        ),
        // `.iter_mut()` chains: `slice::IterMut` is the same `{ptr,end}` cursor as
        // `slice::Iter`, yielding `&mut T`. The closure MUTATES THROUGH it into the live
        // buffer — this reads back the result, so a broken cursor or a lost write diverges.
        // `[1,2,3].iter_mut().for_each(|x| *x *= 10)` -> [10,20,30], sum 60.
        (
            "iter_mut_for_each",
            "fn main() { let mut v = vec![1i32, 2, 3]; v.iter_mut().for_each(|x| *x *= 10); \
             std::process::exit(v[0] + v[1] + v[2]); }",
            60,
        ),
        // `.iter_mut()` with a STATEFUL FnMut writing per-element indices in order:
        // c goes 1,2,3 -> v = [1,2,3]; order-sensitive checksum 123.
        (
            "iter_mut_stateful",
            "fn main() { let mut v = vec![0i32, 0, 0]; let mut c = 0; \
             v.iter_mut().for_each(|x| { c += 1; *x = c; }); \
             std::process::exit(v[0] * 100 + v[1] * 10 + v[2]); }",
            123,
        ),
        // `.rev()` over a slice iterator: `DoubleEndedIterator::next_back` writes the
        // shrinking `*const T` end pointer THROUGH the iterator's slot (`*slot = end`).
        // That pointer store fail-closed "deref memory store type is not scalarizable:
        // PtrConst(i32)" before pointer-like store values were accepted. rev([1,2,3])
        // folds `r = r*10 + x` -> 321, exit = 321 % 256 = 65.
        (
            "rev_slice_iter_fold",
            "fn main() { let a = [1i32, 2, 3]; let mut r = 0i32; \
             for x in a.iter().rev() { r = r * 10 + x; } \
             std::process::exit(r % 256); }",
            65,
        ),
        // `.rev().sum()` — the DoubleEnded terminal over the same back-pointer store. 60.
        (
            "rev_slice_iter_sum",
            "fn main() { let a = [10i32, 20, 30]; let s: i32 = a.iter().rev().sum(); \
             std::process::exit(s); }",
            60,
        ),
        // Tuple-item `.filter()` after `enumerate`: pin each lane separately.
        // Keeping even indices yields 10+30+50 = 90.
        (
            "enumerate_filter_index_lane",
            "fn main() { let v = [10i64, 20, 30, 40, 50]; \
             let s: i64 = v.iter().enumerate().filter(|(i, _)| i % 2 == 0) \
                 .map(|(_, x)| *x).sum(); std::process::exit(s as i32); }",
            90,
        ),
        // Filtering on the tuple's value lane yields 30+40+50 = 120.
        (
            "enumerate_filter_value_lane",
            "fn main() { let v = [10i64, 20, 30, 40, 50]; \
             let s: i64 = v.iter().enumerate().filter(|(_, x)| **x > 25) \
                 .map(|(_, x)| *x).sum(); std::process::exit(s as i32); }",
            120,
        ),
        // `zip` produces two reference lanes. The predicate and downstream map
        // must see the same pair: (1,2) and (3,6) survive, totaling 3+9 = 12.
        (
            "zip_filter_both_lanes",
            "fn main() { let a = [1i64, 5, 3]; let b = [2i64, 4, 6]; \
             let s: i64 = a.iter().zip(b.iter()).filter(|(x, y)| **x < **y) \
                 .map(|(x, y)| *x + *y).sum(); std::process::exit(s as i32); }",
            12,
        ),
        // Tuple-item `.take_while()` must terminate from either lane and preserve
        // the pair for the downstream map. Both predicates keep 10+20+30 = 60.
        (
            "enumerate_take_while_index_lane",
            "fn main() { let v = [10i64, 20, 30, 40, 50]; \
             let s: i64 = v.iter().enumerate().take_while(|(i, _)| *i < 3) \
                 .map(|(_, x)| *x).sum(); std::process::exit(s as i32); }",
            60,
        ),
        (
            "enumerate_take_while_value_lane",
            "fn main() { let v = [10i64, 20, 30, 40, 50]; \
             let s: i64 = v.iter().enumerate().take_while(|(_, x)| **x < 35) \
                 .map(|(_, x)| *x).sum(); std::process::exit(s as i32); }",
            60,
        ),
        // A capturing tuple-item inspect observes both lanes and passes the item
        // through unchanged: seen=(0+10)+(1+20)+(2+30)=63, value sum=60.
        (
            "enumerate_inspect_both_lanes",
            "fn main() { let v = [10i64, 20, 30]; let mut seen = 0i64; \
             let s: i64 = v.iter().enumerate().inspect(|(i, x)| seen += *i as i64 + **x) \
                 .map(|(_, x)| *x).sum(); std::process::exit((s + seen) as i32); }",
            123,
        ),
        // Tuple-by-value `filter_map` must materialize the whole pair. Exercise
        // the index and value lanes independently (90 and 120 respectively).
        (
            "enumerate_filter_map_index_lane",
            "fn main() { let v = [10i64, 20, 30, 40, 50]; \
             let s: i64 = v.iter().enumerate() \
                 .filter_map(|(i, x)| (i % 2 == 0).then(|| *x)).sum(); \
             std::process::exit(s as i32); }",
            90,
        ),
        (
            "enumerate_filter_map_value_lane",
            "fn main() { let v = [10i64, 20, 30, 40, 50]; \
             let s: i64 = v.iter().enumerate() \
                 .filter_map(|(_, x)| (*x > 25).then(|| *x)).sum(); \
             std::process::exit(s as i32); }",
            120,
        ),
        // Tuple-by-value `map_while` terminates on the index lane while deriving
        // its output from both lanes: (10+0)+(20+1)+(30+2) = 63.
        (
            "enumerate_map_while_both_lanes",
            "fn main() { let v = [10i64, 20, 30, 40, 50]; \
             let s: i64 = v.iter().enumerate() \
                 .map_while(|(i, x)| (i < 3).then(|| *x + i as i64)).sum(); \
             std::process::exit(s as i32); }",
            63,
        ),
        // `scan` threads mutable state while consuming both tuple lanes. Outputs
        // are 10, 31, and 62, so the terminal sum is 103.
        (
            "enumerate_scan_state_and_both_lanes",
            "fn main() { let v = [10i64, 20, 30]; \
             let s: i64 = v.iter().enumerate().scan(0i64, |acc, (i, x)| { \
                 *acc += *x; Some(*acc + i as i64) }).sum(); \
             std::process::exit(s as i32); }",
            103,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib));
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM backend exit code for `{name}` is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for `{name}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
