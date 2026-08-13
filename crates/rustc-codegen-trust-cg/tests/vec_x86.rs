// Integration test: heap-allocating std Rust using `Vec<i64>` compiled for
// x86_64 via the rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with
// exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS5 — growable owned collections (`Vec<T>`) RUN on x86_64 via trust-cg.
//
// This is the collections milestone: a std `fn main` that builds a `Vec<i64>`
// (`Vec::new` / `Vec::with_capacity`), pushes a loop of values (`Vec::push`,
// which grows the backing buffer), reads them back by index
// (`<Vec<i64> as Index<usize>>::index` + a deref load) and by `len`, sums them,
// and — crucially — *frees* the buffer (the `Vec`'s `Drop` runs
// `__rust_dealloc`). The bridge:
//
//   * skips the zero-sized fields (`PhantomData<T>`, the `Global` allocator) of
//     the `Vec`/`RawVec` aggregate when flattening, rather than failing closed on
//     their non-memory-scalar (`Unit`) type;
//   * maps a `Vec<T, Global>` (for a scalar element `T`) to a single `Ptr`
//     scalar — the address of a `{ ptr, cap, len }` stack slot it `alloca`s — so
//     a `Vec` local, and every `&Vec` / `&mut Vec`, flows like a pointer;
//   * intercepts the `Vec` methods (whose real bodies descend into unlowerable
//     `alloc::Layout` / `Alignment` / `RawVec::grow` machinery) and synthesizes
//     them directly against the allocator: `new`/`with_capacity` eagerly reserve
//     a real heap buffer via `__rust_alloc`; `push` ensures capacity (a
//     branchless `__rust_realloc` that never shrinks), stores at `ptr+len*size`,
//     and bumps `len`; index returns `&*(ptr+i*size)`; `len` reads the slot's
//     length; `Drop` frees the buffer with `__rust_dealloc(ptr, cap*size, align)`
//     (the `i64` elements are `Copy`, so there is no per-element drop);
//   * exactly as it intercepts `Box::new` (see `heap_types_x86.rs`).
//
// The `__rust_alloc`/`__rust_realloc`/`__rust_dealloc` symbols are provided by
// the bridge's own default-allocator shim (forwarding to libstd's `__rdl_*`
// System allocator); libc provides the underlying malloc/realloc/free.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A wrong `Vec` result —
// or a missing/double free, or a use-after-free from a grow that loses elements
// — is a miscompile, so equal exit codes plus a clean process teardown is the
// differential we assert.

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
    assert!(status.success(), "cargo build failed; cannot run Vec test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_vec_{stem}_{}", std::process::id()));
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
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    (output, bin)
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    let (output, bin) = try_compile(dir, name, src, backend);
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

/// The full differential: each `Vec<i64>` program is compiled by trust-cg AND
/// LLVM, run, and the exit codes must match each other and the expected value. A
/// divergence is a miscompile (a wrong `Vec` element/length, or a crash/abort
/// from a bad allocation or free).
#[test]
fn vec_programs_run_and_match_llvm() {
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
        // The canonical goal: `Vec::new()`, push 1..=10, sum by index, exit 55.
        // The `Vec` is live to `exit` (which diverges), exactly as under LLVM.
        (
            "vec_new_push_index_sum",
            "fn main() { let mut v: Vec<i64> = Vec::new(); let mut i = 1i64; \
             while i <= 10 { v.push(i); i += 1; } let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } std::process::exit(s as i32); }",
            55,
        ),
        // `Vec::with_capacity` + push past capacity (forces a grow) + sum, and the
        // `Vec` is *dropped* (freed) on the normal return from `build` before
        // `main` exits. A missing free is caught by the leak check below; a bad
        // grow that loses elements is caught by the wrong sum here.
        (
            "vec_with_capacity_drop",
            "fn build() -> i64 { let mut v: Vec<i64> = Vec::with_capacity(4); \
             let mut i = 1i64; while i <= 10 { v.push(i); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } s } \
             fn main() { std::process::exit(build() as i32); }",
            55,
        ),
        // A larger build that triggers several reallocations, dropped before exit.
        // 1+..+100 = 5050; 5050 % 251 = 33 fits a u8 exit byte.
        (
            "vec_grow_many_drop",
            "fn build() -> i64 { let mut v: Vec<i64> = Vec::new(); \
             let mut i = 1i64; while i <= 100 { v.push(i); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } s } \
             fn main() { std::process::exit((build() % 251) as i32); }",
            (5050 % 251) as i32,
        ),
        // An empty `Vec` that is never pushed, then dropped: `len() == 0`, and the
        // eagerly-reserved buffer is still freed cleanly.
        (
            "vec_empty_drop",
            "fn build() -> i64 { let v: Vec<i64> = Vec::new(); v.len() as i64 } \
             fn main() { std::process::exit((build() + 7) as i32); }",
            7,
        ),
        // REFUTATION (conditional-grow push, `emit_vec_push_grow`): pin the
        // fast-path/grow-path boundary exactly. `with_capacity(4)` + 4 pushes
        // fill EXACTLY to capacity — every push must take the no-realloc fast
        // path and still land each element at its slot (order-sensitive
        // polynomial checksum diverges on any misplaced element or wrong len).
        // The 5th push hits `new_len > cap` at the boundary and MUST grow —
        // a wrong branch polarity, off-by-one (`>=` vs `>`), or a fast path
        // that skips the grow would either clobber past the buffer or lose
        // the element, diverging the second checksum.
        (
            "vec_push_capacity_boundary",
            "fn main() { let mut v: Vec<i64> = Vec::with_capacity(4); \
             let mut i = 0i64; while i < 4 { v.push(i * 7 + 3); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s = s * 31 + v[j]; j += 1; } \
             v.push(99); \
             let mut t = 0i64; let mut k = 0usize; \
             while k < v.len() { t = t * 31 + v[k]; k += 1; } \
             std::process::exit(((s + t) % 126) as i32); }",
            33,
        ),
        // REFUTATION: the very FIRST push into `Vec::new()` (eager `cap = 1`
        // buffer) takes the fast path — no realloc ever runs. A fast path that
        // stored through a wrong pointer or failed to bump `len` diverges.
        (
            "vec_first_push_fast_path",
            "fn main() { let mut v: Vec<i64> = Vec::new(); v.push(41); \
             std::process::exit((v[0] + v.len() as i64) as i32); }",
            42,
        ),
        // REFUTATION: read `v[0]` and `v[len-1]` after EVERY push across ~6
        // realloc boundaries. The push continuation re-loads the data pointer
        // from the slot (the memory join); a continuation that kept a STALE
        // pre-grow pointer (realloc may move the buffer) reads freed memory
        // and diverges the order-sensitive accumulator.
        (
            "vec_push_read_interleaved",
            "fn main() { let mut v: Vec<i64> = Vec::new(); \
             let mut i = 0i64; let mut s = 0i64; \
             while i < 40 { v.push(i * 3 + 1); \
             s = s.wrapping_mul(7).wrapping_add(v[0] + v[v.len() - 1]); i += 1; } \
             std::process::exit(((s % 126 + 126) % 126) as i32); }",
            76,
        ),
        // REFUTATION: STRUCT-class element (`vec_struct_element_admissible`
        // aggregate-image store) across the same conditional-grow boundary —
        // `with_capacity(2)` + 3 pushes forces one fast path, one boundary
        // fill, one grow; the field-weighted order-sensitive checksum
        // diverges if either field lands at a wrong offset or the grow loses
        // an element image.
        (
            "vec_struct_push_grow_boundary",
            "struct P { a: i64, b: i64 } \
             fn main() { let mut v: Vec<P> = Vec::with_capacity(2); \
             let mut i = 0i64; \
             while i < 3 { v.push(P { a: i + 1, b: (i + 1) * 10 }); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s = s * 5 + v[j].a * 2 + v[j].b; j += 1; } \
             std::process::exit((s % 126) as i32); }",
            78,
        ),
        // `Vec::drain(start..)` — a to-END (suffix) drain. Dropping the Drain
        // truncates the Vec to `start` (no tail to shift). `[1,2,3,4,5].drain(2..)`
        // removes [3,4,5]; v = [1,2], so `len*10 + v[0] + v[1]` = 20 + 1 + 2 = 23.
        // A wrong post-drop length or shifted content diverges.
        (
            "vec_drain_suffix",
            "fn main() { let mut v = vec![1i32, 2, 3, 4, 5]; v.drain(2..); \
             std::process::exit(v.len() as i32 * 10 + v[0] + v[1]); }",
            23,
        ),
        // `Vec::drain(..)` — the full-range drain-all, REGRESSION for the suffix
        // rework (the post-drop length must be 0). v cleared -> len 0.
        (
            "vec_drain_full",
            "fn main() { let mut v = vec![1i32, 2, 3, 4, 5]; v.drain(..); \
             std::process::exit(v.len() as i32); }",
            0,
        ),
        // `Vec::drain(start..)` then REUSE the truncated Vec (push). drain(1..)
        // leaves [10]; push(99) -> [10, 99]; `len*50 + v[0] + v[1]` = 100+10+99 = 209.
        (
            "vec_drain_suffix_reuse",
            "fn main() { let mut v = vec![10i32, 20, 30, 40]; v.drain(1..); v.push(99); \
             std::process::exit((v.len() as i32 * 50 + v[0] + v[1]) & 0xFF); }",
            209,
        ),
        // `for x in v.drain(start..)` — ITERATE the drained suffix (the Drain
        // into_iter-identity + modeled next), THEN the drop truncates the Vec.
        // drain(2..) yields 3,4,5 (s=12); v = [1,2]; `s + len*10 + v[0] + v[1]`
        // = 12 + 20 + 1 + 2 = 35. Wrong yield set, or a drop that failed to
        // truncate, diverges.
        (
            "vec_drain_suffix_iter",
            "fn main() { let mut v = vec![1i32, 2, 3, 4, 5]; let mut s = 0i32; \
             for x in v.drain(2..) { s += x; } \
             std::process::exit(s + v.len() as i32 * 10 + v[0] + v[1]); }",
            35,
        ),
        // `for x in v.into_iter()` — the EXPLICIT by-value iterator (vec::IntoIter
        // into_iter-identity + modeled next + buffer-freeing drop). Distinct from
        // the common `for x in v` (single `Vec::into_iter`). Sum 3+4+5 = 12.
        (
            "vec_explicit_into_iter",
            "fn main() { let v = vec![3i32, 4, 5]; let mut s = 0i32; \
             for x in v.into_iter() { s += x; } std::process::exit(s); }",
            12,
        ),
        // `Vec::extend_from_within(0..2)` — clone `self[0..2]` and append.
        // [10,20,30] -> [10,20,30,10,20]; `len*10 + v[3] + v[4]` = 50 + 10 + 20 = 80.
        (
            "vec_extend_from_within",
            "fn main() { let mut v = vec![10i32, 20, 30]; v.extend_from_within(0..2); \
             std::process::exit(v.len() as i32 * 10 + v[3] + v[4]); }",
            80,
        ),
        // `extend_from_within` where the buffer is FULL (`with_capacity(3)` + 3 pushes),
        // so the append forces a REALLOC. The source `[0..3]` base must be re-read from
        // the POST-grow buffer — a stale pre-grow pointer reads freed memory and
        // diverges. [10,20,30] -> [10,20,30,10,20,30]; `len*10 + v[3..6]` = 60+60 = 120.
        (
            "vec_extend_from_within_realloc",
            "fn main() { let mut v = Vec::with_capacity(3); \
             v.push(10i32); v.push(20); v.push(30); v.extend_from_within(0..3); \
             std::process::exit(v.len() as i32 * 10 + v[3] + v[4] + v[5]); }",
            120,
        ),
        // `Vec::reserve(additional)` GUARANTEE: `capacity() >= len + additional` after
        // the call (grow to len+additional). `[1,2,3].reserve(10)` -> cap >= 13; then
        // two pushes. `(cap_ok?100:0) + sum` = 100 + (1+2+3+4+5) = 115. A no-op reserve
        // (cap unchanged, < 13) would diverge to 15.
        (
            "vec_reserve_capacity",
            "fn main() { let mut v = vec![1i32, 2, 3]; v.reserve(10); \
             let ok = v.capacity() >= 13; v.push(4); v.push(5); \
             std::process::exit((if ok { 100 } else { 0 }) \
             + v.iter().copied().fold(0i32, |a, b| a + b)); }",
            115,
        ),
        // `reserve` then a burst of pushes must keep every element intact (the reserved
        // buffer holds them; a mis-sized grow would corrupt or lose one). [0,0] +
        // reserve(8) + push 1..=8 -> sum 36, len 10 -> 46.
        (
            "vec_reserve_then_push",
            "fn main() { let mut v = vec![0i32; 2]; v.reserve(8); \
             let mut i = 0i32; while i < 8 { v.push(i + 1); i += 1; } \
             std::process::exit(v.iter().copied().fold(0i32, |a, b| a + b) \
             + v.len() as i32); }",
            46,
        ),
        // `Vec::resize_with(n, f)` with a STATEFUL `FnMut` — each new element is a
        // fresh `f()` call that mutates captured state, in order. [1,2] + resize_with(5,
        // ||{c+=1;c}) with c=10 -> pushes 11,12,13 -> [1,2,11,12,13], sum 39. A single
        // reused call, wrong order, or a constant fill diverges.
        (
            "vec_resize_with_fnmut",
            "fn main() { let mut v = vec![1i32, 2]; let mut c = 10; \
             v.resize_with(5, || { c += 1; c }); \
             std::process::exit(v.iter().copied().fold(0i32, |a, b| a + b)); }",
            39,
        ),
        // `resize_with` GROW that forces a REALLOC (buffer full), stateful closure —
        // the fill's data pointer must come from the post-grow buffer. with_capacity(2)
        // + 2 pushes (full) + resize_with(5, ||{c+=1;c}) c=100 -> pushes 101,102,103;
        // sum 1+2+101+102+103 = 309 -> & 0xFF = 53.
        (
            "vec_resize_with_realloc",
            "fn main() { let mut v = Vec::with_capacity(2); v.push(1i32); v.push(2); \
             let mut c = 100; v.resize_with(5, || { c += 1; c }); \
             std::process::exit((v.iter().copied().fold(0i32, |a, b| a + b)) & 0xFF); }",
            53,
        ),
        // `resize_with` TRUNCATE (n < len): drops the tail, no `f()` calls. [5,6,7,8] ->
        // [5,6]; `len*10 + v[0] + v[1]` = 20 + 5 + 6 = 31.
        (
            "vec_resize_with_truncate",
            "fn main() { let mut v = vec![5i32, 6, 7, 8]; v.resize_with(2, || 0); \
             std::process::exit(v.len() as i32 * 10 + v[0] + v[1]); }",
            31,
        ),
        // `Vec::extend` from a BY-VALUE array `[a, b, c]` (`v.extend([3, 4, 5])`). Grow +
        // copy the N array elements (source is a disjoint stack array — no stale pointer,
        // no free). [1,2] -> [1,2,3,4,5]; `len*10 + v[2] + v[4]` = 50 + 3 + 5 = 58.
        (
            "vec_extend_array",
            "fn main() { let mut v = vec![1i32, 2]; v.extend([3, 4, 5]); \
             std::process::exit(v.len() as i32 * 10 + v[2] + v[4]); }",
            58,
        ),
        // `extend([..])` that forces a REALLOC (buffer full) — the array source is
        // disjoint from the (reallocated) dest buffer, so the copy stays valid.
        // with_capacity(2) + 2 pushes (full) + extend([3,4,5,6]) -> [1,2,3,4,5,6], sum 21.
        (
            "vec_extend_array_realloc",
            "fn main() { let mut v = Vec::with_capacity(2); v.push(1i32); v.push(2); \
             v.extend([3, 4, 5, 6]); \
             std::process::exit(v.iter().copied().fold(0i32, |a, b| a + b)); }",
            21,
        ),
        // `Vec<char>` byte-movement: a `char` is a 4-byte scalar (U32), byte-identical to
        // `u32`, so the byte-mover lowerings handle it. `vec!['a','b','c']` (box_into_vec);
        // read back v[0]='a'=97 + len 3 = 100.
        (
            "vec_char_literal",
            "fn main() { let v = vec!['a', 'b', 'c']; \
             std::process::exit(v[0] as i32 + v.len() as i32); }",
            100,
        ),
        // `Vec<char>` via `to_vec` then extend: [a,b,c,d].to_vec() extended with [e,f].
        // len 6, v[5]='f'=102 -> 108.
        (
            "vec_char_to_vec_extend",
            "fn main() { let mut v = ['a', 'b', 'c', 'd'].to_vec(); v.extend(['e', 'f']); \
             std::process::exit(v[5] as i32 + v.len() as i32); }",
            108,
        ),
        // `Vec::extend` from an ITERATOR CHAIN (`v.extend((2..5).map(|x| x*10))`): drive
        // the chain and push each element onto the existing Vec ("collect into existing").
        // [1] + [20,30,40] -> sum 91.
        (
            "vec_extend_iter_map",
            "fn main() { let mut v = vec![1i32]; v.extend((2..5).map(|x| x * 10)); \
             std::process::exit(v.iter().copied().fold(0i32, |a, b| a + b)); }",
            91,
        ),
        // `extend` from a `.filter().copied()` chain over a DISJOINT source Vec — the
        // push-grow of `self` cannot invalidate the source cursor. [10] + evens of
        // [1,2,3,4] = 10 + 2 + 4 = 16.
        (
            "vec_extend_iter_filter",
            "fn main() { let mut v = vec![10i32]; let o = vec![1i32, 2, 3, 4]; \
             v.extend(o.iter().filter(|&&x| x % 2 == 0).copied()); \
             std::process::exit(v.iter().copied().fold(0i32, |a, b| a + b)); }",
            16,
        ),
        // `Vec<bool>` byte-movement: bool is a 1-byte scalar the store path handles. EXACT
        // read-back `vec![true, false, true]` -> `v[0]*100 + v[1]*10 + v[2]` = 101 catches
        // any mis-sized Bool store (a full-register store would corrupt neighbours).
        (
            "vec_bool_readback",
            "fn main() { let v = vec![true, false, true]; \
             std::process::exit((v[0] as i32) * 100 + (v[1] as i32) * 10 + (v[2] as i32)); }",
            101,
        ),
        // `Vec<bool>` via `collect` from an iterator, then read back: [t,f,t] -> 2 trues,
        // len 3 -> 23.
        (
            "vec_bool_collect",
            "fn main() { let v: Vec<bool> = [true, false, true].into_iter().collect(); \
             std::process::exit(v.iter().filter(|&&b| b).count() as i32 * 10 + v.len() as i32); }",
            23,
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

/// A `Vec` that is *dropped* (freed) on a normal return path must leave no leaked
/// allocation — the bridge's `Drop` -> `__rust_dealloc` actually runs. We run the
/// trust-cg binary under macOS `leaks` and assert zero leaked bytes (a missing
/// free would leak the buffer; a double free would crash, which `leaks` reports
/// as a non-zero exit / abort). Guard-edge malloc would additionally trap a
/// grow that overran its buffer.
#[test]
fn dropped_vec_frees_its_buffer() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if Command::new("leaks").arg("--help").output().is_err() {
        eprintln!("skipping: `leaks` tool unavailable");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("leak");

    // `build` returns normally, so the `Vec` is dropped (freed) inside it before
    // `main` exits — the leak check therefore exercises the real free path.
    let src = "fn build() -> i64 { let mut v: Vec<i64> = Vec::new(); \
               let mut i = 1i64; while i <= 50 { v.push(i); i += 1; } \
               let mut s = 0i64; let mut j = 0usize; \
               while j < v.len() { s += v[j]; j += 1; } s } \
               fn main() { std::process::exit((build() % 251) as i32); }";
    let bin = compile(&dir, "vec_leak_tcg", src, Some(&dylib));

    let output = Command::new("leaks")
        .arg("--atExit")
        .arg("--")
        .arg(&bin)
        .output()
        .expect("run under leaks");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        combined.contains("0 leaks for 0 total leaked bytes"),
        "trust-cg Vec did not free cleanly under `leaks`; output: <<<{combined}>>>"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// The iterator-based `Vec` sum (`v.iter().sum::<i64>()`) now LOWERS at -O0: the
/// bridge intercepts `<Vec<T> as Deref>::deref` (binding the `&[T]` slice's
/// `{ data, len }` to the Vec's `ptr`/`len`), so the subsequent `slice::iter()`
/// + `sum()` consumer drives the Vec's buffer directly. (This was previously a
/// fail-closed blocker — the `Vec::deref` interception, added alongside `collect`
/// and `sort`, promoted it into the run+match set.) `1..=10` sums to 55.
///
/// NOTE: a LONGER push-then-iter-sum shape (e.g. a `for i in 0..50` build) still
/// fails closed on a SEPARATE SSA/loop-completeness limit unrelated to the deref;
/// this short `while`-loop form is the one that lowers cleanly.
#[test]
fn vec_iter_sum_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("iter");

    let src = "fn main() { let mut v: Vec<i64> = Vec::new(); let mut i = 1i64; \
               while i <= 10 { v.push(i); i += 1; } \
               let s: i64 = v.iter().sum(); std::process::exit(s as i32); }";

    // Both backends compile + run it; the exit codes must match (= 55). A wrong
    // sum (e.g. a dropped element or a bad slice length) would be a miscompile.
    let llvm_bin = compile(&dir, "vec_iter_llvm", src, None);
    assert_eq!(run_exit_code(&llvm_bin), 55, "LLVM Vec iter-sum should be 55");

    let tcg_bin = compile(&dir, "vec_iter_tcg", src, Some(&dylib));
    assert_eq!(
        run_exit_code(&tcg_bin),
        55,
        "trust-cg Vec iter-sum should match LLVM (55)"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
