#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: RUNTIME FAT-POINTER `&[T]` / `&str` VALUES across function
// boundaries — compiled for x86_64 via the rustc_codegen_trust_cg bridge,
// COMPILED, LINKED, and RUN, with exit codes checked against the default LLVM
// backend at the SAME optimization level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The keystone covered here is a `&[T]` / `&str` passed BY VALUE through a real
// (non-inlined) function boundary: a 2-eightbyte `{ data: *const T, meta: usize }`
// fat pointer in a SysV register pair (or returned in RAX:RDX). The const-slice
// machinery (a slice whose length is a compile-time constant, fully inlined into
// `main`) is covered by `static_data_x86`; here every helper is `#[inline(never)]`
// so the slice fat pointer must genuinely flow as a runtime value:
//   * a `fn f(s: &[T])` PARAMETER receives data+len in two registers; `s.len()`
//     reads the length half, `s[i]` loads `data + i*size_of::<T>()`.
//   * a `&str` parameter whose `.len()` is read and returned.
//   * slicing `&a[lo..hi]` produces a `{ data + lo*size, hi-lo }` pair that is
//     itself iterated.
//   * the slice is built from a STACK array's address (`&arr as &[T]`) at the
//     caller and passed across the boundary.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A wrong data pointer,
// length, or element load shows up as a mismatched exit code.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const OPT_LEVEL: &str = "-Copt-level=3";

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
    assert!(status.success(), "cargo build failed; cannot run slice-fatptr test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_slc_{stem}_{}", std::process::id()));
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
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", OPT_LEVEL])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if output.status.success() {
        Ok(bin)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    match try_compile(dir, name, src, backend) {
        Ok(bin) => bin,
        Err(stderr) => panic!(
            "compile of `{name}` failed ({} backend). stderr: <<<{stderr}>>>",
            if backend.is_some() { "trust-cg" } else { "llvm" },
        ),
    }
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The full differential: each slice-fat-pointer `fn main` is compiled by
/// trust-cg AND LLVM, run, and the exit codes must match each other and the
/// expected value.
#[test]
fn slice_fatptr_runs_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("cases");

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // 1. A `fn sum(s: &[i64]) -> i64` called with a slice of a STACK array.
        //    `s.len()` reads the runtime length half (`PtrMetadata`); `s[i]` loads
        //    `data + i*8`. Sum 1..=10 = 55.
        (
            "sum_slice",
            "#[inline(never)] \
             fn sum(s: &[i64]) -> i64 { \
                 let mut total = 0i64; let mut i = 0usize; \
                 while i < s.len() { total += s[i]; i += 1; } total } \
             fn main(){ let a: [i64; 10] = [1,2,3,4,5,6,7,8,9,10]; \
                 std::process::exit(sum(&a) as i32); }",
            55,
        ),
        // 2. A `fn first(s: &[i64]) -> i64 { s[0] }` — a single element load through
        //    the fat-pointer parameter's data half.
        (
            "first_elem",
            "#[inline(never)] \
             fn first(s: &[i64]) -> i64 { s[0] } \
             fn main(){ let a: [i64; 4] = [42, 7, 8, 9]; \
                 std::process::exit(first(&a) as i32); }",
            42,
        ),
        // 3. A `fn strlen(s: &str) -> i32` returning the `&str`'s length: reads the
        //    metadata half of the fat pointer. `"hello"` has length 5.
        (
            "str_len_fn",
            "#[inline(never)] \
             fn strlen(s: &str) -> i32 { s.len() as i32 } \
             fn main(){ std::process::exit(strlen(\"hello\")); }",
            5,
        ),
        // 4. Slicing then summing: `sub_and_sum(&a)` slices `&a[1..4]` (a
        //    `{ data + 1*8, 3 }` subslice pair) and sums it: a[1]+a[2]+a[3]
        //    = 20+30+40 = 90.
        (
            "subslice_sum",
            "#[inline(never)] \
             fn sub_and_sum(a: &[i64]) -> i64 { \
                 let s = &a[1..4]; \
                 let mut t = 0i64; let mut i = 0usize; \
                 while i < s.len() { t += s[i]; i += 1; } t } \
             fn main(){ let a: [i64; 6] = [10,20,30,40,50,60]; \
                 std::process::exit(sub_and_sum(&a) as i32); }",
            90,
        ),
        // 5. Iterating a slice by index in a loop, accumulating: a max-finder over
        //    a `&[i64]` parameter. max(3, 1, 4, 1, 5, 9, 2, 6) = 9.
        (
            "max_slice",
            "#[inline(never)] \
             fn maxv(s: &[i64]) -> i64 { \
                 let mut m = s[0]; let mut i = 1usize; \
                 while i < s.len() { if s[i] > m { m = s[i]; } i += 1; } m } \
             fn main(){ let a: [i64; 8] = [3,1,4,1,5,9,2,6]; \
                 std::process::exit(maxv(&a) as i32); }",
            9,
        ),
        // 6. A slice passed THROUGH a helper to a second helper (threading the fat
        //    pointer across two boundaries), summing the result. 1+2+3+4 = 10.
        (
            "thread_slice",
            "#[inline(never)] \
             fn sum2(s: &[i64]) -> i64 { \
                 let mut t = 0i64; let mut i = 0usize; \
                 while i < s.len() { t += s[i]; i += 1; } t } \
             #[inline(never)] \
             fn forward(s: &[i64]) -> i64 { sum2(s) } \
             fn main(){ let a: [i64; 4] = [1,2,3,4]; \
                 std::process::exit(forward(&a) as i32); }",
            10,
        ),
        // 7. `as_ptr` + length: a helper reads the first element via `s.as_ptr()`
        //    (the data half) and adds the length (the meta half). first=100, len=3
        //    => 103.
        (
            "as_ptr_len",
            "#[inline(never)] \
             fn probe(s: &[i64]) -> i64 { \
                 let p = s.as_ptr(); \
                 let first = unsafe { *p }; \
                 first + s.len() as i64 } \
             fn main(){ let a: [i64; 3] = [100, 200, 300]; \
                 std::process::exit(probe(&a) as i32); }",
            103,
        ),
        // ADDRESS-TAKEN fat-pointer LOCAL. `<&str as PartialEq>::eq` takes `&&str`, so
        // `a == b` on `&str` LOCALS needs `&a`/`&b` — references to the fat-pointer
        // locals. A scalarized `{data,len}` local has no address, so `&a` produced a
        // GARBAGE thin pointer and the compare read junk: `"abc"=="abc"` MISCOMPILED to
        // false. Memory-backing the address-taken fat local fixes it (`&a` = slot addr).
        (
            "str_eq_local",
            "fn main(){ let a = \"abc\"; let b = \"abc\"; \
                 std::process::exit(if a == b { 7 } else { 9 }); }",
            7,
        ),
        // The same for a bare `&(fat &str local)` read through a `&&str` param — the
        // isolated repro. `takeref(&a).len()` returned garbage (128) pre-fix; 3 now.
        (
            "ref_to_str_local_len",
            "#[inline(never)] fn takeref(r: &&str) -> usize { r.len() } \
             fn main(){ let a = \"abc\"; std::process::exit(takeref(&a) as i32); }",
            3,
        ),
        // `mem::swap` of two `&str` — `typed_swap_nonoverlapping::<&str>`. A fat pointer
        // collapses to one thin `Ptr` in the scalar swap path, which would swap only the
        // data half and TEAR the length (fail-closed pre-fix); the fat swap exchanges
        // BOTH {data,len} lanes. Content-checked: after swap a=="longer" (len 6), b=="short".
        (
            "mem_swap_str",
            "fn main(){ let mut a = \"short\"; let mut b = \"longer\"; \
                 std::mem::swap(&mut a, &mut b); \
                 std::process::exit(if a == \"longer\" && b == \"short\" { a.len() as i32 } \
                     else { 0 }); }",
            6,
        ),
        // `mem::swap` of two `&[i32]` slices of DIFFERENT lengths — the length lane must
        // travel with the data lane. After swap a.len()==4, b.len()==3 -> 43.
        (
            "mem_swap_slice",
            "fn main(){ let x = [1i32, 2, 3]; let y = [4i32, 5, 6, 7]; \
                 let mut a: &[i32] = &x; let mut b: &[i32] = &y; \
                 std::mem::swap(&mut a, &mut b); \
                 std::process::exit((a.len() * 10 + b.len()) as i32); }",
            43,
        ),
        // POST-CONSTRUCTION fat-pointer FIELD write (`t.0 = t.1`). A single-lane store
        // would leave a TORN {data,len} (stale length); both lanes must be written
        // TOGETHER at the field offset. After `t.0 = t.1` both hold \"bbbb\": verify the
        // LENGTH lane (4) AND the DATA lane (first byte 'b').
        (
            "fat_field_write_f2f",
            "fn main(){ let mut t = (\"aa\", \"bbbb\"); t.0 = t.1; \
                 std::process::exit(if t.0.len() == 4 && t.0.as_bytes()[0] == b'b' \
                     { t.0.len() as i32 } else { 0 }); }",
            4,
        ),
        // The TORN-WRITE stress: overwrite a LONG field with a SHORT string. If only the
        // data lane were written, the length lane would stay 10 (stale) — an OOB hazard.
        // Correct = len shrinks to 1 and the data is 'z'.
        (
            "fat_field_write_shrink",
            "fn main(){ let mut t = (\"longstring\", \"z\"); t.0 = t.1; \
                 std::process::exit(if t.0.len() == 1 && t.0.as_bytes()[0] == b'z' { 7 } \
                     else { t.0.len() as i32 }); }",
            7,
        ),
        // A const `&str` LITERAL written into a struct field (`r.a = \"hello\"`), the
        // other field left intact — both lanes of both fields correct.
        (
            "fat_field_write_const",
            "struct R { a: &'static str, b: &'static str } \
             fn main(){ let mut r = R { a: \"x\", b: \"y\" }; r.a = \"hello\"; \
                 std::process::exit(if r.a.len() == 5 && r.a.as_bytes()[0] == b'h' \
                     && r.b.len() == 1 && r.b.as_bytes()[0] == b'y' { r.a.len() as i32 } \
                     else { 0 }); }",
            5,
        ),
        // Fat-pointer FIELD borrow for a comparison (`r.name == \"key\"`). This lowers
        // to `str::eq(&r.name, ..)`; `&r.name` is a THIN pointer to the field's
        // {data,len}. The generic field-borrow demanded a single scalar leaf and
        // rejected the fat pointer (`memory_scalar_leaf_ty`); the address-only walker
        // binds the field address so the fat leaf is read through it. Match arm -> 7.
        (
            "fat_field_eq",
            "struct R { name: &'static str, n: i32 } \
             fn main(){ let r = R { name: \"key\", n: 5 }; \
                 std::process::exit(if r.name == \"key\" && r.n == 5 { 7 } else { 9 }); }",
            7,
        ),
        // A `&mut` fat-field borrow written THROUGH a `&mut &str` param — the field
        // address must carry the whole {data,len} write. After it, r.name==\"changed\"
        // (len 7, first 'c').
        (
            "fat_field_mut_borrow",
            "struct R { name: &'static str } \
             fn setit(s: &mut &'static str) { *s = \"changed\"; } \
             fn main(){ let mut r = R { name: \"orig\" }; setit(&mut r.name); \
                 std::process::exit(if r.name.len() == 7 && r.name.as_bytes()[0] == b'c' \
                     { 7 } else { r.name.len() as i32 }); }",
            7,
        ),
        // Read a fat-pointer ELEMENT out of a `[&str; N]` array (`let s = a[i]`). The
        // array is memory-backed (fat-leaf); each element's {data,len} lives at
        // slot + i*16. A scalar-element read would truncate the length — so verify BOTH
        // lanes of EACH element (len AND first byte) after a const-index read.
        (
            "fat_array_element_read",
            "fn main(){ let a = [\"ab\", \"cde\", \"f\"]; \
                 let ok = a[0].len() == 2 && a[0].as_bytes()[0] == b'a' \
                     && a[1].len() == 3 && a[1].as_bytes()[0] == b'c' \
                     && a[2].len() == 1 && a[2].as_bytes()[0] == b'f'; \
                 std::process::exit(if ok { 7 } else { 9 }); }",
            7,
        ),
        // A RUNTIME-index element read (`a[i]` for a non-const `i`) — the element
        // address is `slot + i*16` via the runtime index walker. -> len of \"yyy\" = 3.
        (
            "fat_array_runtime_index",
            "fn main(){ let a = [\"xx\", \"yyy\", \"z\"]; let i = 1usize; \
                 let s = a[i]; std::process::exit(s.len() as i32); }",
            3,
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
