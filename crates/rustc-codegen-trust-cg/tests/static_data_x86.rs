// Integration test: STATIC DATA / const-allocation lowering — string literals,
// `&'static` references, const tables, and `&str`/`&[T]` slices — compiled for
// x86_64 via the rustc_codegen_trust_cg bridge, COMPILED, LINKED, and RUN, with
// exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The keystone covered here is a Rust constant whose value is (or contains) a
// pointer into a const-eval ALLOCATION — a `&'static T`, a string/byte literal,
// a `const`/`static` table referenced by value or by `&`, a `&str`/`&[T]` slice.
// The bridge materializes each allocation as a trust-ir module GLOBAL (its bytes,
// with provenance pointers emitted as `Constant::SymbolAddr` data relocations,
// recursively) and produces the pointer as the global's data-relocated address.
// String/byte-string literals and slices become the `{ data, len }` fat-pointer
// split the slice machinery consumes (data = the global address, len = the
// const-known length).
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). This is a strict
// differential: a wrong static byte or relocation address shows up as a
// mismatched exit code. The programs are compiled at `-Copt-level=3` so the
// `str::len` / `str::as_bytes` / slice-index calls inline to the `PtrMetadata` /
// `Transmute` / element-load forms the const-data + slice machinery models (at
// `-Copt-level=0` those remain out-of-line library calls — a separate, larger
// fat-pointer-ABI feature — and the bridge fails closed on them, never
// miscompiling). The static-ref / byte-string / const-table data cases pass at
// every opt level; the level is held common to both backends so the comparison
// stays a true like-for-like differential.

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
    assert!(status.success(), "cargo build failed; cannot run static-data test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_sd_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the given backend (None = default LLVM) at `opt_level`.
/// On success returns `Ok(binary_path)`; on a compile failure returns
/// `Err(stderr)`.
fn try_compile_at(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt_level: &str,
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
    cmd.args(["--target", TARGET, "-Cpanic=abort", opt_level])
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

fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    try_compile_at(dir, name, src, backend, OPT_LEVEL)
}

fn compile_at(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt_level: &str,
) -> PathBuf {
    match try_compile_at(dir, name, src, backend, opt_level) {
        Ok(bin) => bin,
        Err(stderr) => panic!(
            "compile of `{name}` failed ({} backend, {opt_level}). stderr: <<<{stderr}>>>",
            if backend.is_some() { "trust-cg" } else { "llvm" },
        ),
    }
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    compile_at(dir, name, src, backend, OPT_LEVEL)
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The full differential: each static-data `fn main` is compiled by trust-cg AND
/// LLVM, run, and the exit codes must match each other and the expected value.
#[test]
fn static_data_runs_and_matches_llvm() {
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
        // 1. A `&'static T` scalar reference: `&X` is the data-relocated address
        //    of `static X`'s materialized global; the deref reads its bytes (5).
        (
            "static_ref",
            "static X: i64 = 5; \
             fn main(){ std::process::exit(*(&X) as i32); }",
            5,
        ),
        // 2. A `const TABLE: [i64; N]` referenced BY VALUE and indexed: the array
        //    constant is materialized and read element-wise (TABLE[2] == 30).
        (
            "const_table",
            "const TABLE: [i64; 5] = [10, 20, 30, 40, 50]; \
             fn main(){ std::process::exit(TABLE[2] as i32); }",
            30,
        ),
        // 3. A string literal's bytes accessed by index: `\"ABCDE\".as_bytes()[2]`
        //    is the byte `C` == 67. The `&str` literal's bytes become a global; the
        //    `&[u8]` view is the `{ data, len }` fat pointer; the element load
        //    reads `data + 2`.
        (
            "str_byte_index",
            "fn main(){ let s = \"ABCDE\"; std::process::exit(s.as_bytes()[2] as i32); }",
            67,
        ),
        // 4. A `&str` length: `\"hello\".len()` reads the fat pointer's metadata
        //    (the const-known length 5).
        (
            "str_len",
            "fn main(){ std::process::exit(\"hello\".len() as i32); }",
            5,
        ),
        // 5. A slice over a const array: `&A as &[i64]` unsizes the array's global
        //    address + length, and `s[i]` element-loads through the data pointer.
        (
            "slice_over_const_array",
            "const A: [i64; 4] = [7, 8, 9, 10]; \
             fn main(){ let s: &[i64] = &A; \
             let i = std::hint::black_box(2usize); \
             std::process::exit(s[i] as i32); }",
            9,
        ),
        // 6. A byte-string literal `b\"...\"` (a thin `&[u8; N]` pointer into the
        //    bytes global) indexed directly.
        (
            "byte_string_literal",
            "fn main(){ let s = b\"ABCDE\"; std::process::exit(s[2] as i32); }",
            67,
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

/// PTR-BEARING STATICS: a `static` whose initializer BYTES contain pointer
/// relocations — `static GREETING: &str = "hello"` (a `&str`/`&[T]`/`&T`/fn-ptr
/// referencing another allocation). The definition is emitted through the same
/// `SymbolAddr` data-relocation machinery vtables use (each referenced anonymous
/// allocation becomes an owner-prefixed Internal global; the relocation slot
/// becomes `SymbolAddr(+addend)`), the canonical symbol is exported, and READERS
/// import that canonical symbol (an initializer-less External global — the
/// `static mut` reader shape) so the static's pointer VALUE is identical in
/// every function/object (`ptr::eq` on its pointee holds, the
/// `ptr_value_identity` case).
///
/// Runs at O0 AND O3 (unlike the base test's O3-only cases, the fat-pointer
/// deref-load reader arm covers the out-of-line O0 forms too).
#[test]
fn ptr_bearing_static_data_runs_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("ptrbearing");

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // A `&str` static: the fat pointer's data half is a relocation to the
        // "hello" byte allocation, the len half is plain bytes. `.len()` reads
        // the metadata through the canonical-symbol import.
        (
            "static_str_len",
            "static GREETING: &str = \"hello\"; \
             fn main(){ std::process::exit(GREETING.len() as i32); }",
            5,
        ),
        // A `&[i32]` static: len (3) * 10 + element read NUMS[1] (2) — the
        // element load proves the relocation resolves to the RIGHT bytes.
        (
            "static_slice_len_index",
            "static NUMS: &[i32] = &[1, 2, 3]; \
             fn main(){ std::process::exit((NUMS.len() as i32) * 10 + NUMS[1]); }",
            32,
        ),
        // A thin `&i32` static: deref reads the pointee through the relocation.
        (
            "static_thin_ref",
            "static P: &i32 = &7; fn main(){ std::process::exit(*P); }",
            7,
        ),
        // Pointee DATA correctness: sum the referenced string's bytes through a
        // fn boundary ('h'+'e'+'l'+'l'+'o' = 532; % 97 = 47) + NUMS[2]/10 (3).
        (
            "static_pointee_bytes",
            "static GREETING: &str = \"hello\"; \
             static NUMS: &[i32] = &[10, 20, 30]; \
             #[inline(never)] fn sum_bytes(s: &str) -> i32 { \
                 let mut acc = 0i32; \
                 for &b in s.as_bytes() { acc = acc.wrapping_add(b as i32); } \
                 acc } \
             fn main(){ std::process::exit(sum_bytes(GREETING) % 97 + NUMS[2] / 10); }",
            50,
        ),
        // A nested `&&i32` reference chain: Memory -> Memory recursion.
        (
            "static_nested_ref_chain",
            "static DEEP: &&i32 = &&9; fn main(){ std::process::exit(**DEEP); }",
            9,
        ),
        // A byte-string `&[u8]` static, len + element read.
        (
            "static_byte_slice",
            "static BYTES: &[u8] = b\"abc\"; \
             fn main(){ std::process::exit(((BYTES.len() * 100 + BYTES[2] as usize) % 97) as i32); }",
            11,
        ),
        // A NONZERO ADDEND: `&ARR[1]` points 4 bytes INTO the interned const
        // array allocation (also a 12-byte, non-8-multiple nested global — the
        // padding path).
        (
            "static_elem_addend",
            "const ARR: [i32; 3] = [10, 20, 30]; static P1: &i32 = &ARR[1]; \
             fn main(){ std::process::exit(*P1); }",
            20,
        ),
        // A fn-pointer static: the relocation is the FUNCTION's own symbol (the
        // vtable Method-slot shape); calling through it must reach the fn.
        (
            "static_fn_ptr",
            "fn double(x: i32) -> i32 { x * 2 } \
             static F: fn(i32) -> i32 = double; \
             fn main(){ std::process::exit(F(21)); }",
            42,
        ),
        // A ptr-bearing `static mut`, read-only use: definition + canonical
        // import compose with the writable-static (E-slice) machinery.
        (
            "static_mut_str_read",
            "static mut MSG: &str = \"hello\"; \
             #[inline(never)] fn get_len() -> usize { unsafe { MSG.len() } } \
             fn main(){ std::process::exit(get_len() as i32); }",
            5,
        ),
        // A `static mut &mut i32` (promoted MUTABLE cell = a nested static):
        // the relocation resolves to the cell's CANONICAL symbol; writing then
        // reading through it observes the one shared cell.
        (
            "static_mut_shared_cell",
            "static mut X: &mut i32 = &mut 42; \
             fn main(){ unsafe { *X = 7; std::process::exit(*X); } }",
            7,
        ),
        // Pointer-VALUE identity: the SAME static's data pointer read from two
        // functions must be one address (the canonical-symbol import model;
        // per-reader private copies would make this 0 while LLVM gives 1).
        (
            "ptr_value_identity",
            "static G: &str = \"hello\"; \
             #[inline(never)] fn p1() -> *const u8 { G.as_ptr() } \
             #[inline(never)] fn p2() -> *const u8 { G.as_ptr() } \
             fn main(){ std::process::exit(std::ptr::eq(p1(), p2()) as i32); }",
            1,
        ),
    ];

    for opt_level in ["-Copt-level=0", "-Copt-level=3"] {
        for (name, src, expected) in shapes {
            let name = format!("{name}_{}", &opt_level[opt_level.len() - 1..]);
            let llvm_bin = compile_at(&dir, &format!("{name}_llvm"), src, None, opt_level);
            let tcg_bin = compile_at(&dir, &format!("{name}_tcg"), src, Some(&dylib), opt_level);
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
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// The ptr-bearing-static shapes that must keep their SOUND REJECTION (fail
/// closed, never wrong bytes/identity):
///
///   * a vtable-bearing `static D: &dyn Trait` (dedicated lowering path).
///
/// The former cross-static-to-an-IMMUTABLE-static rejections (`static R: &i64 =
/// &A`, `static T: [&i64; 3] = [&A, &B, &C]`, a struct with a `&'static` field)
/// NOW COMPILE AND RUN CORRECTLY via canonical weak-linked statics
/// [WEAKLINK-1 Part 2] — see `m130_cross_static_ptreq_x86` (they were the STAT-1
/// hazard: `ptr::eq(R, &A)` was tcg=0 vs llvm=1). Only the vtable shape (and a
/// FOREIGN immutable target, not exercisable in a single-file test) stays
/// fail-closed here.
#[test]
fn cross_static_and_vtable_statics_still_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("ptrbearing_neg");

    // (name, source, required rejection substring).
    let rejects: &[(&str, &str, &str)] = &[
        (
            "dyn_vtable_static",
            "trait T { fn v(&self) -> i32; } struct S; \
             impl T for S { fn v(&self) -> i32 { 3 } } \
             static D: &(dyn T + Sync) = &S; \
             fn main(){ std::process::exit(D.v()); }",
            "vtable / type-id allocation",
        ),
    ];

    for (name, src, needle) in rejects {
        // LLVM compiles and runs these fine (sanity that the source is valid).
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None);
        let _ = run_exit_code(&llvm_bin);
        // trust-cg must FAIL CLOSED with the precise named diagnostic.
        match try_compile(&dir, &format!("{name}_tcg"), src, Some(&dylib)) {
            Ok(_) => panic!(
                "`{name}` unexpectedly compiled under trust-cg; it must fail closed \
                 (sound rejection: {needle})"
            ),
            Err(stderr) => assert!(
                stderr.contains(needle),
                "`{name}` failed for the wrong reason (wanted a rejection containing \
                 {needle:?}). stderr: <<<{stderr}>>>"
            ),
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
