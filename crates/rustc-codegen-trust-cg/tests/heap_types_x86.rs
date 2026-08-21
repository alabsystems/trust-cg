#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: heap-allocating std Rust (`Box<T>`) compiled for x86_64 via
// the rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS4 — owned heap values (`Box<T>`) RUN on x86_64 through trust-cg.
//
// This is the heap milestone: a std `fn main` that allocates on the Rust global
// heap (`Box::new`), computes through the box pointer (read, write-through), and
// — crucially — *frees* the box (its `Drop` runs `__rust_dealloc`). The bridge:
//
//   * maps a `Box<T>` to its single niche pointer (`*const T`): the
//     `pattern_type!(*const T is !null)` of `NonNull<T>`'s field is treated as a
//     plain pointer (`ty::Pat` -> base type), so the
//     `Box(Unique(NonNull(*const T)))` newtype chain collapses to one scalar;
//   * intercepts `Box::<T>::new(x)` (whose real MIR descends into unlowerable
//     `Layout`/`Alignment` machinery) and synthesizes the allocation directly:
//     `__rust_alloc(size_of::<T>, align_of::<T>)` + a store of `x`, binding the
//     destination to the returned pointer;
//   * lowers the `Drop` terminator: for a `Box<T>` with a no-drop payload it
//     frees the storage with `__rust_dealloc(ptr, size, align)` (matching what
//     `drop_in_place::<Box<T>>` -> `<Box as Drop>::drop` -> `Global::deallocate`
//     does) then threads the normal successor; under `-Cpanic=abort` there is no
//     unwind edge. A no-drop value drops to nothing (just a branch);
//   * supports raw-pointer (`*const T`/`*mut T`) deref load/store (how a box
//     reads and writes its payload), `Transmute`/`PtrToPtr` pointer casts, the
//     pointer-deref validity asserts (`MisalignedPointerDereference` /
//     `NullPointerDereference`), and const-evaluation of the `SizedTypeProperties`
//     `SIZE`/`ALIGN` associated consts those asserts reference.
//
// The `__rust_alloc`/`__rust_dealloc` symbols are provided by the bridge's own
// default-allocator shim (which forwards to libstd's `__rdl_*` System
// allocator); libc provides the underlying malloc/free.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A wrong heap result —
// or a missing free — is a miscompile, so equal exit codes plus a clean process
// teardown is the differential we assert.
//
// NOTE on `Vec`: a `Vec<i64>` push+sum now COMPILES and RUNS via trust-cg — see
// `tests/vec_x86.rs` for the run-and-match-LLVM differential. The bridge skips
// the ZST `PhantomData`/`Global` fields of `Vec`/`RawVec` when flattening, and
// intercepts the `Vec` methods (`new`/`with_capacity`/`push`/`len`/index/`Drop`)
// just as it intercepts `Box::new`, synthesizing them against the allocator on a
// `{ptr,cap,len}` stack slot. The fail-closed test below was removed once `Vec`
// lowered; iter-based `Vec` sums (the `Vec -> slice -> Iter -> Sum` path) still
// fail closed precisely and are covered in `tests/vec_x86.rs`.

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
    assert!(status.success(), "cargo build failed; cannot run heap test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_heap_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Run rustc on `src` with the given backend (None = default LLVM). Returns the
/// full `Output` so callers can assert success or inspect a fail-closed
/// diagnostic. The binary path is `dir/name`.
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

/// The full differential: each heap-allocating `Box` program is compiled by
/// trust-cg AND LLVM, run, and the exit codes must match each other and the
/// expected value. A divergence is a miscompile (wrong heap value or a
/// crash/abort from a bad free).
#[test]
fn box_programs_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("box");

    // (name, source, expected exit code). Each boxes an integer, computes
    // through the box, and exits with the (byte-truncated) result.
    let shapes: &[(&str, &str, i32)] = &[
        // The canonical goal: box 0, sum 1..=10 through it into a second box,
        // exit with the result. Two `Box::new` allocations; both leak only at
        // `exit` (which diverges), exactly as under LLVM.
        (
            "box_sum",
            "fn main() { let b = Box::new(0i64); let mut s = *b; let mut i = 1i64; \
             while i <= 10 { s += i; i += 1; } let r = Box::new(s); \
             std::process::exit(*r as i32); }",
            55,
        ),
        // A `Box<i32>` read straight through to the exit code.
        (
            "box_i32",
            "fn main() { let b = Box::new(42i32); std::process::exit(*b); }",
            42,
        ),
        // A `Box<u32>` read + arithmetic (different element width / signedness).
        (
            "box_u32",
            "fn main() { let b = Box::new(7u32); let v = *b; std::process::exit((v * 6) as i32); }",
            42,
        ),
        // Write-through a box (`*b += 10`): a deref-store to the heap storage.
        (
            "box_mut",
            "fn main() { let mut b = Box::new(3i64); *b += 10; std::process::exit(*b as i32); }",
            13,
        ),
        // A box that is *actually dropped* (freed) on a normal return path: the
        // `Drop` terminator -> `__rust_dealloc`. `compute` returns normally (the
        // box is dropped at scope end) before `main` exits with the result.
        (
            "box_drop",
            "fn compute() -> i64 { let b = Box::new(5i64); let s = *b; s + 1 } \
             fn main() { let r = compute(); std::process::exit(r as i32); }",
            6,
        ),
        // A box dropped after a loop that accumulates through its (read) value.
        (
            "box_loop_drop",
            "fn compute() -> i64 { let b = Box::new(0i64); let mut s = *b; let mut i = 1i64; \
             while i <= 10 { s += i; i += 1; } s } \
             fn main() { std::process::exit(compute() as i32); }",
            55,
        ),
        // AGGREGATE payload: `Box<S>` for a two-field struct. `Box::new(S{x,y})`
        // allocates `size_of::<S>` bytes and stores each scalar leaf at its layout
        // offset; the readback transmutes the box to `*const S` and loads `(*p).x`
        // / `(*p).y` at the SAME rustc-layout byte offsets. Exercises the
        // aggregate-Box alloc/store + the raw-pointer aggregate-deref readback.
        (
            "box_struct",
            "struct S{x:i32,y:i32} \
             fn main(){ let b=Box::new(S{x:3,y:4}); std::process::exit(b.x+b.y); }",
            7,
        ),
        // AGGREGATE payload: `Box<(i32,i32)>` for a tuple. Same path as the struct
        // case (tuples are excluded from `memory_aggregate_layout` but their leaves
        // are still fixed-offset scalars addressed lane-wise through the box ptr).
        (
            "box_tuple",
            "fn main(){ let b=Box::new((10i32,20i32)); std::process::exit(b.0+b.1); }",
            30,
        ),
        // AGGREGATE payload, write-through: mutate a boxed struct field in place
        // (`b.x += 5`, a deref-store to a heap aggregate leaf) then read it back.
        (
            "box_struct_mut",
            "struct S{x:i32,y:i32} \
             fn main(){ let mut b=Box::new(S{x:3,y:4}); b.x+=5; std::process::exit(b.x+b.y); }",
            12,
        ),
        // AGGREGATE payload that is *dropped* (freed): `Box<(i64,i64)>` summed and
        // dropped on a normal return path (the `Drop` -> `__rust_dealloc` with the
        // aggregate's `size_of`/`align_of`), before `main` exits with the result.
        (
            "box_struct_drop",
            "fn compute()->i64{ let b=Box::new((20i64,22i64)); let s=b.0+b.1; s } \
             fn main(){ std::process::exit(compute() as i32); }",
            42,
        ),
        // ZST payload: `Box::new(A)` for a field-less unit struct allocates nothing
        // (a dangling, well-aligned pointer == `NonNull::dangling()`) and stores no
        // payload bytes. The box crosses a function boundary and is dropped at scope
        // end — exercising the ZST alloc + the matching no-op ZST `Drop` (a size-0
        // box must NOT call `__rust_dealloc`) — before `main` exits with a
        // separately-computed value, so a stray free of the dangling pointer would
        // crash the process and diverge from LLVM.
        (
            "box_zst",
            "struct A; fn make()->Box<A>{ Box::new(A) } \
             fn main(){ let _b = make(); std::process::exit(7); }",
            7,
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

// (The former `vec_push_sum_fails_closed_with_precise_blocker` test was removed:
//  `Vec<i64>` now compiles and runs. The run-and-match-LLVM differential — plus
//  the precise fail-closed assertion for the still-unsupported iter-based sum —
//  lives in `tests/vec_x86.rs`.)
