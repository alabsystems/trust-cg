#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: GENERAL-AGGREGATE memory-model lowering — by-value aggregate
// PARAMETERS (callee side, validated cross-backend), ADDRESS-TAKEN aggregate
// locals (mutation through `&mut`), and NESTED aggregate fields — compiled for
// x86_64 via the rustc_codegen_trust_cg bridge, COMPILED, LINKED, and RUN, with
// results checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// This is the second wave of the memory model, past the call/return boundary
// that the keystone `memory_model_x86` test covers:
//
//   * BY-VALUE AGGREGATE PARAMETERS (callee side): a `struct{a:i64,b:i64}` and a
//     `Result<i64,i64>` taken BY VALUE are validated by compiling the callee with
//     trust-cg (it stores the incoming SysV aggregate ABI value into a slot at
//     entry and reads it from memory) and calling it from an LLVM-compiled caller
//     that passes the aggregate per the System V ABI.
//
//   * BY-VALUE AGGREGATE CALL ARGUMENTS (caller side): a full-trust-cg program
//     constructs an aggregate and passes it BY VALUE to a function (the caller
//     passes the aggregate's slot/materialized address; the adapter seeds the
//     callee's aggregate parameter type onto the argument so the verified System
//     V eightbyte classifier places it correctly). Compiled by BOTH backends and
//     run; the trust-cg exit code must equal LLVM's. See
//     `by_value_aggregate_call_arguments_run_and_match_llvm`.
//
//   * ADDRESS-TAKEN aggregate locals: a `&mut struct` whose field is mutated
//     through the reference, the mutation observed by the caller (the local is
//     address-taken => slot-backed; `&mut p` lowers to the slot pointer).
//
//   * NESTED aggregate fields: a `struct Outer { inner: Inner{x,y}, z }` whose
//     deep fields are read, and a Direct-tagged enum `Shape { Origin, At(Pt{x,y}) }`
//     (an enum with a struct payload) matched and its nested fields summed.
//
// The address-taken and nested cases are full-program differentials: each is
// compiled with BOTH backends and run; the trust-cg exit code must equal the LLVM
// exit code (and the expected value). A miscompile shows up as a mismatch.

use std::ffi::OsString;
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

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let name = dylib_name();
    let candidates = [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
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
    assert!(status.success(), "cargo build failed; cannot run aggregate test");
    let built = target_dir.join("debug").join(&name);
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
    let dir = std::env::temp_dir().join(format!("rcl2_mma_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile a self-contained program binary with the given backend (None = LLVM).
fn compile_bin(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> Result<PathBuf, String> {
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
    if output.status.success() {
        Ok(bin)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
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

/// ADDRESS-TAKEN and NESTED aggregate cases as full-program differentials: each
/// is compiled by trust-cg AND LLVM, run, and the exit codes must match each
/// other and the expected value. `#[inline(never)]` keeps the aggregate crossing
/// a real call/return boundary, so the memory-model path is genuinely exercised.
#[test]
fn address_taken_and_nested_aggregates_run_and_match_llvm() {
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

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // A `&mut struct` whose field is mutated through the reference; the local
        // is address-taken => slot-backed, and the caller observes the write.
        // (5+10) + (11*2) = 15 + 22 = 37.
        (
            "mut_ref_struct_field",
            "use std::hint::black_box; \
             struct P { a: i64, b: i64 } \
             #[inline(never)] fn bump(p: &mut P) { p.a += 10; p.b *= 2; } \
             fn main(){ let mut p = P { a: black_box(5), b: black_box(11) }; \
             bump(&mut p); std::process::exit((p.a + p.b) as i32); }",
            37,
        ),
        // A NESTED struct-of-struct whose deep fields are read. 7 + 14 + 21 = 42.
        (
            "nested_struct_fields",
            "use std::hint::black_box; \
             struct Inner { x: i64, y: i64 } \
             struct Outer { inner: Inner, z: i64 } \
             #[inline(never)] fn make(v: i64) -> Outer { Outer { inner: Inner { x: v, y: v*2 }, z: v*3 } } \
             fn main(){ let o = make(black_box(7)); \
             std::process::exit((o.inner.x + o.inner.y + o.z) as i32); }",
            42,
        ),
        // A NESTED Direct-tagged enum (an enum with a struct payload), `At` arm.
        // x + y = 20 + 21 = 41.
        (
            "nested_direct_enum_at",
            "use std::hint::black_box; \
             struct Pt { x: i64, y: i64 } \
             enum Shape { Origin, At(Pt) } \
             #[inline(never)] fn make(n: i64) -> Shape { if n==0 { Shape::Origin } else { Shape::At(Pt { x: n, y: n+1 }) } } \
             fn main(){ let s = make(black_box(20)); \
             let r = match s { Shape::Origin => 1, Shape::At(p) => p.x + p.y }; \
             std::process::exit(r as i32); }",
            41,
        ),
        // The `Origin` (unit) arm of the same nested Direct-tagged enum.
        (
            "nested_direct_enum_origin",
            "use std::hint::black_box; \
             struct Pt { x: i64, y: i64 } \
             enum Shape { Origin, At(Pt) } \
             #[inline(never)] fn make(n: i64) -> Shape { if n==0 { Shape::Origin } else { Shape::At(Pt { x: n, y: n+1 }) } } \
             fn main(){ let s = make(black_box(0)); \
             let r = match s { Shape::Origin => 1, Shape::At(p) => p.x + p.y }; \
             std::process::exit(r as i32); }",
            1,
        ),
        // A NEWTYPE (single-scalar-field struct) `&self` METHOD receiver. `C` is
        // `adt_maps_to_single_scalar`, so `&C` is a THIN pointer to the bare scalar
        // (aggregate_reference_pointee declines the 1-field flatten) — the receiver
        // lowers through the same scalar-reference path as `&i32`, not the aggregate
        // borrow path (which fail-closed "before aggregate borrow binding"). 21*2 = 42.
        (
            "newtype_getter_method",
            "use std::hint::black_box; \
             struct C { n: i32 } \
             impl C { #[inline(never)] fn doubled(&self) -> i32 { self.n * 2 } } \
             fn main(){ let c = C { n: black_box(21) }; std::process::exit(c.doubled()); }",
            42,
        ),
        // A NEWTYPE `&mut self` setter whose write is observed through a later
        // `&self` getter — the scalar-reference `&mut` write-back must land in the
        // caller's binding. set(7) => 7.
        (
            "newtype_setter_method_writeback",
            "use std::hint::black_box; \
             struct C { n: i32 } \
             impl C { \
                 #[inline(never)] fn set(&mut self, v: i32) { self.n = v; } \
                 #[inline(never)] fn get(&self) -> i32 { self.n } \
             } \
             fn main(){ let mut c = C { n: black_box(1) }; c.set(black_box(7)); \
             std::process::exit(c.get()); }",
            7,
        ),
        // An INLINE by-ref destructure of a SCALARIZED struct: `let P { a, b } = &p`
        // binds `a`/`b` as `&i32` field refs `&((*&p).0)` through a borrowed-aggregate
        // base — no field ADDRESS exists, so each ref binds to the aggregate's
        // projected scalar (borrowed_scalar → Projection{p, field}), not a slot
        // pointer. Read side: 5 + 8 = 13.
        (
            "inline_ref_destructure_struct",
            "use std::hint::black_box; \
             struct P { a: i32, b: i32 } \
             fn main(){ let p = P { a: black_box(5), b: black_box(8) }; \
             let P { a, b } = &p; std::process::exit(a + b); }",
            13,
        ),
        // The `&mut` form: writes through the field refs must land in the projected
        // scalars. (5+10) + (8+20) = 15 + 28 = 43.
        (
            "inline_ref_destructure_struct_mut",
            "use std::hint::black_box; \
             struct P { a: i32, b: i32 } \
             fn main(){ let mut p = P { a: black_box(5), b: black_box(8) }; \
             let P { a, b } = &mut p; *a += 10; *b += 20; \
             std::process::exit(p.a + p.b); }",
            43,
        ),
        // The single-variant multi-field ENUM form: `match &e { E::P(a, b) => .. }`
        // takes `&((*&e as P).field)` refs — the Downcast is on the sole variant, so
        // the field index maps straight to the projected key. 5 + 8 = 13.
        (
            "inline_ref_match_enum",
            "use std::hint::black_box; \
             enum E { P(i32, i32) } \
             fn main(){ let e = E::P(black_box(5), black_box(8)); \
             let r = match &e { E::P(a, b) => a + b }; std::process::exit(r); }",
            13,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile_bin(&dir, &format!("{name}_llvm"), src, None)
            .unwrap_or_else(|e| panic!("LLVM compile of `{name}` failed: <<<{e}>>>"));
        let tcg_bin = compile_bin(&dir, &format!("{name}_tcg"), src, Some(&dylib))
            .unwrap_or_else(|e| panic!("trust-cg compile of `{name}` failed: <<<{e}>>>"));
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

/// WHOLE-AGGREGATE-VALUE element stores into a memory-backed aggregate-element
/// array: `a[i] = P{..}` (a runtime-indexed whole-struct store), the const-index
/// form `a[0] = P{..}`, and a `[(i32,i32); N]` tuple-element store. Each writes an
/// ENTIRE inner aggregate value at a (possibly runtime) element address by
/// decomposing it into its scalar leaves at fixed offsets; a later `a[i].field`
/// read must observe exactly those bytes. Differential against LLVM (exit codes
/// must match) at the gate's `-O` level.
#[test]
fn whole_aggregate_element_stores_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("whole_elem_store");

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // `a[i] = P{..}` at a RUNTIME index in a loop. a[0]={0,1}, a[1]={1,2};
        // a[0].y + a[1].x = 1 + 1 = 2.
        (
            "runtime_index_struct_store",
            "struct P{x:i32,y:i32} \
             fn main(){ let mut a=[P{x:0,y:0},P{x:0,y:0}]; let mut i=0; \
             while i<2 { a[i]=P{x:i as i32, y:(i as i32)+1}; i+=1; } \
             std::process::exit(a[0].y+a[1].x); }",
            2,
        ),
        // The const-index whole-element store form `a[0] = P{..}`.
        // a[0].y + a[1].x = 7 + 11 = 18.
        (
            "const_index_struct_store",
            "struct P{x:i32,y:i32} \
             fn main(){ let mut a=[P{x:0,y:0},P{x:0,y:0}]; \
             a[0]=P{x:5,y:7}; a[1]=P{x:11,y:13}; \
             std::process::exit(a[0].y+a[1].x); }",
            18,
        ),
        // A `[(i32,i32); N]` tuple-element whole store at a runtime index.
        // a[0]=(0,0), a[1]=(1,10); a[0].1 + a[1].0 + a[1].1 = 0 + 1 + 10 = 11.
        (
            "runtime_index_tuple_store",
            "fn main(){ let mut a=[(0i32,0i32),(0i32,0i32)]; let mut i=0; \
             while i<2 { a[i]=(i as i32, (i as i32)*10); i+=1; } \
             std::process::exit(a[0].1 + a[1].0 + a[1].1); }",
            11,
        ),
        // A CONST-GENERIC array repeat `[x; N]` inside `fn f<const N: usize>()`. The body
        // MIR carries `N` as an unsubstituted const param, so the array-repeat count is not
        // `try_to_target_usize`-evaluable until the instance's args are substituted
        // (monomorphize_const). `make::<4>() == [7; 4]`; a[0] + a[3] = 14.
        (
            "const_generic_array_repeat",
            "fn make<const N: usize>() -> [i32; N] { [7; N] } \
             fn main(){ let a = make::<4>(); std::process::exit(a[0] + a[3]); }",
            14,
        ),
        // A const-generic zero-fill `[0; N]` summed + the length: sum_zeros::<5>() = 0 + 5.
        (
            "const_generic_zero_fill",
            "fn sum_zeros<const N: usize>() -> i32 { let a=[0i32; N]; \
             a.iter().copied().fold(0,|x,y|x+y) + N as i32 } \
             fn main(){ std::process::exit(sum_zeros::<5>()); }",
            5,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile_bin(&dir, &format!("{name}_llvm"), src, None)
            .unwrap_or_else(|e| panic!("LLVM compile of `{name}` failed: <<<{e}>>>"));
        let tcg_bin = compile_bin(&dir, &format!("{name}_tcg"), src, Some(&dylib))
            .unwrap_or_else(|e| panic!("trust-cg compile of `{name}` failed: <<<{e}>>>"));
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

/// BY-VALUE AGGREGATE PARAMETERS (callee side): the functions that take a
/// `struct{a,b}` and a `Result<i64,i64>` BY VALUE are compiled with trust-cg into
/// a static library; an LLVM-compiled `main` passes the aggregates per the System
/// V ABI and checks the returned values. This exercises the by-value-parameter
/// memory store across a real ABI boundary. The whole binary's exit code is 0 on
/// success (every case matched its LLVM-computed oracle value).
#[test]
fn by_value_aggregate_parameters_run_across_abi_boundary() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("byval_param");

    // Library callees, compiled with trust-cg. Each takes a by-value aggregate.
    let lib_src = "#![crate_type = \"staticlib\"] \
        #[repr(C)] pub struct P { pub a: i64, pub b: i64 } \
        #[inline(never)] #[no_mangle] pub extern \"C\" fn tcg_use_struct(p: P) -> i64 { p.a * 10 + p.b } \
        #[inline(never)] #[no_mangle] pub extern \"C\" fn tcg_use_result(r: Result<i64,i64>) -> i64 { \
            match r { Ok(x) => x, Err(e) => e + 100 } }";
    let lib_path = dir.join("libtcgagg.a");
    {
        let src_path = dir.join("tcgagg.rs");
        std::fs::write(&src_path, lib_src).expect("write lib source");
        let mut cmd = Command::new("rustup");
        cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
            .arg(backend_arg(&dylib))
            .args(["--target", TARGET, "-Cpanic=abort"])
            .arg("-o")
            .arg(&lib_path)
            .arg(&src_path);
        let out = cmd.output().expect("spawn rustc for lib");
        assert!(
            out.status.success(),
            "trust-cg failed to build by-value-aggregate-param lib. stderr: <<<{}>>>",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    assert!(lib_path.exists(), "trust-cg produced no static lib");

    // LLVM-compiled C caller that passes the aggregates by value per System V and
    // verifies the trust-cg callee returned the right values. Returns 0 on
    // success, non-zero otherwise.
    let c_src = "\
#include <stdint.h>\n\
struct P { int64_t a; int64_t b; };\n\
struct ResI64 { int64_t tag; int64_t payload; };\n\
extern int64_t tcg_use_struct(struct P p);\n\
extern int64_t tcg_use_result(struct ResI64 r);\n\
int main(void) {\n\
    struct P p = { 4, 2 };\n\
    if (tcg_use_struct(p) != 42) return 1;\n\
    struct ResI64 ok = { 0, 42 };\n\
    struct ResI64 err = { 1, 7 };\n\
    if (tcg_use_result(ok) != 42) return 2;\n\
    if (tcg_use_result(err) != 107) return 3;\n\
    return 0;\n\
}\n";
    let c_path = dir.join("caller.c");
    std::fs::write(&c_path, c_src).expect("write C caller");
    let bin = dir.join("byval_param_bin");
    let cc_out = Command::new("cc")
        .args(["-arch", "x86_64"])
        .arg(&c_path)
        .arg(&lib_path)
        .arg("-o")
        .arg(&bin)
        .output()
        .expect("spawn cc to link C caller with trust-cg lib");
    assert!(
        cc_out.status.success(),
        "linking C caller with trust-cg lib failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&cc_out.stderr)
    );

    let exit = run_exit_code(&bin);
    assert_eq!(
        exit, 0,
        "by-value aggregate parameter cross-ABI test failed at check {exit} \
         (1=struct, 2=Ok, 3=Err)"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// BY-VALUE AGGREGATE CALL ARGUMENTS (caller side): a full-trust-cg program
/// constructs an aggregate and passes it BY VALUE to a function, the whole
/// program compiled by trust-cg AND LLVM and run; the trust-cg exit code must
/// equal the LLVM exit code (and the expected value). This closes the gap the
/// earlier `by_value_aggregate_parameters_run_across_abi_boundary` test had to
/// work around by crossing a real ABI boundary — the caller-side by-value
/// argument is now lowered (the slot/scalarized aggregate's address is passed
/// and the backend applies the verified System V eightbyte classification).
/// `#[inline(never)]` forces a real call so the argument ABI is exercised.
#[test]
fn by_value_aggregate_call_arguments_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("byval_arg");

    // (name, source, expected exit code). All values are in 0..=255.
    let cases: &[(&str, &str, i32)] = &[
        // The task keystone: a 16-byte `{i64,i64}` struct passed by value to a
        // function returning the field sum. 3 + 4 = 7.
        (
            "use_point",
            "use std::hint::black_box; \
             struct Point { a: i64, b: i64 } \
             #[inline(never)] fn use_point(p: Point) -> i64 { p.a + p.b } \
             fn main(){ let p = Point { a: black_box(3), b: black_box(4) }; \
             std::process::exit(use_point(p) as i32); }",
            7,
        ),
        // A >16-byte `{i64,i64,i64}` struct: SysV MEMORY class, passed on the
        // stack. 10 + 20 + 30 = 60.
        (
            "use_struct3",
            "use std::hint::black_box; \
             struct S3 { a: i64, b: i64, c: i64 } \
             #[inline(never)] fn sum3(s: S3) -> i64 { s.a + s.b + s.c } \
             fn main(){ let s = S3 { a: black_box(10), b: black_box(20), c: black_box(30) }; \
             std::process::exit(sum3(s) as i32); }",
            60,
        ),
        // Register args + a by-value 16-byte struct + a trailing arg: the struct
        // sits between scalar arguments, so the register/stack indices must stay
        // consistent. 1 + 2 + (5+6) + 9 = 23.
        (
            "mixed_reg_and_byval",
            "use std::hint::black_box; \
             struct Pair { x: i64, y: i64 } \
             #[inline(never)] fn combine(a: i64, b: i64, p: Pair, c: i64) -> i64 { a + b + p.x + p.y + c } \
             fn main(){ let p = Pair { x: black_box(5), y: black_box(6) }; \
             std::process::exit(combine(black_box(1), black_box(2), p, black_box(9)) as i32); }",
            23,
        ),
    ];

    for (name, src, expected) in cases {
        let llvm_bin = compile_bin(&dir, &format!("{name}_llvm"), src, None)
            .unwrap_or_else(|e| panic!("LLVM compile of `{name}` failed: <<<{e}>>>"));
        let tcg_bin = compile_bin(&dir, &format!("{name}_tcg"), src, Some(&dylib))
            .unwrap_or_else(|e| panic!("trust-cg compile of `{name}` failed: <<<{e}>>>"));
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
