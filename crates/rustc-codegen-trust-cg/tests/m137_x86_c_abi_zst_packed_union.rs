#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test — C-ABI by-value ZST-field structs, `#[repr(packed)]` structs,
// and by-value UNIONS across a REAL `extern "C"` boundary, validated against an
// INDEPENDENT clang-compiled C object (the System V AMD64 C-ABI oracle), in BOTH
// directions, at -O0/-O2/-O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Found by the FUZZ-6 clang-oracle C-ABI conformance sweep. Only an INDEPENDENT
// C-ABI implementation (clang) catches a self-consistent-but-nonconformant ABI
// defect: the Rust ABI passes both sides of a pure-bridge program the same way, so a
// rustc-vs-rustc differential is BLIND to these. Three findings, three regimes:
//
//   1. ZST-FIELD STRUCT (a WRONG-VALUE bug, now a PROPER FIX): a `#[repr(C)]` struct
//      with a zero-sized field BEFORE a scalar field (`{ a: u64, _z: (), b: u64 }`)
//      passed BY VALUE read `b` from the ZST's stale binding — a wrong ABI value.
//      The by-value scalarized-aggregate repack now keys each field's projected value
//      by the SAME index its construction bound (MIR field index for a flat struct),
//      so the field after the ZST is read correctly. These MUST compile and MATCH.
//
//   2. PACKED MISALIGNED AGGREGATE (a WRONG-VALUE bug, now a SOUND FAIL-CLOSED): a
//      `#[repr(C, packed)]` struct with a misaligned wide field (`{ u8, u64 }`, the
//      u64 at offset 1) marshaled through the bridge's uniform sub-eightbyte lane ABI
//      diverged from the System V GPR-eightbyte C ABI — garbage at the boundary. Now
//      fails closed (`[TCG-SYSV-PACKED-AGGREGATE]`) rather than emitting a wrong
//      value. A packed struct whose fields are all naturally aligned still MATCHES.
//
//   3. MIXED-CLASS UNION (a WRONG-VALUE bug, now a SOUND FAIL-CLOSED): a by-value
//      `union { f64, u64 }` is INTEGER-classed by SysV (GPR), but the bridge passed
//      its scalar carrier in an XMM register — garbage at the boundary. Now fails
//      closed (`[TCG-SYSV-MIXED-UNION]`). A pure-integer union still MATCHES.
//
// Each Rust side is compiled by BOTH trust-cg AND stock LLVM, linked against the SAME
// clang C object, run, and the exit codes compared. A packed/union WRONG shape must
// make trust-cg FAIL to compile (fail-closed), NEVER produce a differing exit code.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

// ---- clang C oracle: by-value consumers + producers ----
// WithZst / NoZst pin the ZST-field proper fix; AlignedPacked + IntUnion pin the
// working siblings of the two fail-closed regimes.
const ORACLE_C: &str = r#"
#include <stdint.h>
typedef struct { } E;
typedef struct { uint64_t a; E z; uint64_t b; } WithZst;   /* ZST field before b */
typedef struct { E z; uint64_t a; uint64_t b; } ZstFirst;  /* leading ZST field */
typedef struct { uint64_t a; uint64_t b; } NoZst;
#pragma pack(push,1)
typedef struct { uint64_t a; uint64_t b; } AlignedPacked;   /* packed but aligned fields */
#pragma pack(pop)
typedef union { uint64_t i; uint32_t pair[2]; uint8_t b; } IntUnion;

int64_t c_use_WithZst(WithZst s){ return (int64_t)(s.a*31 + s.b); }
int64_t c_use_ZstFirst(ZstFirst s){ return (int64_t)(s.a*31 + s.b); }
int64_t c_use_NoZst(NoZst s){ return (int64_t)(s.a*31 + s.b); }
int64_t c_use_AlignedPacked(AlignedPacked s){ return (int64_t)(s.a ^ s.b); }
int64_t c_use_IntUnion(IntUnion s){ return (int64_t)(s.i * 5); }
WithZst c_make_WithZst(uint64_t a, uint64_t b){ WithZst s={a,{},b}; return s; }
ZstFirst c_make_ZstFirst(uint64_t a, uint64_t b){ ZstFirst s={{},a,b}; return s; }
AlignedPacked c_make_AlignedPacked(uint64_t a, uint64_t b){ AlignedPacked s={a,b}; return s; }

extern int64_t rust_use_WithZst(WithZst s);
extern int64_t rust_use_ZstFirst(ZstFirst s);
extern int64_t rust_use_NoZst(NoZst s);
extern int64_t rust_use_AlignedPacked(AlignedPacked s);
extern int64_t rust_use_IntUnion(IntUnion s);
extern WithZst rust_make_WithZst(uint64_t a, uint64_t b);
extern ZstFirst rust_make_ZstFirst(uint64_t a, uint64_t b);
extern AlignedPacked rust_make_AlignedPacked(uint64_t a, uint64_t b);
#ifndef NO_MAIN
int main(void){
    int64_t acc=0;
    acc+=rust_use_WithZst((WithZst){100,{},7});
    acc+=rust_use_ZstFirst((ZstFirst){{},100,7});
    acc+=rust_use_NoZst((NoZst){100,7});
    acc+=rust_use_AlignedPacked((AlignedPacked){0x1122334455667788ULL,0x99AABBCCDDEEFF00ULL});
    { IntUnion u; u.i=0x1122334455667788ULL; acc+=rust_use_IntUnion(u); }
    { WithZst s=rust_make_WithZst(100,7); acc+=(int64_t)(s.a*31+s.b); }
    { ZstFirst s=rust_make_ZstFirst(100,7); acc+=(int64_t)(s.a*31+s.b); }
    { AlignedPacked s=rust_make_AlignedPacked(0xABCDEF12ULL,0x3344ULL); acc+=(int64_t)(s.a ^ s.b); }
    return (int)(acc % 251);
}
#endif
"#;

const RUST_TYPES: &str = r#"
#[repr(C)] #[derive(Clone,Copy)] pub struct E;
#[repr(C)] #[derive(Clone,Copy)] pub struct WithZst { pub a: u64, pub _z: E, pub b: u64 }
#[repr(C)] #[derive(Clone,Copy)] pub struct ZstFirst { pub _z: E, pub a: u64, pub b: u64 }
#[repr(C)] #[derive(Clone,Copy)] pub struct NoZst { pub a: u64, pub b: u64 }
#[repr(C, packed)] #[derive(Clone,Copy)] pub struct AlignedPacked { pub a: u64, pub b: u64 }
#[repr(C)] #[derive(Clone,Copy)] pub union IntUnion { pub i: u64, pub pair: [u32;2], pub b: u8 }
"#;

// Direction A: Rust main calls the clang helpers by value.
fn rust_dir_a() -> String {
    format!(
        "#![no_std]\n#![no_main]\n#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box;\n{RUST_TYPES}\n\
         extern \"C\" {{\n\
         fn c_use_WithZst(s: WithZst) -> i64; fn c_use_ZstFirst(s: ZstFirst) -> i64;\n\
         fn c_use_NoZst(s: NoZst) -> i64; fn c_use_AlignedPacked(s: AlignedPacked) -> i64;\n\
         fn c_use_IntUnion(s: IntUnion) -> i64;\n\
         fn c_make_WithZst(a: u64, b: u64) -> WithZst; fn c_make_ZstFirst(a: u64, b: u64) -> ZstFirst;\n\
         fn c_make_AlignedPacked(a: u64, b: u64) -> AlignedPacked;\n\
         }}\n\
         #[no_mangle]\npub extern \"C\" fn main() -> i32 {{\n\
         let mut acc: i64 = 0;\n\
         unsafe {{\n\
         acc += c_use_WithZst(black_box(WithZst {{ a: 100, _z: E, b: 7 }}));\n\
         acc += c_use_ZstFirst(black_box(ZstFirst {{ _z: E, a: 100, b: 7 }}));\n\
         acc += c_use_NoZst(black_box(NoZst {{ a: 100, b: 7 }}));\n\
         acc += c_use_AlignedPacked(black_box(AlignedPacked {{ a: 0x1122334455667788, b: 0x99AABBCCDDEEFF00 }}));\n\
         acc += c_use_IntUnion(black_box(IntUnion {{ i: 0x1122334455667788 }}));\n\
         let s = c_make_WithZst(black_box(100), black_box(7)); acc += (s.a*31 + s.b) as i64;\n\
         let s = c_make_ZstFirst(black_box(100), black_box(7)); acc += (s.a*31 + s.b) as i64;\n\
         let s = c_make_AlignedPacked(black_box(0xABCDEF12), black_box(0x3344)); let a = s.a; let b = s.b; acc += (a ^ b) as i64;\n\
         }}\n(acc % 251) as i32\n}}\n"
    )
}

// Direction B: Rust extern "C" fns called by the clang main.
fn rust_dir_b() -> String {
    format!(
        "#![no_std]\n#![no_main]\n#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box;\n{RUST_TYPES}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_WithZst(s: WithZst) -> i64 {{ (s.a*31 + s.b) as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_ZstFirst(s: ZstFirst) -> i64 {{ (s.a*31 + s.b) as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_NoZst(s: NoZst) -> i64 {{ (s.a*31 + s.b) as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_AlignedPacked(s: AlignedPacked) -> i64 {{ let a = s.a; let b = s.b; (a ^ b) as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_IntUnion(s: IntUnion) -> i64 {{ unsafe {{ (s.i * 5) as i64 }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_WithZst(a: u64, b: u64) -> WithZst {{ WithZst {{ a: black_box(a), _z: E, b: black_box(b) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_ZstFirst(a: u64, b: u64) -> ZstFirst {{ ZstFirst {{ _z: E, a: black_box(a), b: black_box(b) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_AlignedPacked(a: u64, b: u64) -> AlignedPacked {{ AlignedPacked {{ a: black_box(a), b: black_box(b) }} }}\n"
    )
}

// A `#[repr(C, packed)]` struct with a MISALIGNED wide field, and a MIXED union —
// both must FAIL CLOSED under trust-cg (never a wrong value), while LLVM compiles.
const RUST_MUST_FAIL_CLOSED_PACKED: &str = r#"
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[repr(C, packed)] #[derive(Clone,Copy)] pub struct PackedMisaligned { pub a: u8, pub b: u64 }
extern "C" { fn c_use(s: PackedMisaligned) -> i64; }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    unsafe { c_use(black_box(PackedMisaligned { a: 0x7E, b: 0x1122334455667788 })) as i32 }
}
"#;

const RUST_MUST_FAIL_CLOSED_UNION: &str = r#"
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[repr(C)] #[derive(Clone,Copy)] pub union MixUnion { pub d: f64, pub i: u64 }
extern "C" { fn c_use(u: MixUnion) -> i64; }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    unsafe { c_use(black_box(MixUnion { i: 0x4008000000000000 })) as i32 }
}
"#;

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            if let Some((_, value)) = raw_channel.split_once('=') {
                return value.trim().trim_matches('"').to_owned();
            }
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
    for cand in [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
    ] {
        if cand.exists() {
            return cand;
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m137");
    let built = target_dir.join("release").join(&name);
    assert!(built.exists(), "expected dylib at {built:?}");
    built
}

fn x86_64_std_available() -> bool {
    Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output()
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .lines()
                .any(|l| l.trim() == TARGET)
        })
        .unwrap_or(false)
}

fn clang_available() -> bool {
    Command::new("clang")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m137_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn compile_rust_obj(
    dylib: Option<&Path>,
    dir: &Path,
    src: &Path,
    opt_level: u8,
    tag: &str,
) -> Option<PathBuf> {
    let out_dir = dir.join(format!("obj_{tag}"));
    let _ = std::fs::remove_dir_all(&out_dir);
    std::fs::create_dir_all(&out_dir).expect("obj dir");
    let mut cmd = Command::new("rustup");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin", "--target", TARGET])
        .args(["-Cpanic=abort", "-Coverflow-checks=off", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt_level}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&out_dir);
    if let Some(dylib) = dylib {
        let mut b = std::ffi::OsString::from("-Zcodegen-backend=");
        b.push(dylib);
        cmd.arg(b);
    }
    cmd.arg(src);
    let output = cmd.output().expect("spawn rustc");
    if !output.status.success() {
        return None;
    }
    std::fs::read_dir(&out_dir)
        .expect("read obj dir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .find(|p| p.extension().is_some_and(|x| x == "o"))
}

fn compile_c_oracle(dir: &Path, no_main: bool) -> PathBuf {
    let c = dir.join(if no_main { "oracle_nomain.c" } else { "oracle_main.c" });
    std::fs::write(&c, ORACLE_C).expect("write oracle.c");
    let obj = dir.join(if no_main { "oracle_nomain.o" } else { "oracle_main.o" });
    let mut cmd = Command::new("clang");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET)
        .args(["-target", TARGET, "-O2"])
        .arg(format!("-mmacosx-version-min={MACOS_DEPLOYMENT_TARGET}"));
    if no_main {
        cmd.arg("-DNO_MAIN");
    }
    let status = cmd
        .arg("-c")
        .arg(&c)
        .arg("-o")
        .arg(&obj)
        .status()
        .expect("clang");
    assert!(status.success(), "clang failed to compile the C oracle");
    obj
}

fn panic_stubs(dir: &Path, objs: &[&Path]) -> PathBuf {
    let mut nm = Command::new("nm");
    nm.arg("-u");
    for o in objs {
        nm.arg(o);
    }
    let out = nm.output().expect("nm");
    let mut stubs = String::from("#include <stdlib.h>\n");
    let mut seen = std::collections::HashSet::new();
    for line in String::from_utf8_lossy(&out.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if sym.contains("panic") && seen.insert(sym.to_owned()) {
            let c = sym.strip_prefix('_').unwrap_or(sym);
            stubs.push_str(&format!(
                "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
            ));
        }
    }
    let path = dir.join("stubs.c");
    std::fs::write(&path, stubs).expect("write stubs");
    path
}

fn link_and_run(dir: &Path, tag: &str, rust_obj: &Path, c_obj: &Path) -> Option<i32> {
    let stubs = panic_stubs(dir, &[rust_obj, c_obj]);
    let bin = dir.join(format!("bin_{tag}"));
    let status = Command::new("clang")
        .env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET)
        .args(["-target", TARGET])
        .arg(format!("-mmacosx-version-min={MACOS_DEPLOYMENT_TARGET}"))
        .arg("-o")
        .arg(&bin)
        .arg(rust_obj)
        .arg(c_obj)
        .arg(&stubs)
        .status()
        .expect("clang link");
    assert!(status.success(), "[{tag}] link failed");
    Command::new(&bin).output().expect("run").status.code()
}

/// The clang-oracle differential for one direction at all opt levels: trust-cg MUST
/// compile these supported ZST-field / aligned-packed / pure-int-union shapes and
/// MATCH LLVM (== the clang-computed value).
fn run_direction(stem: &str, rust_src: &str, c_no_main: bool) {
    if !x86_64_std_available() || !clang_available() {
        eprintln!("skipping {stem}: x86_64 std or clang unavailable");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir(stem);
    let src = dir.join("prog.rs");
    std::fs::write(&src, rust_src).expect("write rust src");
    let c_obj = compile_c_oracle(&dir, c_no_main);

    for opt in [0u8, 2, 3] {
        let llvm_obj = compile_rust_obj(None, &dir, &src, opt, &format!("llvm{opt}"))
            .unwrap_or_else(|| panic!("[{stem} O{opt}] LLVM failed to compile the Rust side"));
        let tcg_obj = compile_rust_obj(Some(&dylib), &dir, &src, opt, &format!("tcg{opt}"))
            .unwrap_or_else(|| {
                panic!(
                    "[{stem} O{opt}] trust-cg FAILED CLOSED on a SUPPORTED C-ABI shape \
                     (ZST-field struct / aligned-packed / pure-int union — must compile & match)"
                )
            });
        let tcg_exit = link_and_run(&dir, &format!("tcg{opt}"), &tcg_obj, &c_obj);
        let llvm_exit = link_and_run(&dir, &format!("llvm{opt}"), &llvm_obj, &c_obj);
        assert_eq!(
            tcg_exit, llvm_exit,
            "[{stem} O{opt}] trust-cg exit {tcg_exit:?} != LLVM/clang exit {llvm_exit:?} \
             (C-ABI ZST/packed/union nonconformance)"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A shape trust-cg must FAIL CLOSED on: LLVM compiles it, trust-cg must NOT
/// (refusing to emit a wrong ABI value). Compile-only (never linked/run).
fn assert_fails_closed(stem: &str, rust_src: &str) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: x86_64 std unavailable");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir(stem);
    let src = dir.join("prog.rs");
    std::fs::write(&src, rust_src).expect("write rust src");
    for opt in [0u8, 2, 3] {
        assert!(
            compile_rust_obj(None, &dir, &src, opt, &format!("llvm{opt}")).is_some(),
            "[{stem} O{opt}] LLVM should compile this shape"
        );
        assert!(
            compile_rust_obj(Some(&dylib), &dir, &src, opt, &format!("tcg{opt}")).is_none(),
            "[{stem} O{opt}] trust-cg must FAIL CLOSED on this ABI-nonconformant shape \
             (a packed misaligned aggregate / mixed-class union), never emit a wrong value"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// DIRECTION A — Rust `main` calls clang helpers by value (Rust->C argument passing +
/// C->Rust return receiving) for ZST-field / aligned-packed / pure-int-union shapes.
#[test]
fn c_abi_zst_packed_union_rust_calls_c() {
    run_direction("dirA", &rust_dir_a(), /*c_no_main=*/ true);
}

/// DIRECTION B — clang `main` calls Rust `extern "C"` fns by value (C->Rust
/// parameter receiving + Rust->C return producing).
#[test]
fn c_abi_zst_packed_union_c_calls_rust() {
    run_direction("dirB", &rust_dir_b(), /*c_no_main=*/ false);
}

/// A packed struct with a MISALIGNED wide field must fail closed, never miscompile.
#[test]
fn c_abi_packed_misaligned_fails_closed() {
    assert_fails_closed("packed", RUST_MUST_FAIL_CLOSED_PACKED);
}

/// A by-value union with MIXED float/integer members must fail closed, never miscompile.
#[test]
fn c_abi_mixed_union_fails_closed() {
    assert_fails_closed("union", RUST_MUST_FAIL_CLOSED_UNION);
}
