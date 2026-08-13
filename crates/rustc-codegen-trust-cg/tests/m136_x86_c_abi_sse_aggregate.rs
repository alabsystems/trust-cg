// Integration test — C-ABI by-value SSE (floating-point) AGGREGATES across a REAL
// `extern "C"` boundary, validated against an INDEPENDENT clang-compiled C object
// (the System V AMD64 C-ABI oracle), in BOTH directions, at -O0/-O2/-O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A `#[repr(C)]` aggregate with a System V SSE eightbyte (`{ f64, i64 }`,
// `{ f32, f32, f32, f32 }`, `{ f64, f64 }`, a lone-`f32` high eightbyte
// `{ i64, f32 }`, …) MUST pass/return that eightbyte in an XMM register, not a GPR.
// The bridge originally built a by-value aggregate's ABI as uniform INTEGER lanes
// (`memory_slot_lane_ty` -> `{ I64, I64 }`), erasing the float fields and marshaling
// every eightbyte through a GPR — self-consistent inside a pure-bridge program (so a
// rustc-vs-rustc differential is BLIND to it) but a silent WRONG VALUE at a real ABI
// boundary (FUZZ-5). The fix threads CLASS-CORRECT per-eightbyte SSE/INTEGER lane
// types so an SSE eightbyte routes to XMM.
//
// Only an INDEPENDENT C-ABI implementation (clang) catches a self-consistent-but-
// nonconformant ABI defect, so each Rust side is compiled by BOTH trust-cg AND stock
// LLVM, linked against the SAME clang C object, run, and the exit codes compared:
//   * DIRECTION A — Rust `main` (bridge) calls clang helpers by value: exercises
//     Rust->C SSE-aggregate ARGUMENT passing + C->Rust SSE-aggregate RETURN.
//   * DIRECTION B — clang `main` calls Rust `extern "C"` fns by value: exercises
//     C->Rust SSE-aggregate FORMAL PARAMETER + Rust->C SSE-aggregate RETURN.
// The INTEGER-merged `{ f32, i32 }` eightbyte (correctly GPR-passed) is included to
// pin that it stays on the GPR path. All shapes must agree with clang/LLVM.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

// ---- clang C oracle: by-value consumers + producers for each shape ----
const ORACLE_C: &str = r#"
#include <stdint.h>
typedef struct { double x; int64_t a; } F64I64;
typedef struct { int64_t a; double x; } I64F64;
typedef struct { float a, b, c, d; } F32x4;
typedef struct { float a, b; } F32x2;
typedef struct { double a, b; } F64x2;
typedef struct { int64_t a; float x; } I64F32;
typedef struct { float x; int32_t a; } F32I32;
typedef struct { double x; } F64New;
typedef struct { float a, b; int64_t c; } F32F32I64;
int64_t c_use_F64I64(F64I64 s){return (int64_t)(s.x)*1000+s.a;}
int64_t c_use_I64F64(I64F64 s){return (int64_t)(s.x)*1000+s.a;}
int64_t c_use_F32x4(F32x4 s){return (int64_t)(s.a+2.0f*s.b+3.0f*s.c+4.0f*s.d);}
int64_t c_use_F32x2(F32x2 s){return (int64_t)(s.a*100.0f+s.b);}
int64_t c_use_F64x2(F64x2 s){return (int64_t)(s.a*1000.0+s.b);}
int64_t c_use_I64F32(I64F32 s){return (int64_t)(s.x)*1000+s.a;}
int64_t c_use_F32I32(F32I32 s){return (int64_t)(s.x)*1000+s.a;}
int64_t c_use_F64New(F64New s){return (int64_t)(s.x*7.0);}
int64_t c_use_F32F32I64(F32F32I64 s){return (int64_t)(s.a*100.0f+s.b)+s.c*1000;}
F64I64 c_make_F64I64(double x,int64_t a){F64I64 s={x,a};return s;}
I64F64 c_make_I64F64(int64_t a,double x){I64F64 s={a,x};return s;}
F32x4 c_make_F32x4(float a,float b,float c,float d){F32x4 s={a,b,c,d};return s;}
F32x2 c_make_F32x2(float a,float b){F32x2 s={a,b};return s;}
F64x2 c_make_F64x2(double a,double b){F64x2 s={a,b};return s;}
I64F32 c_make_I64F32(int64_t a,float x){I64F32 s={a,x};return s;}
F32I32 c_make_F32I32(float x,int32_t a){F32I32 s={x,a};return s;}
F64New c_make_F64New(double x){F64New s={x};return s;}
F32F32I64 c_make_F32F32I64(float a,float b,int64_t c){F32F32I64 s={a,b,c};return s;}
extern int64_t rust_use_F64I64(F64I64 s); extern int64_t rust_use_I64F64(I64F64 s);
extern int64_t rust_use_F32x4(F32x4 s); extern int64_t rust_use_F32x2(F32x2 s);
extern int64_t rust_use_F64x2(F64x2 s); extern int64_t rust_use_I64F32(I64F32 s);
extern int64_t rust_use_F32I32(F32I32 s); extern int64_t rust_use_F64New(F64New s);
extern int64_t rust_use_F32F32I64(F32F32I64 s);
extern F64I64 rust_make_F64I64(double x,int64_t a); extern I64F64 rust_make_I64F64(int64_t a,double x);
extern F32x4 rust_make_F32x4(float a,float b,float c,float d); extern F32x2 rust_make_F32x2(float a,float b);
extern F64x2 rust_make_F64x2(double a,double b); extern I64F32 rust_make_I64F32(int64_t a,float x);
extern F32I32 rust_make_F32I32(float x,int32_t a); extern F64New rust_make_F64New(double x);
extern F32F32I64 rust_make_F32F32I64(float a,float b,int64_t c);
#ifndef NO_MAIN
int main(void){
    int64_t acc=0;
    acc+=rust_use_F64I64((F64I64){5.0,7}); acc+=rust_use_I64F64((I64F64){7,5.0});
    acc+=rust_use_F32x4((F32x4){1.0f,2.0f,3.0f,4.0f}); acc+=rust_use_F32x2((F32x2){3.0f,4.0f});
    acc+=rust_use_F64x2((F64x2){2.0,9.0}); acc+=rust_use_I64F32((I64F32){7,5.0f});
    acc+=rust_use_F32I32((F32I32){5.0f,7}); acc+=rust_use_F64New((F64New){6.0});
    acc+=rust_use_F32F32I64((F32F32I64){3.0f,4.0f,2});
    {F64I64 s=rust_make_F64I64(5.0,7); acc+=(int64_t)(s.x)*1000+s.a;}
    {I64F64 s=rust_make_I64F64(7,5.0); acc+=(int64_t)(s.x)*1000+s.a;}
    {F32x4 s=rust_make_F32x4(1,2,3,4); acc+=(int64_t)(s.a+2*s.b+3*s.c+4*s.d);}
    {F32x2 s=rust_make_F32x2(3,4); acc+=(int64_t)(s.a*100.0f+s.b);}
    {F64x2 s=rust_make_F64x2(2,9); acc+=(int64_t)(s.a*1000.0+s.b);}
    {I64F32 s=rust_make_I64F32(7,5.0f); acc+=(int64_t)(s.x)*1000+s.a;}
    {F32I32 s=rust_make_F32I32(5.0f,7); acc+=(int64_t)(s.x)*1000+s.a;}
    {F64New s=rust_make_F64New(6.0); acc+=(int64_t)(s.x*7.0);}
    {F32F32I64 s=rust_make_F32F32I64(3,4,2); acc+=(int64_t)(s.a*100.0f+s.b)+s.c*1000;}
    return (int)(acc%251);
}
#endif
"#;

const RUST_STRUCTS: &str = r#"
#[repr(C)] #[derive(Clone,Copy)] pub struct F64I64 { pub x: f64, pub a: i64 }
#[repr(C)] #[derive(Clone,Copy)] pub struct I64F64 { pub a: i64, pub x: f64 }
#[repr(C)] #[derive(Clone,Copy)] pub struct F32x4 { pub a: f32, pub b: f32, pub c: f32, pub d: f32 }
#[repr(C)] #[derive(Clone,Copy)] pub struct F32x2 { pub a: f32, pub b: f32 }
#[repr(C)] #[derive(Clone,Copy)] pub struct F64x2 { pub a: f64, pub b: f64 }
#[repr(C)] #[derive(Clone,Copy)] pub struct I64F32 { pub a: i64, pub x: f32 }
#[repr(C)] #[derive(Clone,Copy)] pub struct F32I32 { pub x: f32, pub a: i32 }
#[repr(C)] #[derive(Clone,Copy)] pub struct F64New { pub x: f64 }
#[repr(C)] #[derive(Clone,Copy)] pub struct F32F32I64 { pub a: f32, pub b: f32, pub c: i64 }
"#;

// Direction A: Rust main calls the clang helpers by value.
fn rust_dir_a() -> String {
    format!(
        "#![no_std]\n#![no_main]\n#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box;\n{RUST_STRUCTS}\n\
         extern \"C\" {{\n\
         fn c_use_F64I64(s: F64I64) -> i64; fn c_use_I64F64(s: I64F64) -> i64;\n\
         fn c_use_F32x4(s: F32x4) -> i64; fn c_use_F32x2(s: F32x2) -> i64;\n\
         fn c_use_F64x2(s: F64x2) -> i64; fn c_use_I64F32(s: I64F32) -> i64;\n\
         fn c_use_F32I32(s: F32I32) -> i64; fn c_use_F64New(s: F64New) -> i64;\n\
         fn c_use_F32F32I64(s: F32F32I64) -> i64;\n\
         fn c_make_F64I64(x: f64, a: i64) -> F64I64; fn c_make_I64F64(a: i64, x: f64) -> I64F64;\n\
         fn c_make_F32x4(a: f32, b: f32, c: f32, d: f32) -> F32x4; fn c_make_F32x2(a: f32, b: f32) -> F32x2;\n\
         fn c_make_F64x2(a: f64, b: f64) -> F64x2; fn c_make_I64F32(a: i64, x: f32) -> I64F32;\n\
         fn c_make_F32I32(x: f32, a: i32) -> F32I32; fn c_make_F64New(x: f64) -> F64New;\n\
         fn c_make_F32F32I64(a: f32, b: f32, c: i64) -> F32F32I64;\n\
         }}\n\
         #[no_mangle]\npub extern \"C\" fn main() -> i32 {{\n\
         let mut acc: i64 = 0;\n\
         unsafe {{\n\
         acc += c_use_F64I64(black_box(F64I64 {{ x: 5.0, a: 7 }}));\n\
         acc += c_use_I64F64(black_box(I64F64 {{ a: 7, x: 5.0 }}));\n\
         acc += c_use_F32x4(black_box(F32x4 {{ a: 1.0, b: 2.0, c: 3.0, d: 4.0 }}));\n\
         acc += c_use_F32x2(black_box(F32x2 {{ a: 3.0, b: 4.0 }}));\n\
         acc += c_use_F64x2(black_box(F64x2 {{ a: 2.0, b: 9.0 }}));\n\
         acc += c_use_I64F32(black_box(I64F32 {{ a: 7, x: 5.0 }}));\n\
         acc += c_use_F32I32(black_box(F32I32 {{ x: 5.0, a: 7 }}));\n\
         acc += c_use_F64New(black_box(F64New {{ x: 6.0 }}));\n\
         acc += c_use_F32F32I64(black_box(F32F32I64 {{ a: 3.0, b: 4.0, c: 2 }}));\n\
         let s = c_make_F64I64(black_box(5.0), black_box(7)); acc += (s.x as i64)*1000 + s.a;\n\
         let s = c_make_I64F64(black_box(7), black_box(5.0)); acc += (s.x as i64)*1000 + s.a;\n\
         let s = c_make_F32x4(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0)); acc += (s.a + 2.0*s.b + 3.0*s.c + 4.0*s.d) as i64;\n\
         let s = c_make_F32x2(black_box(3.0), black_box(4.0)); acc += (s.a*100.0 + s.b) as i64;\n\
         let s = c_make_F64x2(black_box(2.0), black_box(9.0)); acc += (s.a*1000.0 + s.b) as i64;\n\
         let s = c_make_I64F32(black_box(7), black_box(5.0)); acc += (s.x as i64)*1000 + s.a;\n\
         let s = c_make_F32I32(black_box(5.0), black_box(7)); acc += (s.x as i64)*1000 + s.a as i64;\n\
         let s = c_make_F64New(black_box(6.0)); acc += (s.x*7.0) as i64;\n\
         let s = c_make_F32F32I64(black_box(3.0), black_box(4.0), black_box(2)); acc += (s.a*100.0 + s.b) as i64 + s.c*1000;\n\
         }}\n(acc % 251) as i32\n}}\n"
    )
}

// Direction B: Rust extern "C" fns called by the clang main.
fn rust_dir_b() -> String {
    format!(
        "#![no_std]\n#![no_main]\n#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box;\n{RUST_STRUCTS}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_F64I64(s: F64I64) -> i64 {{ (s.x as i64)*1000 + s.a }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_I64F64(s: I64F64) -> i64 {{ (s.x as i64)*1000 + s.a }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_F32x4(s: F32x4) -> i64 {{ (s.a + 2.0*s.b + 3.0*s.c + 4.0*s.d) as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_F32x2(s: F32x2) -> i64 {{ (s.a*100.0 + s.b) as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_F64x2(s: F64x2) -> i64 {{ (s.a*1000.0 + s.b) as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_I64F32(s: I64F32) -> i64 {{ (s.x as i64)*1000 + s.a }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_F32I32(s: F32I32) -> i64 {{ (s.x as i64)*1000 + s.a as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_F64New(s: F64New) -> i64 {{ (s.x*7.0) as i64 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_use_F32F32I64(s: F32F32I64) -> i64 {{ (s.a*100.0 + s.b) as i64 + s.c*1000 }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_F64I64(x: f64, a: i64) -> F64I64 {{ F64I64 {{ x: black_box(x), a: black_box(a) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_I64F64(a: i64, x: f64) -> I64F64 {{ I64F64 {{ a: black_box(a), x: black_box(x) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_F32x4(a: f32, b: f32, c: f32, d: f32) -> F32x4 {{ F32x4 {{ a: black_box(a), b: black_box(b), c: black_box(c), d: black_box(d) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_F32x2(a: f32, b: f32) -> F32x2 {{ F32x2 {{ a: black_box(a), b: black_box(b) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_F64x2(a: f64, b: f64) -> F64x2 {{ F64x2 {{ a: black_box(a), b: black_box(b) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_I64F32(a: i64, x: f32) -> I64F32 {{ I64F32 {{ a: black_box(a), x: black_box(x) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_F32I32(x: f32, a: i32) -> F32I32 {{ F32I32 {{ x: black_box(x), a: black_box(a) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_F64New(x: f64) -> F64New {{ F64New {{ x: black_box(x) }} }}\n\
         #[no_mangle] pub extern \"C\" fn rust_make_F32F32I64(a: f32, b: f32, c: i64) -> F32F32I64 {{ F32F32I64 {{ a: black_box(a), b: black_box(b), c: black_box(c) }} }}\n"
    )
}

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
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
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
    assert!(status.success(), "cargo build failed; cannot run m136");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m136_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile a Rust source to an OBJECT with the given backend at `opt_level`.
/// Returns `Some(obj)` on success, `None` on compile failure (fail-closed).
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

/// Compile the clang C oracle to an object (`no_main` = helpers only).
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
    let status = cmd.arg("-c").arg(&c).arg("-o").arg(&obj).status().expect("clang");
    assert!(status.success(), "clang failed to compile the C oracle");
    obj
}

/// `abort()` stubs for undefined `panic*` symbols (an LLVM/O0 rem-overflow panic
/// ref), so the object links standalone (the inputs never trip a panic).
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

/// Link the Rust object + the C oracle object (+ panic stubs) and run; return the
/// exit code.
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

/// The clang-oracle differential for one direction at all opt levels: for each of
/// -O0/-O2/-O3, compile the Rust side with trust-cg AND with LLVM, link each against
/// the same clang C object, run, and assert trust-cg == LLVM (== the clang-computed
/// value). trust-cg must NOT fail closed on these supported SSE-aggregate shapes.
fn run_direction(stem: &str, rust_src: &str, c_no_main: bool, rust_owns_main: bool) {
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
                    "[{stem} O{opt}] trust-cg FAILED CLOSED on a supported C-ABI SSE-aggregate \
                     shape (should compile and route the SSE eightbyte to XMM)"
                )
            });
        // Link order does not affect symbol resolution across objects; always pass
        // (rust_obj, c_obj). `rust_owns_main` only documents which object holds main.
        let _ = rust_owns_main;
        let tcg_exit = link_and_run(&dir, &format!("tcg{opt}"), &tcg_obj, &c_obj);
        let llvm_exit = link_and_run(&dir, &format!("llvm{opt}"), &llvm_obj, &c_obj);
        assert_eq!(
            tcg_exit, llvm_exit,
            "[{stem} O{opt}] trust-cg exit {tcg_exit:?} != LLVM/clang exit {llvm_exit:?} \
             (C-ABI SSE-aggregate ABI nonconformance)"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// DIRECTION A — Rust `main` (bridge) calls clang helpers by value: Rust->C
/// SSE-aggregate argument passing + C->Rust SSE-aggregate return receiving.
#[test]
fn c_abi_sse_aggregate_rust_calls_c() {
    run_direction("dirA", &rust_dir_a(), /*c_no_main=*/ true, /*rust_owns_main=*/ true);
}

/// DIRECTION B — clang `main` calls Rust `extern "C"` fns by value: C->Rust
/// SSE-aggregate formal-parameter receiving + Rust->C SSE-aggregate return producing.
#[test]
fn c_abi_sse_aggregate_c_calls_rust() {
    run_direction("dirB", &rust_dir_b(), /*c_no_main=*/ false, /*rust_owns_main=*/ false);
}
