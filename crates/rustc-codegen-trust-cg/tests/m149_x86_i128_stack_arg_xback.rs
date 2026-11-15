#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a 128-bit INTEGER argument (`u128`, `i128`, a `u128`
// beside an `i128`, an `Option<u128>`) after k = 0..=7 leading `u64`s, so at
// EVERY System V register-exhaustion position, checked ACROSS the backend
// boundary in all four rlib x bin combinations at every optimization level,
// for the Rust ABI, the `extern "C"` ABI and an indirect call through a `fn`
// pointer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The AMD64 psABI (3.2.3) passes a 128-bit integer in two consecutive INTEGER
// registers, or, when fewer than two remain, WHOLLY on the stack at a 16-byte
// boundary; a later eightbyte still takes the register the 128-bit value left
// free. So `fn(a0..a4: u64, x: u128, y: u64, z: u64)` passes `x` at stack +0/+8,
// `y` in R9 and `z` at +16, and with seven leading `u64`s `x` skips the
// eightbyte at +8 to start at +16. GCC 16 and the LLVM 22 that `trustc` uses
// place it that way; Apple clang 14.0.3 (LLVM 15) splits the rolled-back value
// between R9 and the stack and aligns a stack `__int128` to 8 only, which is
// why trust-cg-codegen's `e2e_x86_64_i128_stack_abi` no longer takes the host C
// compiler as its oracle (reports/2026-10-02-x86-i128-stack-abi). This file asks
// the question that matters for Rust: does a backend-compiled caller or callee
// agree with LLVM's placement for every k?
//
// Rows. The callee crate's functions check every argument against the
// constants the caller passes and return a mask of the wrong ones (bit i: a_i,
// bits 8/9: the low/high eightbyte of `x`, bits 10/11: those of the `i128`
// `v` of the pair rows, 12: `y`, 13: `z`). The caller exits 42 for an empty
// mask and 100 + the lowest wrong bit otherwise, so a failing cell names the
// first misplaced eightbyte. `k` runs 0..=7 for `u128` and `i128` in the Rust
// and `extern "C"` ABIs; the pair rows take `x: u128, v: i128` together (with
// k = 3 the `u128` fills RCX:R8 and the `i128` rolls back past R9); the `opt`
// rows pass `Some(x)` as an `Option<u128>`, which rustc passes as a
// `PassMode::Pair` of two `i128`s (the bridge's two-value lane, not the scalar
// one: bit 10 means the callee saw `None`); the `fnptr` rows call through a
// `fn` pointer at k = 4..=7.
//
// The bridge compiles with `no-proof-certs`, as `tests/tools/m145_xback.py`
// does: the rows judge ABI agreement, not proof promotion.
//
// Executes only on an x86-64 host with the host x86-64 `rust-std`. The cargo
// harness cannot dlopen a stage1-linked bridge under the pinned pack compiler;
// `tests/tools/m145_xback.py --test tests/m149_x86_i128_stack_arg_xback.rs`
// drives the same callee and rows (extracted from this file) with a `trustc`
// that can.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m149_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Backend {
    Llvm,
    TrustCg,
}

impl Backend {
    fn tag(self) -> &'static str {
        match self {
            Backend::Llvm => "llvm",
            Backend::TrustCg => "tcg",
        }
    }
}

fn compile_callee_rlib(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join("callee.rs");
    std::fs::write(&src_path, CALLEE_SRC).expect("write callee source");
    let out_dir = dir.join(format!("callee_{}_O{opt}", backend.tag()));
    std::fs::create_dir_all(&out_dir).expect("create callee out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", "callee"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("--out-dir")
    .arg(&out_dir)
    .arg(&src_path);
    let output = cmd.output().expect("spawn rustc for the callee rlib");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(out_dir.join("libcallee.rlib"))
}

#[allow(clippy::too_many_arguments)]
fn compile_caller_bin(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    shape: &str,
    body: &str,
    rlib: &Path,
    rlib_backend: Backend,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("caller_{shape}.rs"));
    std::fs::write(&src_path, format!("{CALLER_HDR}{body}")).expect("write caller source");
    let bin = dir.join(format!(
        "caller_{shape}_{}rlib_{}bin_O{opt}",
        rlib_backend.tag(),
        backend.tag()
    ));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let mut extern_arg = OsString::from("callee=");
    extern_arg.push(rlib);
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("--extern")
    .arg(&extern_arg)
    .arg("-L")
    .arg(rlib.parent().expect("rlib directory"))
    .arg("-o")
    .arg(&bin)
    .arg(&src_path);
    let output = cmd.output().expect("spawn rustc for the caller bin");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

fn run_exit_code(bin: &Path) -> i32 {
    let out = Command::new(bin).output().expect("run binary");
    out.status
        .code()
        .unwrap_or_else(|| panic!("{bin:?} exited via signal: {:?}", out.status))
}

/// The callee crate: `one!` defines a Rust-ABI and an `extern "C"` function
/// taking k `u64`s, the 128-bit `x`, then `y` and `z`; `two!` the same with
/// `x: u128, v: i128`; `opt!` a Rust-ABI function with `x: Option<u128>`. Each
/// returns the mask of arguments that did not arrive as the constants the
/// caller passes.
const CALLEE_SRC: &str = r#"
#![allow(improper_ctypes_definitions)]
pub const A: [u64; 7] = [
    0x1111_1111_1111_1111, 0x2222_2222_2222_2222, 0x3333_3333_3333_3333, 0x4444_4444_4444_4444,
    0x5555_5555_5555_5555, 0x6666_6666_6666_6666, 0x7777_7777_7777_7777,
];
pub const XU: u128 = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210;
pub const XI: i128 = -0x0f1e_2d3c_4b5a_6978_8796_a5b4_c3d2_e1f0;
pub const V: i128 = -0x7a6b_5c4d_3e2f_1001_9988_7766_5544_3322;
pub const Y: u64 = 0x8877_6655_4433_2211;
pub const Z: u64 = 0x0f0e_0d0c_0b0a_0908;
macro_rules! wide {
    ($got:expr, $want:expr, $bit:literal) => {
        ((((($got as u128) as u64 != ($want as u128) as u64) as u64) << $bit)
            | ((((($got as u128) >> 64) as u64 != (($want as u128) >> 64) as u64) as u64) << ($bit + 1)))
    };
}
macro_rules! one {
    ($r:ident, $c:ident, $t:ty, $want:expr; $($a:ident $i:literal)*) => {
        #[inline(never)]
        pub fn $r($($a: u64,)* x: $t, y: u64, z: u64) -> u64 {
            0u64 $(| ((($a != A[$i]) as u64) << $i))* | wide!(x, $want, 8)
                | (((y != Y) as u64) << 12) | (((z != Z) as u64) << 13)
        }
        #[inline(never)]
        pub extern "C" fn $c($($a: u64,)* x: $t, y: u64, z: u64) -> u64 {
            0u64 $(| ((($a != A[$i]) as u64) << $i))* | wide!(x, $want, 8)
                | (((y != Y) as u64) << 12) | (((z != Z) as u64) << 13)
        }
    };
}
macro_rules! two {
    ($r:ident, $c:ident; $($a:ident $i:literal)*) => {
        #[inline(never)]
        pub fn $r($($a: u64,)* x: u128, v: i128, y: u64, z: u64) -> u64 {
            0u64 $(| ((($a != A[$i]) as u64) << $i))* | wide!(x, XU, 8) | wide!(v, V, 10)
                | (((y != Y) as u64) << 12) | (((z != Z) as u64) << 13)
        }
        #[inline(never)]
        pub extern "C" fn $c($($a: u64,)* x: u128, v: i128, y: u64, z: u64) -> u64 {
            0u64 $(| ((($a != A[$i]) as u64) << $i))* | wide!(x, XU, 8) | wide!(v, V, 10)
                | (((y != Y) as u64) << 12) | (((z != Z) as u64) << 13)
        }
    };
}
macro_rules! opt {
    ($r:ident; $($a:ident $i:literal)*) => {
        #[inline(never)]
        pub fn $r($($a: u64,)* x: Option<u128>, y: u64, z: u64) -> u64 {
            0u64 $(| ((($a != A[$i]) as u64) << $i))*
                | match x { Some(w) => wide!(w, XU, 8), None => 1 << 10 }
                | (((y != Y) as u64) << 12) | (((z != Z) as u64) << 13)
        }
    };
}
one!(ur0, uc0, u128, XU;);
one!(ur1, uc1, u128, XU; a0 0);
one!(ur2, uc2, u128, XU; a0 0 a1 1);
one!(ur3, uc3, u128, XU; a0 0 a1 1 a2 2);
one!(ur4, uc4, u128, XU; a0 0 a1 1 a2 2 a3 3);
one!(ur5, uc5, u128, XU; a0 0 a1 1 a2 2 a3 3 a4 4);
one!(ur6, uc6, u128, XU; a0 0 a1 1 a2 2 a3 3 a4 4 a5 5);
one!(ur7, uc7, u128, XU; a0 0 a1 1 a2 2 a3 3 a4 4 a5 5 a6 6);
one!(ir0, ic0, i128, XI;);
one!(ir1, ic1, i128, XI; a0 0);
one!(ir2, ic2, i128, XI; a0 0 a1 1);
one!(ir3, ic3, i128, XI; a0 0 a1 1 a2 2);
one!(ir4, ic4, i128, XI; a0 0 a1 1 a2 2 a3 3);
one!(ir5, ic5, i128, XI; a0 0 a1 1 a2 2 a3 3 a4 4);
one!(ir6, ic6, i128, XI; a0 0 a1 1 a2 2 a3 3 a4 4 a5 5);
one!(ir7, ic7, i128, XI; a0 0 a1 1 a2 2 a3 3 a4 4 a5 5 a6 6);
two!(wr0, wc0;);
two!(wr1, wc1; a0 0);
two!(wr2, wc2; a0 0 a1 1);
two!(wr3, wc3; a0 0 a1 1 a2 2);
two!(wr4, wc4; a0 0 a1 1 a2 2 a3 3);
two!(wr5, wc5; a0 0 a1 1 a2 2 a3 3 a4 4);
two!(wr6, wc6; a0 0 a1 1 a2 2 a3 3 a4 4 a5 5);
two!(wr7, wc7; a0 0 a1 1 a2 2 a3 3 a4 4 a5 5 a6 6);
opt!(or0;);
opt!(or1; a0 0);
opt!(or2; a0 0 a1 1);
opt!(or3; a0 0 a1 1 a2 2);
opt!(or4; a0 0 a1 1 a2 2 a3 3);
opt!(or5; a0 0 a1 1 a2 2 a3 3 a4 4);
opt!(or6; a0 0 a1 1 a2 2 a3 3 a4 4 a5 5);
opt!(or7; a0 0 a1 1 a2 2 a3 3 a4 4 a5 5 a6 6);
"#;

const CALLER_HDR: &str = "use std::hint::black_box as bb;\n\
    use callee::*;\n\
    fn exit(m: u64) -> ! { std::process::exit(if m == 0 { 42 } else { 100 + m.trailing_zeros() as i32 }) }\n";

/// `(shape, caller body, expected exit code)`. Every row exits 42 exactly when
/// every argument reached the callee intact.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        (
            "u128_rust_k0",
            r#"fn main() { exit(ur0(bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_c_k0",
            r#"fn main() { exit(uc0(bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_rust_k0",
            r#"fn main() { exit(ir0(bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_c_k0",
            r#"fn main() { exit(ic0(bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_rust_k1",
            r#"fn main() { exit(ur1(bb(A[0]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_c_k1",
            r#"fn main() { exit(uc1(bb(A[0]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_rust_k1",
            r#"fn main() { exit(ir1(bb(A[0]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_c_k1",
            r#"fn main() { exit(ic1(bb(A[0]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_rust_k2",
            r#"fn main() { exit(ur2(bb(A[0]), bb(A[1]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_c_k2",
            r#"fn main() { exit(uc2(bb(A[0]), bb(A[1]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_rust_k2",
            r#"fn main() { exit(ir2(bb(A[0]), bb(A[1]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_c_k2",
            r#"fn main() { exit(ic2(bb(A[0]), bb(A[1]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_rust_k3",
            r#"fn main() { exit(ur3(bb(A[0]), bb(A[1]), bb(A[2]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_c_k3",
            r#"fn main() { exit(uc3(bb(A[0]), bb(A[1]), bb(A[2]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_rust_k3",
            r#"fn main() { exit(ir3(bb(A[0]), bb(A[1]), bb(A[2]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_c_k3",
            r#"fn main() { exit(ic3(bb(A[0]), bb(A[1]), bb(A[2]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_rust_k4",
            r#"fn main() { exit(ur4(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_c_k4",
            r#"fn main() { exit(uc4(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_rust_k4",
            r#"fn main() { exit(ir4(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_c_k4",
            r#"fn main() { exit(ic4(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_rust_k5",
            r#"fn main() { exit(ur5(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_c_k5",
            r#"fn main() { exit(uc5(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_rust_k5",
            r#"fn main() { exit(ir5(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_c_k5",
            r#"fn main() { exit(ic5(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_rust_k6",
            r#"fn main() { exit(ur6(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_c_k6",
            r#"fn main() { exit(uc6(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_rust_k6",
            r#"fn main() { exit(ir6(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_c_k6",
            r#"fn main() { exit(ic6(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_rust_k7",
            r#"fn main() { exit(ur7(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "u128_c_k7",
            r#"fn main() { exit(uc7(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_rust_k7",
            r#"fn main() { exit(ir7(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "i128_c_k7",
            r#"fn main() { exit(ic7(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_rust_k0",
            r#"fn main() { exit(wr0(bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_c_k0",
            r#"fn main() { exit(wc0(bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_rust_k1",
            r#"fn main() { exit(wr1(bb(A[0]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_c_k1",
            r#"fn main() { exit(wc1(bb(A[0]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_rust_k2",
            r#"fn main() { exit(wr2(bb(A[0]), bb(A[1]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_c_k2",
            r#"fn main() { exit(wc2(bb(A[0]), bb(A[1]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_rust_k3",
            r#"fn main() { exit(wr3(bb(A[0]), bb(A[1]), bb(A[2]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_c_k3",
            r#"fn main() { exit(wc3(bb(A[0]), bb(A[1]), bb(A[2]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_rust_k4",
            r#"fn main() { exit(wr4(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_c_k4",
            r#"fn main() { exit(wc4(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_rust_k5",
            r#"fn main() { exit(wr5(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_c_k5",
            r#"fn main() { exit(wc5(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_rust_k6",
            r#"fn main() { exit(wr6(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_c_k6",
            r#"fn main() { exit(wc6(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_rust_k7",
            r#"fn main() { exit(wr7(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "pair_c_k7",
            r#"fn main() { exit(wc7(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(XU), bb(V), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "opt_rust_k0",
            r#"fn main() { exit(or0(bb(Some(XU)), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "opt_rust_k1",
            r#"fn main() { exit(or1(bb(A[0]), bb(Some(XU)), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "opt_rust_k2",
            r#"fn main() { exit(or2(bb(A[0]), bb(A[1]), bb(Some(XU)), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "opt_rust_k3",
            r#"fn main() { exit(or3(bb(A[0]), bb(A[1]), bb(A[2]), bb(Some(XU)), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "opt_rust_k4",
            r#"fn main() { exit(or4(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(Some(XU)), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "opt_rust_k5",
            r#"fn main() { exit(or5(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(Some(XU)), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "opt_rust_k6",
            r#"fn main() { exit(or6(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(Some(XU)), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "opt_rust_k7",
            r#"fn main() { exit(or7(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(Some(XU)), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "fnptr_u128_rust_k4",
            r#"fn main() { let f: fn(u64, u64, u64, u64, u128, u64, u64) -> u64 = bb(ur4); exit(f(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "fnptr_i128_c_k4",
            r#"fn main() { let f: extern "C" fn(u64, u64, u64, u64, i128, u64, u64) -> u64 = bb(ic4); exit(f(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "fnptr_u128_rust_k5",
            r#"fn main() { let f: fn(u64, u64, u64, u64, u64, u128, u64, u64) -> u64 = bb(ur5); exit(f(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "fnptr_i128_c_k5",
            r#"fn main() { let f: extern "C" fn(u64, u64, u64, u64, u64, i128, u64, u64) -> u64 = bb(ic5); exit(f(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "fnptr_u128_rust_k6",
            r#"fn main() { let f: fn(u64, u64, u64, u64, u64, u64, u128, u64, u64) -> u64 = bb(ur6); exit(f(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "fnptr_i128_c_k6",
            r#"fn main() { let f: extern "C" fn(u64, u64, u64, u64, u64, u64, i128, u64, u64) -> u64 = bb(ic6); exit(f(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "fnptr_u128_rust_k7",
            r#"fn main() { let f: fn(u64, u64, u64, u64, u64, u64, u64, u128, u64, u64) -> u64 = bb(ur7); exit(f(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(XU), bb(Y), bb(Z))) }"#,
            42,
        ),
        (
            "fnptr_i128_c_k7",
            r#"fn main() { let f: extern "C" fn(u64, u64, u64, u64, u64, u64, u64, i128, u64, u64) -> u64 = bb(ic7); exit(f(bb(A[0]), bb(A[1]), bb(A[2]), bb(A[3]), bb(A[4]), bb(A[5]), bb(A[6]), bb(XI), bb(Y), bb(Z))) }"#,
            42,
        ),
    ]
}

#[test]
fn i128_arguments_cross_the_backend_boundary_at_every_exhaustion_position() {
    if !cfg!(target_arch = "x86_64") || !host_target_support::HOST_OS_SUPPORTED {
        eprintln!("skipping: the lane runs natively on an x86-64 Linux or macOS host");
        return;
    }
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("skipping: rust-std for {TARGET} not installed for the pinned toolchain");
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("i128");
    let mut failures = Vec::new();
    for opt in ["0", "1", "2", "3"] {
        let llvm_rlib = compile_callee_rlib(&dir, &dylib, Backend::Llvm, opt)
            .unwrap_or_else(|e| panic!("LLVM `callee` rlib failed at O{opt}: <<<{e}>>>"));
        let tcg_rlib = match compile_callee_rlib(&dir, &dylib, Backend::TrustCg, opt) {
            Ok(rlib) => rlib,
            Err(e) => {
                failures.push(format!(
                    "O{opt}: trust-cg callee rlib failed closed: <<<{}>>>",
                    e.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
                ));
                continue;
            }
        };
        for (shape, body, expected) in shapes() {
            let oracle = compile_caller_bin(
                &dir,
                &dylib,
                Backend::Llvm,
                opt,
                shape,
                body,
                &llvm_rlib,
                Backend::Llvm,
            )
            .unwrap_or_else(|e| panic!("LLVM caller `{shape}` failed at O{opt}: <<<{e}>>>"));
            let oracle_exit = run_exit_code(&oracle);
            assert_eq!(
                oracle_exit, expected,
                "oracle (LLVM+LLVM) exit for `{shape}` at O{opt} is {oracle_exit}, expected {expected}"
            );
            for (bin_backend, rlib, rlib_backend, label) in [
                (
                    Backend::TrustCg,
                    &llvm_rlib,
                    Backend::Llvm,
                    "LLVM callee + trust-cg caller",
                ),
                (
                    Backend::Llvm,
                    &tcg_rlib,
                    Backend::TrustCg,
                    "trust-cg callee + LLVM caller",
                ),
                (
                    Backend::TrustCg,
                    &tcg_rlib,
                    Backend::TrustCg,
                    "trust-cg callee + trust-cg caller",
                ),
            ] {
                match compile_caller_bin(
                    &dir,
                    &dylib,
                    bin_backend,
                    opt,
                    shape,
                    body,
                    rlib,
                    rlib_backend,
                ) {
                    Ok(bin) => {
                        let exit = run_exit_code(&bin);
                        if exit != oracle_exit {
                            failures.push(format!(
                                "O{opt} `{shape}` {label}: exit {exit}, oracle {oracle_exit}"
                            ));
                        }
                    }
                    Err(e) => failures.push(format!(
                        "O{opt} `{shape}` {label}: trust-cg caller failed closed: <<<{}>>>",
                        e.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                    )),
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} i128-argument combination(s) disagreed or refused:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
