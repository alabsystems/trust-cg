#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a Rust-ABI `PassMode::Pair` ARGUMENT at REGISTER
// EXHAUSTION on AArch64 — exactly ONE argument register of the pair's class
// left when the pair is reached — checked ACROSS the backend boundary in all
// four rlib x bin combinations at every optimization level. The AArch64 twin of
// `m144_x86_pair_arg_exhaustion_xback.rs`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc passes a `PassMode::Pair` as TWO INDEPENDENT scalar arguments, so after
// seven integer arguments lane 0 takes x7 and lane 1 the first stack slot; after
// seven floats a float pair's lane 0 takes d7 / s7 and lane 1 the stack. The
// bridge declared an integer pair as ONE whole-slot aggregate on Apple AArch64
// (the independent lane was scoped to x86-64 and Linux AArch64), and a float pair
// on every target as ONE `Tuple([F64; 2])` float carrier; both are placed
// all-or-nothing, so the whole pair went to the stack and every later argument
// shifted. `check_param_abi` classifies a parameter in ISOLATION, so it passed.
// Measured 2026-09-29 on aarch64-apple-darwin before the fix (O0, O3): 33 of the
// 40 shape x level rows below disagreed with the LLVM oracle in a mixed-backend
// direction — `slice7`, `mut7`, `fnptr_slice7`, `self_method` SIGSEGV, the rest
// return wrong values — while every same-backend cell and the three controls
// (`slice6`, `f64pair6`: the pair fits; `slice8`: it is wholly on the stack)
// agreed. Every Rust `Pair` argument on AArch64 now rides the two-value lane
// (`scalar_pair_param_plan`), float pairs included.
//
// Rows: `&[u8]` with a byte read, `&str`, `*const [u8]`, a `&mut [u8]` the callee
// writes through, `(u64, u64)`, `(u32, u64)`, `Option<u64>` both variants, a
// trailing scalar after the pair (it must not be back-filled out of order), a
// pair returned by value, `(f64, f64)` and `(f32, f32)` after seven floats, a
// float after the float pair, a float pair returned, `fn` pointers (the `FnPtr`
// ABI source), a `&self` method, a trait-object method called from the other
// backend (the virtual lane), and the three controls.
//
// Executes on an AArch64 host (Apple or Linux). The bridge side passes
// `no-proof-certs`: with per-compile proof certificates on, AArch64 refuses
// every program with `[TCG-PROOF-465]`, unrelated to argument placement.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::AARCH64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn aarch64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn host_is_aarch64() -> bool {
    cfg!(target_arch = "aarch64") && host_target_support::HOST_OS_SUPPORTED
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m147_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn backend_knobs() -> String {
    toolchain_support::backend_knobs_arg(&["no-proof-certs"])
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

/// One callee rlib named `krate` compiled by `backend` at `opt`. The shapes of
/// a crate share one compile, so one refusal names every shape in it.
fn compile_callee_rlib(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    krate: &str,
    src: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{krate}.rs"));
    std::fs::write(&src_path, src).expect("write callee source");
    let out_dir = dir.join(format!("{krate}_{}_O{opt}", backend.tag()));
    std::fs::create_dir_all(&out_dir).expect("create callee out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", krate]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.arg(backend_knobs());
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
    let rlib = out_dir.join(format!("lib{krate}.rlib"));
    if !rlib.is_file() {
        return Err(format!("no rlib produced at {rlib:?}"));
    }
    Ok(rlib)
}

/// One caller bin for `shape`, compiled by `backend` at `opt` against `rlib`.
fn compile_caller_bin(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    shape: &str,
    body: &str,
    rlib: &Path,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("caller_{shape}.rs"));
    std::fs::write(&src_path, format!("{CALLER_HDR}{body}")).expect("write caller source");
    let bin = dir.join(format!(
        "caller_{shape}_{}rlib_{}bin_O{opt}",
        rlib_backend_tag(rlib),
        backend.tag()
    ));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.arg(backend_knobs());
    }
    let krate = rlib
        .file_stem()
        .and_then(|s| s.to_str())
        .and_then(|s| s.strip_prefix("lib"))
        .expect("rlib file name");
    let mut extern_arg = OsString::from(format!("{krate}="));
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

fn rlib_backend_tag(rlib: &Path) -> &'static str {
    let dir = rlib
        .parent()
        .and_then(|d| d.file_name())
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    if dir.contains("_tcg_") { "tcg" } else { "llvm" }
}

/// The exit code, or MINUS the signal number for a binary killed by a signal:
/// a mixed-backend cell that SIGSEGVs is one more disagreement to report, not a
/// reason to stop before the other cells have run.
fn run_exit_code(bin: &Path) -> i32 {
    let out = Command::new(bin).output().expect("run binary");
    if let Some(code) = out.status.code() {
        return code;
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = out.status.signal() {
            return -signal;
        }
    }
    panic!(
        "{bin:?} exited with neither a code nor a signal: {:?}",
        out.status
    )
}

/// The callee crate: one `#[inline(never)]` function per shape taking the pair
/// BY VALUE after seven arguments of its lanes' register class and folding the
/// lanes asymmetrically into a scalar, so a swapped, truncated or dirty lane is a
/// different exit code. The caller passes every input through `black_box`, so
/// nothing constant-folds across the boundary.
const CALLEE_SRC: &str = r#"
#[inline(never)] pub fn slice7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, s: &[u8]) -> u64 { a + b + c + d + e + f + g + s.len() as u64 * 100 + s[0] as u64 }
#[inline(never)] pub fn str7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, t: &str) -> u64 { a + b + c + d + e + f + g + t.len() as u64 * 100 + t.as_bytes()[t.len() - 1] as u64 }
#[inline(never)] pub fn raw7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, p: *const [u8]) -> u64 { a + b + c + d + e + f + g + p.len() as u64 * 100 }
#[inline(never)] pub fn mut7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, s: &mut [u8]) { s[0] = (a + b + c + d + e + f + g) as u8; let n = s.len(); s[n - 1] = n as u8; }
#[inline(never)] pub fn pair7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, p: (u64, u64)) -> u64 { a + b + c + d + e + f + g + p.0 * 10 + p.1 * 100 }
#[inline(never)] pub fn mix7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, p: (u32, u64)) -> u64 { a + b + c + d + e + f + g + p.0 as u64 * 10 + p.1 * 100 }
#[inline(never)] pub fn opt7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, o: Option<u64>) -> u64 { a + b + c + d + e + f + g + match o { Some(v) => v * 10, None => 7 } }
#[inline(never)] pub fn slice7_trailing(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, s: &[u8], k: u64) -> u64 { a + b + c + d + e + f + g + s.len() as u64 * 10 + k * 3 }
#[inline(never)] pub fn pair7_ret(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, p: (u64, u64)) -> (u64, u64) { (p.1 * 3 + a + b + c, p.0 * 5 + d + e + f + g) }
#[inline(never)] pub fn f64pair7(a: f64, b: f64, c: f64, d: f64, e: f64, f: f64, g: f64, p: (f64, f64), k: u64) -> u64 { (a + b + c + d + e + f + g + p.0 * 3.0 + p.1 * 5.0) as u64 + k }
#[inline(never)] pub fn f32pair7(a: f32, b: f32, c: f32, d: f32, e: f32, f: f32, g: f32, p: (f32, f32), k: u64) -> u64 { (a + b + c + d + e + f + g + p.0 * 3.0 + p.1 * 5.0) as u64 + k }
#[inline(never)] pub fn f64pair7_trailing(a: f64, b: f64, c: f64, d: f64, e: f64, f: f64, g: f64, p: (f64, f64), z: f64) -> u64 { (a + b + c + d + e + f + g + p.0 * 3.0 + p.1 * 5.0 + z * 7.0) as u64 }
#[inline(never)] pub fn f64pair7_ret(a: f64, b: f64, c: f64, d: f64, e: f64, f: f64, g: f64, p: (f64, f64)) -> (f64, f64) { (p.1 * 3.0 + a + b + c, p.0 * 5.0 + d + e + f + g) }
pub struct H(pub u64);
impl H { #[inline(never)] pub fn m(&self, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, s: &[u8]) -> u64 { self.0 + a + b + c + d + e + f + s.len() as u64 * 30 + s[0] as u64 } }
pub trait Tk { fn m(&self, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, s: &[u8]) -> u64; }
impl Tk for H { fn m(&self, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, s: &[u8]) -> u64 { self.0 * 2 + a + b + c + d + e + f + s.len() as u64 * 40 + s[s.len() - 1] as u64 } }
#[inline(never)] pub fn slice6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, s: &[u8]) -> u64 { a + b + c + d + e + f + s.len() as u64 * 100 + s[0] as u64 }
#[inline(never)] pub fn slice8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, s: &[u8]) -> u64 { a + b + c + d + e + f + g + h + s.len() as u64 * 100 + s[0] as u64 }
#[inline(never)] pub fn f64pair6(a: f64, b: f64, c: f64, d: f64, e: f64, f: f64, p: (f64, f64), k: u64) -> u64 { (a + b + c + d + e + f + p.0 * 3.0 + p.1 * 5.0) as u64 + k }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n";

/// `(shape, caller body, expected exit code)`. The expected code is the
/// oracle's (LLVM callee + LLVM caller), measured on aarch64-apple-darwin at O0
/// and O3, and is asserted so a corrupted oracle cannot make every combination
/// agree on a wrong value.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        (
            "slice7",
            r#"fn main() { exit(callee::slice7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(&b"ab"[..]))) }"#,
            74,
        ),
        (
            "str7",
            r#"fn main() { exit(callee::str7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box("abc"))) }"#,
            176,
        ),
        (
            "raw7",
            r#"fn main() { let s: &[u8] = black_box(&b"abcd"[..]); exit(callee::raw7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), s as *const [u8])) }"#,
            177,
        ),
        (
            "mut7",
            r#"fn main() { let mut b = [0u8; 3]; callee::mut7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(&mut b[..])); exit(b[0] as u64 * 10 + b[2] as u64) }"#,
            32,
        ),
        (
            "pair7",
            r#"fn main() { exit(callee::pair7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box((8, 9)))) }"#,
            4,
        ),
        (
            "mix7",
            r#"fn main() { exit(callee::mix7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box((8u32, 9u64)))) }"#,
            4,
        ),
        (
            "opt7",
            r#"fn main() { exit(callee::opt7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(Some(8))) + callee::opt7(black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), black_box(None))) }"#,
            122,
        ),
        (
            "slice7_trailing",
            r#"fn main() { exit(callee::slice7_trailing(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(&b"ab"[..]), black_box(9))) }"#,
            75,
        ),
        (
            "pair7_ret",
            r#"fn main() { let r = callee::pair7_ret(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box((8, 9))); exit(r.0 + r.1 * 2) }"#,
            157,
        ),
        (
            "f64pair7",
            r#"fn main() { exit(callee::f64pair7(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0), black_box(5.0), black_box(6.0), black_box(7.0), black_box((10.5, 0.25)), black_box(11))) }"#,
            71,
        ),
        (
            "f32pair7",
            r#"fn main() { exit(callee::f32pair7(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0), black_box(5.0), black_box(6.0), black_box(7.0), black_box((10.5, 0.25)), black_box(11))) }"#,
            71,
        ),
        (
            "f64pair7_trailing",
            r#"fn main() { exit(callee::f64pair7_trailing(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0), black_box(5.0), black_box(6.0), black_box(7.0), black_box((10.5, 0.25)), black_box(4.0))) }"#,
            88,
        ),
        (
            "f64pair7_ret",
            r#"fn main() { let r = callee::f64pair7_ret(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0), black_box(5.0), black_box(6.0), black_box(7.0), black_box((10.5, 0.25))); exit((r.0 + r.1 * 2.0) as u64) }"#,
            155,
        ),
        (
            "fnptr_slice7",
            r#"fn main() { let f: fn(u64, u64, u64, u64, u64, u64, u64, &[u8]) -> u64 = black_box(callee::slice7); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(&b"xyz"[..]))) }"#,
            197,
        ),
        (
            "fnptr_f64pair7",
            r#"fn main() { let f: fn(f64, f64, f64, f64, f64, f64, f64, (f64, f64), u64) -> u64 = black_box(callee::f64pair7); exit(f(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0), black_box(5.0), black_box(6.0), black_box(7.0), black_box((10.5, 0.25)), black_box(11))) }"#,
            71,
        ),
        (
            "self_method",
            r#"fn main() { let h = callee::H(black_box(50)); exit(h.m(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(&b"ab"[..]))) }"#,
            228,
        ),
        (
            "dyn_method",
            r#"fn main() { let h = callee::H(black_box(5)); let t: &dyn callee::Tk = &h; exit(t.m(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(&b"abc"[..]))) }"#,
            250,
        ),
        (
            "slice6",
            r#"fn main() { exit(callee::slice6(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(&b"ab"[..]))) }"#,
            67,
        ),
        (
            "slice8",
            r#"fn main() { exit(callee::slice8(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box(&b"ab"[..]))) }"#,
            82,
        ),
        (
            "f64pair6",
            r#"fn main() { exit(callee::f64pair6(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0), black_box(5.0), black_box(6.0), black_box((10.5, 0.25)), black_box(11))) }"#,
            64,
        ),
    ]
}

#[test]
fn pair_arguments_at_register_exhaustion_agree_across_backends_aarch64() {
    if !host_is_aarch64() {
        eprintln!("skipping: the AArch64 run requires an AArch64 Linux or macOS host");
        return;
    }
    if toolchain_support::skip_without_backend_knobs(
        "pair_arguments_at_register_exhaustion_agree_across_backends_aarch64",
    ) {
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("exh");
    let mut failures = Vec::new();
    let krate = "callee";
    for opt in ["0", "1", "2", "3"] {
        let llvm_rlib = compile_callee_rlib(&dir, &dylib, Backend::Llvm, opt, krate, CALLEE_SRC)
            .unwrap_or_else(|e| panic!("LLVM `{krate}` rlib failed at O{opt}: <<<{e}>>>"));
        let tcg_rlib =
            match compile_callee_rlib(&dir, &dylib, Backend::TrustCg, opt, krate, CALLEE_SRC) {
                Ok(rlib) => rlib,
                Err(e) => {
                    failures.push(format!(
                        "O{opt} `{krate}`: trust-cg callee rlib failed closed: <<<{}>>>",
                        e.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
                    ));
                    continue;
                }
            };
        for (shape, body, expected) in shapes() {
            let oracle =
                compile_caller_bin(&dir, &dylib, Backend::Llvm, opt, shape, body, &llvm_rlib)
                    .unwrap_or_else(|e| {
                        panic!("LLVM caller `{shape}` failed at O{opt}: <<<{e}>>>")
                    });
            let oracle_exit = run_exit_code(&oracle);
            assert_eq!(
                oracle_exit, expected,
                "oracle (LLVM+LLVM) exit for `{shape}` at O{opt} is {oracle_exit}, expected {expected}"
            );
            let combos = [
                (
                    Backend::TrustCg,
                    &llvm_rlib,
                    "LLVM callee + trust-cg caller",
                ),
                (Backend::Llvm, &tcg_rlib, "trust-cg callee + LLVM caller"),
                (
                    Backend::TrustCg,
                    &tcg_rlib,
                    "trust-cg callee + trust-cg caller",
                ),
            ];
            for (backend, rlib, label) in combos {
                match compile_caller_bin(&dir, &dylib, backend, opt, shape, body, rlib) {
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
        "{} pair-argument-at-exhaustion combination(s) disagreed or refused:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
