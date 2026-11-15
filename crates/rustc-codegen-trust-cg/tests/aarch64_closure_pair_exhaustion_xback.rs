#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a CLOSURE BODY's scalar-pair argument at REGISTER
// EXHAUSTION, where code the other backend compiled calls the body BY SYMBOL,
// checked across the backend boundary in all four rlib x bin combinations at
// every optimization level on AArch64.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A closure BODY now declares a `PassMode::Pair` argument as rustc does, two
// values (`scalar_pair_param_plan` claims closure bodies), and every call of it
// passes two, through the one closure-argument builder
// (`closure_call_arg_values`). Under `-Zshare-generics` (on by default at
// `-Copt-level=0` / `1` / `s` / `z`) a closure body whose type escapes through its defining
// function's signature (a returned `impl Fn`) is exported by an rlib that
// instantiates it and linked by the downstream bin, so the body's own placement
// crosses the boundary.
//
// History: before the pair lane took closure bodies they declared the pair as
// ONE whole slot, placed all-or-nothing. Against the bridge at `60ed18893`
// (aarch64-apple-darwin, `targo --unverified`, no proof claim) this file's
// `refuse` rows gave, at O0, LLVM rlib x bridge bin / bridge rlib x LLVM bin
// `pair` 96 / 121 against 134, `option` 245 / 91 against 205, `range` 82 / 166
// against 243, `fnmut` 25 / 140 against 135, `slice` 240 / SIGTRAP against 133;
// the interim fix REFUSED those rlibs by name (`closure_pair_boundary_
// disagreement`, deleted with this change). Against origin/main `47f63ec1d`
// (that refusal) the `refuse` rlib is refused at O0 and none of its cells runs.
//
// THE RULE this file holds now: every cell of every row compiles and agrees
// with the LLVM oracle at every level — the former `refuse` rows (the pair at
// the last integer register) included. Nothing is refused.
// The `wide` and `wide2` rows put a `u128` before the pair (AAPCS64 starts it
// at an even register, so `wide`'s pair again meets only x7): measured wrong at
// O0 on AArch64 Linux at `fd6f7475f` (2026-10-02, before the closure-body
// whole-slot bound counted the skip); they are rows that must agree too.
//
// Executes only on an AArch64 host with its native `rust-std`.

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
    cfg!(target_arch = "aarch64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("a64clo_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// On AArch64 the per-compile proof certificates refuse every program with
/// `[TCG-PROOF-465]` (unrelated to argument placement), so this run turns them
/// off, as `tests/aarch64_arg_exhaustion_xback.rs` does.
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Set {
    Exhausted,
    Admit,
}

impl Set {
    fn tag(self) -> &'static str {
        match self {
            Set::Exhausted => "exhausted",
            Set::Admit => "admit",
        }
    }

    fn callee_src(self) -> &'static str {
        match self {
            Set::Exhausted => EXHAUSTED_CALLEE_SRC,
            Set::Admit => ADMIT_CALLEE_SRC,
        }
    }
}

fn compile_callee_rlib(
    dir: &Path,
    dylib: &Path,
    set: Set,
    backend: Backend,
    opt: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("callee_{}.rs", set.tag()));
    std::fs::write(&src_path, set.callee_src()).expect("write callee source");
    let out_dir = dir.join(format!("callee_{}_{}_O{opt}", set.tag(), backend.tag()));
    std::fs::create_dir_all(&out_dir).expect("create callee out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", "callee"]);
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
    let rlib = out_dir.join("libcallee.rlib");
    if !rlib.is_file() {
        return Err(format!("no rlib produced at {rlib:?}"));
    }
    Ok(rlib)
}

fn compile_caller_bin(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    shape: &str,
    body: &str,
    rlib: (Backend, &Path),
) -> Result<PathBuf, String> {
    let (rlib_backend, rlib) = rlib;
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
        cmd.arg(backend_arg(dylib));
        cmd.arg(backend_knobs());
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

/// The exit code, or the signal as a failure: a SIGSEGV is how a misplaced
/// argument can show, so it is a failed cell, not a harness panic.
fn run_exit_code(bin: &Path) -> Result<i32, String> {
    let out = Command::new(bin).output().expect("run binary");
    out.status
        .code()
        .ok_or_else(|| format!("exited via signal: {:?}", out.status))
}

/// Each `mkX` returns a closure whose type escapes through its signature, and
/// each `use_mkX` calls it, so the rlib instantiates (and at O0 exports) the
/// closure body. The pair follows the `&self` environment and six `u64`s, so
/// only x7 is left for it; in `mkw` it follows a `u128` and three `u64`s, and
/// AAPCS64 starts the `u128` at an even register (x1 skipped, x2:x3), so again
/// only x7 is left. Measured at `fd6f7475f`, whose bound counted the `u128`'s
/// two lanes but not the skip (2026-10-02 review, AArch64 Linux, O0, the
/// review's `shared_u128_pair` program): LLVM rlib x bridge bin and bridge rlib
/// x LLVM bin both gave wrong values.
const EXHAUSTED_CALLEE_SRC: &str = r#"
use core::hint::black_box as bb;
use core::ops::Range;
#[inline(never)] pub fn mkp(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, (u64, u64)) -> u64 { move |a, b, c, d, e, f, p| a + b + c + d + e + f + p.0 * 5 + p.1 * 3 + k * 7 }
#[inline(never)] pub fn use_mkp() -> u64 { let f = mkp(bb(1)); f(1, 2, 3, 4, 5, 6, (bb(5), 6)) }
#[inline(never)] pub fn mko(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, Option<u64>, u64) -> u64 { move |a, b, c, d, e, f, o, z| a + b + c + d + e + f + o.map_or(99, |v| v * 3) + z * 11 + k * 7 }
#[inline(never)] pub fn use_mko() -> u64 { let f = mko(bb(1)); f(1, 2, 3, 4, 5, 6, Some(bb(5)), 9) }
#[inline(never)] pub fn mkr(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, Range<usize>, u64) -> u64 { move |a, b, c, d, e, f, r, z| a + b + c + d + e + f + r.start as u64 * 5 + r.end as u64 * 3 + z * 11 + k * 7 }
#[inline(never)] pub fn use_mkr() -> u64 { let f = mkr(bb(1)); f(1, 2, 3, 4, 5, 6, bb(3)..9, 10) }
#[inline(never)] pub fn mkm(k: u64) -> impl FnMut(u64, u64, u64, u64, u64, u64, (u64, u64)) -> u64 { let mut n = 0u64; move |a, b, c, d, e, f, p| { n += 1; a + b + c + d + e + f + p.0 * 5 + p.1 * 3 + k * 7 + n } }
#[inline(never)] pub fn use_mkm() -> u64 { let mut f = mkm(bb(1)); f(1, 2, 3, 4, 5, 6, (bb(5), 6)) }
#[inline(never)] pub fn mks(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, &[u8]) -> u64 { move |a, b, c, d, e, f, s| a + b + c + d + e + f + s.len() as u64 * 5 + s[0] as u64 * 3 + k * 7 }
#[inline(never)] pub fn use_mks() -> u64 { let f = mks(bb(1)); f(1, 2, 3, 4, 5, 6, &[bb(9u8), 1][..]) }
#[inline(never)] pub fn mkw(k: u64) -> impl Fn(u128, u64, u64, u64, (u64, u64)) -> u64 { move |w, a, b, c, p| w as u64 + (w >> 64) as u64 * 2 + a + b + c + p.0 * 5 + p.1 * 3 + k * 7 }
#[inline(never)] pub fn use_mkw() -> u64 { let f = mkw(bb(1)); f((bb(3) << 64) | 1, 2, 3, 4, (bb(5), 6)) }
"#;

/// The same kind of closures with a register to spare (the environment and
/// five `u64`s before the pair, or a `u128` and two `u64`s, which leave x6:x7
/// in every register state), a 12-byte argument rustc passes by pointer
/// (the indirect argument lane) after seven `u64`s, and a closure whose type
/// never leaves its defining function.
const ADMIT_CALLEE_SRC: &str = r#"
use core::hint::black_box as bb;
#[inline(never)] pub fn mkp5(k: u64) -> impl Fn(u64, u64, u64, u64, u64, (u64, u64)) -> u64 { move |a, b, c, d, e, p| a + b + c + d + e + p.0 * 5 + p.1 * 3 + k * 7 }
#[inline(never)] pub fn use_mkp5() -> u64 { let f = mkp5(bb(1)); f(1, 2, 3, 4, 5, (bb(5), 6)) }
#[inline(never)] pub fn mks5(k: u64) -> impl Fn(u64, u64, u64, u64, u64, &[u8]) -> u64 { move |a, b, c, d, e, s| a + b + c + d + e + s.len() as u64 * 5 + s[0] as u64 * 3 + k * 7 }
#[inline(never)] pub fn use_mks5() -> u64 { let f = mks5(bb(1)); f(1, 2, 3, 4, 5, &[bb(9u8), 1][..]) }
pub struct T12 { pub a: u32, pub b: u32, pub c: u32 }
#[inline(never)] pub fn mkt(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, u64, T12, u32) -> u64 { move |a, b, c, d, e, f, g, t, y| a + b + c + d + e + f + g + t.a as u64 + t.c as u64 * 2 + y as u64 * 3 + k * 7 }
#[inline(never)] pub fn use_mkt() -> u64 { let f = mkt(bb(1)); f(1, 2, 3, 4, 5, 6, 7, T12 { a: bb(5), b: 77, c: 6 }, 10) }
#[inline(never)] pub fn mkw2(k: u64) -> impl Fn(u128, u64, u64, (u64, u64)) -> u64 { move |w, a, b, p| w as u64 + (w >> 64) as u64 * 2 + a + b + p.0 * 5 + p.1 * 3 + k * 7 }
#[inline(never)] pub fn use_mkw2() -> u64 { let f = mkw2(bb(1)); f((bb(3) << 64) | 1, 2, 3, (bb(5), 6)) }
#[inline(never)] pub fn internal(k: u64) -> u64 { let c = move |a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, p: (u64, u64)| a + b + c + d + e + f + p.0 * 5 + p.1 * 3 + k * 7; bb(&c)(1, 2, 3, 4, 5, 6, (bb(5), 6)) }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n";

/// `(set, shape, caller body, expected exit code)`. The expected code is the
/// oracle's (LLVM callee + LLVM caller) and is asserted.
fn shapes() -> Vec<(Set, &'static str, &'static str, i32)> {
    vec![
        (
            Set::Exhausted,
            "pair",
            r#"fn main() { let f = callee::mkp(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box((5, 6)))) }"#,
            134,
        ),
        (
            Set::Exhausted,
            "option",
            r#"fn main() { let f = callee::mko(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(Some(5)), black_box(9))) }"#,
            205,
        ),
        (
            Set::Exhausted,
            "range",
            r#"fn main() { let f = callee::mkr(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(3)..black_box(9), black_box(10))) }"#,
            243,
        ),
        (
            Set::Exhausted,
            "fnmut",
            r#"fn main() { let mut f = callee::mkm(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box((5, 6)))) }"#,
            135,
        ),
        (
            Set::Exhausted,
            "slice",
            r#"fn main() { let f = callee::mks(black_box(10)); let v = [black_box(9u8), 1, 2]; exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), &v[..])) }"#,
            133,
        ),
        (
            Set::Exhausted,
            "wide",
            r#"fn main() { let f = callee::mkw(black_box(10)); exit(f(black_box((3u128 << 64) | 1), black_box(2), black_box(3), black_box(4), black_box((5, 6)))) }"#,
            129,
        ),
        (
            Set::Admit,
            "pair5",
            r#"fn main() { let f = callee::mkp5(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box((5, 6)))) }"#,
            128,
        ),
        (
            Set::Admit,
            "slice5",
            r#"fn main() { let f = callee::mks5(black_box(10)); let v = [black_box(9u8), 1, 2]; exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), &v[..])) }"#,
            127,
        ),
        (
            Set::Admit,
            "mem7",
            r#"fn main() { let f = callee::mkt(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), callee::T12 { a: black_box(5), b: 77, c: black_box(6) }, black_box(10))) }"#,
            145,
        ),
        (
            Set::Admit,
            "wide2",
            r#"fn main() { let f = callee::mkw2(black_box(10)); exit(f(black_box((3u128 << 64) | 1), black_box(2), black_box(3), black_box((5, 6)))) }"#,
            125,
        ),
        (
            Set::Admit,
            "internal",
            r#"fn main() { exit(callee::internal(black_box(10))) }"#,
            134,
        ),
    ]
}

fn tail(stderr: &str) -> String {
    stderr.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
}

#[test]
fn closure_pairs_at_register_exhaustion_agree_aarch64() {
    if !host_is_aarch64() {
        eprintln!("skipping: the AArch64 run requires an AArch64 Linux or macOS host");
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("pair");
    let mut failures = Vec::new();
    for opt in ["0", "1", "2", "3"] {
        for set in [Set::Exhausted, Set::Admit] {
            let llvm_rlib = compile_callee_rlib(&dir, &dylib, set, Backend::Llvm, opt)
                .unwrap_or_else(|e| {
                    panic!("LLVM {} callee rlib failed at O{opt}: <<<{e}>>>", set.tag())
                });
            let tcg_rlib = match compile_callee_rlib(&dir, &dylib, set, Backend::TrustCg, opt) {
                Ok(rlib) => Some(rlib),
                Err(e) => {
                    failures.push(format!(
                        "O{opt}: trust-cg {} callee rlib failed: <<<{}>>>",
                        set.tag(),
                        tail(&e)
                    ));
                    None
                }
            };
            for (shape_set, shape, body, expected) in shapes() {
                if shape_set != set {
                    continue;
                }
                let oracle = compile_caller_bin(
                    &dir,
                    &dylib,
                    Backend::Llvm,
                    opt,
                    shape,
                    body,
                    (Backend::Llvm, &llvm_rlib),
                )
                .unwrap_or_else(|e| panic!("LLVM caller `{shape}` failed at O{opt}: <<<{e}>>>"));
                let oracle_exit = run_exit_code(&oracle)
                    .unwrap_or_else(|e| panic!("oracle (LLVM+LLVM) `{shape}` at O{opt}: {e}"));
                assert_eq!(
                    oracle_exit, expected,
                    "oracle (LLVM+LLVM) exit for `{shape}` at O{opt} is {oracle_exit}, \
                     expected {expected}"
                );
                let mut combos = vec![(
                    Backend::TrustCg,
                    (Backend::Llvm, llvm_rlib.as_path()),
                    "LLVM callee + trust-cg caller",
                )];
                if let Some(tcg_rlib) = tcg_rlib.as_deref() {
                    combos.push((
                        Backend::Llvm,
                        (Backend::TrustCg, tcg_rlib),
                        "trust-cg callee + LLVM caller",
                    ));
                    combos.push((
                        Backend::TrustCg,
                        (Backend::TrustCg, tcg_rlib),
                        "trust-cg callee + trust-cg caller",
                    ));
                }
                for (backend, rlib, label) in combos {
                    match compile_caller_bin(&dir, &dylib, backend, opt, shape, body, rlib) {
                        Ok(bin) => match run_exit_code(&bin) {
                            Ok(exit) if exit == oracle_exit => {}
                            Ok(exit) => failures.push(format!(
                                "O{opt} `{shape}` {label}: exit {exit}, oracle {oracle_exit}"
                            )),
                            Err(e) => failures.push(format!("O{opt} `{shape}` {label}: {e}")),
                        },
                        Err(e) => failures.push(format!(
                            "O{opt} `{shape}` {label}: failed to compile: <<<{}>>>",
                            tail(&e)
                        )),
                    }
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} closure-pair combination(s) disagreed or failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
