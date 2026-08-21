#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: the dynamic-growth bulk-append memcpy path —
// `String::push_str`, `Vec::extend_from_slice`, and the `-O3`-inlined
// `Vec::<T>::append_elements` kernel both reduce to — compiled + run for
// x86_64 via the rustc_codegen_trust_cg bridge and DIFFERENTIALLY compared
// against rustc's default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: task #100 — bulk-append (typed memcpy + grow).
//
// `String::push_str(&str)` and `Vec::<T>::extend_from_slice(&[T])` both APPEND a
// run of elements to a `{ ptr, cap, len }` slot's heap buffer: grow the buffer to
// `len + n` (an unconditional `__rust_realloc` to `max(cap, len+n)*size` — sound
// because the buffer is always a real allocation), `copy_nonoverlapping` the `n`
// source elements to `buf + len` (a runtime element-by-element typed copy loop —
// the bridge has no memcpy opcode), then `len += n`. At `-O3` BOTH reduce to a
// single `Vec::<T>::append_elements(&mut self, *const [T])` whose source slice is
// REBUILT from a `slice::Iter::as_slice` round-trip (`ptr_offset_from_unsigned` +
// `*const [T] from (data, meta)`); the interception traces that reconstruction
// back to the original slice's `(data, len)` rather than executing the arithmetic.
//
// SOUNDNESS-FIRST: only INTEGER / `u8` element types with a computable element
// size are modeled. A non-integer / ZST / wider-than-64-bit element, an
// unresolvable source slice, or a projected destination FAILS CLOSED (a precise
// diagnostic) — never a wrong byte or a wrong length.
//
// LEVEL SCOPE:
//   * `String::push_str`        — O0 AND O3 (byte-correct).
//   * `Vec::extend_from_slice`  — O0 AND O3 (byte-correct).
//   * `write!(s, ...)`          — O0 only (intercepted via `write_fmt`); at -O3
//     `write!` does NOT inline through `push_str` — it builds `fmt::Arguments` and
//     calls the generic `std::fmt::write` engine (a `core::fmt::rt::ArgumentType`
//     placeholder + Formatter machinery the bridge cannot lower), so `write!`@O3
//     FAILS CLOSED (a SAFE coverage gap, never a miscompile — a DIFFERENT beast
//     from `push_str`, see the task report).
//
// The CONTENT checks read the buffer back through `v[i]` / `s.as_bytes()[i]` in a
// counted loop and exit with a 31-rolling-hash of the bytes — a wrong byte or a
// wrong offset surfaces as a mismatch. The Vec content reader lowers at O0 AND O3;
// the String `as_bytes()` reader needs a runtime-length fat pointer that lowers
// only at O3 (the O0 slice-metadata side table carries compile-time lengths only),
// so the String content check is asserted at O3 and allowed to fail closed at O0 —
// a HARNESS limitation, not an append bug (the O0 push_str bytes are themselves
// correct; the O0 `len()` test exercises the append, and the O3 content test the
// bytes).

use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output};
use std::sync::OnceLock;

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m100 test");
    let built = target_dir
        .join("release")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TargetHostPair {
    target: &'static str,
    host_os: &'static str,
    host_arch: &'static str,
}

impl TargetHostPair {
    fn current() -> Self {
        Self {
            target: TARGET,
            host_os: std::env::consts::OS,
            host_arch: std::env::consts::ARCH,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TargetRunnerCapability {
    Runnable,
    UnsupportedMacOsArm64Ebadarch {
        pair: TargetHostPair,
        raw_os_error: i32,
    },
    /// The pinned toolchain has no x86_64-apple-darwin rust-std component,
    /// so the probe cannot even COMPILE for the foreign target. Every
    /// sibling x86 suite (m90/m126/m128/...) treats exactly this state as a
    /// whole-suite self-skip ("skipping: rust-std for {TARGET} not
    /// installed"); this suite's probe previously hard-panicked on it,
    /// which failed the release gate on hosts that deliberately do not
    /// carry the foreign std (an aarch64 release box without Rosetta could
    /// not run the produced binaries anyway).
    MissingForeignStd {
        pair: TargetHostPair,
    },
}

/// Classify execution of the known-trivial target probe.
///
/// The sole skippable result is macOS/arm64 refusing an x86_64 Mach-O with
/// `EBADARCH` (raw OS error 86). A non-zero program status, another spawn error,
/// another host/target pair, or even adjacent raw error 85 stays HARD: those are
/// not evidence that this machine merely lacks the target runner.
fn classify_target_runner_status(
    pair: TargetHostPair,
    result: io::Result<ExitStatus>,
) -> Result<TargetRunnerCapability, String> {
    match result {
        Ok(status) if status.success() => Ok(TargetRunnerCapability::Runnable),
        Ok(status) => Err(format!(
            "known-trivial target runner probe exited unsuccessfully: status={status}, \
             target={}, host={}/{}",
            pair.target, pair.host_os, pair.host_arch
        )),
        Err(err)
            if pair.target == TARGET
                && pair.host_os == "macos"
                && pair.host_arch == "aarch64"
                && err.raw_os_error() == Some(86) =>
        {
            Ok(TargetRunnerCapability::UnsupportedMacOsArm64Ebadarch {
                pair,
                raw_os_error: 86,
            })
        }
        Err(err) => Err(format!(
            "known-trivial target runner probe could not execute: error={err}, raw_os_error={:?}, \
             target={}, host={}/{}",
            err.raw_os_error(),
            pair.target,
            pair.host_os,
            pair.host_arch
        )),
    }
}

fn probe_compile_missing_foreign_std(output: &Output) -> bool {
    let stderr = String::from_utf8_lossy(&output.stderr);
    stderr.contains("E0463") || stderr.contains("can't find crate for `std`")
}

fn require_probe_compile_success(pair: TargetHostPair, output: &Output) -> Result<(), String> {
    if output.status.success() {
        return Ok(());
    }
    Err(format!(
        "known-trivial target runner probe failed to compile: status={}, target={}, host={}/{}, \
         stderr=<<<{}>>>",
        output.status,
        pair.target,
        pair.host_os,
        pair.host_arch,
        String::from_utf8_lossy(&output.stderr)
    ))
}

fn probe_x86_64_target_runner() -> Result<TargetRunnerCapability, String> {
    let pair = TargetHostPair::current();
    let dir = workdir("runner_probe");
    let result = (|| {
        let src = dir.join("trivial.rs");
        std::fs::write(&src, "fn main() {}\n")
            .map_err(|err| format!("write target runner probe source: {err}"))?;
        let bin = dir.join("trivial_x86_64");
        let output = Command::new("rustup")
            .args([
                "run",
                pinned_toolchain().as_str(),
                "rustc",
                "--edition=2021",
            ])
            .args(["--crate-type", "bin", "--target", TARGET, "-Cpanic=abort"])
            .arg("-o")
            .arg(&bin)
            .arg(&src)
            .output()
            .map_err(|err| {
                format!(
                    "spawn target runner probe compiler: {err}; target={}, host={}/{}",
                    pair.target, pair.host_os, pair.host_arch
                )
            })?;
        if probe_compile_missing_foreign_std(&output) {
            return Ok(TargetRunnerCapability::MissingForeignStd { pair });
        }
        require_probe_compile_success(pair, &output)?;
        classify_target_runner_status(pair, Command::new(&bin).status())
    })();
    let _ = std::fs::remove_dir_all(&dir);
    result
}


fn runner_probe_result() -> &'static Result<TargetRunnerCapability, String> {
    static RUNNER_PROBE: OnceLock<Result<TargetRunnerCapability, String>> = OnceLock::new();
    RUNNER_PROBE.get_or_init(probe_x86_64_target_runner)
}

fn x86_64_runtime_available() -> bool {
    match runner_probe_result() {
        Ok(TargetRunnerCapability::Runnable) => true,
        Ok(TargetRunnerCapability::UnsupportedMacOsArm64Ebadarch { pair, raw_os_error }) => {
            eprintln!(
                "skipping x86 execution only: target={}, host={}/{}, macOS EBADARCH raw_os_error={raw_os_error}; compile authority remains mandatory",
                pair.target, pair.host_os, pair.host_arch
            );
            false
        }
        Ok(TargetRunnerCapability::MissingForeignStd { pair }) => {
            eprintln!(
                "skipping: rust-std for {} not installed for pinned toolchain (host {}/{})",
                pair.target, pair.host_os, pair.host_arch
            );
            false
        }
        Err(err) => panic!("x86 target runner capability probe failed hard: {err}"),
    }
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m100_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with rustc's default LLVM backend at `-O` and return the run's
/// exit code (the GROUND TRUTH).
fn run_llvm(dir: &Path, src: &str) -> i32 {
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join("llvm_out");
    let status = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin", "-Cpanic=abort", "-O"])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .status()
        .expect("spawn rustc (LLVM)");
    assert!(status.success(), "LLVM reference failed to compile: <<<{src}>>>");
    Command::new(&bin)
        .status()
        .expect("run LLVM binary")
        .code()
        .expect("LLVM binary exit code")
}

/// Compile `src` via the trust-cg bridge at `opt_level`. Returns the target
/// binary when compilation and linking succeeded; `None` is reserved for the
/// bridge's explicit fail-closed/unsupported diagnostics.
fn compile_bridge(dir: &Path, dylib: &Path, src: &str, opt_level: &str) -> Option<PathBuf> {
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("bridge_out_{opt_level}"));
    let output = Command::new("rustup")
        .args([
            "run",
            pinned_toolchain().as_str(),
            "rustc",
            "--edition=2021",
        ])
        .args(["--crate-type", "bin"])
        .arg(backend_arg(dylib))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt_level}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc (bridge)");
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        if probe_compile_missing_foreign_std(&output) {
            // Same self-skip as every sibling suite: without the foreign
            // rust-std component neither runtime NOR compile authority is
            // testable for this target on this host.
            eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
            return None;
        }
        if stderr.contains("failing closed") || stderr.contains("unsupported") {
            eprintln!("bridge failed closed at -O{opt_level}: <<<{stderr}>>>");
            return None;
        }
        panic!("bridge compile failed (not fail-closed) at -O{opt_level}: <<<{stderr}>>>");
    }
    assert!(
        !stderr.contains("Undefined symbols"),
        "bridge link has an undefined symbol at -O{opt_level}: <<<{stderr}>>>"
    );
    Some(bin)
}

/// Compile and execute through the bridge. Target execution is called only
/// after the process-wide known-trivial runner probe says the exact host/target
/// pair is runnable; any later spawn failure remains hard.
fn run_bridge(dir: &Path, dylib: &Path, src: &str, opt_level: &str) -> Option<i32> {
    let bin = compile_bridge(dir, dylib, src, opt_level)?;
    let code = Command::new(&bin)
        .status()
        .unwrap_or_else(|err| {
            let pair = TargetHostPair::current();
            panic!(
                "run bridge binary failed after successful target-runner probe: {err}; \
                 raw_os_error={:?}, target={}, host={}/{}",
                err.raw_os_error(),
                pair.target,
                pair.host_os,
                pair.host_arch
            )
        })
        .code()
        .expect("bridge binary exit code");
    Some(code)
}

#[test]
fn runner_probe_classifies_only_macos_arm64_ebadarch_86_as_skippable() {
    let supported_skip_pair = TargetHostPair {
        target: TARGET,
        host_os: "macos",
        host_arch: "aarch64",
    };
    assert_eq!(
        classify_target_runner_status(supported_skip_pair, Err(io::Error::from_raw_os_error(86))),
        Ok(TargetRunnerCapability::UnsupportedMacOsArm64Ebadarch {
            pair: supported_skip_pair,
            raw_os_error: 86,
        })
    );

    for (pair, raw_os_error) in [
        (supported_skip_pair, 85),
        (
            TargetHostPair {
                target: TARGET,
                host_os: "macos",
                host_arch: "x86_64",
            },
            86,
        ),
        (
            TargetHostPair {
                target: TARGET,
                host_os: "linux",
                host_arch: "aarch64",
            },
            86,
        ),
        (
            TargetHostPair {
                target: "aarch64-apple-darwin",
                host_os: "macos",
                host_arch: "aarch64",
            },
            86,
        ),
    ] {
        assert!(
            classify_target_runner_status(pair, Err(io::Error::from_raw_os_error(raw_os_error)))
                .is_err(),
            "raw error {raw_os_error} for {pair:?} must remain hard"
        );
    }
}

#[test]
fn runner_probe_nonzero_and_compile_failures_remain_hard() {
    let pair = TargetHostPair::current();
    let nonzero = Command::new("/usr/bin/false")
        .output()
        .expect("invoke ordinary failing process");
    assert!(
        classify_target_runner_status(pair, Ok(nonzero.status)).is_err(),
        "an ordinary non-zero execution is not an unsupported-host skip"
    );
    assert!(
        require_probe_compile_success(pair, &nonzero).is_err(),
        "an ordinary compiler failure is not an unsupported-host skip"
    );
}

/// Compile-only authority is deliberately independent of host execution. On an
/// arm64 Mac without Rosetta the runtime rows skip only after the runner probe,
/// but these representative TrustIR/codegen paths still MUST compile. In
/// particular the dyn-Fn `ClosureOnceShim` failure remains hard rather than
/// being hidden by the target-runner classification. A missing target stdlib or
/// any compiler/toolchain failure is likewise hard; EBADARCH 86 classifies only
/// execution of an artifact that has already compiled successfully.
#[test]
fn compile_authority_runs_even_when_x86_target_cannot_execute() {
    // Without the foreign rust-std component, compile authority itself is
    // untestable (the sibling-suite skip state); the EBADARCH-only case this
    // test exists for requires std present but execution impossible.
    if matches!(
        runner_probe_result(),
        Ok(TargetRunnerCapability::MissingForeignStd { .. })
    ) {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("compile_authority");
    let cases = [
        (
            "push_str/copy_nonoverlapping",
            "fn main(){let mut s=String::new();s.push_str(std::hint::black_box(\"trust\"));\
             std::process::exit(s.len() as i32);}",
        ),
        (
            "write_bytes/memset",
            "fn main(){let mut b=[9u8;8];unsafe{std::ptr::write_bytes(b.as_mut_ptr(),1,4);}\
             std::process::exit(b[0] as i32);}",
        ),
        (
            "dyn-Fn tuple spread / ZST ClosureOnceShim",
            "fn main(){let f:&dyn Fn(i64,i64,i64)->i64=&|a,b,c| a-b*10+c*100;\
             std::process::exit((f(2,3,4)).rem_euclid(128) as i32);}",
        ),
        (
            "dyn-Fn tuple spread / captured ClosureOnceShim",
            "fn main(){let k=7i64;let f:&dyn Fn(i64,i64)->i64=&|a,b| a*k+b;\
             std::process::exit((f(3,5)).rem_euclid(128) as i32);}",
        ),
        (
            "dyn-FnMut tuple spread / captured ClosureOnceShim",
            "fn main(){let mut acc=0i64;{let mut g:&mut dyn FnMut(i64,i64,i64)->i64=&mut |a,b,c|{acc+=a+b+c;acc};\
             let r=g(1,2,3)+g(4,5,6);std::process::exit(r.rem_euclid(128) as i32);}}",
        ),
        (
            "dyn-Fn tuple spread / reference arg ClosureOnceShim",
            "fn main(){let x=41i64;let f:&dyn Fn(&i64,i64,i64)->i64=&|p,b,c| *p+b+c;\
             std::process::exit((f(&x,3,4)).rem_euclid(128) as i32);}",
        ),
    ];
    for (label, src) in cases {
        assert!(
            compile_bridge(&dir, &dylib, src, "0").is_some(),
            "compile-only authority failed closed for {label}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `String::push_str` and `Vec::extend_from_slice` LENGTH check: every case must
/// be intercepted and MATCH LLVM at BOTH -O0 AND -O3. The exit value derives from
/// the collection's `len()` (a strong check on the per-append `len += n` and the
/// grow accounting across many capacity doublings).
#[test]
fn push_str_and_extend_len_match_llvm_at_o0_and_o3() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("len");

    // (program, human label). Each exits with a `len`-derived value.
    let cases: &[(&str, &str)] = &[
        // single + repeated push_str (multiple grows past capacity).
        (
            "fn main(){let mut s=String::new(); s.push_str(std::hint::black_box(\"hello\")); \
             std::process::exit(s.len() as i32);}",
            "push_str single",
        ),
        (
            "fn main(){let mut s=String::new(); \
             s.push_str(std::hint::black_box(\"hello\")); \
             s.push_str(std::hint::black_box(\" world!\")); \
             std::process::exit(s.len() as i32);}",
            "push_str twice (grow)",
        ),
        (
            "fn main(){let mut s=String::new(); let mut k=0; \
             while k<25 {s.push_str(std::hint::black_box(\"abcé\")); k+=1;} \
             std::process::exit((s.len()%250) as i32);}",
            "push_str x25 multibyte (many grows)",
        ),
        // mixed Vec push (single integer element) + extend_from_slice. Both the
        // single `push` and the bulk `extend` grow the SAME `{ptr,cap,len}` slot;
        // interleaving them stresses the len/cap bookkeeping across both paths.
        // (`String::push(char)` is a separate char-based method NOT in this task's
        // scope — it fails closed safely — so the mixed case uses an integer Vec.)
        (
            "fn main(){let mut v:Vec<i32>=Vec::new(); let mut k=0i32; \
             while k<10 {v.push(std::hint::black_box(k)); \
             v.extend_from_slice(std::hint::black_box(&[k+100,k+200])); k+=1;} \
             std::process::exit((v.len()%250) as i32);}",
            "mixed Vec push + extend",
        ),
        // Vec::extend_from_slice of various widths, with grow.
        (
            "fn main(){let mut v:Vec<i64>=Vec::new(); \
             v.extend_from_slice(std::hint::black_box(&[1i64,2,3])); \
             std::process::exit(v.len() as i32);}",
            "extend i64 single",
        ),
        (
            "fn main(){let mut v:Vec<u8>=Vec::new(); let mut k=0; \
             while k<30 {v.extend_from_slice(std::hint::black_box(&[7u8,8,9,10,11])); k+=1;} \
             std::process::exit((v.len()%250) as i32);}",
            "extend u8 x30 (many grows)",
        ),
        (
            "fn main(){let mut v:Vec<i32>=Vec::new(); let mut k=0i32; \
             while k<15 {v.extend_from_slice(std::hint::black_box(&[k,k+1,k+2,k+3])); k+=1;} \
             std::process::exit((v.len()%250) as i32);}",
            "extend i32 x15",
        ),
    ];

    let mut ok_o0 = 0usize;
    let mut ok_o3 = 0usize;
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        match run_bridge(&dir, &dylib, src, "0") {
            Some(code) => {
                assert_eq!(code, llvm, "O0 MISMATCH `{label}`: bridge={code} llvm={llvm}");
                ok_o0 += 1;
            }
            None => panic!("`{label}` unexpectedly FAILED CLOSED at O0"),
        }
        match run_bridge(&dir, &dylib, src, "3") {
            Some(code) => {
                assert_eq!(
                    code, llvm,
                    "O3 MISMATCH `{label}`: bridge={code} llvm={llvm} (a miscompile!)"
                );
                ok_o3 += 1;
            }
            None => panic!("`{label}` unexpectedly FAILED CLOSED at O3"),
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(ok_o0, cases.len(), "every push_str/extend case intercepted at O0");
    assert_eq!(ok_o3, cases.len(), "every push_str/extend case intercepted at O3");
}

/// CONTENT check for `Vec::extend_from_slice` (not just length): build the Vec via
/// repeated extends with grow, then read it back through `v[i]` in a counted loop
/// and exit with a 31-rolling-hash of the elements. A wrong byte, a wrong copy
/// offset, or a dropped element surfaces as a mismatch. The `v[i]` reader lowers
/// at BOTH -O0 AND -O3, so the content MUST match LLVM at both.
#[test]
fn extend_byte_content_matches_llvm_at_o0_and_o3() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("vec_content");

    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let mut v:Vec<i32>=Vec::new(); let mut k=0i32; \
             while k<15 {v.extend_from_slice(std::hint::black_box(&[k,k+1,k+2,k+3])); k+=1;} \
             let mut h:i64=0; let mut i=0usize; \
             while i<v.len() {h=h.wrapping_add((v[i] as i64).wrapping_mul(i as i64+1)); i+=1;} \
             std::process::exit((h.rem_euclid(240)) as i32);}",
            "i32 extend content",
        ),
        (
            "fn main(){let mut v:Vec<i64>=Vec::new(); let mut k=0i64; \
             while k<12 {v.extend_from_slice(std::hint::black_box(&[k*2,k*3,k*5])); k+=1;} \
             let mut h:i64=0; let mut i=0usize; \
             while i<v.len() {h=h.wrapping_add(v[i].wrapping_mul(i as i64+1)); i+=1;} \
             std::process::exit((h.rem_euclid(240)) as i32);}",
            "i64 extend content",
        ),
        (
            "fn main(){let mut v:Vec<u8>=Vec::new(); let mut k=0u8; \
             while k<40 {v.extend_from_slice(std::hint::black_box(&[k,k.wrapping_add(1)])); k=k.wrapping_add(1);} \
             let mut h:i64=0; let mut i=0usize; \
             while i<v.len() {h=h.wrapping_add((v[i] as i64).wrapping_mul(i as i64+1)); i+=1;} \
             std::process::exit((h.rem_euclid(240)) as i32);}",
            "u8 extend content",
        ),
    ];

    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                Some(code) => assert_eq!(
                    code, llvm,
                    "content MISMATCH `{label}` at -O{opt}: bridge={code} llvm={llvm}"
                ),
                None => panic!("`{label}` unexpectedly FAILED CLOSED at -O{opt} (content)"),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// CONTENT check for `String::push_str` at -O3: build the String via repeated
/// push_str with grow (ascii + multibyte), read it back through `s.as_bytes()[i]`
/// in a counted loop, and exit with a 31-rolling-hash. A wrong byte / offset
/// surfaces as a mismatch. The runtime-length `as_bytes()` reader lowers at -O3;
/// at -O0 it fails closed (the constant-length slice-metadata side table) — a
/// HARNESS limitation (the O0 push_str bytes are themselves correct, exercised by
/// the length test), so O0 is allowed to fail closed here.
#[test]
fn push_str_byte_content_matches_llvm_at_o3() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("str_content");

    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let mut s=String::new(); \
             s.push_str(std::hint::black_box(\"hello\")); \
             s.push_str(std::hint::black_box(\" world!\")); \
             let b=s.as_bytes(); let mut h:i32=0; let mut i=0usize; \
             while i<b.len() {h=(h.wrapping_mul(31).wrapping_add(b[i] as i32))%1000; i+=1;} \
             std::process::exit(((h%250)+250)%250);}",
            "ascii push_str content",
        ),
        (
            "fn main(){let mut s=String::new(); let mut k=0; \
             while k<20 {s.push_str(std::hint::black_box(\"abcé\")); k+=1;} \
             let b=s.as_bytes(); let mut h:i32=0; let mut i=0usize; \
             while i<b.len() {h=(h.wrapping_mul(31).wrapping_add(b[i] as i32))%1000; i+=1;} \
             std::process::exit(((h%250)+250)%250);}",
            "multibyte push_str x20 content",
        ),
    ];

    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        match run_bridge(&dir, &dylib, src, "3") {
            Some(code) => assert_eq!(
                code, llvm,
                "content MISMATCH `{label}` at -O3: bridge={code} llvm={llvm}"
            ),
            None => panic!("`{label}` unexpectedly FAILED CLOSED at -O3 (content)"),
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `write!(s, ...)` at -O0 appends through the intercepted `<String as
/// Write>::write_fmt` path (reusing the `format!` synthesis into the String slot),
/// so it MATCHES LLVM at -O0. At -O3 `write!` does NOT inline through `push_str` —
/// it builds `fmt::Arguments` and calls the generic `std::fmt::write` engine
/// (`core::fmt::rt::ArgumentType` + Formatter machinery), which the bridge cannot
/// lower, so `write!`@O3 FAILS CLOSED (a safe coverage gap). This test pins BOTH:
/// O0 matches, O3 fails closed (never a wrong answer).
#[test]
fn write_matches_at_o0_and_fails_closed_at_o3() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("write");

    let cases: &[(&str, &str)] = &[
        (
            "use std::fmt::Write; \
             fn main(){let mut s=String::new(); \
             write!(s, \"v={}\", std::hint::black_box(789i32)).unwrap(); \
             std::process::exit(s.len() as i32);}",
            "write! single int",
        ),
        (
            "use std::fmt::Write; \
             fn main(){let mut s=String::new(); \
             write!(s, \"{}x{}\", std::hint::black_box(12i32), std::hint::black_box(34i32)).unwrap(); \
             std::process::exit(s.len() as i32);}",
            "write! two ints",
        ),
    ];

    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        match run_bridge(&dir, &dylib, src, "0") {
            Some(code) => assert_eq!(code, llvm, "O0 write! MISMATCH `{label}`: bridge={code} llvm={llvm}"),
            None => panic!("`{label}` unexpectedly FAILED CLOSED at O0 (write! should intercept)"),
        }
        // O3 must EITHER match OR fail closed — never a wrong answer.
        if let Some(code) = run_bridge(&dir, &dylib, src, "3") {
            assert_eq!(
                code, llvm,
                "O3 write! `{label}` compiled but is WRONG: bridge={code} llvm={llvm} (a miscompile!)"
            );
        }
        // (None at O3 is the expected, accepted fail-closed outcome.)
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Item names plus String-shaped arguments are not sufficient authority for the
/// fmt/String interceptor. User items deliberately named like std entry points
/// must execute their own semantics or fail closed, never be synthesized as the
/// unrelated std operation.
#[test]
fn user_fmt_and_string_name_spoofs_fail_closed_or_match() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("fmt_name_spoofs");
    let cases: &[(&str, &str, i32)] = &[
        (
            "user new returning a nonempty String",
            "#[inline(never)] fn new()->String{String::from(\"spoof\")} \
             fn main(){let s=new();std::process::exit(s.len() as i32);}",
            5,
        ),
        (
            "user must_use mutating its String",
            "#[inline(never)] fn must_use(mut s:String)->String{s.push_str(\"!\");s} \
             fn main(){let s=must_use(String::from(\"abc\"));std::process::exit(s.len() as i32);}",
            4,
        ),
        (
            "user Evil::len over String",
            "trait Evil{fn len(&self)->usize;} impl Evil for String{ \
             #[inline(never)] fn len(&self)->usize{77}} \
             fn main(){let s=String::from(\"abc\");std::process::exit(Evil::len(&s) as i32);}",
            77,
        ),
        (
            "user EvilWrite::write_fmt over String",
            "trait EvilWrite{fn write_fmt(&mut self,a:std::fmt::Arguments<'_>)->std::fmt::Result;} \
             impl EvilWrite for String{#[inline(never)] fn write_fmt( \
             &mut self,_a:std::fmt::Arguments<'_>)->std::fmt::Result{self.push_str(\"evil\");Ok(())}} \
             fn main(){let mut s=String::new();EvilWrite::write_fmt( \
             &mut s,format_args!(\"ignored\")).unwrap();std::process::exit(s.len() as i32);}",
            4,
        ),
    ];

    for (label, src, expected) in cases {
        let llvm = run_llvm(&dir, src);
        assert_eq!(llvm, *expected, "LLVM sanity result for `{label}`");
        for opt in ["0", "2", "3"] {
            if let Some(code) = run_bridge(&dir, &dylib, src, opt) {
                assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} was intercepted by name and miscompiled"
                );
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// FAIL-CLOSED pins: shapes the bulk-append model must REFUSE (never miscompile).
/// A non-integer element type (`Vec<&str>`, `Vec<(i64,i64)>`) has no single-scalar
/// leaf the per-element copy loop can store, so `extend_from_slice` of it must
/// fail closed (or — if some unrelated path happens to compile it — still MATCH
/// LLVM; it must never be WRONG).
#[test]
fn non_integer_extend_fails_closed_or_matches() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("failclosed");

    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let mut v:Vec<(i64,i64)>=Vec::new(); \
             v.extend_from_slice(std::hint::black_box(&[(1i64,2i64),(3,4)])); \
             std::process::exit(v.len() as i32);}",
            "extend tuple element",
        ),
        (
            "fn main(){let mut v:Vec<[i64;2]>=Vec::new(); \
             v.extend_from_slice(std::hint::black_box(&[[1i64,2],[3,4]])); \
             std::process::exit(v.len() as i32);}",
            "extend array element",
        ),
    ];

    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                // Either it failed closed (the expected safe outcome) ...
                None => {}
                // ... or it compiled — in which case it must still be CORRECT.
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} compiled but is WRONG: bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// [TCG-STR-CASE] `str::to_uppercase` / `to_lowercase` build a NEW heap `String`
/// via a per-char Unicode case-mapping iterator collected through a `RawVec`
/// allocation (`ConvertVec::to_vec`) the bridge cannot lower. Before the fail-close
/// fix they SILENTLY MISCOMPILED at EVERY opt level: the unlowerable allocation
/// helper was GC-dropped as unreachable and the emitted body produced a
/// garbage/empty `String` (`to_uppercase().len()` returned 0 or SEGFAULTED vs the
/// real length). They MUST now fail CLOSED (never miscompile). If a future change
/// models them, it MUST match LLVM — this pin then catches a re-miscompile
/// (compiled-but-wrong) at O0/O2/O3.
#[test]
fn str_case_conversion_fails_closed_or_matches() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("strcase");
    let cases: &[(&str, &str)] = &[
        (
            "fn main(){ let s=String::from(\"hello\"); let u=s.to_uppercase(); \
             std::process::exit(u.len() as i32); }",
            "to_uppercase().len()",
        ),
        (
            "fn main(){ let s=String::from(\"HeLLo\"); let u=s.to_lowercase(); \
             std::process::exit(u.len() as i32); }",
            "to_lowercase().len()",
        ),
        (
            "fn main(){ let s=String::from(\"abc\"); let u=s.to_uppercase(); \
             let b=u.as_bytes(); \
             std::process::exit(if b.len()==3 && b[0]==b'A' {1} else {0}); }",
            "to_uppercase() content",
        ),
    ];
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                // Fail-closed is the current, correct behavior (safe -- not a
                // miscompile).
                None => {}
                // If it compiled, it MUST be correct (a future real model), else a
                // re-introduced SILENT MISCOMPILE.
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} compiled but is WRONG (silent miscompile): \
                     bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `write_bytes` intrinsic (`ptr::write_bytes` and the `[T]::fill` size-1
/// `SpecFill` specialization) lowered to a libc `memset` — the memset twin of the
/// `memcpy` `copy_nonoverlapping` path. Every case must be FAIL-CLOSED-OR-MATCH at
/// -O0/-O2/-O3, and the NON-DEGENERACY guard requires the core `fill` cases to
/// actually compile+match at every level (so the intercept is exercised, not
/// silently fail-closed away). The critical correctness checks: an `i64`/`i32`
/// element `fill(v)` must write the VALUE `v` (via the element loop, not a
/// byte-broadcast), while a `u8` `fill` and a direct `write_bytes` on a wide
/// element must reproduce `memset`'s exact byte-broadcast — both verified against
/// LLVM.
#[test]
fn write_bytes_fill_fails_closed_or_matches() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("writebytes");
    // (program, label, must_intercept) — the value-bearing `fill` cases MUST be
    // modeled (byte-broadcast would give a WRONG i64/i32 result, caught by the
    // match); the write_bytes byte cases pin memset's broadcast semantics.
    let cases: &[(&str, &str, bool)] = &[
        (
            "fn main(){let mut v=[0i64;5];v.fill(3);std::process::exit(v.iter().sum::<i64>() as i32);}",
            "[i64;5].fill(3) => 15 (value, not 0x0303..)",
            true,
        ),
        (
            "fn main(){let mut v=[1i32;6];v.fill(4);std::process::exit(v.iter().sum::<i32>());}",
            "[i32;6].fill(4) => 24",
            true,
        ),
        (
            "fn main(){let mut v=[0u8;9];v.fill(5);let s:u32=v.iter().map(|&x|x as u32).sum();std::process::exit(s as i32);}",
            "[u8;9].fill(5) => 45 (genuine memset live path)",
            true,
        ),
        (
            "fn main(){let mut b=[9u8;8];unsafe{std::ptr::write_bytes(b.as_mut_ptr(),0,8);\
             std::ptr::write_bytes(b.as_mut_ptr(),1,4);}\
             let s:u32=b.iter().map(|&x|x as u32).sum();std::process::exit(s as i32);}",
            "ptr::write_bytes zero-then-set-4 => 4",
            true,
        ),
        (
            "fn main(){let mut b=[0i64;2];unsafe{std::ptr::write_bytes(b.as_mut_ptr(),1,1);}\
             std::process::exit((b[0].wrapping_mul(1)%25 + b[1]) as i32);}",
            "write_bytes byte-broadcast on i64 matches memset",
            true,
        ),
    ];
    let mut intercepted = 0usize;
    for (src, label, must_intercept) in cases {
        let llvm = run_llvm(&dir, src);
        let mut all_levels_intercepted = true;
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                // Fail-closed is safe (never a miscompile) — but a must-intercept
                // case failing closed means the intercept regressed.
                None => all_levels_intercepted = false,
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} compiled but is WRONG (silent miscompile): \
                     bridge={code} llvm={llvm}"
                ),
            }
        }
        if *must_intercept {
            assert!(
                all_levels_intercepted,
                "`{label}` must be modeled (compile+match) at O0/O2/O3 — the \
                 write_bytes/memset intercept regressed to fail-closed"
            );
            intercepted += 1;
        }
    }
    // Non-degeneracy: the intercept genuinely fires (not a vacuous all-fail-closed).
    assert_eq!(
        intercepted,
        cases.iter().filter(|c| c.2).count(),
        "every must-intercept write_bytes/fill case is exercised"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// Slice fat-pointer FIELD reads through richer projections — `[Deref, Field…]`
/// (a `(*r).slice_field`, e.g. `slice::contains`) and `[Downcast, Field…]` (a
/// slice field of a memory-backed enum/tuple, e.g. `Option<&[T]>` from
/// `v.get(range)` or the tuple of `v.split_first()`). Every case must be
/// FAIL-CLOSED-OR-MATCH at -O0/-O2/-O3 (the load-`{data,len}`-and-store arms use
/// the trusted memory-projection address helpers, so a wrong offset would surface
/// as a mismatch, never silently). NON-DEGENERACY: the `Option<&[T]>`
/// destructuring (`v.get(1..4)`) and the two-slice `split_at` MUST actually
/// compile+match at -O0 — proving the fat-pointer field-read path fires. (The
/// generic `contains::<i64>` and non-empty `split_first` remain fail-closed on
/// SEPARATE, deeper gaps — an unbound reference deref-base and an unsized `[T]`
/// value — not modeled here; this pin locks in the coverage that IS correct and
/// guards against a future miscompile in the field-read arms.)
#[test]
fn slice_fat_ptr_field_reads_fail_closed_or_match() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("fatfield");
    // (program, label, must_compile_and_match_at_o0)
    let cases: &[(&str, &str, bool)] = &[
        (
            "fn main(){let v=[1i64,2,3,4,5];if let Some(s)=v.get(1..4){\
             std::process::exit(s.iter().sum::<i64>() as i32);}else{std::process::exit(99);}}",
            "Option<&[i64]> from v.get(range) destructure => 9",
            true,
        ),
        (
            "fn main(){let v=[1i64,2,3,4,5,6];let (a,b)=v.split_at(2);\
             std::process::exit((a.iter().sum::<i64>()*10+b.iter().sum::<i64>()) as i32);}",
            "split_at two-slice tuple => 48",
            true,
        ),
        (
            "fn main(){let v=[10u8,20,30];std::process::exit(if v.contains(&20){33}else{0});}",
            "[u8].contains => 33",
            false,
        ),
        (
            "fn main(){let v=[7i64,1,2,3];if let Some((h,t))=v.split_first(){\
             std::process::exit((*h*10+t.iter().sum::<i64>()) as i32);}else{std::process::exit(99);}}",
            "split_first (i64, non-empty) — deeper gap, fail-closed-or-match",
            false,
        ),
    ];
    let mut proved = 0usize;
    for (src, label, must_o0) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => {
                    assert!(
                        !(*must_o0 && opt == "0"),
                        "`{label}` must compile+match at -O0 (fat-ptr field-read path regressed)"
                    );
                }
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} compiled but is WRONG (silent miscompile): \
                     bridge={code} llvm={llvm}"
                ),
            }
        }
        if *must_o0 {
            proved += 1;
        }
    }
    assert_eq!(
        proved,
        cases.iter().filter(|c| c.2).count(),
        "the fat-pointer field-read arms are exercised (non-degenerate)"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// P0 REGRESSION (found by the differential fuzz hunt): `str::parse::<f64>()`
/// consumed via `if let Ok(v)` compiled CLEANLY but shipped a SIGSEGV-ing binary
/// at EVERY opt level (the `dec2flt::<f64>` decimal parser is unlowerable and its
/// GC-dropped helper left a crashing body — the same deferred-unlowerable GC-drop
/// hazard as `str::to_uppercase`). Every `f64`-parse case MUST now be
/// fail-closed-or-match at O0/O2/O3 (NEVER a crash: exit code < 132). `f32` parse
/// IS correctly modeled and MUST keep matching (non-degeneracy: the fix must not
/// over-fail-close the working f32 path).
#[test]
fn parse_f64_fails_closed_never_crashes_f32_ok() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("parsef64");
    // (program, label, must_match) — f64 cases: fail-closed-or-match, NEVER crash.
    // f32 cases: must compile+match (guard against over-fail-closing).
    let cases: &[(&str, &str, bool)] = &[
        (
            "fn main(){ if let Ok(v)=\"3.14\".parse::<f64>(){ std::process::exit((v as i32)&255);} std::process::exit(200);}",
            "f64 parse via if-let-Ok (the P0 repro)",
            false,
        ),
        (
            "fn main(){ let v=\"2.5\".parse::<f64>().unwrap_or(0.0); std::process::exit((v as i32)&255);}",
            "f64 parse via unwrap_or",
            false,
        ),
        (
            "fn main(){ let mut t=0f64; for s in [\"1.0\",\"2.0\",\"3.0\"]{ if let Ok(v)=s.parse::<f64>(){t+=v;} } std::process::exit(t as i32);}",
            "f64 parse in a loop",
            false,
        ),
        (
            "fn main(){ if let Ok(v)=\"3.14\".parse::<f32>(){ std::process::exit((v as i32)&255);} std::process::exit(200);}",
            "f32 parse via if-let-Ok (must stay modeled)",
            true,
        ),
    ];
    let mut f32_matched = 0usize;
    for (src, label, must_match) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => assert!(
                    !*must_match,
                    "`{label}` at -O{opt} must compile+match but failed closed (over-fail-close regression)"
                ),
                Some(code) => {
                    assert!(
                        code < 132,
                        "`{label}` at -O{opt} produced a CRASHING binary (exit {code} >= 132) — \
                         the parse-f64 SIGSEGV P0 regressed"
                    );
                    assert_eq!(
                        code, llvm,
                        "`{label}` at -O{opt} compiled but is WRONG: bridge={code} llvm={llvm}"
                    );
                }
            }
        }
        if *must_match {
            f32_matched += 1;
        }
    }
    assert_eq!(
        f32_matched,
        cases.iter().filter(|c| c.2).count(),
        "f32 parse stays modeled (the fix did not over-fail-close it)"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// P0 REGRESSION (found by the differential fuzz hunt): an
/// `iter.by_ref().take(n)` terminal (`Take<&mut Iter>::spec_fold`) failed closed
/// at -O0 but at -O2/-O3 rustc reshaped the chain so the fail-close guard was
/// bypassed and the backend shipped a `ud2` trap stub that SIGILL'd (exit 132).
/// Every `by_ref()` chain MUST now be fail-closed-or-match at O0/O2/O3 (NEVER a
/// crash: exit < 132). NON-DEGENERACY: by-VALUE `take`/`skip` chains (which ARE
/// modeled) MUST keep compiling+matching — the fix must not over-fail-close them
/// (it excludes ONLY an adapter whose inner iterator is a `&mut` reference).
#[test]
fn by_ref_iter_chain_fails_closed_never_sigills() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("byref");
    // (program, label, must_match) — by_ref cases: fail-closed-or-match, NEVER crash.
    // by-value take/skip cases: must compile+match (guard against over-fail-close).
    let cases: &[(&str, &str, bool)] = &[
        (
            "fn main(){let a=[2i32,4,6,8,10];let mut it=a.iter();let first:i32=it.by_ref().take(2).sum();let rest:i32=it.sum();std::process::exit(first+rest);}",
            "by_ref().take(2).sum() then it.sum() (the P0 repro)",
            false,
        ),
        (
            "fn main(){let a=[2i32,4,6,8,10];let mut it=a.iter();let s:i32=it.by_ref().take(2).sum();std::process::exit(s%256);}",
            "by_ref().take(2).sum() alone",
            false,
        ),
        (
            "fn main(){let a=[2i32,4,6,8,10];let s:i32=a.iter().take(3).sum();std::process::exit(s);}",
            "by-VALUE take(3).sum() (must stay modeled)",
            true,
        ),
        (
            "fn main(){let a=[1i32,2,3,4,5,6];let s:i32=a.iter().skip(1).take(3).sum();std::process::exit(s);}",
            "by-VALUE skip(1).take(3).sum() (must stay modeled)",
            true,
        ),
    ];
    let mut modeled = 0usize;
    for (src, label, must_match) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => assert!(
                    !*must_match,
                    "`{label}` at -O{opt} must compile+match but failed closed (over-fail-close regression)"
                ),
                Some(code) => {
                    assert!(
                        code < 132,
                        "`{label}` at -O{opt} produced a CRASHING binary (exit {code} >= 132) — \
                         the by_ref ud2/SIGILL P0 regressed"
                    );
                    assert_eq!(
                        code, llvm,
                        "`{label}` at -O{opt} compiled but is WRONG: bridge={code} llvm={llvm}"
                    );
                }
            }
        }
        if *must_match {
            modeled += 1;
        }
    }
    assert_eq!(
        modeled,
        cases.iter().filter(|c| c.2).count(),
        "by-value take/skip chains stay modeled (the fix did not over-fail-close them)"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// P0 REGRESSION (found by the differential fuzz hunt): a mutating `&mut dyn
/// Trait` coercion of a SCALARIZED (register-held) aggregate dropped the mutation
/// at -O2/-O3 (the fat pointer's data half pointed at a fresh `alloca` COPY, so a
/// `self.v += ..` through the trait object was written to the copy and lost;
/// verified WRONG value with a phi-selected `&mut dyn`, and O0 already failed
/// closed). Every `&mut dyn` case MUST now be fail-closed-or-match at O0/O2/O3
/// (NEVER a wrong value). NON-DEGENERACY: a SHARED `&dyn` (read-only) coercion of
/// the same shape MUST keep compiling+matching — the fix must fail-close only the
/// MUTABLE coercion of a copy-materialized source.
#[test]
fn mut_dyn_over_scalarized_fails_closed_shared_dyn_ok() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("mutdyn");
    // (program, label, must_match) — &mut dyn cases: fail-closed-or-match, NEVER wrong.
    // shared &dyn cases: must compile+match (guard against over-fail-close).
    let cases: &[(&str, &str, bool)] = &[
        (
            "trait Bump{fn bump(&mut self);} struct C{v:i64} impl Bump for C{fn bump(&mut self){self.v+=10;}} \
             fn main(){let mut a=C{v:1};let mut b=C{v:2};for i in 0..2{let t:&mut dyn Bump=if i==0{&mut a}else{&mut b};t.bump();}std::process::exit((a.v+b.v) as i32);}",
            "phi-of-&mut dyn, mutate in loop (the P0 repro)",
            false,
        ),
        (
            "trait Bump{fn bump(&mut self);fn get(&self)->i64;} struct C{v:i64} impl Bump for C{fn bump(&mut self){self.v+=10;}fn get(&self)->i64{self.v}} \
             fn main(){let mut a=C{v:5};let t:&mut dyn Bump=&mut a;t.bump();std::process::exit(t.get() as i32);}",
            "single &mut dyn, mutate",
            false,
        ),
        (
            // The FN-PARAM route into the same class: `f(&mut a)` where `f` takes
            // `&mut dyn B`. Pre-fix this SILENTLY MISCOMPILED at -O3 (exit 5 — the
            // initial value, mutation dropped — vs LLVM 15); the [TCG-DYN-MUT-COPY]
            // guard now fails it closed.
            "trait B{fn b(&mut self);fn g(&self)->i64;} struct C{v:i64} impl B for C{fn b(&mut self){self.v+=10;}fn g(&self)->i64{self.v}} \
             fn f(x:&mut dyn B){x.b();} fn main(){let mut a=C{v:5};f(&mut a);std::process::exit(a.g() as i32);}",
            "fn-param &mut dyn, mutate (latent 4th instance)",
            false,
        ),
        (
            "trait S{fn v(&self)->i64;} struct C{v:i64} impl S for C{fn v(&self)->i64{self.v}} \
             fn main(){let a=C{v:42};let t:&dyn S=&a;std::process::exit(t.v() as i32);}",
            "shared &dyn read-only (must stay modeled)",
            true,
        ),
        (
            // MULTI-FIELD `&mut dyn` — UPGRADED to a real lowering by the (0e)
            // memory-back rule (`compute_memory_backed_locals`): a mut-dyn-coerced
            // multi-field local is forced memory-backed, so the coercion reuses the
            // REAL slot address and the vtable method's stores land in the local.
            // Pre-guard this shape silently DROPPED the stores (exit 3, initial
            // values, at -O0). MUST compile+match at O0/O2/O3.
            "trait B{fn b(&mut self);fn g(&self)->i64;} struct C{v:i64,w:i64} \
             impl B for C{fn b(&mut self){self.v+=10;self.w+=1;}fn g(&self)->i64{self.v+self.w}} \
             fn main(){let mut a=C{v:1,w:2};{let t:&mut dyn B=&mut a;t.b();} std::process::exit(a.g() as i32);}",
            "multi-field &mut dyn mutate (real lowering via (0e) memory-back)",
            true,
        ),
        (
            "trait S{fn v(&self)->i64;} struct C{v:i64} impl S for C{fn v(&self)->i64{self.v}} \
             fn main(){let a=C{v:3};let b=C{v:4};let c=true;let t:&dyn S=if c{&a}else{&b};std::process::exit(t.v() as i32);}",
            "phi-of-shared &dyn read-only (must stay modeled)",
            true,
        ),
    ];
    let mut shared_ok = 0usize;
    for (src, label, must_match) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => assert!(
                    !*must_match,
                    "`{label}` at -O{opt} must compile+match but failed closed (over-fail-close regression)"
                ),
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} compiled but is WRONG (store-drop miscompile): \
                     bridge={code} llvm={llvm}"
                ),
            }
        }
        if *must_match {
            shared_ok += 1;
        }
    }
    assert_eq!(
        shared_ok,
        cases.iter().filter(|c| c.2).count(),
        "shared &dyn read-only stays modeled (the fix did not over-fail-close it)"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// P0 REGRESSION (round-2 differential fuzz hunt): a `&mut <scalar local>` call
/// arg whose borrow is taken BEFORE a value-divergent join (a diamond that itself
/// mutates the local through the same-style call on both arms) threads the borrow
/// through a block param with a SELF-PLACEHOLDER binding; the post-join call's
/// write-back then rebound the placeholder (the ref local) instead of the
/// borrowed local — the mutation was SILENTLY DROPPED (verified wrong value at
/// O2/O3: 38 vs LLVM 202; O0's shape lowered correctly). Now fail-closed
/// [TCG-MUTREF-ARG-PHI] (the call-arg twin of [TCG-PTRSEL-STORE]). Every case
/// MUST be fail-closed-or-match at O0/O2/O3 (never a wrong value); the common
/// working `&mut`-accumulator shapes (loop / straight-line) MUST keep
/// compiling+matching.
#[test]
fn mut_scalar_ref_arg_across_join_fails_closed_or_matches() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("mutrefarg");
    const HELPERS: &str = "#[inline(never)] fn hb<T>(x:T)->T{std::hint::black_box(x)} \
        #[inline(never)] fn put(dst:&mut u64,v:u64){*dst=dst.wrapping_mul(37).wrapping_add(v);} ";
    // (program, label, must_match)
    let cases: &[(&str, &str, bool)] = &[
        (
            "fn main(){let mut acc:u64=1;let m=hb(i8::MIN);\
             put(&mut acc,(m.wrapping_abs()==i8::MIN) as u64);\
             put(&mut acc,m.checked_abs().is_none() as u64);\
             std::process::exit((acc%241) as i32);}",
            "borrow-before-diamond put chain (the P0 repro, i8)",
            false,
        ),
        (
            "fn main(){let mut acc:u64=1;let m=hb(i32::MIN);\
             put(&mut acc,(m.wrapping_abs()==i32::MIN) as u64);\
             put(&mut acc,m.checked_abs().is_none() as u64);\
             std::process::exit((acc%241) as i32);}",
            "borrow-before-diamond put chain (i32)",
            false,
        ),
        (
            "fn main(){let mut acc:u64=1;for i in 0..4u64{put(&mut acc,hb(i));}\
             std::process::exit((acc%241) as i32);}",
            "put(&mut acc) in a loop (must stay modeled)",
            true,
        ),
        (
            "fn main(){let mut acc:u64=1;put(&mut acc,hb(3u64));put(&mut acc,hb(5u64));\
             std::process::exit((acc%241) as i32);}",
            "straight-line put chain (must stay modeled)",
            true,
        ),
    ];
    let mut modeled = 0usize;
    for (body_src, label, must_match) in cases {
        let src = format!("{HELPERS}{body_src}");
        let llvm = run_llvm(&dir, &src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, &src, opt) {
                None => assert!(
                    !*must_match,
                    "`{label}` at -O{opt} must compile+match but failed closed (over-fail-close regression)"
                ),
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} compiled but is WRONG (dropped &mut write-back): \
                     bridge={code} llvm={llvm}"
                ),
            }
        }
        if *must_match {
            modeled += 1;
        }
    }
    assert_eq!(
        modeled,
        cases.iter().filter(|c| c.2).count(),
        "loop/straight-line &mut-accumulator shapes stay modeled"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// STRENGTH REDUCTION: unsigned integer div/rem by a constant POWER OF TWO is
/// rewritten to a shift / mask (`x /u 2^k == x >>u k`, `x %u 2^k == x & (2^k-1)`)
/// — exact identities over already-proven primitives, no `Idiv`. This pins the
/// hard invariant: the rewritten result MUST equal LLVM at O0/O2/O3 (a wrong
/// shift/mask would be a silent miscompile), AND the non-reduced forms (signed
/// div/rem, non-power-of-two divisors) MUST also stay correct.
#[test]
fn unsigned_pow2_div_rem_strength_reduction_matches_llvm() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("srpow2");
    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let x=std::hint::black_box(1234567u32);std::process::exit(((x/8+x%16)%251) as i32);}",
            "u32 /8 and %16 (reduced)",
        ),
        (
            "fn main(){let x=std::hint::black_box(0xFFFF_FFFF_1234u64);std::process::exit(((x/1024+x%64)%251) as i32);}",
            "u64 /1024 and %64 (reduced)",
        ),
        (
            "fn main(){let x=std::hint::black_box(200u8);std::process::exit(((x/2+x%32)%251) as i32);}",
            "u8 /2 and %32 (reduced)",
        ),
        (
            "fn main(){let a=[std::hint::black_box(1234567u32),89,4242];let mut s=0u32;\
             for i in 0..3{s=s.wrapping_add(a[i]/8).wrapping_add(a[i]%16);}std::process::exit((s%251) as i32);}",
            "runtime array elem /8 %16 in a loop (reduced, non-foldable)",
        ),
        (
            "fn main(){let a=std::hint::black_box(0u32);let b=std::hint::black_box(u32::MAX);\
             std::process::exit((((a/2)+(b/2))%251) as i32);}",
            "u32 /2 edges 0 and MAX (reduced)",
        ),
        (
            "fn main(){let x=std::hint::black_box(-1000i32);std::process::exit(((x/8+x%16)+400) as i32);}",
            "SIGNED /8 %16 (reduced via round-toward-zero bias)",
        ),
        (
            "fn main(){let mut s=0i64;for &v in [-7i32,-8,-9,-1,7,8,9,0,i32::MIN+1,i32::MAX].iter(){\
             s=s.wrapping_add((v/4) as i64).wrapping_mul(3).wrapping_add((v%8) as i64);}\
             std::process::exit((s.rem_euclid(251)) as i32);}",
            "SIGNED /4 %8 over negatives/edges (round-toward-zero, reduced)",
        ),
        (
            "fn main(){let v=std::hint::black_box(-100i8);std::process::exit(((v/2+v%16) as i32)+200);}",
            "SIGNED i8 /2 %16 (narrow width, reduced)",
        ),
        (
            "fn main(){let x=std::hint::black_box(123456u32);std::process::exit(((x/3+x%1000)%251) as i32);}",
            "non-power-of-two /3 %1000 (NOT reduced — must stay correct)",
        ),
    ];
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => panic!("`{label}` at -O{opt} fail-closed — div/rem must always lower"),
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} WRONG (strength-reduction miscompile): bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// SIGNED magic-number division/remainder by a compile-time constant (the b18
/// `% 1000` win): the x86 isel replaces IDIV with an unsigned MULHI + sign
/// corrections + shifts, gated on the exhaustively-validated
/// `magic_udiv::smagic_band_holds`. Every case MUST equal LLVM at O0/O2/O3 — a
/// wrong magic/correction would be a silent miscompile; the non-magic and
/// power-of-two divisors keep IDIV / the shift path.
#[test]
fn signed_magic_division_matches_llvm() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("smagic");
    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let a=[std::hint::black_box(-123456i32),789,-999,500123];let mut s=0i32;\
             for i in 0..4{s=s.wrapping_add(a[i]%1000).wrapping_mul(3).wrapping_add(a[i]/1000);}\
             std::process::exit((s.rem_euclid(251)) as i32);}",
            "i32 %1000 /1000 over negatives (the b18 shape)",
        ),
        (
            "fn main(){let mut s=0i64;for &v in [i32::MIN,i32::MIN+1,-9973,-3,-1,0,1,7,i32::MAX].iter(){\
             s=s.wrapping_add((v/7) as i64).wrapping_mul(5).wrapping_add((v%7) as i64);}\
             std::process::exit((s.rem_euclid(251)) as i32);}",
            "i32 /7 %7 over extremes (magic + sign correction)",
        ),
        (
            "fn main(){let x=std::hint::black_box(-1234567890123i64);\
             std::process::exit((((x/99991)+(x%99991)).rem_euclid(251)) as i32);}",
            "i64 /99991 %99991 negative (64-bit magic)",
        ),
        (
            "fn main(){let x=std::hint::black_box(-100i32);\
             std::process::exit(((x/(-3)+x%(-7))+200) as i32);}",
            "NEGATIVE divisors -3 -7 (negated magic)",
        ),
    ];
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => panic!("`{label}` at -O{opt} fail-closed — signed div must always lower"),
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} WRONG (signed magic miscompile): bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Completeness: `uN::from_le_bytes([u8; N])` / whole-array `Use` copy of a
/// SCALARIZED (non-memory-backed) array value into a memory-backed array slot.
/// rustc lowers `black_box([..])` feeding `from_le_bytes` to `mem_arr =
/// Move(scalarized_arr)`; the frontend now stores each flat scalar leaf into the
/// slot (via the shared, internally-fail-safe operand→memory writer) rather than
/// failing closed. Every case MUST equal LLVM at O0/O2/O3.
#[test]
fn from_le_bytes_scalarized_array_matches_llvm() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("fromle");
    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let b=core::hint::black_box([1u8,2,3,4,5,6,7,8]);\
             std::process::exit(((u64::from_le_bytes(b))&0xff) as i32);}",
            "u64::from_le_bytes([u8;8])",
        ),
        (
            "fn main(){let b=core::hint::black_box([9u8,8,7,6]);\
             std::process::exit(((u32::from_le_bytes(b).wrapping_mul(3))&0xff) as i32);}",
            "u32::from_le_bytes([u8;4]) x3",
        ),
        (
            "fn main(){let b=core::hint::black_box([200u8,100]);\
             std::process::exit(((u16::from_le_bytes(b) as i32))&0xff);}",
            "u16::from_le_bytes([u8;2])",
        ),
        (
            "fn main(){let b=core::hint::black_box([1u8,2,3,4,5,6,7,8]);\
             let x=u32::from_le_bytes([b[0],b[1],b[2],b[3]]);\
             let y=u32::from_be_bytes([b[4],b[5],b[6],b[7]]);\
             std::process::exit(((x.wrapping_add(y))&0xff) as i32);}",
            "sub-array from_le + from_be",
        ),
        (
            "fn main(){let x=core::hint::black_box(-123456789i64);let by=x.to_le_bytes();\
             std::process::exit(((i64::from_le_bytes(by))&0xff) as i32);}",
            "round-trip to_le_bytes -> from_le_bytes (signed)",
        ),
    ];
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => panic!("`{label}` at -O{opt} fail-closed — from_le_bytes must lower"),
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} WRONG: bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Switch/`match` binary-search lowering: a `match` with >=5 non-negative,
/// i32-range arms lowers to a balanced BST (O(log n) direct branches) instead
/// of the linear `CMP;JE` chain. Correctness-critical — a wrong compare/branch
/// or block-id collision is a silent miscompile. Every case MUST equal LLVM at
/// O0/O2/O3 (dense, sparse, ranges, defaults, nested, edge values).
#[test]
fn switch_binary_search_matches_llvm() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("switchbst");
    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let mut a=0u64;let mut x=0u32;while x<200{let s=(x.wrapping_mul(7))%15;\
             let v=match s{0=>10u64,1=>20,2=>30,3=>40,4=>50,5=>60,6=>70,7=>80,8=>90,9=>100,\
             10=>110,11=>120,12=>130,13=>140,_=>150};a=a.wrapping_add(v);x+=1;}\
             std::process::exit((a&0xff) as i32);}",
            "15-arm dense",
        ),
        (
            "fn main(){let mut a=0i64;let mut x=0i32;while x<300{let s=x%13;\
             let v=match s{0=>1i64,1=>2,2|3=>5,4=>7,5=>11,6..=8=>13,9=>17,10=>19,11|12=>23,_=>0};\
             a=a.wrapping_add(v);x+=1;}std::process::exit((a.rem_euclid(251)) as i32);}",
            "ranges + | patterns",
        ),
        (
            "fn main(){let mut a=0u64;let mut x=0u32;while x<400{let s=(x*7)%100;\
             let v=match s{0=>1u64,25=>2,50=>3,75=>4,99=>5,10=>6,20=>7,30=>8,_=>9};\
             a=a.wrapping_add(v);x+=1;}std::process::exit((a&0xff) as i32);}",
            "sparse 9-arm",
        ),
        (
            "fn main(){let mut a=0u64;let mut st=0u32;let mut x=0u64;while x<500{\
             x=x.wrapping_mul(6364136223846793005).wrapping_add(1);let sym=((x>>59)&0x1f) as u32;\
             st=match st{0=>match sym{0..=5=>1,6..=10=>2,_=>0},1=>match sym{0..=3=>3,20..=31=>4,_=>1},\
             2=>match sym{7=>5,_=>2},3=>match sym{3..=9=>3,_=>0},4=>match sym{0..=2=>2,_=>4},\
             _=>match sym{4|5=>0,_=>5}};a=a.wrapping_add(st as u64);x+=1;}\
             std::process::exit((a&0xff) as i32);}",
            "nested match (state x sym)",
        ),
    ];
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => panic!("`{label}` at -O{opt} fail-closed — switch must lower"),
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} WRONG (switch BST miscompile): bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Nested CONST-FOLDED aggregate construction: an aggregate whose field is itself
/// an aggregate literal (e.g. the inner `(1, 2)` of `((1, 2), (3, 4))`) is
/// const-folded to an `Operand::Constant`, so there is no place to project the
/// nested scalar leaves from. `const_scalar_aggregate_field_values` decodes each
/// nested scalar leaf byte-exact from the const's own in-memory image and pushes
/// it into the parent's flat scalar bindings — the const-folded analogue of the
/// place-operand nested path. Correctness-critical: a wrong offset/width/sign
/// decode is a silent miscompile, so every case MUST equal LLVM at O0/O2/O3.
#[test]
fn nested_const_aggregate_field_decode_matches_llvm() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("nestedconst");
    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let t=((1i32,2i32),(3i32,4i32));\
             std::process::exit(t.0.0+t.0.1+t.1.0+t.1.1);}",
            "((i32,i32),(i32,i32))",
        ),
        (
            "fn main(){let t=(((1i32,2i32),3i32),0i32);\
             std::process::exit(t.0.0.0+t.0.0.1+t.0.1);}",
            "3-level nesting",
        ),
        (
            "fn main(){let t=((-1i32,2i32),(-4i32,6i32));\
             std::process::exit(t.0.0+t.0.1+t.1.0+t.1.1);}",
            "negative int leaves",
        ),
        (
            "struct P{a:i16,b:i16} fn main(){let t=(P{a:3,b:4},P{a:2,b:6});\
             std::process::exit((t.0.a+t.0.b+t.1.a+t.1.b) as i32);}",
            "struct-in-tuple (i16 leaves)",
        ),
        (
            "fn main(){let t=((40i64,2i64),0i64);\
             std::process::exit((t.0.0+t.0.1) as i32);}",
            "i64 leaves",
        ),
        (
            "fn main(){let t=((1u8,2u8),(3u8,4u8),(5u8,6u8),(9u8,0u8));\
             std::process::exit((t.0.0+t.0.1+t.1.0+t.1.1+t.2.0+t.2.1+t.3.0+t.3.1) as i32);}",
            "u8 leaves, 4 nested pairs",
        ),
        (
            "fn main(){let t=((true,2i32),(false,3i32));\
             std::process::exit((t.0.0 as i32)*100 + t.0.1 + t.1.1);}",
            "bool leaf decode",
        ),
    ];
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => panic!("`{label}` at -O{opt} fail-closed — nested const aggregate must lower"),
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} WRONG (nested const decode miscompile): bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// PIN for the intercepted-terminal ADDRESS-TAKEN-destination cell store
/// (P0 class fixed 2026-07-17). The intercepted iterator terminals
/// (`sum`/`count`/`fold`/`product`/`any`/`all`, flat_map, ControlFlow-eq) used
/// to bind their scalar result SSA-only (`bind_scalar_value`) and never store
/// the destination local's scalar CELL. When the destination is address-taken —
/// most commonly a non-`move` closure capturing it BY REFERENCE (`&first` in
/// the env) — every reader loads through the cell and saw uninitialized frame
/// garbage (silent wrong answers at -O0; -O2/-O3 shapes fail-close). The fix
/// routes the result binding through `finish_assign_target` (the same primitive
/// every plain call/cast/binop assignment uses). Each case MUST lower at -O0
/// and MUST equal LLVM wherever it compiles; a fail-close is tolerated ONLY at
/// -O2/-O3 (the pre-existing inlined-shape declines).
#[test]
fn terminal_result_capture_cell_store_matches_llvm() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("termcell");
    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let a=[2i64,7,3];let b=[1i64,5,4,6];\
             let first:i64=a.iter().sum();\
             let s:i64=b.iter().map(|&y| y ^ first).sum();\
             std::process::exit(s.rem_euclid(128) as i32);}",
            "sum result captured by-ref in a map closure (the minimal P0 repro)",
        ),
        (
            "fn main(){let a=[2i64,7,3];let b=[1i64,5,4,6];\
             let first:i64=a.iter().sum();\
             let s:i64=b.iter().map(|&y| y ^ first).sum();\
             std::process::exit((s+first).rem_euclid(128) as i32);}",
            "sum captured + post-capture re-read",
        ),
        (
            "fn main(){let k:i64=3;let a=[2i64,7,3];let b=[1i64,5,4,6];\
             let first:i64=a.iter().map(|&x| x*k).sum();\
             let second:i64=b.iter().map(|&y| (y ^ first)%7).sum();\
             std::process::exit((second*2+first).rem_euclid(128) as i32);}",
            "two capturing chains, second captures the first's result",
        ),
        (
            "fn main(){let a=[2i64,7,3];let b=[1i64,5,4,6];\
             let big=a.iter().any(|&x| x>5);\
             let s:i64=b.iter().map(|&y| if big {y*2} else {y}).sum();\
             std::process::exit(s.rem_euclid(128) as i32);}",
            "any() bool result captured by-ref",
        ),
        (
            "fn main(){let a=[2i64,3,4];let b=[1i64,5,4,6];\
             let p:i64=a.iter().product();\
             let s:i64=b.iter().map(|&y| y+p).sum();\
             std::process::exit(s.rem_euclid(128) as i32);}",
            "product() result captured by-ref",
        ),
        (
            "fn main(){let a=[2i64,7,3];let b=[1i64,5,4,6];\
             let n=a.iter().count() as i64;\
             let s:i64=b.iter().map(|&y| y*n).sum();\
             std::process::exit(s.rem_euclid(128) as i32);}",
            "count() result captured by-ref",
        ),
        (
            "fn main(){let a=[2i64,7,3];let b=[1i64,5,4,6];\
             let first=a.iter().fold(1i64,|acc,&x| acc+x*2);\
             let s:i64=b.iter().map(|&y| y ^ first).sum();\
             std::process::exit(s.rem_euclid(128) as i32);}",
            "non-capturing fold result captured by-ref",
        ),
        (
            "fn main(){let a=[2i64,7,3];\
             let first:i64=a.iter().sum();\
             let r=&first;\
             std::process::exit((*r).rem_euclid(128) as i32);}",
            "plain borrow of a sum result",
        ),
    ];
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => assert_ne!(
                    opt, "0",
                    "`{label}` at -O0 fail-closed — the terminal-result cell store must lower"
                ),
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} WRONG (terminal-result cell miscompile): bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// PIN for the flat_map+position reachable-ud2 P0 (fixed 2026-07-17): the
/// `is_dead_std_iterator_reduction_body` `try_fold` trap used to claim
/// `FlattenCompat::iter_try_fold` dead, but only the BOUNDED flat_map shapes are
/// intercepted — `.flat_map(..).position(..)` at -O2/-O3 kept a LIVE call to the
/// trapped stub and shipped a deterministic SIGILL (132) instead of failing
/// closed. The `flatten`/`flat_map` exclude routes the unlowerable body through
/// the deferred verdict (GC-drop or whole-compile fail-close). Each case must
/// either FAIL-CLOSE (safe) or, if it ever compiles, MATCH LLVM — never signal.
#[test]
fn flatmap_position_fails_closed_never_sigill() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("flatmappos");
    let cases: &[(&str, &str)] = &[
        (
            "fn main(){let pos=(0..20i64).flat_map(|x| 0..x).position(|y| y==5);\
             let d=pos.map(|v| v as i64).unwrap_or(-1);\
             let f=|| d+100; let r=f()-d+d*3;\
             std::process::exit((r).rem_euclid(128) as i32);}",
            "flat_map+position result captured by-ref (the SIGILL repro)",
        ),
        (
            "fn main(){let b=(0..20i64).flat_map(|x| 0..x).any(|y| y==7);\
             std::process::exit(if b {33} else {44});}",
            "flat_map+any (unmodeled consumer)",
        ),
        (
            "fn main(){let s:i64=(0..20i64).flat_map(|x| 0..x).sum();\
             std::process::exit((s%128) as i32);}",
            "MODELED bounded flat_map sum (must still lower at -O0)",
        ),
    ];
    for (src, label) in cases {
        let llvm = run_llvm(&dir, src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                // Fail-close is SAFE for the unmodeled shapes; the modeled
                // bounded sum must still lower at -O0 (its intercept level).
                None => {
                    if label.contains("MODELED") {
                        assert_ne!(
                            opt, "0",
                            "`{label}` at -O0 fail-closed — the bounded flat_map intercept regressed"
                        );
                    }
                }
                Some(code) => assert_eq!(
                    code, llvm,
                    "`{label}` at -O{opt} WRONG (flat_map trap/miscompile): bridge={code} llvm={llvm}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// PIN for the two trap-claim-hunt P0 classes (gated 2026-07-17):
/// (1) [TCG-DYN-FN-ARGS] dynamic Fn-trait dispatch marshals the tupled args as
///     ONE SysV aggregate while the vtable target uses the UNTUPLED closure
///     convention — 3+-arg `&dyn Fn` / `&mut dyn FnMut` silently CORRUPTED
///     arguments at every opt level (returning param `b` gave garbage). Gated:
///     only 0-arg and 1-thin-scalar-arg dispatch (the demonstrably-coinciding
///     ABIs) still lower; everything else fail-closes.
/// (2) `.enumerate()` + `find_map`/`any`/`all` reached the trap-stubbed
///     `Enumerate::try_fold` check-glue at -O2/-O3 (deterministic SIGILL 132).
///     The `enumerate` exclude routes those bodies through the deferred verdict.
/// Every case must FAIL-CLOSE or MATCH LLVM — never signal, never mismatch.
#[test]
fn dyn_fn_args_and_enumerate_trap_gates() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("dynfnenum");
    let cases: &[(&str, &str, bool)] = &[
        // (src, label, must_lower_somewhere)
        (
            "fn main(){let f:&dyn Fn(i64,i64,i64)->i64=&|_a,b,_c| b;\
             std::process::exit((f(9,6,3)).rem_euclid(128) as i32)}",
            "3-arg &dyn Fn (the argument-corruption repro)",
            false,
        ),
        (
            "fn main(){let mut acc=0i64;{let g:&mut dyn FnMut(i64,i64,i64)->i64=&mut |a,b,c|{acc+=1;a+b+c+acc};\
             let r=g(1,2,3)+g(4,5,6);std::process::exit((r).rem_euclid(128) as i32)}}",
            "3-arg &mut dyn FnMut (corrupted at ALL levels pre-gate)",
            false,
        ),
        (
            "fn main(){let k=5i64;let f:&dyn Fn(i64)->i64=&|x| x+k;\
             std::process::exit((f(37)).rem_euclid(128) as i32)}",
            "1-arg &dyn Fn MUST still lower at -O0 (coinciding ABI)",
            true,
        ),
        (
            "fn main(){let a=[10i64,20,33,40,55];\
             let fm=a.iter().enumerate().find_map(|(i,&v)| if v%2==1 {Some(i as i64*100+v)} else {None});\
             std::process::exit((fm.unwrap_or(-7)%90).rem_euclid(128) as i32)}",
            "enumerate+find_map (the SIGILL repro)",
            false,
        ),
        (
            "fn main(){let a=[2i64,9,4,7];let x=a.iter().enumerate().any(|(i,&v)| i as i64==v);\
             std::process::exit(((x as i64)*44+20).rem_euclid(128) as i32)}",
            "enumerate+any (SIGILL repro)",
            false,
        ),
        (
            "fn main(){let a=[3i64,1,4,1,5];let s:i64=a.iter().enumerate().map(|(i,&v)| i as i64*v).sum();\
             std::process::exit((s.rem_euclid(128)) as i32)}",
            "enumerate+map+sum MUST still lower (modeled surface canary)",
            true,
        ),
    ];
    for (src, label, must_lower) in cases {
        let llvm = run_llvm(&dir, src);
        let mut lowered_anywhere = false;
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, src, opt) {
                None => {}
                Some(code) => {
                    lowered_anywhere = true;
                    assert_eq!(
                        code, llvm,
                        "`{label}` at -O{opt} WRONG (dyn-fn/enumerate gate miscompile): bridge={code} llvm={llvm}"
                    );
                }
            }
        }
        if *must_lower {
            assert!(
                lowered_anywhere,
                "`{label}` fail-closed at every opt level — the allowed surface regressed"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// PIN for the capturing-closure fold terminal (landed 2026-07-17 on top of the
/// intercepted-terminal cell-store fix). `iter.fold(init, |acc, x| ...)` with a
/// CAPTURING closure now materializes the closure's env pointer once in the
/// preheader (via `closure_env_ptr`) and passes it at the call site, instead of
/// fail-closing on any non-ZST closure. The earlier revert cause — a captured
/// fold/sum RESULT reading garbage — was the address-taken-cell P0, now fixed;
/// its repros (two sequential capturing folds where the second captures the
/// first's result) are pinned here as must-lower-and-match. A capture shape the
/// env resolver cannot model still fail-closes; each case must FAIL-CLOSE or
/// MATCH LLVM — never signal, never mismatch.
#[test]
fn capturing_fold_terminal_matches_llvm() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("capfold");
    // (src, must_lower_somewhere)
    let cases: &[(&str, bool)] = &[
        (
            "fn main(){let w:i64=7;let d=[3i64,1,4,1,5,9,2,6];\
             let r=d.iter().fold(0i64,|acc,&x| acc+w*x);\
             std::process::exit((r.rem_euclid(128)) as i32);}",
            true, // single Copy capture
        ),
        (
            "fn main(){let a=[2i64,7,3];let b=[1i64,5,4,6];let k:i64=3;\
             let first=a.iter().fold(1i64,|acc,&x| acc+x*k);\
             let second=b.iter().fold(first,|acc,&y| acc*2+(y^first)%7);\
             std::process::exit((second).rem_euclid(128) as i32);}",
            true, // the REVERT-CAUSE repro: second fold captures the first's result
        ),
        (
            "fn main(){let a=[2i64,7,3];let b=[1i64,5,4,6];let k:i64=3;\
             let first=a.iter().fold(1i64,|acc,&x| acc+x*k);\
             let second=b.iter().fold(0i64,|acc,&y| acc+(y^first));\
             std::process::exit((second).rem_euclid(128) as i32);}",
            true, // m2 variant: constant init, closure captures the prior result
        ),
        (
            "fn main(){let mut side:i64=0;let data=[2i64,4,6,8,10];\
             let r=data.iter().fold(0i64,|acc,&x| { side += 1; acc + x*side });\
             std::process::exit(((r+side).rem_euclid(128)) as i32);}",
            true, // captured &mut write-back, read after the fold
        ),
        (
            "fn main(){let k:f64=1.5;let data=[1.0f64,2.0,3.0,4.0];\
             let r=data.iter().fold(0.0f64,|acc,&x| acc + k*x);\
             std::process::exit(((r*2.0) as i64 % 128) as i32);}",
            true, // float accumulator + captured float
        ),
        (
            "fn main(){let data=[1i64,2,3,4,5,6,7,8,9,10];\
             let r=data.iter().fold(0i64,|acc,&x| acc+x);\
             std::process::exit((r.rem_euclid(128)) as i32);}",
            true, // NON-capturing regression (dummy env retained)
        ),
        (
            "fn main(){let outer=[1i64,2,3];let inner=[10i64,20];\
             let r=outer.iter().fold(0i64,|acc,&i| acc + inner.iter().fold(0i64,|a2,&j| a2+j+i));\
             std::process::exit((r.rem_euclid(128)) as i32);}",
            false, // nested fold-in-fold: MUST NOT ICE — fail-close or match, never panic
        ),
    ];
    for (src, must_lower) in cases {
        let llvm = run_llvm(&dir, src);
        let mut lowered = false;
        for opt in ["0", "2", "3"] {
            if let Some(code) = run_bridge(&dir, &dylib, src, opt) {
                lowered = true;
                assert_eq!(
                    code, llvm,
                    "capturing fold at -O{opt} WRONG: bridge={code} llvm={llvm} src=<<<{src}>>>"
                );
            }
        }
        if *must_lower {
            assert!(lowered, "capturing fold fail-closed at every level: src=<<<{src}>>>");
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// PIN for the dyn-Fn tuple-SPREAD (re-landed 2026-07-17 after the flag-error
/// revert). Dynamic Fn-trait dispatch (`&dyn Fn` / `&mut dyn FnMut`) untuples its
/// rust-call argument tuple to the vtable method's spread ABI, so dyn-Fn calls
/// now lower and MATCH LLVM (were fail-closed). Cases are ≤3-arg: this harness
/// compiles overflow-checks ON (rustc default), and a SEPARATE pre-existing
/// backend regalloc bug (task #66, overflow-ON only) corrupts the 4th+
/// simultaneously-live call value under that mode — so 4+-arg dyn cases are
/// correct in the bridge's real `-Coverflow-checks=off` mode but NOT testable
/// here. Each case must lower at -O0 and MATCH; -O2/-O3 declines are tolerated.
#[test]
fn dyn_fn_arg_spread_matches_llvm() {
    if !x86_64_runtime_available() {
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("dynfnspread");
    let cases: &[&str] = &[
        "fn main(){let f:&dyn Fn(i64,i64,i64)->i64=&|a,b,c| a-b*10+c*100;\
         std::process::exit((f(2,3,4)).rem_euclid(128) as i32);}",
        "fn main(){let k=7i64;let f:&dyn Fn(i64,i64)->i64=&|a,b| a*k+b;\
         std::process::exit((f(3,5)).rem_euclid(128) as i32);}",
        "fn main(){let mut acc=0i64;{let mut g:&mut dyn FnMut(i64,i64,i64)->i64=&mut |a,b,c|{acc+=a+b+c;acc};\
         let r=g(1,2,3)+g(4,5,6);std::process::exit((r).rem_euclid(128) as i32);}}",
        "fn main(){let x=41i64;let f:&dyn Fn(&i64,i64,i64)->i64=&|p,b,c| *p+b+c;\
         std::process::exit((f(&x,3,4)).rem_euclid(128) as i32);}",
    ];
    for src in cases {
        let llvm = run_llvm(&dir, src);
        let mut lowered = false;
        for opt in ["0", "2", "3"] {
            if let Some(code) = run_bridge(&dir, &dylib, src, opt) {
                lowered = true;
                assert_eq!(
                    code, llvm,
                    "dyn-Fn spread at -O{opt} WRONG: bridge={code} llvm={llvm} src=<<<{src}>>>"
                );
            }
        }
        assert!(lowered, "dyn-Fn spread fail-closed at every level: src=<<<{src}>>>");
    }
    let _ = std::fs::remove_dir_all(&dir);
}
