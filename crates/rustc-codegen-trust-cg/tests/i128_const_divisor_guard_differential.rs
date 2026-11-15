#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: 128-bit division and remainder by a nonzero divisor whose
// low 64 bits are zero.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD. A div/rem by a nonzero integer literal carries `DivNonZero`, and
// the adapter emits `GuardDivZero [divisor]` ahead of it. An i128 divisor is a
// `(lo, hi)` register pair. Instruction selection used to bind the guard's
// runtime carrier to the LOW register only, and its constant elision read only
// single-immediate `Iconst`s, so a divisor materialized as `Iconst128` with
// `lo == 0` (`1 << 64`, `3 << 64`, `-(1 << 64)`, `i128::MIN`) kept a carrier
// that expanded to `CBNZ lo; BRK #1` and trapped on every call. Measured on
// f349c8652 (proofs-off lane, LLVM caller, bridge library): SIGTRAP for a named
// const and `i128::MIN` at -O0..-O3, a folded `a / (3u128 << 64)` from -O1,
// and `checked_div` / `checked_rem` / `div_ceil` / `/ NonZeroU128` from -O2,
// where LLVM prints the quotient. Runtime divisors carry no `DivNonZero` and
// are checked by rustc's own full-width `Assert`; their rows (including the
// high-word-only divisors and a zero divisor that must still panic) are the
// controls, with the low-word-nonzero and 64-bit-and-narrower constants.
//
// THE GATE, per row. Each row is ONE library function `k` compiled by LLVM
// (the oracle) and by the bridge at the row's optimization level; the caller is
// always compiled by LLVM. The caller runs `k` over every input of the row's
// shape and prints each result. Every row must compile, print exactly what the
// oracle prints and exit with its code. Anything else fails: a different stdout
// or exit code (the miscompile, or the spurious trap: exit code None is a
// signal), a run past `RUN_TIMEOUT`, an ICE, or any refusal (each shape here
// compiled at f349c8652, so a refusal would be a regression, not a fix).
// The oracle is asserted first on every row, so a row cannot pass vacuously.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin nothing.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const RUN_TIMEOUT: Duration = Duration::from_secs(30);
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

/// The dividends, as Rust array literals the caller iterates.
const U128_INPUTS: &str = "[0u128, 1, 7u128 << 64, (7u128 << 64) + 9, (3u128 << 64) - 1, \
                           u128::MAX, 1u128 << 127]";
const I128_INPUTS: &str = "[0i128, 1, -1, 5i128 << 64, -((5i128 << 64) + 9), i128::MAX, \
                           i128::MIN + 1, i128::MIN]";
/// Runtime divisors: high-word-only, low-word-only, both, and the extremes.
const U128_DIVISORS: &str = "[1u128 << 64, 3u128 << 64, (1u128 << 64) + 1, 7, u128::MAX, \
                             1u128 << 127]";
const I128_DIVISORS: &str = "[1i128 << 64, -(1i128 << 64), i128::MIN, -7, i128::MAX, \
                             3i128 << 64]";

/// `k`'s signature, and how the LLVM caller drives it.
#[derive(Clone, Copy, Debug)]
enum Shape {
    /// `k(a: u128) -> u128` over every u128 dividend.
    U128,
    /// `k(a: i128) -> i128` over every i128 dividend.
    I128,
    /// `k(a: u128) -> Option<u128>`.
    U128Option,
    /// `k(a: i128) -> Option<i128>`.
    I128Option,
    /// `k(a: u128, d: u128) -> u128` over every dividend and runtime divisor.
    U128Runtime,
    /// `k(a: i128, d: i128) -> i128` over every dividend and runtime divisor.
    I128Runtime,
    /// `k(a: u128, d: u128) -> u128` with a nonzero divisor, then a ZERO one:
    /// both programs must print the first quotient and then panic (abort).
    U128RuntimeZero,
    /// `k(xs: &[u128]) -> u128` over a four-element slice.
    U128Slice,
    /// `k(a: u64) -> u64`.
    U64,
}

struct Row {
    name: &'static str,
    opt: &'static str,
    shape: Shape,
    body: &'static str,
}

fn rows() -> Vec<Row> {
    // (name, shape, kernel body)
    let table: [(&str, Shape, &str); 30] = [
        // A named constant with a zero low word: the defect at every level.
        (
            "u128_div_named",
            Shape::U128,
            "const D: u128 = 3 << 64;\n    a / D",
        ),
        (
            "u128_rem_named",
            Shape::U128,
            "const D: u128 = 3 << 64;\n    a % D",
        ),
        (
            "i128_div_named",
            Shape::I128,
            "const D: i128 = 1 << 64;\n    a / D",
        ),
        (
            "i128_rem_named",
            Shape::I128,
            "const D: i128 = 1 << 64;\n    a % D",
        ),
        (
            "i128_div_named_negative",
            Shape::I128,
            "const D: i128 = -(1 << 64);\n    a / D",
        ),
        (
            "i128_rem_named_negative",
            Shape::I128,
            "const D: i128 = -(3 << 64);\n    a % D",
        ),
        ("i128_div_min", Shape::I128, "a / i128::MIN"),
        ("i128_rem_min", Shape::I128, "a % i128::MIN"),
        // A constant expression MIR folds into the divisor from -O1.
        ("u128_div_folded", Shape::U128, "a / (3u128 << 64)"),
        ("u128_rem_folded", Shape::U128, "a % (5u128 << 64)"),
        ("i128_div_folded", Shape::I128, "a / (7i128 << 64)"),
        ("i128_rem_folded", Shape::I128, "a % -(5i128 << 64)"),
        // std helpers whose divisor becomes a literal after MIR inlining (-O2).
        (
            "u128_checked_div",
            Shape::U128Option,
            "a.checked_div(3 << 64)",
        ),
        (
            "u128_checked_rem",
            Shape::U128Option,
            "a.checked_rem(3 << 64)",
        ),
        (
            "i128_checked_div",
            Shape::I128Option,
            "a.checked_div(1 << 64)",
        ),
        (
            "i128_checked_rem_min",
            Shape::I128Option,
            "a.checked_rem(i128::MIN)",
        ),
        ("u128_div_ceil", Shape::U128, "a.div_ceil(3 << 64)"),
        (
            "u128_div_nonzero",
            Shape::U128,
            "const NZ: core::num::NonZeroU128 = match core::num::NonZeroU128::new(3 << 64) {\n        \
             Some(n) => n,\n        \
             None => panic!(),\n    \
             };\n    \
             a / NZ",
        ),
        ("i128_div_euclid", Shape::I128, "a.div_euclid(1 << 64)"),
        ("i128_rem_euclid", Shape::I128, "a.rem_euclid(1 << 64)"),
        // A loop-invariant constant divisor.
        (
            "u128_sum_div_loop",
            Shape::U128Slice,
            "const D: u128 = 5 << 64;\n    \
             let mut s = 0u128;\n    \
             let mut i = 0;\n    \
             while i < xs.len() {\n        \
             s = s.wrapping_add(xs[i] / D);\n        \
             i += 1;\n    \
             }\n    \
             s",
        ),
        // Runtime divisors, including high-word-only ones and a zero divisor.
        ("u128_div_runtime", Shape::U128Runtime, "a / d"),
        ("u128_rem_runtime", Shape::U128Runtime, "a % d"),
        ("i128_div_runtime", Shape::I128Runtime, "a / d"),
        ("i128_rem_runtime", Shape::I128Runtime, "a % d"),
        ("u128_div_runtime_zero", Shape::U128RuntimeZero, "a / d"),
        // Constants whose low word is nonzero, a small i128, and a u64.
        (
            "u128_div_low_word_one",
            Shape::U128,
            "const D: u128 = (3 << 64) + 1;\n    a / D",
        ),
        (
            "u128_div_u64_max",
            Shape::U128,
            "const D: u128 = u64::MAX as u128;\n    a / D",
        ),
        ("i128_div_small", Shape::I128, "a / -7"),
        (
            "u64_div_3x2p32",
            Shape::U64,
            "const D: u64 = 3 << 32;\n    a / D",
        ),
    ];
    let mut rows = Vec::with_capacity(table.len() * OPT_LEVELS.len());
    for (name, shape, body) in table {
        for opt in OPT_LEVELS {
            rows.push(Row {
                name,
                opt,
                shape,
                body,
            });
        }
    }
    rows
}

fn lib_source(row: &Row) -> String {
    let signature = match row.shape {
        Shape::U128 => "a: u128) -> u128",
        Shape::I128 => "a: i128) -> i128",
        Shape::U128Option => "a: u128) -> Option<u128>",
        Shape::I128Option => "a: i128) -> Option<i128>",
        Shape::U128Runtime | Shape::U128RuntimeZero => "a: u128, d: u128) -> u128",
        Shape::I128Runtime => "a: i128, d: i128) -> i128",
        Shape::U128Slice => "xs: &[u128]) -> u128",
        Shape::U64 => "a: u64) -> u64",
    };
    format!(
        "#[inline(never)]\npub fn k({signature} {{\n    {}\n}}\n",
        row.body
    )
}

fn main_source(row: &Row) -> String {
    let drive = match row.shape {
        Shape::U128 | Shape::U128Option => format!(
            "for a in {U128_INPUTS} {{\n        println!(\"{{a}} -> {{:?}}\", klib::k(black_box(a)));\n    }}"
        ),
        Shape::I128 | Shape::I128Option => format!(
            "for a in {I128_INPUTS} {{\n        println!(\"{{a}} -> {{:?}}\", klib::k(black_box(a)));\n    }}"
        ),
        Shape::U128Runtime => format!(
            "for a in {U128_INPUTS} {{\n        for d in {U128_DIVISORS} {{\n            \
             println!(\"{{a}} {{d}} -> {{}}\", klib::k(black_box(a), black_box(d)));\n        }}\n    }}"
        ),
        Shape::I128Runtime => format!(
            "for a in {I128_INPUTS} {{\n        for d in {I128_DIVISORS} {{\n            \
             println!(\"{{a}} {{d}} -> {{}}\", klib::k(black_box(a), black_box(d)));\n        }}\n    }}"
        ),
        Shape::U128RuntimeZero => "for d in [1u128 << 64, 0] {\n        \
             println!(\"{d} -> {}\", klib::k(black_box(7u128 << 64), black_box(d)));\n    }"
            .to_owned(),
        Shape::U128Slice => {
            "let v: Vec<u128> = (1..=4u128).map(|k| k * (11u128 << 64)).collect();\n    \
             println!(\"{}\", klib::k(black_box(&v[..])));"
                .to_owned()
        }
        Shape::U64 => "for a in [0u64, 7 << 32, (3 << 32) - 1, u64::MAX] {\n        \
             println!(\"{a} -> {}\", klib::k(black_box(a)));\n    }"
            .to_owned(),
    };
    format!("use std::hint::black_box;\nfn main() {{\n    {drive}\n}}\n")
}

/// Lines the oracle prints, and whether it must exit successfully.
fn oracle_contract(shape: Shape) -> (usize, bool) {
    match shape {
        Shape::U128 | Shape::U128Option => (7, true),
        Shape::I128 | Shape::I128Option => (8, true),
        Shape::U128Runtime => (7 * 6, true),
        Shape::I128Runtime => (8 * 6, true),
        // The first quotient, then the divide-by-zero panic.
        Shape::U128RuntimeZero => (1, false),
        Shape::U128Slice => (1, true),
        Shape::U64 => (4, true),
    }
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tcg_i128_divisor_guard_{stem}_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn base_command(opt: &str) -> Command {
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(format!("-Copt-level={opt}"));
    cmd
}

fn add_backend(cmd: &mut Command, dylib: &Path) {
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(backend_arg);
    cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
}

/// Compile the row's library; `Err` carries the compiler's stderr.
fn compile_lib(dir: &Path, row: &Row, backend: Option<&Path>, rlib: &Path) -> Result<(), String> {
    let src = dir.join("klib.rs");
    std::fs::write(&src, lib_source(row)).expect("write library source");
    let mut cmd = base_command(row.opt);
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    if let Some(dylib) = backend {
        add_backend(&mut cmd, dylib);
    }
    cmd.arg("-o").arg(rlib).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Link the LLVM-compiled caller against `rlib`.
fn compile_main(dir: &Path, row: &Row, rlib: &Path, bin: &Path) {
    let src = dir.join("kmain.rs");
    std::fs::write(&src, main_source(row)).expect("write caller source");
    let mut cmd = base_command("3");
    cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(rlib);
    cmd.arg("--extern").arg(extern_arg);
    cmd.arg("-o").arg(bin).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    assert!(
        output.status.success(),
        "row {}@O{}: the LLVM-compiled caller did not build: <<<{}>>>",
        row.name,
        row.opt,
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_with_timeout(bin: &Path) -> Option<Output> {
    let mut child = Command::new(bin)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the compiled program");
    let start = Instant::now();
    loop {
        if child
            .try_wait()
            .expect("poll the compiled program")
            .is_some()
        {
            return Some(child.wait_with_output().expect("collect program output"));
        }
        if start.elapsed() >= RUN_TIMEOUT {
            child.kill().expect("kill the timed-out program");
            let _ = child.wait_with_output();
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Every `[TCG-...]` code in `stderr`.
fn refusal_codes(stderr: &str) -> Vec<String> {
    let mut codes = Vec::new();
    let mut rest = stderr;
    while let Some(start) = rest.find("[TCG-") {
        let tail = &rest[start + 1..];
        let Some(end) = tail.find(']') else {
            break;
        };
        codes.push(tail[..end].to_owned());
        rest = &tail[end..];
    }
    codes
}

/// The oracle's output, then the bridge's verdict for one row.
fn check_row(dylib: &Path, row: &Row) -> String {
    let label = format!("{}@O{}", row.name, row.opt);
    let dir = workdir(&label);
    let oracle_rlib = dir.join("llvm").join("libklib.rlib");
    let bridge_rlib = dir.join("bridge").join("libklib.rlib");
    std::fs::create_dir_all(oracle_rlib.parent().unwrap()).expect("create oracle dir");
    std::fs::create_dir_all(bridge_rlib.parent().unwrap()).expect("create bridge dir");

    compile_lib(&dir, row, None, &oracle_rlib).unwrap_or_else(|e| {
        panic!("row {label}: the LLVM oracle library did not build: <<<{e}>>>")
    });
    let oracle_bin = dir.join("llvm_kmain");
    compile_main(&dir, row, &oracle_rlib, &oracle_bin);
    let oracle = run_with_timeout(&oracle_bin)
        .unwrap_or_else(|| panic!("row {label}: the LLVM oracle did not finish"));
    let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
    let (lines, succeeds) = oracle_contract(row.shape);
    assert!(
        oracle.status.success() == succeeds && oracle_stdout.lines().count() == lines,
        "row {label}: the LLVM oracle must print {lines} lines and {}; status {:?}, \
         stdout <<<{oracle_stdout}>>>",
        if succeeds { "exit 0" } else { "then panic" },
        oracle.status
    );

    let verdict = match compile_lib(&dir, row, Some(dylib), &bridge_rlib) {
        Ok(()) => {
            let bridge_bin = dir.join("bridge_kmain");
            compile_main(&dir, row, &bridge_rlib, &bridge_bin);
            let Some(bridge) = run_with_timeout(&bridge_bin) else {
                panic!(
                    "row {label}: the bridge-compiled library did not finish within \
                     {RUN_TIMEOUT:?}; oracle printed <<<{oracle_stdout}>>>"
                );
            };
            let bridge_stdout = String::from_utf8_lossy(&bridge.stdout).into_owned();
            assert_eq!(
                (bridge.status.code(), bridge_stdout.as_str()),
                (oracle.status.code(), oracle_stdout.as_str()),
                "row {label}: the bridge-compiled library disagrees with LLVM (exit code \
                 None is a signal; SIGTRAP with no output is a div-by-zero guard that tested \
                 one half of a 128-bit divisor). Test the whole divisor, rather than relaxing \
                 this assertion. stderr <<<{}>>>",
                String::from_utf8_lossy(&bridge.stderr)
            );
            "MATCHED LLVM".to_owned()
        }
        Err(stderr) => {
            assert!(
                !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
                "row {label}: the bridge crashed instead of failing closed: <<<{stderr}>>>"
            );
            panic!(
                "row {label}: this shape compiles and runs correctly and must not be refused \
                 (codes {:?}): <<<{stderr}>>>",
                refusal_codes(&stderr)
            )
        }
    };
    let _ = std::fs::remove_dir_all(&dir);
    verdict
}

#[test]
fn i128_constant_divisors_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("i128_constant_divisors_match_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let rows = rows();
    let mut report = Vec::new();
    for row in &rows {
        let verdict = check_row(&dylib, row);
        eprintln!("row {}@O{}: {verdict}", row.name, row.opt);
        report.push(format!("{}@O{} {verdict}", row.name, row.opt));
    }
    eprintln!("i128 constant-divisor rows ({}): {report:#?}", rows.len());
}

/// The same divisors with the WHOLE program compiled by the bridge, so the std
/// helpers are bridge-compiled too. Measured on f349c8652: the program died
/// with SIGTRAP before its first line at -O0 and -O3. The driver walks its
/// inputs by index and prints with plain `{}`: a bridge-compiled caller refuses
/// `zip` over arrays ([TCG-MIR-UNSUPPORTED]) and `{:?}` ([TCG-FMT-DECLINED]).
#[test]
fn whole_program_i128_constant_divisors_match_llvm() {
    if toolchain_support::skip_without_backend_knobs(
        "whole_program_i128_constant_divisors_match_llvm",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("whole_program");
    let src = dir.join("whole.rs");
    std::fs::write(
        &src,
        format!(
            "use std::hint::black_box;\n\
             #[inline(never)]\n\
             fn div_named(a: u128) -> u128 {{\n    const D: u128 = 3 << 64;\n    a / D\n}}\n\
             #[inline(never)]\n\
             fn rem_min(a: i128) -> i128 {{\n    a % i128::MIN\n}}\n\
             #[inline(never)]\n\
             fn div_neg(a: i128) -> i128 {{\n    a / -(1i128 << 64)\n}}\n\
             #[inline(never)]\n\
             fn checked(a: u128) -> Option<u128> {{\n    a.checked_div(3 << 64)\n}}\n\
             #[inline(never)]\n\
             fn ceil(a: u128) -> u128 {{\n    a.div_ceil(3 << 64)\n}}\n\
             #[inline(never)]\n\
             fn runtime(a: u128, d: u128) -> u128 {{\n    a / d\n}}\n\
             fn main() {{\n\
             \x20   let (us, is) = ({U128_INPUTS}, {I128_INPUTS});\n\
             \x20   let mut i = 0;\n\
             \x20   while i < us.len() {{\n\
             \x20       let (ua, ia) = (black_box(us[i]), black_box(is[i]));\n\
             \x20       let c = match checked(ua) {{\n\
             \x20           Some(q) => q,\n\
             \x20           None => u128::MAX,\n\
             \x20       }};\n\
             \x20       println!(\"{{}} {{}}: {{}} {{}} {{}} {{}} {{}} {{}}\", ua, ia, div_named(ua), rem_min(ia),\n\
             \x20           div_neg(ia), c, ceil(ua), runtime(ua, black_box(1u128 << 64)));\n\
             \x20       i += 1;\n\
             \x20   }}\n\
             }}\n"
        ),
    )
    .expect("write program source");
    for opt in ["0", "3"] {
        let build = |backend: Option<&Path>, bin: &Path| -> Result<(), String> {
            let mut cmd = base_command(opt);
            cmd.args(["--crate-type", "bin", "--crate-name", "whole"]);
            if let Some(dylib) = backend {
                add_backend(&mut cmd, dylib);
            }
            cmd.arg("-o").arg(bin).arg(&src);
            let output = cmd.output().expect("spawn the compiler");
            if output.status.success() {
                Ok(())
            } else {
                Err(String::from_utf8_lossy(&output.stderr).into_owned())
            }
        };
        let oracle_bin = dir.join(format!("llvm_whole_O{opt}"));
        build(None, &oracle_bin)
            .unwrap_or_else(|e| panic!("O{opt}: the LLVM oracle did not build: <<<{e}>>>"));
        let oracle = run_with_timeout(&oracle_bin)
            .unwrap_or_else(|| panic!("O{opt}: the LLVM oracle did not finish"));
        let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
        assert!(
            oracle.status.success()
                && oracle_stdout.contains(
                    "129127208515966861321 92233720368547758080: 2 92233720368547758080 -5 2 \
                     3 7\n"
                ),
            "O{opt}: the LLVM oracle must print the (7 << 64) + 9 row: <<<{oracle_stdout}>>>"
        );
        let bridge_bin = dir.join(format!("bridge_whole_O{opt}"));
        build(Some(&dylib), &bridge_bin).unwrap_or_else(|e| {
            panic!(
                "O{opt}: the bridge must compile the whole program (codes {:?}): <<<{e}>>>",
                refusal_codes(&e)
            )
        });
        let bridge = run_with_timeout(&bridge_bin).unwrap_or_else(|| {
            panic!("O{opt}: the bridge-compiled program did not finish within {RUN_TIMEOUT:?}")
        });
        assert_eq!(
            (
                bridge.status.code(),
                String::from_utf8_lossy(&bridge.stdout).as_ref()
            ),
            (oracle.status.code(), oracle_stdout.as_str()),
            "O{opt}: the bridge-compiled program disagrees with LLVM (exit code None is a signal)"
        );
        eprintln!("whole program O{opt}: MATCHED LLVM");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn refusal_codes_lists_every_bracketed_code() {
    let stderr = "error: [TCG-MIR-UNSUPPORTED] rustc_codegen_trust_cg: cannot compile\n  \
                  - _RNvCs0_4klib1k (reachable): [TCG-ARG-ABI] the argument";
    assert_eq!(
        refusal_codes(stderr),
        vec!["TCG-MIR-UNSUPPORTED".to_owned(), "TCG-ARG-ABI".to_owned()]
    );
    assert!(refusal_codes("no codes here").is_empty());
}
