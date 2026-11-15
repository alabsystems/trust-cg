#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a slice STRIDE iterator whose constructor and methods rustc's
// MIR inliner splits between the bridge's interceptions and std's own bodies.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD (fixed 2026-10-02; the rows below now pin the fix). The bridge
// modeled `Chunks` / `Windows` / `ChunksExact` / `RChunks` / `RChunksExact`
// (scalar elements) with its own cursor: the intercepted constructor call wrote
// `{ ptr@0, end@8, n@16 }` (plus `{ rem_data@24, rem_len@32 }` for the `*_exact`
// kinds) and the intercepted `next` read it back.
// std's bodies read std's fields at rustc's offsets instead (`ChunksExact { v,
// rem, chunk_size }`). At `-O3` the `chunks_exact` / `rchunks_exact` CALL survives
// inlining while `next` / `count` / `remainder` are inlined into the caller as
// field projections, so the two meet in one body: std's `v.len` is the cursor's
// `end` pointer and std's `chunk_size` is the cursor's remainder length. Measured
// on f349c8652 (the proofs-off lane, `-Copt-level=3`): `chunks_exact(256).count()`
// over 1000 bytes returned about 18.6 million (an address divided by 232) where
// LLVM returns 3, then aborted; the `chunks_exact` (u8 and u32), `rchunks_exact`
// and `remainder` rows below bus-errored or segfaulted; and with `len % w == 0`
// the zero remainder became a zero stride that never advances.
//
// The bridge now writes and reads std's own state at rustc's offsets
// (`StrideIterLayout`), so the two agree by construction; the interim refusals
// are withdrawn and the stride rows below expect MATCH. The full element/shape
// matrix lives in `stride_iter_layout_differential.rs`.
//
// THE GATE, per row. Each row is ONE library function compiled by LLVM (the
// oracle) and by the bridge at the row's optimization level; the caller is
// always compiled by LLVM, as in the census lanes that found the defect.
//   * `Expect::Match`: the bridge must compile the library and the program must
//     print exactly what the oracle prints and exit with its code.
//   * `Expect::MatchOrRefusal { code, root }`: the same, OR the bridge refuses
//     the library with the named `[code]` diagnostic for that root (now only the
//     unmodeled `chunks_exact_mut` row at -O0, refused for an unrelated reason).
//   * Anything else fails: a different stdout or exit code (the miscompile), a
//     run that exceeds `RUN_TIMEOUT` (the non-terminating loop), a signal, an
//     ICE, or a refusal with any other or no code.
// The oracle is asserted first on every row, so a row cannot pass vacuously.
//
// The widths cover `len % w == 0` (250, 100, 1000, 1) and `len % w != 0` (256,
// 999, 7, and 1001 > len), because the failure modes differ: a zero remainder
// produced the hang (or a division by zero), a nonzero one the wrong count and
// the crash.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin nothing.
// The defect was found in exactly this proofs-off lane.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const STRIDE_INLINE: &str = "TCG-STRIDE-ITER-INLINE";
const RUN_TIMEOUT: Duration = Duration::from_secs(30);
/// `len % w == 0` comes first: with the defect, a zero remainder became a zero
/// stride, and the `chunks_exact_sum_rows` kernel then never terminates.
const WIDTHS: &str = "[250usize, 256, 100, 999, 1000, 1, 1001, 7]";

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// Compiles, and the program's stdout and exit code equal LLVM's.
    Match,
    /// `Match`, or a refusal whose `[code]` line names the root `root`.
    MatchOrRefusal {
        code: &'static str,
        root: &'static str,
    },
}

struct Row {
    name: &'static str,
    opt: &'static str,
    elem: &'static str,
    mutable: bool,
    body: &'static str,
    expect: Expect,
}

/// A loop over the yielded sub-slices that folds every chunk's LENGTH and its
/// FIRST and LAST elements, so a wrong data pointer, a wrong length or a wrong
/// chunk count changes the result.
macro_rules! fold_rows {
    ($iter:literal) => {
        concat!(
            "let mut s = 0u64;\n",
            "    for row in ",
            $iter,
            " {\n",
            "        s = s.wrapping_mul(31).wrapping_add(row.len() as u64 * 1000)\n",
            "            .wrapping_add(row[0] as u64 * 7).wrapping_add(row[row.len() - 1] as u64);\n",
            "    }\n",
            "    s"
        )
    };
}

/// Like `fold_rows!`, over a `_mut` iterator that first writes each chunk.
macro_rules! fold_rows_mut {
    ($iter:literal) => {
        concat!(
            "let mut s = 0u64;\n",
            "    for row in ",
            $iter,
            " {\n",
            "        row[0] = row[0].wrapping_add(3);\n",
            "        s = s.wrapping_mul(31).wrapping_add(row.len() as u64 * 1000)\n",
            "            .wrapping_add(row[0] as u64 * 7).wrapping_add(row[row.len() - 1] as u64);\n",
            "    }\n",
            "    s"
        )
    };
}

fn rows() -> Vec<Row> {
    // EXPECTATIONS UPDATED 2026-10-02 (layout migration stage 3). These rows were
    // `MatchOrRefusal` on `[TCG-STRIDE-ITER-INLINE]` (-O3: an inlined std method
    // read the bridge's private cursor) or `[TCG-STRIDE-ITER-METHOD]` (-O0: a
    // non-`next` method on it). The bridge now keeps std's own state at rustc's
    // offsets (`StrideIterLayout`, certified per instance), both refusals are
    // withdrawn under that certificate, and every stride row must MATCH LLVM. A
    // refusal of any of them is now a coverage regression and fails.
    let inline = Expect::Match;
    let method = Expect::Match;
    // (name, element, `&mut` receiver, kernel body, -O0 expectation, -O3 expectation)
    let table: [(&str, &str, bool, &str, Expect, Expect); 18] = [
        // The rows the defect hit: at -O3 the `chunks_exact` / `rchunks_exact` call
        // is intercepted while `count` / `next` / `remainder` are inlined. At -O0
        // every method is a call: `next` and `remainder` are modeled on the cursor,
        // `count` is refused by name.
        (
            "chunks_exact_count",
            "u8",
            false,
            "img.chunks_exact(w).count() as u64",
            method,
            inline,
        ),
        (
            "chunks_exact_iter",
            "u8",
            false,
            fold_rows!("img.chunks_exact(w)"),
            Expect::Match,
            inline,
        ),
        (
            "chunks_exact_sum_rows",
            "u8",
            false,
            "let mut s = 0u64;\n    \
             for row in img.chunks_exact(w) {\n        \
             let r: u64 = row.iter().map(|&p| p as u64).sum();\n        \
             s = s.wrapping_mul(31).wrapping_add(r);\n    \
             }\n    \
             s",
            Expect::Match,
            inline,
        ),
        (
            "chunks_exact_iter_u32",
            "u32",
            false,
            fold_rows!("img.chunks_exact(w)"),
            Expect::Match,
            inline,
        ),
        (
            "chunks_exact_remainder",
            "u8",
            false,
            "let r = img.chunks_exact(w).remainder();\n    \
             let mut s = r.len() as u64 * 1000;\n    \
             if !r.is_empty() { s += r[0] as u64; }\n    \
             s",
            Expect::Match,
            inline,
        ),
        (
            "rchunks_exact_iter",
            "u8",
            false,
            fold_rows!("img.rchunks_exact(w)"),
            Expect::Match,
            inline,
        ),
        // Before the fix this row exited 0 with a wrong value: the silent case.
        (
            "rchunks_exact_remainder",
            "u8",
            false,
            "let r = img.rchunks_exact(w).remainder();\n    \
             let mut s = r.len() as u64 * 1000;\n    \
             if !r.is_empty() { s += r[0] as u64; }\n    \
             s",
            Expect::Match,
            inline,
        ),
        // `rev` inlines `next_back`; at -O0 the `rev` call is refused by name.
        (
            "chunks_exact_rev",
            "u8",
            false,
            fold_rows!("img.chunks_exact(w).rev()"),
            method,
            inline,
        ),
        // An adapter that moves the cursor and reaches it only through `next` calls
        // reads no field and still compiles at -O3.
        (
            "chunks_exact_enumerate",
            "u8",
            false,
            "let mut s = 0u64;\n    \
             for (i, r) in img.chunks_exact(w).enumerate() {\n        \
             s = s.wrapping_mul(31).wrapping_add(i as u64 + r.len() as u64);\n    \
             }\n    \
             s",
            method,
            Expect::Match,
        ),
        // The siblings. At -O3 `chunks` / `windows` inline their constructor to
        // std's aggregate literal (refused), or `count` and the `rchunks` loop fold
        // the iterator away entirely, leaving no stride iterator to model.
        (
            "chunks_count",
            "u8",
            false,
            "img.chunks(w).count() as u64",
            method,
            Expect::Match,
        ),
        (
            "chunks_iter",
            "u8",
            false,
            fold_rows!("img.chunks(w)"),
            Expect::Match,
            inline,
        ),
        (
            "windows_count",
            "u8",
            false,
            "img.windows(w).count() as u64",
            method,
            Expect::Match,
        ),
        (
            "windows_iter",
            "u8",
            false,
            fold_rows!("img.windows(w)"),
            Expect::Match,
            inline,
        ),
        (
            "rchunks_iter",
            "u8",
            false,
            fold_rows!("img.rchunks(w)"),
            Expect::Match,
            Expect::Match,
        ),
        // The `_mut` twins are never modeled: std's layout on both sides, so no
        // stride refusal may fire. At -O0 std's own `ChunksExactMut::next` stops
        // at an unrelated `[TCG-IR-LOWER]` (a `Ptr` branch argument into a
        // `RefMut(Ptr)` block parameter).
        (
            "chunks_mut_iter",
            "u8",
            true,
            fold_rows_mut!("img.chunks_mut(w)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "chunks_exact_mut_iter",
            "u8",
            true,
            fold_rows_mut!("img.chunks_exact_mut(w)"),
            Expect::MatchOrRefusal {
                code: "TCG-IR-LOWER",
                root: "14ChunksExactMut",
            },
            Expect::Match,
        ),
        (
            "rchunks_mut_iter",
            "u8",
            true,
            fold_rows_mut!("img.rchunks_mut(w)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "rchunks_exact_mut_iter",
            "u8",
            true,
            fold_rows_mut!("img.rchunks_exact_mut(w)"),
            Expect::Match,
            Expect::Match,
        ),
    ];
    let mut rows = Vec::new();
    for (opt, pick_o3) in [("0", false), ("3", true)] {
        for &(name, elem, mutable, body, o0, o3) in &table {
            rows.push(Row {
                name,
                opt,
                elem,
                mutable,
                body,
                expect: if pick_o3 { o3 } else { o0 },
            });
        }
    }
    rows
}

fn lib_source(row: &Row) -> String {
    let param = if row.mutable {
        format!("&mut [{}]", row.elem)
    } else {
        format!("&[{}]", row.elem)
    };
    format!(
        "#[inline(never)]\npub fn k(img: {param}, w: usize) -> u64 {{\n    {}\n}}\n",
        row.body
    )
}

fn main_source(row: &Row) -> String {
    let borrow = if row.mutable {
        "&mut buf[..]"
    } else {
        "&buf[..]"
    };
    format!(
        "use std::hint::black_box;\n\
         fn main() {{\n\
         \x20   let img: Vec<{elem}> = (0..1000u32).map(|i| (i % 7 + 1) as {elem}).collect();\n\
         \x20   for &w in &{WIDTHS} {{\n\
         \x20       let mut buf = img.clone();\n\
         \x20       let k = klib::k(black_box({borrow}), black_box(w));\n\
         \x20       println!(\"w={{}} k={{}}\", w, k);\n\
         \x20   }}\n\
         }}\n",
        elem = row.elem,
    )
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_stride_inline_{stem}_{}", std::process::id()));
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

/// Compile the row's library; `Err` carries the compiler's stderr.
fn compile_lib(dir: &Path, row: &Row, backend: Option<&Path>, rlib: &Path) -> Result<(), String> {
    let src = dir.join("klib.rs");
    std::fs::write(&src, lib_source(row)).expect("write library source");
    let mut cmd = base_command(row.opt);
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
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
    assert!(
        oracle.status.success() && oracle_stdout.lines().count() == 8,
        "row {label}: the LLVM oracle must print one line per width and exit 0; \
         status {:?}, stdout <<<{oracle_stdout}>>>",
        oracle.status
    );

    let verdict = match compile_lib(&dir, row, Some(dylib), &bridge_rlib) {
        Ok(()) => {
            let bridge_bin = dir.join("bridge_kmain");
            compile_main(&dir, row, &bridge_rlib, &bridge_bin);
            let Some(bridge) = run_with_timeout(&bridge_bin) else {
                panic!(
                    "row {label}: the bridge-compiled library did not finish within \
                     {RUN_TIMEOUT:?} (the non-terminating stride loop); oracle printed \
                     <<<{oracle_stdout}>>>"
                );
            };
            let bridge_stdout = String::from_utf8_lossy(&bridge.stdout).into_owned();
            assert_eq!(
                (bridge.status.code(), bridge_stdout.as_str()),
                (oracle.status.code(), oracle_stdout.as_str()),
                "row {label}: the bridge-compiled library disagrees with LLVM (exit code \
                 None is a signal). A stride iterator's std fields were read from the \
                 bridge's state, or the state under another layout: fix the layout \
                 (`StrideIterLayout`) rather than relaxing this assertion. stderr <<<{}>>>",
                String::from_utf8_lossy(&bridge.stderr)
            );
            "MATCHED LLVM".to_owned()
        }
        Err(stderr) => {
            assert!(
                !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
                "row {label}: the bridge crashed instead of failing closed: <<<{stderr}>>>"
            );
            let codes = refusal_codes(&stderr);
            match row.expect {
                Expect::Match => panic!(
                    "row {label}: this shape compiles and runs correctly and must not be \
                     refused (codes {codes:?}): <<<{stderr}>>>"
                ),
                Expect::MatchOrRefusal { code, root } => {
                    let names_root = stderr
                        .lines()
                        .any(|line| line.contains(&format!("[{code}]")) && line.contains(root));
                    assert!(
                        names_root,
                        "row {label}: expected a match or the named [{code}] refusal of the \
                         root `…{root}`; got codes {codes:?}: <<<{stderr}>>>"
                    );
                    format!("REFUSED [{code}] (fail-closed)")
                }
            }
        }
    };
    let _ = std::fs::remove_dir_all(&dir);
    verdict
}

#[test]
fn stride_iterators_never_mix_the_bridge_cursor_with_std_fields() {
    if toolchain_support::skip_without_backend_knobs(
        "stride_iterators_never_mix_the_bridge_cursor_with_std_fields",
    ) {
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
    eprintln!("stride-iterator rows ({}): {report:#?}", rows.len());
}

/// The same defect with the WHOLE program compiled by the bridge. Measured on
/// f349c8652: `w=256 nrows=18605702` and SIGABRT, and with `w = 250` first,
/// SIGABRT at once (a zero `chunk_size` divisor). Refused by name after the
/// interim fix; since the layout migration (2026-10-02) it must MATCH.
#[test]
fn whole_program_chunks_exact_count_matches_llvm_or_refuses() {
    if toolchain_support::skip_without_backend_knobs(
        "whole_program_chunks_exact_count_matches_llvm_or_refuses",
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
             fn nrows(img: &[u8], w: usize) -> u64 {{ img.chunks_exact(w).count() as u64 }}\n\
             fn main() {{\n\
             \x20   let img: Vec<u8> = (0..1000u32).map(|i| (i % 7) as u8).collect();\n\
             \x20   for &w in &{WIDTHS} {{\n\
             \x20       let n = nrows(black_box(&img), black_box(w));\n\
             \x20       println!(\"w={{}} nrows={{}}\", w, n);\n\
             \x20   }}\n\
             }}\n"
        ),
    )
    .expect("write program source");
    let build = |backend: Option<&Path>, bin: &Path| -> Result<(), String> {
        let mut cmd = base_command("3");
        cmd.args(["--crate-type", "bin", "--crate-name", "whole"]);
        if let Some(dylib) = backend {
            let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
            backend_arg.push(dylib);
            cmd.arg(backend_arg);
            cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
        }
        cmd.arg("-o").arg(bin).arg(&src);
        let output = cmd.output().expect("spawn the compiler");
        if output.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).into_owned())
        }
    };
    let oracle_bin = dir.join("llvm_whole");
    build(None, &oracle_bin).unwrap_or_else(|e| panic!("the LLVM oracle did not build: <<<{e}>>>"));
    let oracle = run_with_timeout(&oracle_bin).expect("the LLVM oracle did not finish");
    let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
    assert!(
        oracle.status.success() && oracle_stdout.contains("\nw=256 nrows=3\n"),
        "the LLVM oracle must count 3 full 256-byte chunks in 1000 bytes: <<<{oracle_stdout}>>>"
    );
    let bridge_bin = dir.join("bridge_whole");
    match build(Some(&dylib), &bridge_bin) {
        Ok(()) => {
            let bridge = run_with_timeout(&bridge_bin).unwrap_or_else(|| {
                panic!("the bridge-compiled program did not finish within {RUN_TIMEOUT:?}")
            });
            assert_eq!(
                (
                    bridge.status.code(),
                    String::from_utf8_lossy(&bridge.stdout).as_ref()
                ),
                (oracle.status.code(), oracle_stdout.as_str()),
                "the bridge-compiled program disagrees with LLVM (exit code None is a signal)"
            );
            eprintln!("whole program: MATCHED LLVM");
        }
        Err(stderr) => {
            panic!(
                "the bridge must compile the whole program since the stride iterators keep \
                 rustc's layout (the [{STRIDE_INLINE}] refusal is withdrawn under the \
                 certificate); got codes {:?}: <<<{stderr}>>>",
                refusal_codes(&stderr)
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn refusal_code_scan_reads_every_bracketed_code() {
    let stderr = "error: [TCG-MIR-UNSUPPORTED] cannot compile\n  - _RNvCs0_4klib1k (reachable): \
                  [TCG-STRIDE-ITER-INLINE] a slice stride iterator field";
    assert_eq!(
        refusal_codes(stderr),
        vec!["TCG-MIR-UNSUPPORTED".to_owned(), STRIDE_INLINE.to_owned()]
    );
    assert!(refusal_codes("no codes here").is_empty());
}
