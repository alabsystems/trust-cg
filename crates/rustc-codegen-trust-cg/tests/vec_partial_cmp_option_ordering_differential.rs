#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: `<Vec<T> as PartialOrd>::partial_cmp`, which the bridge
// intercepts, must produce the `Option<Ordering>` byte rustc's layout defines.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD. `lower_vec_partial_cmp` calls the lexicographic
// `__trustcg_slice_cmp_*` helper and stores its result as the whole
// `Option<Ordering>`. The ordered codes `-1`/`0`/`1` are the `Some(Less/Equal/
// Greater)` bytes, but `None` is a niche value the compiler chooses, and its
// placement is unspecified layout. The bridge used to store a hard-coded `2`
// for an unordered (`NaN`) lane; the pinned Trust compiler encodes `None` as
// `0xFE`, so `2` is not a valid `Option<Ordering>` at all. Measured on
// f349c8652 (proofs-off lane, LLVM caller, bridge library): `is_none()` and
// `== None` were false, a four-way `match` took `Some(Equal)` at -O0 and leaked
// the raw `2` at -O1, `unwrap_or` returned the invalid `Ordering` 2 with
// `is_some()` true, and the LLVM caller's `{:?}` of the returned value died
// with SIGSEGV at -O1. A direct call is intercepted at -O0/-O1 (at -O2/-O3
// the MIR inliner substitutes std's slice code); a monomorphized generic
// `T: PartialOrd` wrapper keeps the intercepted call at every level.
//
// THE GATE, per row. A row is one library of kernels for one (dispatch,
// element) family, compiled by LLVM (the oracle) and by the bridge at the
// row's optimization level; the caller is always compiled by LLVM. The caller
// runs every kernel over every case in the family's table and prints one line
// per (kernel, case). Its first line is `Option<Ordering>`'s layout as the
// LLVM-compiled caller measures it.
//   * The bridge must compile the library, and the program must print exactly
//     what the oracle prints and exit with its code.
//   * A `[TCG-OPTION-ORDERING-LAYOUT]` refusal of the library is accepted only
//     when the measured layout is not the one-byte shape the bridge models
//     (`Some(Less/Equal/Greater)` = 0xff/0x00/0x01, `None` outside them), and
//     only for families that reach the interception.
//   * Anything else fails: a different stdout or exit code (the miscompile), a
//     run past `RUN_TIMEOUT`, a signal, an ICE, or any other refusal.
// The oracle is asserted first on every row, so a row cannot pass vacuously.
// Every row runs; the failures are reported together at the end.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin nothing.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const LAYOUT_REFUSAL: &str = "TCG-OPTION-ORDERING-LAYOUT";
const RUN_TIMEOUT: Duration = Duration::from_secs(30);
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

/// Float cases, as `(a, b)` element lists over `N` (NaN) and `I` (infinity):
/// NaN against NaN and against a number on either side; NaN first, in the
/// middle and last after an equal prefix; a decisive lane before a NaN; numbers
/// only; a strict prefix; empty against empty and against a NaN; a NaN past the
/// shared prefix (never compared); signed zeros; infinities.
const FLOAT_CASES: &[(&str, &str)] = &[
    ("N", "N"),
    ("N", "1.0"),
    ("1.0", "N"),
    ("N, 1.0, 2.0", "N, 1.0, 2.0"),
    ("1.0, N, 2.0", "1.0, N, 2.0"),
    ("1.0, 2.0, N", "1.0, 2.0, 3.0"),
    ("1.0, 2.0", "1.0, N"),
    ("0.0, N", "1.0, N"),
    ("2.0, N", "1.0, 0.0"),
    ("1.0, 2.0", "1.0, 2.0"),
    ("1.0, 3.0", "1.0, 2.0"),
    ("1.0", "1.0, 2.0"),
    ("", ""),
    ("", "N"),
    ("N", ""),
    ("1.0, N", "1.0"),
    ("-0.0", "0.0"),
    ("I", "N"),
    ("-I, 5.0", "-I, 4.0"),
];

/// Integer cases: every ordered outcome, a strict prefix, empty, and the
/// signed extremes (an unsigned comparison would invert the last one).
const INT_CASES: &[(&str, &str)] = &[
    ("1", "2"),
    ("2", "1"),
    ("1, 2", "1, 2"),
    ("1", "1, 2"),
    ("", ""),
    ("-1, 5", "-1, 4"),
    ("i32::MIN", "i32::MAX"),
];

#[derive(Clone, Copy, Debug)]
enum Dispatch {
    /// `x.partial_cmp(&y)` in the kernel.
    Direct,
    /// Through a non-inlined `fn pcmp<T: PartialOrd>(&T, &T)`.
    Generic,
}

/// A library of kernels compiled for one row.
#[derive(Clone, Copy, Debug)]
enum Family {
    /// Every `Option<Ordering>` consumer over `Vec<elem>`.
    Consumers {
        elem: &'static str,
        dispatch: Dispatch,
    },
    /// Shapes that never reach the interception: a slice, a `fn` pointer to the
    /// Vec impl, and std's scalar `f64::partial_cmp`.
    Controls,
}

struct Row {
    name: String,
    opt: &'static str,
    family: Family,
}

fn rows() -> Vec<Row> {
    let families = [
        Family::Consumers {
            elem: "f64",
            dispatch: Dispatch::Direct,
        },
        Family::Consumers {
            elem: "f64",
            dispatch: Dispatch::Generic,
        },
        Family::Consumers {
            elem: "f32",
            dispatch: Dispatch::Direct,
        },
        Family::Consumers {
            elem: "f32",
            dispatch: Dispatch::Generic,
        },
        Family::Consumers {
            elem: "i32",
            dispatch: Dispatch::Direct,
        },
        Family::Consumers {
            elem: "i32",
            dispatch: Dispatch::Generic,
        },
        Family::Controls,
    ];
    let mut rows = Vec::new();
    for opt in OPT_LEVELS {
        for family in families {
            let name = match family {
                Family::Consumers {
                    elem,
                    dispatch: Dispatch::Direct,
                } => format!("direct_{elem}"),
                Family::Consumers {
                    elem,
                    dispatch: Dispatch::Generic,
                } => format!("generic_{elem}"),
                Family::Controls => "controls_f64".to_owned(),
            };
            rows.push(Row { name, opt, family });
        }
    }
    rows
}

/// The kernels of a `Consumers` library, as `(name, return type, body)`;
/// `CMP` is replaced by the family's `partial_cmp` call on `x` and `y`.
const CONSUMERS: &[(&str, &str, &str)] = &[
    ("match_enc", "i32", "enc(CMP)"),
    ("is_none", "bool", "CMP.is_none()"),
    ("eq_none", "bool", "CMP == None"),
    (
        "unwrap_or",
        "i8",
        "let r = CMP;\n    r.unwrap_or(Ordering::Greater) as i8 * 10 + r.is_some() as i8",
    ),
    ("byte_image", "u8", "byte(&CMP)"),
    ("returned", "Option<Ordering>", "CMP"),
];

/// The control kernels, all over `f64`.
const CONTROLS: &[(&str, &str, &str)] = &[
    ("slice_enc", "i32", "enc(a.partial_cmp(b))"),
    (
        "fn_pointer_enc",
        "i32",
        "let x: Vec<f64> = a.iter().copied().collect();\n    \
         let y: Vec<f64> = b.iter().copied().collect();\n    \
         let f: fn(&Vec<f64>, &Vec<f64>) -> Option<Ordering> =\n        \
         std::hint::black_box(<Vec<f64> as PartialOrd>::partial_cmp);\n    \
         enc(f(&x, &y))",
    ),
    (
        "scalar_byte",
        "u8",
        "let _ = b;\n    byte(&a.first().copied().unwrap_or(0.0).partial_cmp(&f64::NAN))",
    ),
];

/// The library prelude shared by every family: the four-way `match` and a sound
/// one-byte read of an `Option<Ordering>` (the type is one initialized byte, and
/// every byte is a valid `u8`). Each kernel builds its two Vecs as separate
/// locals from the caller's slices: a function returning them as a tuple would
/// be refused as `[TCG-COLLECTION-IMAGE]` (a Vec inside a memory aggregate),
/// which is not the boundary under test.
const PRELUDE: &str = "use std::cmp::Ordering;
fn enc(o: Option<Ordering>) -> i32 {
    match o {
        Some(Ordering::Less) => -1,
        Some(Ordering::Equal) => 0,
        Some(Ordering::Greater) => 1,
        None => 9,
    }
}
#[inline(never)]
fn byte(o: &Option<Ordering>) -> u8 {
    unsafe { *(o as *const Option<Ordering> as *const u8) }
}
";

/// `(kernel name, library source)` for `family`.
fn kernels(family: Family) -> (Vec<&'static str>, String) {
    match family {
        Family::Consumers { elem, dispatch } => {
            let mut src = PRELUDE.to_owned();
            let cmp = match dispatch {
                Dispatch::Direct => "x.partial_cmp(&y)",
                Dispatch::Generic => {
                    src.push_str(
                        "#[inline(never)]\n\
                         fn pcmp<T: PartialOrd>(a: &T, b: &T) -> Option<Ordering> {\n    \
                         a.partial_cmp(b)\n\
                         }\n",
                    );
                    "pcmp(&x, &y)"
                }
            };
            let mut names = Vec::new();
            for &(name, ret, body) in CONSUMERS {
                names.push(name);
                src.push_str(&format!(
                    "#[inline(never)]\n\
                     pub fn {name}(a: &[{elem}], b: &[{elem}]) -> {ret} {{\n    \
                     let x: Vec<{elem}> = a.iter().copied().collect();\n    \
                     let y: Vec<{elem}> = b.iter().copied().collect();\n    \
                     {}\n\
                     }}\n",
                    body.replace("CMP", cmp)
                ));
            }
            (names, src)
        }
        Family::Controls => {
            let mut src = PRELUDE.to_owned();
            let mut names = Vec::new();
            for &(name, ret, body) in CONTROLS {
                names.push(name);
                src.push_str(&format!(
                    "#[inline(never)]\n\
                     pub fn {name}(a: &[f64], b: &[f64]) -> {ret} {{\n    {body}\n}}\n"
                ));
            }
            (names, src)
        }
    }
}

fn elem_and_cases(family: Family) -> (&'static str, &'static [(&'static str, &'static str)]) {
    match family {
        Family::Consumers { elem, .. } if elem.starts_with('f') => (elem, FLOAT_CASES),
        Family::Consumers { elem, .. } => (elem, INT_CASES),
        Family::Controls => ("f64", FLOAT_CASES),
    }
}

/// The LLVM-compiled caller: the layout line, then one line per (kernel, case).
/// The cases are borrowed constants, so the caller never drops a `Vec<elem>`:
/// at -O0/-O1 share-generics would bind that drop to the library's exported
/// `drop_glue::<Vec<elem>>`, which the bridge emits as a trap stub (hunt
/// cluster C5), a defect outside this boundary.
fn main_source(family: Family, kernels: &[&str]) -> String {
    let (elem, cases) = elem_and_cases(family);
    let mut table = String::new();
    for (a, b) in cases {
        table.push_str(&format!("        (&[{a}], &[{b}]),\n"));
    }
    let mut calls = String::new();
    for kernel in kernels {
        calls.push_str(&format!(
            "        println!(\"{kernel} #{{i}} -> {{:?}}\", \
             klib::{kernel}(black_box(a), black_box(b)));\n"
        ));
    }
    let float_consts = if elem.starts_with('f') {
        format!("    const N: {elem} = {elem}::NAN;\n    const I: {elem} = {elem}::INFINITY;\n")
    } else {
        String::new()
    };
    format!(
        "use std::cmp::Ordering;\n\
         use std::hint::black_box;\n\
         fn image(o: Option<Ordering>) -> u8 {{\n    \
         let o = black_box(o);\n    \
         unsafe {{ *(&o as *const Option<Ordering> as *const u8) }}\n\
         }}\n\
         fn main() {{\n\
         \x20   println!(\"layout size={{}} none={{:#04x}} less={{:#04x}} equal={{:#04x}} greater={{:#04x}}\",\n\
         \x20       std::mem::size_of::<Option<Ordering>>(), image(None),\n\
         \x20       image(Some(Ordering::Less)), image(Some(Ordering::Equal)),\n\
         \x20       image(Some(Ordering::Greater)));\n\
         {float_consts}\
         \x20   let cases: &[(&[{elem}], &[{elem}])] = &[\n{table}    ];\n\
         \x20   for (i, &(a, b)) in cases.iter().enumerate() {{\n\
         {calls}\
         \x20   }}\n\
         }}\n"
    )
}

/// Whether the oracle's layout line is the one-byte shape the bridge models.
fn layout_is_modeled(layout_line: &str) -> bool {
    let field = |key: &str| {
        layout_line
            .split_whitespace()
            .find_map(|item| item.strip_prefix(key))
            .map(str::to_owned)
    };
    let byte = |key: &str| {
        field(key).and_then(|v| u8::from_str_radix(v.trim_start_matches("0x"), 16).ok())
    };
    field("size=").as_deref() == Some("1")
        && byte("less=") == Some(0xff)
        && byte("equal=") == Some(0x00)
        && byte("greater=") == Some(0x01)
        && byte("none=").is_some_and(|none| !matches!(none, 0xff | 0x00 | 0x01))
}

fn workdir(stem: &str) -> PathBuf {
    let dir =
        std::env::temp_dir().join(format!("tcg_vec_partial_cmp_{stem}_{}", std::process::id()));
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
fn compile_lib(
    dir: &Path,
    row: &Row,
    src: &str,
    backend: Option<&Path>,
    rlib: &Path,
) -> Result<(), String> {
    let path = dir.join("klib.rs");
    std::fs::write(&path, src).expect("write library source");
    let mut cmd = base_command(row.opt);
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    if let Some(dylib) = backend {
        add_backend(&mut cmd, dylib);
    }
    cmd.arg("-o").arg(rlib).arg(&path);
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Link the LLVM-compiled caller (at the row's level) against `rlib`.
fn compile_main(dir: &Path, row: &Row, src: &str, rlib: &Path, bin: &Path) {
    let path = dir.join("kmain.rs");
    std::fs::write(&path, src).expect("write caller source");
    let mut cmd = base_command(row.opt);
    cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(rlib);
    cmd.arg("--extern").arg(extern_arg);
    cmd.arg("-o").arg(bin).arg(&path);
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

/// Whether `stderr` refuses a `klib` root with the bracketed `code`.
fn names_layout_refusal(stderr: &str, code: &str) -> bool {
    let bracketed = format!("[{code}]");
    stderr.contains(&bracketed)
        && stderr
            .lines()
            .any(|line| line.contains("4klib") && line.contains(&bracketed))
}

/// The lines on which two outputs differ, for the failure message.
fn differing_lines(oracle: &str, bridge: &str) -> Vec<String> {
    let mut diff = Vec::new();
    let (mut o, mut b) = (oracle.lines(), bridge.lines());
    loop {
        match (o.next(), b.next()) {
            (None, None) => break,
            (left, right) if left != right => {
                diff.push(format!("llvm {left:?} / bridge {right:?}"));
            }
            _ => {}
        }
    }
    diff
}

/// The oracle's output, then the bridge's verdict for one row: `Ok` names a
/// match or an admissible refusal, `Err` is the failure. A broken oracle or a
/// crashed compiler panics at once.
fn check_row(dylib: &Path, row: &Row) -> Result<String, String> {
    let label = format!("{}@O{}", row.name, row.opt);
    let dir = workdir(&label);
    let (names, lib_src) = kernels(row.family);
    let main_src = main_source(row.family, &names);
    let (_, cases) = elem_and_cases(row.family);
    let oracle_rlib = dir.join("llvm").join("libklib.rlib");
    let bridge_rlib = dir.join("bridge").join("libklib.rlib");
    std::fs::create_dir_all(oracle_rlib.parent().unwrap()).expect("create oracle dir");
    std::fs::create_dir_all(bridge_rlib.parent().unwrap()).expect("create bridge dir");

    compile_lib(&dir, row, &lib_src, None, &oracle_rlib).unwrap_or_else(|e| {
        panic!("row {label}: the LLVM oracle library did not build: <<<{e}>>>")
    });
    let oracle_bin = dir.join("llvm_kmain");
    compile_main(&dir, row, &main_src, &oracle_rlib, &oracle_bin);
    let oracle = run_with_timeout(&oracle_bin)
        .unwrap_or_else(|| panic!("row {label}: the LLVM oracle did not finish"));
    let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
    let layout_line = oracle_stdout.lines().next().unwrap_or_default().to_owned();
    assert!(
        oracle.status.success()
            && layout_line.starts_with("layout ")
            && oracle_stdout.lines().count() == 1 + names.len() * cases.len(),
        "row {label}: the LLVM oracle must print the layout line and one line per kernel \
         and case, and exit 0; status {:?}, stdout <<<{oracle_stdout}>>>",
        oracle.status
    );
    // The NaN-vs-NaN case is `None` under IEEE partial order; a float family
    // whose oracle says otherwise would pin nothing.
    if let Family::Consumers { elem, .. } = row.family {
        if elem.starts_with('f') {
            assert!(
                oracle_stdout.contains("\nis_none #0 -> true\n")
                    && oracle_stdout.contains("\nmatch_enc #0 -> 9\n"),
                "row {label}: the oracle must report NaN vs NaN as None: <<<{oracle_stdout}>>>"
            );
        }
    }

    let verdict = match compile_lib(&dir, row, &lib_src, Some(dylib), &bridge_rlib) {
        Ok(()) => {
            let bridge_bin = dir.join("bridge_kmain");
            compile_main(&dir, row, &main_src, &bridge_rlib, &bridge_bin);
            let Some(bridge) = run_with_timeout(&bridge_bin) else {
                return Err(format!(
                    "row {label}: the bridge-compiled library did not finish within \
                     {RUN_TIMEOUT:?}; oracle printed <<<{oracle_stdout}>>>"
                ));
            };
            let bridge_stdout = String::from_utf8_lossy(&bridge.stdout).into_owned();
            if (bridge.status.code(), bridge_stdout.as_str())
                == (oracle.status.code(), oracle_stdout.as_str())
            {
                Ok("MATCHED LLVM".to_owned())
            } else {
                Err(format!(
                    "row {label}: the bridge-compiled library disagrees with LLVM (exit code \
                     {:?} vs {:?}; None is a signal). Differing lines: {:#?}\nstderr <<<{}>>>",
                    bridge.status.code(),
                    oracle.status.code(),
                    differing_lines(&oracle_stdout, &bridge_stdout),
                    String::from_utf8_lossy(&bridge.stderr)
                ))
            }
        }
        Err(stderr) => {
            assert!(
                !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
                "row {label}: the bridge crashed instead of failing closed: <<<{stderr}>>>"
            );
            let codes = refusal_codes(&stderr);
            let refusal_admissible =
                matches!(row.family, Family::Consumers { .. }) && !layout_is_modeled(&layout_line);
            if refusal_admissible && names_layout_refusal(&stderr, LAYOUT_REFUSAL) {
                Ok(format!(
                    "REFUSED [{LAYOUT_REFUSAL}] (fail-closed; {layout_line})"
                ))
            } else {
                Err(format!(
                    "row {label}: this family must compile and match LLVM; a \
                     [{LAYOUT_REFUSAL}] refusal is admissible only for an interception family \
                     when the measured layout is not the modeled one-byte shape; got codes \
                     {codes:?}: <<<{stderr}>>>"
                ))
            }
        }
    };
    if verdict.is_ok() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    verdict
}

#[test]
fn vec_partial_cmp_option_ordering_matches_llvm_or_refuses() {
    if toolchain_support::skip_without_backend_knobs(
        "vec_partial_cmp_option_ordering_matches_llvm_or_refuses",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let rows = rows();
    let mut report = Vec::new();
    let mut failures = Vec::new();
    for row in &rows {
        let label = format!("{}@O{}", row.name, row.opt);
        match check_row(&dylib, row) {
            Ok(verdict) => {
                eprintln!("row {label}: {verdict}");
                report.push(format!("{label} {verdict}"));
            }
            Err(failure) => {
                eprintln!("row {label}: FAILED");
                report.push(format!("{label} FAILED"));
                failures.push(failure);
            }
        }
    }
    eprintln!(
        "Vec partial_cmp Option<Ordering> rows ({}): {report:#?}",
        rows.len()
    );
    assert!(
        failures.is_empty(),
        "{} of {} rows failed. `Option<Ordering>` must be written with the bytes of rustc's \
         layout: derive them from `layout_of`, or refuse the shape with [{LAYOUT_REFUSAL}], \
         rather than relaxing this assertion.\n{}",
        failures.len(),
        rows.len(),
        failures.join("\n")
    );
}

#[test]
fn the_modeled_layout_and_the_refusal_match_are_strict() {
    assert!(layout_is_modeled(
        "layout size=1 none=0xfe less=0xff equal=0x00 greater=0x01"
    ));
    assert!(layout_is_modeled(
        "layout size=1 none=0x02 less=0xff equal=0x00 greater=0x01"
    ));
    assert!(!layout_is_modeled(
        "layout size=1 none=0x01 less=0xff equal=0x00 greater=0x01"
    ));
    assert!(!layout_is_modeled(
        "layout size=2 none=0xfe less=0xff equal=0x00 greater=0x01"
    ));
    assert!(!layout_is_modeled("layout size=1 none=0xfe"));
    let stderr = "error: [TCG-MIR-UNSUPPORTED] rustc_codegen_trust_cg: cannot compile\n  \
                  - _RNvCs0_4klib9match_enc (reachable): [TCG-OPTION-ORDERING-LAYOUT] `Option<..>`";
    assert_eq!(
        refusal_codes(stderr),
        vec!["TCG-MIR-UNSUPPORTED".to_owned(), LAYOUT_REFUSAL.to_owned()]
    );
    assert!(names_layout_refusal(stderr, LAYOUT_REFUSAL));
    assert!(!names_layout_refusal(stderr, "TCG-ARG-ABI"));
    assert!(!names_layout_refusal(
        "[TCG-OPTION-ORDERING-LAYOUT] somewhere else",
        LAYOUT_REFUSAL
    ));
    assert_eq!(
        differing_lines("a\nb\n", "a\nc\nd\n"),
        vec![
            "llvm Some(\"b\") / bridge Some(\"c\")".to_owned(),
            "llvm None / bridge Some(\"d\")".to_owned()
        ]
    );
}
