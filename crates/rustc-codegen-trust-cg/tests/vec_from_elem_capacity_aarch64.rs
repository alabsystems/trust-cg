// Other hosts compile no native test; a Darwin host must meet every prerequisite.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// `vec![value; n]` reports rustc's capacity, including 0, for a scalar and for
// a struct element.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Both `from_elem` lowerings (`lower_vec_from_elem` for a scalar element,
// `lower_vec_from_elem_image` for a struct element) used to allocate
// `max(n, 1)` elements, so an EMPTY result reported capacity 1 where rustc/LLVM
// report 0 (LIMITATIONS, candidate 9d). MEASURED before the fix (2026-10-03,
// Trust pack 9192): with a bridge-built `make`, the struct program exits 15
// against LLVM's 117 and the scalar program 223 against LLVM's 74, at O0 and
// O3. The buffer now holds exactly `n` elements (none, and no allocator call,
// for `n == 0`), and the struct prototype lives in a stack slot.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::path::Path;
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

/// One cross-crate program: the library's `make` builds the `Vec`, the binary
/// folds capacity, length and contents for `n = 0, 1, 5` into its exit code.
struct Case {
    name: &'static str,
    lib: &'static str,
    main: &'static str,
    oracle: i32,
}

const CASES: &[Case] = &[
    Case {
        name: "struct",
        lib: r#"#![crate_name = "xlib"]
#[derive(Clone, Copy)]
pub struct Pair { pub a: u32, pub b: u16 }
#[inline(never)]
pub fn make(n: usize, a: u32) -> Vec<Pair> { vec![Pair { a, b: 7 }; n] }
"#,
        main: r#"extern crate xlib;
fn main() {
    let mut acc: u64 = 0;
    for n in [0usize, 1, 5] {
        let v = xlib::make(std::hint::black_box(n), 3);
        let mut s = 0u64; for p in v.iter() { s += p.a as u64 * 10 + p.b as u64; }
        acc = acc * 131 + v.capacity() as u64 * 7 + v.len() as u64 * 3 + s;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        oracle: 117,
    },
    Case {
        name: "scalar",
        lib: r#"#![crate_name = "xlib"]
#[inline(never)]
pub fn make(n: usize, x: u64) -> Vec<u64> { vec![x; n] }
"#,
        main: r#"extern crate xlib;
fn main() {
    let mut acc: u64 = 0;
    for n in [0usize, 1, 5] {
        let v = xlib::make(std::hint::black_box(n), 9);
        let s: u64 = v.iter().sum();
        acc = acc * 131 + v.capacity() as u64 * 7 + v.len() as u64 * 3 + s;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        oracle: 74,
    },
];

fn rustc(backend: Option<&Path>, opt: u32) -> Command {
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"));
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        command
            .arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    command
}

fn run_pair(
    dir: &Path,
    case: &Case,
    label: &str,
    lib_backend: Option<&Path>,
    bin_backend: Option<&Path>,
    opt: u32,
) -> i32 {
    let out = dir.join(format!("{}-{label}-O{opt}", case.name));
    std::fs::create_dir_all(&out).expect("cell dir");
    let lib_rs = out.join("xlib.rs");
    std::fs::write(&lib_rs, case.lib).expect("write lib");
    let main_rs = out.join("main.rs");
    std::fs::write(&main_rs, case.main).expect("write main");
    let rlib = out.join("libxlib.rlib");
    let mut lib = rustc(lib_backend, opt);
    lib.args(["--crate-type", "rlib", "-o"])
        .arg(&rlib)
        .arg(&lib_rs);
    let lib = lib.output().expect("spawn compiler");
    assert!(
        lib.status.success(),
        "{} {label} O{opt}: lib:\n{}",
        case.name,
        String::from_utf8_lossy(&lib.stderr)
    );
    let exe = out.join("prog");
    let mut extern_arg = std::ffi::OsString::from("xlib=");
    extern_arg.push(&rlib);
    let mut bin = rustc(bin_backend, opt);
    bin.args(["--crate-type", "bin", "--crate-name", "prog", "--extern"])
        .arg(extern_arg)
        .arg("-o")
        .arg(&exe)
        .arg(&main_rs);
    let bin = bin.output().expect("spawn compiler");
    assert!(
        bin.status.success(),
        "{} {label} O{opt}: bin:\n{}",
        case.name,
        String::from_utf8_lossy(&bin.stderr)
    );
    Command::new(&exe)
        .output()
        .expect("run program")
        .status
        .code()
        .unwrap_or(-1)
}

#[test]
fn vec_from_elem_reports_rustc_capacity_including_zero_aarch64() {
    darwin_native::require("vec_from_elem_capacity_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    let backend = Some(backend.as_path());
    let dir = std::env::temp_dir().join(format!("rcl2_vec_elem_a64_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let mut cells = 0;
    let mut wrong = Vec::new();
    for case in CASES {
        for opt in [0, 3] {
            for (lib, bin, label) in [
                (None, None, "llvm-llvm"),
                (backend, None, "tcg-llvm"),
                (None, backend, "llvm-tcg"),
                (backend, backend, "tcg-tcg"),
            ] {
                let code = run_pair(&dir, case, label, lib, bin, opt);
                cells += 1;
                if code != case.oracle {
                    wrong.push(format!(
                        "{} O{opt} {label}: exit {code}, LLVM oracle {}",
                        case.name, case.oracle
                    ));
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        wrong.is_empty(),
        "vec![value; n] capacity disagrees with rustc/LLVM:\n{}",
        wrong.join("\n")
    );
    eprintln!(
        "VEC_FROM_ELEM_CAPACITY cases={} cells={cells} opts=0,3",
        CASES.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
