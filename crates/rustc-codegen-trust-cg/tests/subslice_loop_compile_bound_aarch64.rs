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

// A loop that reborrows a slice by a sub-slice of itself compiles in bounded
// time and agrees with LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `address_identity_referents` propagates the places each reference can
// address to a fixpoint, and a reborrow appends its own steps to its source's
// path. A loop whose reference is reborrowed from its own previous value
// (`p = rest` under `[first, rest @ ..] = p`, a `Subslice` of a slice of the
// same type) appended them once per pass, so the fixpoint never converged.
// MEASURED on trust-cg main c5919a122 (2026-10-08, stage-1 trustc): `one_loop`
// and `four_loops` spun past 120 s at -O0..-O3, where LLVM compiles each in
// 0.6 s. Derived paths are now bounded (`MAX_BORROWED_PLACE_PATH`); a base
// whose path saturates is reported as needing real storage.
//
// Every cell must finish compiling within `COMPILE_BUDGET` and exit with
// LLVM's code.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const TARGET: &str = "aarch64-apple-darwin";
/// Generous for a loaded host: each program compiles in about a second.
const COMPILE_BUDGET: Duration = Duration::from_secs(120);

struct Case {
    name: &'static str,
    src: &'static str,
    oracle: i32,
}

const CASES: &[Case] = &[
    Case {
        name: "one_loop",
        src: r#"fn main() {
    let a = [5i64, -3, 8, 0, 2, -7, 4];
    let mut s = 0i64;
    let mut p: &[i64] = &a;
    while let [first, rest @ ..] = p { s += *first; p = rest; }
    std::process::exit((s.rem_euclid(251)) as i32);
}
"#,
        oracle: 9,
    },
    Case {
        name: "four_loops",
        src: r#"fn main() {
    let a = [5i64, -3, 8, 0, 2, -7, 4, 9];
    let mut s = 0i64;
    let mut p: &[i64] = &a;
    while let [first, rest @ ..] = p { s += *first; p = rest; }
    let mut q: &[i64] = &a;
    while let [rest @ .., last] = q { s = s * 3 + *last; q = rest; }
    let mut r: &[i64] = &a;
    loop { match r { [x, y, tail @ ..] => { s ^= x * y; r = tail; } _ => break } }
    let mut t: &[i64] = &a;
    while let [_, mid @ .., _] = t { s += mid.len() as i64; t = mid; }
    std::process::exit((s.rem_euclid(251)) as i32);
}
"#,
        oracle: 219,
    },
    Case {
        name: "swapped_pair",
        src: r#"fn main() {
    let a = [3u32, 1, 4, 1, 5, 9, 2, 6];
    let b = [2u32, 7, 1, 8, 2, 8];
    let mut p: &[u32] = &a;
    let mut q: &[u32] = &b;
    let mut s = 0u32;
    while let ([x, pr @ ..], [y, qr @ ..]) = (p, q) {
        s = s.wrapping_mul(31).wrapping_add(x * 10 + y);
        p = qr;
        q = pr;
    }
    std::process::exit((s % 251) as i32);
}
"#,
        oracle: 197,
    },
    Case {
        name: "nested_rows",
        src: r#"fn main() {
    let rows = [[1u16, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]];
    let mut s = 0u32;
    for row in &rows {
        let mut p: &[u16] = row;
        while let [h, t @ ..] = p { s = s * 3 + *h as u32; p = t; }
        let mut q: &[u16] = row;
        while let [t @ .., l] = q { s ^= (*l as u32) << 2; q = t; }
    }
    std::process::exit((s % 251) as i32);
}
"#,
        oracle: 154,
    },
];

/// Compile `case` at `opt` (with the bridge when `backend` is set) and run it.
/// `Err` names a compile that failed or did not finish within the budget.
fn compile_and_run(
    dir: &Path,
    case: &Case,
    backend: Option<&Path>,
    opt: u32,
) -> Result<i32, String> {
    let label = if backend.is_some() { "tcg" } else { "llvm" };
    let out = dir.join(format!("{}-{label}-O{opt}", case.name));
    std::fs::create_dir_all(&out).expect("cell dir");
    let src = out.join("main.rs");
    std::fs::write(&src, case.src).expect("write source");
    let exe = out.join("prog");
    // stderr goes to a file, not a pipe: a compiler that wrote more than a pipe
    // holds would block on it and read as a hang.
    let log = out.join("compile.log");
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .args(["--target", TARGET, "-Cpanic=abort", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&exe)
        .arg(&src)
        .stdout(Stdio::null())
        .stderr(std::fs::File::create(&log).expect("create compile log"));
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        command
            .arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let mut child = command.spawn().expect("spawn compiler");
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("wait on compiler") {
            break status;
        }
        if start.elapsed() > COMPILE_BUDGET {
            let _ = child.kill();
            let _ = child.wait();
            return Err(format!(
                "did not finish compiling within {COMPILE_BUDGET:?}"
            ));
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    if !status.success() {
        let stderr = std::fs::read_to_string(&log).unwrap_or_default();
        return Err(format!("compile failed:\n{stderr}"));
    }
    let run = Command::new(&exe).output().expect("run program");
    Ok(run.status.code().unwrap_or(-1))
}

#[test]
fn subslice_reborrow_loops_compile_in_bounded_time_and_match_llvm() {
    darwin_native::require("subslice_loop_compile_bound_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("rcl2_subslice_loop_a64_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let mut cells = 0;
    let mut wrong = Vec::new();
    for case in CASES {
        for opt in 0..=3 {
            let oracle = compile_and_run(&dir, case, None, opt)
                .unwrap_or_else(|why| panic!("{} O{opt}: LLVM {why}", case.name));
            assert_eq!(
                oracle, case.oracle,
                "{} O{opt}: the LLVM oracle is not the case's answer",
                case.name
            );
            cells += 1;
            match compile_and_run(&dir, case, Some(&backend), opt) {
                Ok(code) if code == case.oracle => {}
                Ok(code) => wrong.push(format!(
                    "{} O{opt}: exit {code}, LLVM {}",
                    case.name, case.oracle
                )),
                Err(why) => wrong.push(format!("{} O{opt}: bridge {why}", case.name)),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        wrong.is_empty(),
        "sub-slice reborrow loops:\n{}",
        wrong.join("\n")
    );
    eprintln!(
        "SUBSLICE_LOOP_COMPILE_BOUND cases={} cells={cells} matched={cells} opts=0,1,2,3",
        CASES.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
