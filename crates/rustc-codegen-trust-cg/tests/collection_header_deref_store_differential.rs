#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a `Vec<T>` / `String` stored WHOLE through a pointer must
// write all 24 bytes of rustc's `{cap, ptr, len}` header.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. A default-`Global` `Vec`/`String` LOCAL is bound to the
// address of its own 24-byte slot (which holds rustc's image), so its trust-ir
// type is a one-word `Ptr` carrier. `memory_deref_store_target` took that
// carrier for the POINTEE's memory type, and its pointer-like scalar gate (the
// widening that admits `*p = q` for a real pointer) let it through: `(*p) =
// move v` became ONE 8-byte store. That is the `ptr::write(end, value)` inside
// every `Vec<Vec<T>>::push`/`insert` and `Vec<String>::push`, and a user `*r = v`
// through `&mut Vec<T>`. The outer buffer's element became `{cap, <stale>,
// <stale>}` — measured as `{4, 0, 0}` for a pushed `{cap 4, ptr, len 1}` row —
// so `g[1].len()` read 0 and `g[1][0]` panicked "index out of bounds: the len
// is 0 but the index is 0" where LLVM exits 21. The read-side twin
// (`memory_deref_load_ty`) already refused a pointer-like carrier whose pointee
// is not an 8-byte thin pointer; the store side had no such check.
//
// THE GATE. Each row is compiled by the bridge (`no-proof-certs`, isolating MIR
// lowering from this host's opcode-proof inventory) and by LLVM with the same
// flags, run, and compared on STDOUT, EXIT CODE and KILLING SIGNAL. Every row is
// `Must`: the bridge must COMPILE and MATCH.
//
// FALSIFIED (2026-10-01, aarch64-apple-darwin, base ed7b6afab): the fixture
// panics in its first section at -O0, -O1, -O2 and -O3. Measured separately on
// that base, each shape the fixture carries diverged on its own at -O0 and -O2:
// `Vec<Vec<i64>>` push (`while`, `for`, no loop), a pushed call result,
// `Vec<Vec<u8>>`, `Vec<Vec<Vec<u8>>>`, `Vec<Vec<i64>>::insert`, `Vec<String>`
// push (`String::new` + `push`, and `String::from`), `*r = v` and
// `*r = Vec::new()` through `&mut Vec<i64>` (the last a SILENT wrong value,
// 20 for 14). The tuple / array / reordered-struct sections are controls that
// matched before and after.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

struct Row {
    fixture: &'static str,
    src: &'static str,
    flags: &'static [&'static str],
}

macro_rules! fixture {
    ($name:literal) => {
        ($name, include_str!(concat!("bridge_corpus/", $name, ".rs")))
    };
}

fn rows() -> Vec<Row> {
    const O0: &[&str] = &["-Copt-level=0"];
    const O1: &[&str] = &["-Copt-level=1"];
    const O2: &[&str] = &["-Copt-level=2"];
    const O3: &[&str] = &["-Copt-level=3"];
    let (fixture, src) = fixture!("fix_collection_header_deref_store");
    [O0, O1, O2, O3]
        .into_iter()
        .map(|flags| Row {
            fixture,
            src,
            flags,
        })
        .collect()
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tcg_collection_header_store_{stem}_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn compile_and_run(
    dir: &Path,
    name: &str,
    src: &str,
    flags: &[&str],
    backend: Option<&Path>,
) -> Result<Ending, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(if backend.is_some() {
        format!("{name}_bridge")
    } else {
        format!("{name}_llvm")
    });
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.args(flags);
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&bin).arg(&src_path);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&bin).output().expect("run compiled binary");
    Ok(Ending {
        code: run.status.code(),
        signal: run.status.signal(),
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
    })
}

#[test]
fn whole_collection_header_store_through_a_pointer_moves_all_three_words() {
    if toolchain_support::skip_without_backend_knobs(
        "whole_collection_header_store_through_a_pointer_moves_all_three_words",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures: Vec<String> = Vec::new();
    for (index, row) in rows().iter().enumerate() {
        let dir = workdir(&format!("{}_{index}", row.fixture));
        let oracle =
            compile_and_run(&dir, row.fixture, row.src, row.flags, None).unwrap_or_else(|e| {
                panic!(
                    "{} {:?}: the LLVM oracle failed to compile: <<<{e}>>>",
                    row.fixture, row.flags
                )
            });
        // The oracle must have run every section to completion: a fixture whose
        // LLVM build does not exit 0 is not exercising the stored headers.
        assert_eq!(
            (oracle.code, oracle.signal),
            (Some(0), None),
            "{} {:?}: the LLVM oracle did not exit cleanly: {oracle:?}",
            row.fixture,
            row.flags
        );
        assert_eq!(
            oracle.stdout.lines().count(),
            14,
            "{} {:?}: the LLVM oracle did not print all 14 sections: {oracle:?}",
            row.fixture,
            row.flags
        );
        match compile_and_run(&dir, row.fixture, row.src, row.flags, Some(&dylib)) {
            Ok(bridge) if bridge == oracle => {
                eprintln!("{} {:?}: MATCH", row.fixture, row.flags);
            }
            Ok(bridge) => failures.push(format!(
                "{} {:?}: compiled and DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}",
                row.fixture, row.flags
            )),
            Err(stderr) => failures.push(format!(
                "{} {:?}: the bridge refused a row that must compile: <<<{stderr}>>>",
                row.fixture, row.flags
            )),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(
        failures.is_empty(),
        "{} collection-header store row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
