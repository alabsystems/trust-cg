#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a scalarized aggregate's leaves are read under the keys its
// binder gave them when zero-sized fields come before sized ones.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. A scalarized aggregate with a nested aggregate field
// keys its leaves by flat, zero-sized-skipping position at every level; any
// other aggregate keys each field by its MIR field index, which counts
// zero-sized fields. The nested-field memory store indexed its source by leaf
// position and so refused (`[TCG-ZST-LANE-INDEX]`) every source with a
// zero-sized field before a sized leaf — among them `RawVec`
// (`Unique { pointer, _marker }` before `cap`), which `Vec::new` stores. A
// whole copy out of memory bound leaf positions where every reader uses MIR
// field indices, so `t.a` of a copied `{ z: PhantomData, a, b }` returned `b`
// at -O0. `scalarized_leaf_binding_keys` now states each leaf's key and every
// one of those readers and writers uses it.
//
// THE GATE. `fix_zst_leaf_keys` (the native sibling of the wasm32 corpus crate
// `r7-bridge-zst-leaf-keys.rs`) is compiled by the bridge (`no-proof-certs`) and
// by LLVM with the same flags, run, and compared on STDOUT, EXIT CODE and
// KILLING SIGNAL. Every row must compile and match.
//
// FALSIFIED (2026-10-01, aarch64-apple-darwin): with the key of every leaf
// taken as its position, the crate is refused at -O0..-O2 (`Place projection
// field N before aggregate binding`), and `mem_copy`/`deref_copy` alone compile
// at -O0 and print `b` for `t.a`; before the change the store rows were refused
// `[TCG-ZST-LANE-INDEX]`. With field types left unnormalized when the key
// scheme is chosen, the `al_*` rows (fields declared as `<u8 as Tr>::O`, `T::O`)
// are refused `[TCG-ZST-LANE-INDEX] ... does not normalize` at -O0 and -O2;
// before the normalization the `al_read` shape returned `o` for `s.a` at -O0.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

const FIXTURE: &str = include_str!("bridge_corpus/fix_zst_leaf_keys.rs");
/// The fixture prints 34 rows for each of its 12 grid inputs.
const ROWS: usize = 12 * 34;

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_zst_leaf_keys_{stem}_{}", std::process::id()));
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

/// The bridge's own named refusal tag, if this stderr is a fail-closed refusal
/// rather than a crash.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

#[test]
fn zst_leaf_keys_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("zst_leaf_keys_match_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures: Vec<String> = Vec::new();
    for opt in [
        "-Copt-level=0",
        "-Copt-level=1",
        "-Copt-level=2",
        "-Copt-level=3",
    ] {
        let flags = [opt];
        let dir = workdir(&opt.replace(['-', '='], "_"));
        let oracle = compile_and_run(&dir, "fix_zst_leaf_keys", FIXTURE, &flags, None)
            .unwrap_or_else(|e| panic!("{opt}: the LLVM oracle failed to compile: <<<{e}>>>"));
        assert_eq!(
            (oracle.code, oracle.signal),
            (Some(0), None),
            "{opt}: the LLVM oracle did not exit cleanly: {oracle:?}"
        );
        assert!(
            oracle.stdout.lines().count() == ROWS,
            "{opt}: the oracle did not print every row: {oracle:?}"
        );
        match compile_and_run(&dir, "fix_zst_leaf_keys", FIXTURE, &flags, Some(&dylib)) {
            Ok(bridge) if bridge == oracle => eprintln!("{opt}: MATCH"),
            Ok(bridge) => failures.push(format!(
                "{opt}: compiled and DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}"
            )),
            Err(stderr) => failures.push(format!(
                "{opt}: refused ({:?}) a row that must compile: <<<{stderr}>>>",
                named_refusal(&stderr)
            )),
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(
        failures.is_empty(),
        "{} zst leaf-key row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
