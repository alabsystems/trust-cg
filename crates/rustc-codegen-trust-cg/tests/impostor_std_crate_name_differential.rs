#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: an ORDINARY rlib built with `--crate-name core` (or
// `--crate-name alloc`) must NOT have its own function bodies replaced by the
// bridge's std models, and must not have its own ADTs modeled as std's.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS — FOUR EXECUTED MISCOMPILES.
//
// The bridge decided whether a callee (or an ADT) may be INTERCEPTED — its body
// DISCARDED and replaced by the bridge's own iterator/collection model, or its
// storage overwritten with the bridge's own cursor — with
// `std_def_is_interceptable` (LOCALITY, `!did.is_local()`) plus a crate-NAME
// STRING COMPARE, `matches!(tcx.crate_name(did.krate).as_str(), "core" | "alloc"
// | "std")`. A crate name is chosen by whoever runs the compiler, with NO source
// cooperation, so that test is SPELLED provenance, not proved provenance. All
// four rows below were compiled and RUN against the unpatched backend — the
// values quoted here are the RE-MEASURED ones from pristine `origin/main`
// `e985b634b` (2026-09-27), not the first port's base:
//
//   row `iter_next`   — `pub fn next(&mut ::core::slice::Iter<i64>) -> Option<&i64>`
//                        in an rlib named `core`.   LLVM `probe=0` (the library's
//                        own `None`); bridge `probe=7` (the first slice element,
//                        from the bridge's `{ptr, end}` cursor). Reached through
//                        `lower_iterator_call`'s "SEMANTIC-IDENTITY GATE", whose
//                        own comment claimed it stopped exactly this.
//   row `vec_len`     — `pub fn len(&Vec<i64>) -> usize` in an rlib named
//                        `alloc`.   LLVM `probe=1` (the library returns 99, and
//                        99 > 50); bridge `probe=2` (the real vector length 3).
//                        Reached through `is_std_collection_method_callee`.
//   row `hashbrown_len` — `pub fn len(&Vec<i64>) -> usize` in an rlib named
//                        `hashbrown`.   LLVM `probe=1`; bridge `probe=2`. The
//                        same interception as `vec_len` through the FOURTH crate
//                        name the string compare accepted — and the one that
//                        needs `real_hashbrown_crate`'s TRANSITIVE derivation,
//                        since `hashbrown` carries no lang or diagnostic item.
//   row `chars_ctor`  — `pub struct Chars { p: u64, n: u64 }` plus
//                        `pub fn chars(&str) -> Chars` in an rlib named `core`.
//                        LLVM `probe=1` (the library's own `n == 4242`); bridge
//                        `probe=2` (the bridge wrote its `{ptr, end}` byte cursor
//                        over the crate's own struct, so `n` is an address).
//                        Reached through `is_str_chars_ty`, which was
//                        `item_name == "Chars"` + the same crate-name string.
//
// None refused. All four silently answered from a model of storage or a body
// they had thrown away.
//
// NOT A ROW, and measured so nobody adds it back expecting one: an impostor
// `pub fn as_str<'a>(&::core::str::Chars<'a>) -> &'a str` in a crate named
// `hashbrown` is REFUSED on this base by `[TCG-STRIDE-ITER-METHOD]` (`as_str` on
// a `Chars` receiver) on the patched and the unpatched backend alike, because that
// guard keys on the RECEIVER type — a REAL `Chars` — and not on the callee's
// crate. It therefore measures nothing about provenance in either direction.
// `real_str_chars_adt_did` is pinned by the `chars_ctor` row instead, which keys
// on the impostor's OWN `Chars` ADT.
//
// THE FIX AND HOW THIS TEST FAILS WITHOUT IT. The provenance test is now a
// `CrateNum` IDENTITY test (`is_real_std_crate_def`, anchored on the
// `sized`/`owned_box`/`start` LANG ITEMS — `E0152`-unique graph-wide, so no crate
// can claim one), and `is_str_chars_ty` is a DEF-ID identity test
// (`real_str_chars_adt_did`, the ADT the sysroot's own `str::chars` RETURNS, found
// through the graph-unique `str_chars` diagnostic item). Delete the
// `is_real_std_crate_def` conjunct from `lower_iterator_call`'s gate and row
// `iter_next` COMPILES and prints `probe=7` against the oracle's `probe=0`; delete
// it from `is_std_collection_method_callee` and row `vec_len` COMPILES and prints
// `probe=2` against the oracle's `probe=1`; restore `is_str_chars_ty` to the name
// test and row `chars_ctor` prints `probe=2` against the oracle's `probe=1`. Each
// is a HARD FAILURE here.
//
// WHY THE WITNESS LIBRARY MUST BE A SEPARATE CRATE — the load-bearing part.
// A single-file fixture whose `next`/`len`/`Chars` is LOCAL to the compiled crate
// does NOT distinguish the fix from the bug: `std_def_is_interceptable` is
// locality and refuses a local def on its own, so the refuted string-compare guard
// passes a local fixture too. The row that separates them needs a SECOND crate,
// compiled first, with a chosen `--crate-name` — which is why this cannot live in
// `tests/bridge_corpus/`, and why a local-only fixture would let someone
// "simplify" the identity conjunct back to the crate-name string with every test
// still green.
//
// THE GATE (the `fat_pointer_lane_differential.rs` doctrine):
//   * bridge output differs from LLVM        -> HARD FAIL (the miscompile).
//   * bridge FAILS CLOSED with a named
//     `[TCG-...]` diagnostic                 -> INCOMPLETE row, reported.
//   * bridge crashes / refuses with no named
//     diagnostic                             -> HARD FAIL.
//
// The oracle side is asserted FIRST on every row: if LLVM does not return the
// witness library's own answer, this test is measuring something else and says so
// rather than passing vacuously.
//
// HOST-NATIVE: no `--target` is passed, so this runs wherever the crate builds.
// `-Copt-level=0` only — the interception surface this pins is the O0 one.
//
// WHY THE BRIDGE SIDE PASSES `no-proof-certs`. With proof certificates ON (the
// default) this backend currently refuses EVERY program on this target with
// `[TCG-PROOF-465] … no proof mapping for opcode StpPreIndex` — a whole-lane fact
// about the AArch64 opcode inventory, unrelated to provenance. Left on, all three
// rows would report INCOMPLETE on the patched and the unpatched backend alike and
// pin NOTHING. The knob is the same one `trust_ir_cg_census.py` passes by default,
// and it is applied only to the bridge side (the LLVM oracle has no such lane), so
// the compared values are still the two backends' answers to the same program.

use std::path::{Path, PathBuf};
use std::process::Command;

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_impostor_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

struct Run {
    code: i32,
    stdout: String,
}

/// The bridge's own named refusal tag, if this stderr is a fail-closed refusal
/// rather than a crash. An ICE, a panic, or a refusal with no `[TCG-...]` tag is
/// NOT an honest INCOMPLETE and must fail the gate.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

/// One witness: an rlib deliberately NAMED after a standard-library crate, and a
/// main program that calls into it.
struct Witness {
    /// Row name, for the report.
    row: &'static str,
    /// The `--crate-name` the impostor rlib is built with.
    impostor_crate: &'static str,
    /// The impostor library's source. Ordinary code; nothing privileged.
    lib_src: &'static str,
    /// The main program. Must print exactly one `probe=<int>` line.
    main_src: &'static str,
    /// What the LLVM oracle MUST print — the impostor library's own answer.
    /// Asserted before the bridge is consulted at all.
    oracle_stdout: &'static str,
    /// What the UNPATCHED bridge printed instead (documentation for the reader;
    /// this test never asserts it, it asserts equality with the oracle).
    refuted_stdout: &'static str,
}

fn witnesses() -> Vec<Witness> {
    vec![
        Witness {
            row: "iter_next",
            impostor_crate: "core",
            // `::core::slice::Iter` inside a crate NAMED `core` still names the
            // REAL sysroot type: the impostor is compiled against its own
            // sysroot like any other crate.
            lib_src: "#[inline(never)]\n\
                      pub fn next<'a>(_it: &mut ::core::slice::Iter<'a, i64>) -> Option<&'a i64> {\n\
                      \x20   None\n\
                      }\n",
            main_src: "fn main() {\n\
                       \x20   let arr: [i64; 3] = [7, 8, 9];\n\
                       \x20   let mut it = arr.iter();\n\
                       \x20   let v = core::next(&mut it);\n\
                       \x20   let probe: i64 = match v { Some(x) => *x, None => 0 };\n\
                       \x20   println!(\"probe={}\", probe);\n\
                       }\n",
            oracle_stdout: "probe=0\n",
            refuted_stdout: "probe=7\n",
        },
        Witness {
            row: "vec_len",
            impostor_crate: "alloc",
            lib_src: "#[inline(never)]\n\
                      pub fn len(_v: &Vec<i64>) -> usize {\n\
                      \x20   99\n\
                      }\n",
            // The `.len()` result is consumed through a BRANCH rather than
            // printed: a `format!` placeholder fed directly by a length was
            // refused for an unrelated reason (`[TCG-FMT-LEN]`, removed
            // 2026-10-03), which made this row INCOMPLETE on both sides.
            main_src: "extern crate alloc as impostor;\n\
                       fn main() {\n\
                       \x20   let v: Vec<i64> = vec![4, 5, 6];\n\
                       \x20   let n = impostor::len(&v);\n\
                       \x20   let probe: i64 = if n > 50 { 1 } else { 2 };\n\
                       \x20   println!(\"probe={}\", probe);\n\
                       }\n",
            oracle_stdout: "probe=1\n",
            refuted_stdout: "probe=2\n",
        },
        Witness {
            // The FOURTH crate name the refuted string compare accepted, and the
            // one that cannot be anchored on a lang item because `hashbrown` is a
            // THIRD-PARTY crate carrying neither a lang nor a diagnostic item.
            // `real_hashbrown_crate` derives it TRANSITIVELY instead — the ADT of
            // the real `std::collections::HashMap`'s field 0, reached through the
            // graph-unique `HashMap` diagnostic item — so an ordinary rlib merely
            // NAMED `hashbrown` is a different `CrateNum` and is not intercepted.
            // Measured on pristine `e985b634b` (2026-09-27): LLVM `probe=1` (the
            // library's own 99), bridge `probe=2` (the real vector length 3),
            // through `is_std_collection_method_callee`'s `"hashbrown"` arm.
            row: "hashbrown_len",
            impostor_crate: "hashbrown",
            lib_src: "#[inline(never)]\n\
                      pub fn len(_v: &Vec<i64>) -> usize {\n\
                      \x20   99\n\
                      }\n",
            main_src: "extern crate hashbrown as impostor;\n\
                       fn main() {\n\
                       \x20   let v: Vec<i64> = vec![4, 5, 6];\n\
                       \x20   let n = impostor::len(&v);\n\
                       \x20   let probe: i64 = if n > 50 { 1 } else { 2 };\n\
                       \x20   println!(\"probe={}\", probe);\n\
                       }\n",
            oracle_stdout: "probe=1\n",
            refuted_stdout: "probe=2\n",
        },
        Witness {
            row: "chars_ctor",
            impostor_crate: "core",
            // An ordinary struct that happens to be NAMED `Chars`, with an
            // ordinary free function that happens to be NAMED `chars` taking a
            // `&str`. `lower_str_chars_ctor` keys on exactly that name pair plus
            // `is_str_chars_ty(destination)`, so under the name test the bridge
            // writes its own `{ ptr@0, end@8 }` byte cursor over this crate's
            // 16-byte struct and `n` reads back an address.
            lib_src: "#[repr(C)]\n\
                      pub struct Chars {\n\
                      \x20   pub p: u64,\n\
                      \x20   pub n: u64,\n\
                      }\n\
                      \n\
                      #[inline(never)]\n\
                      pub fn chars(s: &str) -> Chars {\n\
                      \x20   Chars { p: s.len() as u64, n: 4242 }\n\
                      }\n",
            main_src: "fn main() {\n\
                       \x20   let c = core::chars(\"abcdef\");\n\
                       \x20   let probe: i64 = if c.n == 4242 { 1 } else { 2 };\n\
                       \x20   println!(\"probe={}\", probe);\n\
                       }\n",
            oracle_stdout: "probe=1\n",
            refuted_stdout: "probe=2\n",
        },
    ]
}

#[test]
fn an_rlib_merely_named_core_or_alloc_keeps_its_own_bodies() {
    if toolchain_support::skip_without_backend_knobs(
        "an_rlib_merely_named_core_or_alloc_keeps_its_own_bodies",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut incomplete: Vec<String> = Vec::new();
    let mut matched = 0usize;

    for w in witnesses() {
        let dir = workdir(w.row);

        // The impostor library: an ORDINARY crate, named `core`/`alloc` on the
        // command line and nothing more.
        let lib_src = dir.join("impostor.rs");
        std::fs::write(&lib_src, w.lib_src).expect("write impostor library");
        let rlib = dir.join(format!("lib{}.rlib", w.impostor_crate));
        let mut lib_cmd = toolchain_support::rustc_command();
        lib_cmd.args(["--crate-type", "rlib", "--crate-name", w.impostor_crate]);
        lib_cmd.args(["-Cpanic=abort", "-Copt-level=0"]);
        lib_cmd.arg("-o").arg(&rlib).arg(&lib_src);
        let lib_out = lib_cmd.output().expect("spawn the compiler");
        assert!(
            lib_out.status.success(),
            "row {}: the `--crate-name {}` impostor library did not build: <<<{}>>>",
            w.row,
            w.impostor_crate,
            String::from_utf8_lossy(&lib_out.stderr)
        );

        let main_src = dir.join("impostor_main.rs");
        std::fs::write(&main_src, w.main_src).expect("write witness main");

        let compile_main = |backend: Option<&Path>, out: &Path| -> Result<Run, String> {
            let mut cmd = toolchain_support::rustc_command();
            cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
            cmd.args(["-Copt-level=0", "-Clink-arg=-lSystem"]);
            let mut extern_arg = std::ffi::OsString::from(format!("{}=", w.impostor_crate));
            extern_arg.push(&rlib);
            cmd.arg("--extern").arg(extern_arg);
            cmd.arg("-L").arg(&dir);
            if let Some(dylib) = backend {
                let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
                backend_arg.push(dylib);
                cmd.arg(backend_arg);
                cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
            }
            cmd.arg("-o").arg(out).arg(&main_src);
            let output = cmd.output().expect("spawn the compiler");
            if !output.status.success() {
                return Err(String::from_utf8_lossy(&output.stderr).into_owned());
            }
            let run = Command::new(out).output().expect("run compiled binary");
            Ok(Run {
                code: run
                    .status
                    .code()
                    .expect("compiled program exited via signal, not an exit code"),
                stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
            })
        };

        // The oracle FIRST: if LLVM does not return the impostor library's own
        // answer, this row is measuring something else.
        let oracle = compile_main(None, &dir.join("llvm_oracle")).unwrap_or_else(|e| {
            panic!("row {}: the LLVM oracle failed to build: <<<{e}>>>", w.row)
        });
        assert_eq!(
            oracle.stdout, w.oracle_stdout,
            "row {}: the LLVM oracle did not return the impostor library's own body \
             (expected {:?}); this row is measuring something else.",
            w.row, w.oracle_stdout
        );

        match compile_main(Some(&dylib), &dir.join("bridge")) {
            Ok(bridge) => {
                assert_eq!(
                    bridge.stdout, oracle.stdout,
                    "row {}: a crate merely NAMED `{}` had its own body or storage REPLACED \
                     by the bridge's std model. This is the refuted crate-NAME provenance \
                     test, not a new bug: the unpatched backend printed {:?} here. Restore \
                     the `is_real_std_crate_def` / `real_str_chars_adt_did` identity \
                     conjunct (see `real_core_crate`) rather than relaxing this assertion.",
                    w.row, w.impostor_crate, w.refuted_stdout
                );
                assert_eq!(
                    bridge.code, oracle.code,
                    "row {}: exit code differs from LLVM",
                    w.row
                );
                matched += 1;
                eprintln!(
                    "row {}: COMPILED and MATCHED LLVM ({:?})",
                    w.row, oracle.stdout
                );
            }
            Err(stderr) => {
                let tag = named_refusal(&stderr).unwrap_or_else(|| {
                    panic!(
                        "row {}: refused WITHOUT a named [TCG-...] diagnostic, which is a \
                         crash rather than a fail-closed outcome: <<<{stderr}>>>",
                        w.row
                    )
                });
                incomplete.push(format!("{} {}", w.row, tag));
                eprintln!("row {}: INCOMPLETE {tag} (fail-closed, correct)", w.row);
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    eprintln!(
        "impostor-crate-name rows: {matched} matched LLVM, {} incomplete {:?}",
        incomplete.len(),
        incomplete
    );
}
