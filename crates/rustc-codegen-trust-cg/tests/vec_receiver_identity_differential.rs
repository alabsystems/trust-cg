#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration tests: preserve the actual method owner, receiver and complete
// Vec/String header through same-backend and mixed LLVM/bridge calls.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. `lower_vec_call` identified a `Vec` method by its
// DESTINATION before its self (`dest_element.or(self_element)`), a rule meant for
// the Vec-PRODUCING intercepts (`new`, `collect`, `from_elem`, ...). But
// `Vec<Vec<i64>>::remove` / `swap_remove` RETURN a `Vec<i64>`, so they were
// lowered as `Vec<i64>::remove` / `swap_remove`: an 8-byte element stride, the
// `__trustcg_vec_remove_shift_i64` helper and an `i64` loaded as the returned
// header, over a buffer of 24-byte `{cap, ptr, len}` images. Measured: the
// bridge exited 1 where LLVM exits 21 (a SILENT wrong value), and SIGSEGV where
// LLVM exits 12, at -O0..-O3. `lower_btreemap_call` / `lower_hashmap_call` had
// the same receiver test (`Vec<BTreeMap<K, V>>::remove` returns a map).
//
// THE GATE. Each row is compiled by the bridge (`no-proof-certs`, isolating MIR
// lowering from this host's opcode-proof inventory) and by LLVM with the same
// flags, run, and compared on STDOUT, EXIT CODE and KILLING SIGNAL.
//   * `Match`: compilation and an exact native match are required.
//   * `RefuseOrMatch(needles)`: the bridge must MATCH, or REFUSE with every
//     needle in its diagnostics -- a refusal for the named reason (std's real
//     `remove` / `swap_remove` body, or `[TCG-MAP-RECEIVER]`), never one a dead
//     backend or an unrelated refusal would satisfy. It must never compile and
//     diverge.
//
// FALSIFIED (2026-10-01, aarch64-apple-darwin): with the receiver fix's
// non-test source reverted, the remove and swap_remove rows COMPILE and DIVERGE
// at every level (exit 1 vs 21; SIGSEGV vs 12), and the map row refuses without
// naming `[TCG-MAP-RECEIVER]` (the misrouted map `remove` failed deeper, on an
// unrelated "iterator next destination" refusal).

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy)]
enum Expect {
    Match,
    RefuseOrMatch(&'static [&'static str]),
}

struct Row {
    fixture: &'static str,
    src: &'static str,
    flags: &'static [&'static str],
    /// The LLVM oracle's exit status and stdout line count: a fixture whose
    /// oracle does not reach its end is not exercising the stored headers.
    oracle_code: i32,
    oracle_lines: usize,
    expect: Expect,
}

macro_rules! fixture {
    ($name:literal) => {
        ($name, include_str!(concat!("bridge_corpus/", $name, ".rs")))
    };
}

const O0: &[&str] = &["-Copt-level=0"];
const O1: &[&str] = &["-Copt-level=1"];
const O2: &[&str] = &["-Copt-level=2"];
const O3: &[&str] = &["-Copt-level=3"];
const LEVELS: [&[&str]; 4] = [O0, O1, O2, O3];

fn rows() -> Vec<Row> {
    let mut rows = Vec::new();
    let mut add = |(fixture, src): (&'static str, &'static str),
                   flags: &'static [&'static str],
                   oracle_code: i32,
                   oracle_lines: usize,
                   expect: Expect| {
        rows.push(Row {
            fixture,
            src,
            flags,
            oracle_code,
            oracle_lines,
            expect,
        })
    };
    for flags in LEVELS {
        // Associated functions owned by String and NonNull merely take Vec
        // arguments. Require their actual bodies and complete header transport.
        add(
            fixture!("fix_string_from_vec_header"),
            flags,
            0,
            0,
            Expect::Match,
        );
        add(
            fixture!("fix_vec_argument_other_owner"),
            flags,
            0,
            0,
            Expect::Match,
        );
        // std's own `Vec::<Vec<i64>>::remove` / `swap_remove` body is the function
        // the bridge refuses (or it matches) -- never an intercepted `Vec<i64>` one.
        add(
            fixture!("fix_vec_receiver_remove"),
            flags,
            21,
            0,
            Expect::RefuseOrMatch(&["[TCG-MIR-UNSUPPORTED]", "6remove"]),
        );
        add(
            fixture!("fix_vec_receiver_swap_remove"),
            flags,
            12,
            0,
            Expect::RefuseOrMatch(&["[TCG-MIR-UNSUPPORTED]", "11swap_remove"]),
        );
        add(
            fixture!("fix_map_receiver_remove"),
            flags,
            0,
            1,
            Expect::RefuseOrMatch(&["[TCG-MAP-RECEIVER]"]),
        );
    }
    rows
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tcg_vec_receiver_identity_{stem}_{}",
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
    link_object: Option<&Path>,
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
    if let Some(object) = link_object {
        let mut arg = std::ffi::OsString::from("-Clink-arg=");
        arg.push(object);
        cmd.arg(arg);
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
fn a_vec_of_collections_receiver_is_never_the_collection_it_returns() {
    if toolchain_support::skip_without_backend_knobs(
        "a_vec_of_collections_receiver_is_never_the_collection_it_returns",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures: Vec<String> = Vec::new();
    let (mut matched, mut refused) = (0usize, 0usize);
    for (index, row) in rows().iter().enumerate() {
        let dir = workdir(&format!("{}_{index}", row.fixture));
        let oracle = compile_and_run(&dir, row.fixture, row.src, row.flags, None, None)
            .unwrap_or_else(|e| {
                panic!(
                    "{} {:?}: the LLVM oracle failed to compile: <<<{e}>>>",
                    row.fixture, row.flags
                )
            });
        assert_eq!(
            (oracle.code, oracle.signal, oracle.stdout.lines().count()),
            (Some(row.oracle_code), None, row.oracle_lines),
            "{} {:?}: the LLVM oracle did not reach the fixture's end: {oracle:?}",
            row.fixture,
            row.flags
        );
        match (
            compile_and_run(&dir, row.fixture, row.src, row.flags, Some(&dylib), None),
            row.expect,
        ) {
            (Ok(bridge), _) if bridge == oracle => {
                matched += 1;
                eprintln!("{} {:?}: MATCH", row.fixture, row.flags);
            }
            (Ok(bridge), _) => failures.push(format!(
                "{} {:?}: compiled and DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}",
                row.fixture, row.flags
            )),
            (Err(stderr), Expect::Match) => failures.push(format!(
                "{} {:?}: required native match refused: <<<{stderr}>>>",
                row.fixture, row.flags
            )),
            (Err(stderr), Expect::RefuseOrMatch(needles)) => {
                let missing: Vec<&str> = needles
                    .iter()
                    .copied()
                    .filter(|n| !stderr.contains(n))
                    .collect();
                if missing.is_empty() {
                    refused += 1;
                    eprintln!(
                        "{} {:?}: REFUSED by name {needles:?}",
                        row.fixture, row.flags
                    );
                } else {
                    failures.push(format!(
                        "{} {:?}: refused, but not for the named reason (missing {missing:?}): \
                         <<<{stderr}>>>",
                        row.fixture, row.flags
                    ));
                }
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    eprintln!("receiver-identity rows: {matched} MATCH, {refused} REFUSED by name");
    assert!(
        failures.is_empty(),
        "{} receiver-identity row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

// Crossing a real ABI with an independently generated caller/callee checks the
// complete header image, rather than letting two copies of one model agree.
// The consumer's allocator watches the original buffer and requires one free
// after each String drop, including empty Strings that retain capacity.
#[test]
fn vec_to_string_header_crosses_llvm_and_bridge_with_one_buffer_drop() {
    if toolchain_support::skip_without_backend_knobs(
        "vec_to_string_header_crosses_llvm_and_bridge_with_one_buffer_drop",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    const PROVIDER: &str = include_str!("support/collection_header_conversion/provider.rs");
    const CONSUMER: &str = include_str!("support/collection_header_conversion/consumer.rs");
    let mut cases = 0;
    for (opt, flags) in LEVELS.iter().enumerate() {
        let dir = workdir(&format!("mixed_header_O{opt}"));
        let source = dir.join("provider.rs");
        std::fs::write(&source, PROVIDER).expect("write provider");
        for (provider_lane, provider_backend) in [("llvm", None), ("bridge", Some(dylib.as_path()))]
        {
            let object = dir.join(format!("provider_{provider_lane}.o"));
            let mut cmd = toolchain_support::rustc_command();
            cmd.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "-Ccodegen-units=1",
            ]);
            cmd.args(*flags);
            if let Some(backend) = provider_backend {
                let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
                arg.push(backend);
                cmd.arg(arg);
                cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
            }
            let output = cmd
                .arg(&source)
                .arg("-o")
                .arg(&object)
                .output()
                .expect("compile provider");
            assert!(
                output.status.success(),
                "{provider_lane} provider O{opt}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            // The bridge emits the compiler's CGU object name rather than the
            // nominal -o path. Select the actual product in this private dir.
            let object = if object.is_file() {
                object
            } else {
                let prefix = format!("provider_{provider_lane}.");
                let objects: Vec<PathBuf> = std::fs::read_dir(&dir)
                    .expect("read provider products")
                    .map(|entry| entry.expect("provider directory entry").path())
                    .filter(|path| {
                        path.extension().is_some_and(|ext| ext == "o")
                            && path
                                .file_name()
                                .is_some_and(|name| name.to_string_lossy().starts_with(&prefix))
                    })
                    .collect();
                assert_eq!(
                    objects.len(),
                    1,
                    "{provider_lane} provider O{opt} actual products: {objects:?}"
                );
                objects[0].clone()
            };
            for (consumer_lane, consumer_backend) in
                [("llvm", None), ("bridge", Some(dylib.as_path()))]
            {
                let result = compile_and_run(
                    &dir,
                    &format!("consumer_{provider_lane}_{consumer_lane}"),
                    CONSUMER,
                    flags,
                    consumer_backend,
                    Some(&object),
                )
                .unwrap_or_else(|error| {
                    panic!("{provider_lane} provider/{consumer_lane} consumer O{opt}: {error}")
                });
                assert_eq!(
                    result,
                    Ending {
                        code: Some(0),
                        signal: None,
                        stdout: String::new()
                    },
                    "{provider_lane} provider/{consumer_lane} consumer O{opt}"
                );
                cases += 1;
                eprintln!(
                    "mixed header O{opt}: {provider_lane} provider/{consumer_lane} consumer MATCH (5 owned buffers)"
                );
            }
        }
        std::fs::remove_dir_all(&dir).expect("remove mixed header workdir");
    }
    assert_eq!(cases, 16);
}
