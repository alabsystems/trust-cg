//! Over-aligned C composites cross the LLVM / bridge boundary at the AAPCS64
//! placements their NATURAL alignment decides (the `repr(align)` attribute does
//! not count; rustc's Linux FnAbi reads `unadjusted_abi_align`): a
//! `#[repr(C, align(16))]` composite of 8-byte-aligned members starts at x1
//! after one integer, x3, x5, goes whole to the stack with one register left,
//! and takes an 8-aligned stack slot after one 8-byte slot. Memory-slot
//! composites (`aapcs64_unadjusted_block_plan`) and over-aligned single-scalar
//! newtypes (`Aapcs64ScalarBlock`) are declared as rustc's `[2 x i64]`; an
//! over-aligned value rustc casts to `i128` or to a narrow integer that the
//! bridge still declares as its one scalar is refused by name, and so is a
//! padded newtype passed as a FIXED argument of a C-variadic function, where
//! the two-unit declaration is not taken: in a direct call (by the whole-call
//! check of the variadic call lane) and through a C-variadic `fn` pointer with
//! no anonymous argument (by the check of the pointer's signature). A direct
//! call that passes no anonymous argument, which only the whole-call check
//! judges, must be refused or print what the LLVM-built caller prints.
//!
//! Every call runs in all four rlib x bin pairings (LLVM and the bridge on each
//! side) at O0-O3, through C declarations (the FFI shape), a C fn pointer and a
//! C callback, and must print the value computed here. Diagnostic codegen with
//! proof certificates off; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

const CALLEE: &str = include_str!("overaligned_c_arguments/callee.rs");
const CALLER: &str = include_str!("overaligned_c_arguments/caller.rs");
const REFUSED: &str = include_str!("overaligned_c_arguments/refused.rs");
const VARIADIC_CALLEE: &str = include_str!("overaligned_c_arguments/variadic_callee.rs");
const VARIADIC_CALLER: &str = include_str!("overaligned_c_arguments/variadic_caller.rs");

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-overaligned-c.XXXXXX"])
        .output()
        .expect("mktemp over-aligned C artifacts");
    assert!(temp.status.success());
    Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ))
}

fn fold(seed: u64, words: &[u64]) -> u64 {
    words
        .iter()
        .fold(seed, |acc, &word| acc.wrapping_mul(31).wrapping_add(word))
}

/// The binary's output, computed from the fixture's literals without a
/// compiler of the fixture.
fn expected() -> String {
    let range = |n: u64| (1..=n).collect::<Vec<u64>>();
    let mut s8 = range(9);
    s8.extend([10, 11, 12]);
    let callback_seed = 41u64;
    let callback = fold(
        31,
        &[
            callback_seed,
            callback_seed.wrapping_mul(3),
            callback_seed ^ 0x55,
            callback_seed.wrapping_add(9),
        ],
    );
    let lines = [
        ("oa_x1", fold(1, &[1, 2, 3, 4])),
        ("oa_x3", fold(3, &range(6))),
        ("oa_x5", fold(5, &range(8))),
        ("oa_x7", fold(7, &range(10))),
        ("oa_s8", fold(8, &s8)),
        ("oa_u32_x1", fold(11, &[1, 0x2222, 3])),
        ("oa_u8_x5", fold(37, &[1, 2, 3, 4, 5, 0x66, 7])),
        (
            "oa_u64_s8",
            fold(41, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 0x1010, 11]),
        ),
        ("oa_u32x3_x1", fold(13, &[1, 0x3101, 0x3202, 0x3303, 5])),
        (
            "oa_u32x3_s8",
            fold(17, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 0x3101, 0x3202, 0x3303, 13]),
        ),
        ("oa_in16_x1", fold(19, &[1, 0x4444, 5, 6, 7])),
        ("oa_give", 12u64.wrapping_mul(1_000_003).wrapping_add(12)),
        ("oa_pointer", fold(1, &[21, 22, 23, 24])),
        ("oa_callback", fold(29, &[callback])),
    ];
    lines
        .iter()
        .map(|(name, value)| format!("{name}={value:016x}\n"))
        .collect()
}

fn compile(
    source: &Path,
    out: &Path,
    lane: &str,
    opt: u32,
    crate_type: &str,
    library: Option<&Path>,
    backend: &Path,
) -> Command {
    let mut command = rustc_command();
    command.args(["-Cpanic=abort", "-Ccodegen-units=1", "--target", TARGET]);
    command.arg(format!("--crate-type={crate_type}"));
    command.arg(format!("-Copt-level={opt}"));
    if lane == "cg" {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg("-Ztrust-ir-cg-args=no-proof-certs");
    }
    if let Some(library) = library {
        command.arg("-L").arg(library);
    }
    if crate_type == "rlib" {
        command.arg("--out-dir").arg(out);
    } else {
        command.arg("-o").arg(out);
    }
    command.arg(source);
    command
}

#[test]
fn no_proof_overaligned_c_arguments_match_llvm() {
    let artifacts = artifacts();
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let callee = root.join("callee.rs");
    let caller = root.join("caller.rs");
    let refused = root.join("refused.rs");
    std::fs::write(&callee, CALLEE).unwrap();
    std::fs::write(&caller, CALLER).unwrap();
    std::fs::write(&refused, REFUSED).unwrap();
    let want = expected();
    let mut executions = 0;
    let mut refusals = 0;
    for opt in 0..=3u32 {
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("lib-{lane}-O{opt}"));
            std::fs::create_dir(&dir).unwrap();
            checked(
                &mut compile(&callee, &dir, lane, opt, "rlib", None, &backend),
                180,
                &dir.join("compile.log"),
            );
        }
        for caller_lane in ["llvm", "cg"] {
            for callee_lane in ["llvm", "cg"] {
                let stem = format!("bin-{caller_lane}-{callee_lane}-O{opt}");
                let library = root.join(format!("lib-{callee_lane}-O{opt}"));
                let binary = root.join(&stem);
                checked(
                    &mut compile(
                        &caller,
                        &binary,
                        caller_lane,
                        opt,
                        "bin",
                        Some(&library),
                        &backend,
                    ),
                    180,
                    &root.join(format!("{stem}.compile.log")),
                );
                let output = checked(
                    &mut Command::new(&binary),
                    20,
                    &root.join(format!("{stem}.run.log")),
                );
                assert_eq!(
                    String::from_utf8_lossy(&output.stdout),
                    want,
                    "{stem}: an over-aligned C argument was read from another place"
                );
                executions += 1;
            }
        }
        // Still declared as their one scalar: refused by name, never passed in
        // the scalar's register. The LLVM control compiles the same source.
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("refused-{lane}-O{opt}"));
            std::fs::create_dir(&dir).unwrap();
            let log = dir.join("compile.log");
            let (output, transcript) = run_bounded(
                &mut compile(&refused, &dir, lane, opt, "rlib", None, &backend),
                180,
                &log,
            );
            if lane == "llvm" {
                assert!(
                    output.status.success(),
                    "valid-Rust control failed: {transcript}"
                );
                continue;
            }
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(
                output.status.code(),
                Some(1),
                "expected a refusal: {transcript}"
            );
            for needle in [
                "[TCG-MIR-UNSUPPORTED]",
                "[TCG-ARG-ABI]",
                "whole-signature placement check",
                "oa_wrap16_x1",
                "oa2_x1",
                "oa_va_fixed_x1",
                "the C-variadic call of `xoa_va_pad_u64`: argument 1",
                "oa_va_pointer_x1",
                "the `fn` pointer signature `unsafe extern \"C\" fn(u64, Oa16U64, u64, ...) -> u64`: \
                 argument 1",
            ] {
                assert!(
                    stderr.contains(needle),
                    "refusal lacks {needle}: {transcript}"
                );
            }
            refusals += 1;
        }
        assert_eq!(sha256(&backend), digest, "backend changed during O{opt}");
    }
    assert_eq!((executions, refusals), (16, 4));
    println!(
        "TCG_OVERALIGNED_C_ARGUMENTS executions={executions} lines_per_execution={} \
         refusals={refusals} certificates=off backend_sha256={digest}",
        want.lines().count()
    );
}

/// LD-29's residual (landing verifier, round 3): a DIRECT C-variadic call that
/// passes NO anonymous argument, with an over-aligned fixed argument
/// (`variadic_caller.rs`). Its only placement judgment is the variadic call
/// lane's whole-call check (`variadic::call`). A one-statement mutant that runs
/// that check only for a call with an anonymous argument (M5, recorded with
/// LD-29) left every other committed check green while the call put `p2` in
/// x2, where the callee reads x3. So the trust-cg caller must either be refused
/// by name, by that check, or print exactly what the LLVM-built caller prints;
/// a build that compiles and prints anything else fails. The C-variadic
/// definition is LLVM-built (trust-cg refuses variadic definitions), and both
/// callers link the same one at each level.
#[test]
fn no_proof_overaligned_variadic_fixed_argument_without_anonymous_refuses_or_matches_llvm() {
    let artifacts = artifacts();
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let callee = root.join("variadic_callee.rs");
    let caller = root.join("variadic_caller.rs");
    std::fs::write(&callee, VARIADIC_CALLEE).unwrap();
    std::fs::write(&caller, VARIADIC_CALLER).unwrap();
    let want = format!("oa_va_none_x1={:016x}\n", fold(0x1111, &[0x2222, 0x3333]));
    let (mut matches, mut refusals) = (0, 0);
    for opt in 0..=3u32 {
        let library = root.join(format!("variadic-lib-O{opt}"));
        std::fs::create_dir(&library).unwrap();
        checked(
            &mut compile(&callee, &library, "llvm", opt, "rlib", None, &backend),
            180,
            &library.join("compile.log"),
        );
        let run = |lane: &str| -> Option<String> {
            let stem = format!("variadic-bin-{lane}-O{opt}");
            let binary = root.join(&stem);
            let (output, transcript) = run_bounded(
                &mut compile(&caller, &binary, lane, opt, "bin", Some(&library), &backend),
                180,
                &root.join(format!("{stem}.compile.log")),
            );
            if !output.status.success() {
                assert_eq!(lane, "cg", "valid-Rust control failed: {transcript}");
                assert_eq!(
                    output.status.code(),
                    Some(1),
                    "expected a refusal or a build: {transcript}"
                );
                let stderr = String::from_utf8_lossy(&output.stderr);
                for needle in [
                    "[TCG-MIR-UNSUPPORTED]",
                    "oa_va_none_x1: [TCG-ARG-ABI] the C-variadic call of `xoa_va_none`: argument 1",
                ] {
                    assert!(
                        stderr.contains(needle),
                        "refusal lacks {needle}: {transcript}"
                    );
                }
                return None;
            }
            let output = checked(
                &mut Command::new(&binary),
                20,
                &root.join(format!("{stem}.run.log")),
            );
            Some(String::from_utf8_lossy(&output.stdout).into_owned())
        };
        assert_eq!(
            run("llvm").as_deref(),
            Some(want.as_str()),
            "the LLVM-built caller at O{opt}"
        );
        match run("cg") {
            Some(stdout) => {
                assert_eq!(
                    stdout, want,
                    "variadic-bin-cg-O{opt}: the over-aligned fixed argument of a C-variadic \
                     call with no anonymous argument was read from another place than LLVM \
                     passes it"
                );
                matches += 1;
            }
            None => refusals += 1,
        }
        assert_eq!(sha256(&backend), digest, "backend changed during O{opt}");
    }
    assert_eq!(matches + refusals, 4);
    println!(
        "TCG_OVERALIGNED_VARIADIC_NO_ANONYMOUS matches={matches} refusals={refusals} \
         certificates=off backend_sha256={digest}"
    );
}
