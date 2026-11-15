// Compiled only on an aarch64-apple-darwin host: another host builds this
// target with no test in it, never one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// The loop rewrites and size offsets of the 2026-10 Darwin runtime-parity
// work, run natively against the LLVM oracle (L14-P8, L14-P10).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Four trust-cg-opt rewrites change the hot loops of benchmarks/beat-llvm
// programs (reports/perf/2026-10-01-darwin-runtime-per-program):
// xorshift-pair-fusion (`x ^ (x << a)` then `t ^ (t >> b)` computed through a
// `UBFM`), scalar-unroll's unsigned top-tested gather whose lanes load
// `[base + iv*8, #8k]`, mul-shift-reduce's late `Madd` addend for `2^k - 1` /
// `1 - 2^k`, and SROA / LICM through a field address `AddRR slot, k`. Their
// unit tests check each rewrite against independent opcode evaluators and
// carry the negative controls; the corpus checks one constant per program.
// This file runs every shape over many constants and trip counts
// (`bridge_corpus/runtime_parity_rewrites.rs`: 15 shift triples, 15
// multipliers, 4 trip counts, 17 lengths; 179 rows, plus the 154 rows of the
// size offsets below) through the bridge and through LLVM at -O2 and -O3 (the
// levels whose pipelines run these passes) and requires every row's line and
// the exit status to be equal.
//
// A row that matches only because a rewrite did not fire would not test it, so
// the bridge binary is also read back: at -O2 and -O3 every 64-bit
// `xorshift_pair` instance must contain a `UBFX`/`UBFIZ` (the fused pair's
// bitfield move), and at -O3 (the level the beat-llvm harness compiles at)
// `box_sum` must load lanes 2 and 3 with one `LDP` of two X registers at
// `#0x10` off a non-SP base. At -O2 that gather stays rolled (measured). These
// are witnesses that the rewrites ran on this fixture, not proofs of them.
// Measured against the backend of `main` 530a9319a, which has none of these
// rewrites: all 179 rows match at both levels, and the witnesses are absent
// (0 of 15 instances with a bitfield move; `box_sum`'s only non-SP `LDP` is
// the `Vec` header at `#0x8`), so the witness checks fail there.
//
// The size offsets of the same work are checked the same way: division and
// remainder by constants (`rem_i32::<D>`, `div_u64::<D>`, `rem_u32::<D>`;
// 15 divisors x 10 dividends) and `p3_gcd`'s two LCG steps (`lcg_twice`, 4
// trip counts). Witnesses: `rem_i32`'s five `MSUB` tails are the W form and
// none of its eight instances narrows with a `MOV W0, Wn` (`(x % D) as i32`
// writes its remainder tail in the W form), no `div_u64`/`rem_u32` has the
// add-back `ADD ..., LSR #1` (their even divisors are pre-shifted), and
// `lcg_twice` materializes the LCG multiplier once (one `MOVK #0x5851, LSL
// #48`). Through the backend of this branch before those offsets (`9c2f3740a`)
// the 154 new rows match at both levels, and the witnesses are absent:
// `rem_i32` has 5 X-form `MSUB`s and 8 narrowing moves, all 4 `div_u64` and 3
// `rem_u32` instances keep the add-back, and `lcg_twice` materializes the
// multiplier twice.
//
// Proofs off (`no-proof-certs`): this judges codegen, not proof promotion.
// Nothing here is a proof.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";
const FIXTURE: &str = include_str!("bridge_corpus/runtime_parity_rewrites.rs");
const OPTS: &[&str] = &["2", "3"];
/// Rows the fixture prints: (15 xorshift triples + 3 + 15 multipliers) x 4
/// trip counts + 15 divisors x 10 dividends + 3 x 17 lengths.
const ROWS: usize = 333;
/// The 64-bit `xorshift_pair` instances (one per shift triple).
const XORSHIFT_INSTANCES: usize = 15;

fn workdir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_runtime_parity_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile the fixture at `opt`, through the bridge when `bridge` is set.
fn compile(dir: &Path, opt: &str, bridge: bool) -> PathBuf {
    let src = dir.join("runtime_parity_rewrites.rs");
    if !src.exists() {
        std::fs::write(&src, FIXTURE).expect("write fixture");
    }
    let tag = if bridge { "tcg" } else { "llvm" };
    let bin = dir.join(format!("rewrites.{tag}.O{opt}"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.env("MACOSX_DEPLOYMENT_TARGET", "13.0")
        .args(["--crate-type", "bin", "-Ccodegen-units=1", "-Cpanic=abort"])
        .args(["--target", TARGET])
        .arg(format!("-Copt-level={opt}"));
    if bridge {
        let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
        backend.push(backend_artifact_support::current_test_backend());
        cmd.arg(backend)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let output = cmd
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .output()
        .expect("spawn rustc");
    assert!(
        output.status.success(),
        "{tag} -O{opt} compile failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

/// `(exit code, stdout lines)` of one run.
fn run(bin: &Path) -> (Option<i32>, Vec<String>) {
    let output = Command::new(bin).output().expect("run the fixture");
    (
        output.status.code(),
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(str::to_owned)
            .collect(),
    )
}

/// The disassembly of every function whose symbol contains `name`, keyed by
/// symbol line.
fn functions_named(bin: &Path, name: &str) -> BTreeMap<String, String> {
    let output = Command::new("objdump")
        .args(["-d", "--no-show-raw-insn"])
        .arg(bin)
        .output()
        .expect("run objdump");
    assert!(output.status.success(), "objdump -d {}", bin.display());
    let text = String::from_utf8_lossy(&output.stdout);
    let mut out = BTreeMap::new();
    let mut current: Option<String> = None;
    for line in text.lines() {
        if line.ends_with(">:") {
            current = line.contains(name).then(|| line.to_owned());
            if let Some(symbol) = &current {
                out.insert(symbol.clone(), String::new());
            }
        } else if line.is_empty() {
            current = None;
        } else if let Some(symbol) = &current {
            let body = out.get_mut(symbol).expect("symbol recorded");
            body.push_str(line);
            body.push('\n');
        }
    }
    out
}

fn count(asm: &str, needles: &[&str]) -> usize {
    asm.lines()
        .filter(|line| needles.iter().any(|needle| line.contains(needle)))
        .count()
}

/// The division, remainder and repeated-constant offsets ran on the bridge
/// binary (see the header).
fn size_offset_witnesses(bin: &Path, opt: &str) {
    let rem = functions_named(bin, "rem_i32");
    assert_eq!(rem.len(), 8, "-O{opt}: rem_i32 instances: {:?}", rem.keys());
    let all: String = rem.values().cloned().collect();
    // Five of the eight divisors take the MSUB tail (7, 255 and 257 the
    // `2^k +- 1` add/sub tail); none needs a narrowing `MOV W0, Wn`.
    assert!(
        count(&all, &["msub\tw"]) == 5
            && count(&all, &["msub\tx"]) == 0
            && count(&all, &["mov\tw0, w"]) == 0,
        "-O{opt}: rem_i32 remainders are not all written in the W form:\n{all}"
    );
    for name in ["div_u64", "rem_u32"] {
        let funcs = functions_named(bin, name);
        assert!(
            funcs.len() >= 3,
            "-O{opt}: {name} instances: {:?}",
            funcs.keys()
        );
        for (symbol, asm) in &funcs {
            let add_back = asm
                .lines()
                .filter(|line| line.contains("add\t") && line.contains(", lsr #1"))
                .count();
            assert_eq!(
                add_back, 0,
                "-O{opt}: {symbol} keeps the add-back form:\n{asm}"
            );
            assert!(
                count(asm, &["umulh\t", "umull\t"]) == 1,
                "-O{opt}: {symbol} has no magic multiply:\n{asm}"
            );
        }
    }
    let lcg = functions_named(bin, "lcg_twice");
    assert_eq!(lcg.len(), 1, "-O{opt}: one lcg_twice");
    let asm = lcg.values().next().expect("lcg_twice");
    assert_eq!(
        count(asm, &["#0x5851, lsl #48"]),
        1,
        "-O{opt}: lcg_twice materializes the LCG multiplier more than once:\n{asm}"
    );
}

#[test]
fn runtime_parity_rewrites_match_llvm_aarch64() {
    darwin_native::require("runtime_parity_rewrites_aarch64", &["objdump"]);
    let dir = workdir();
    let mut rows = 0usize;
    let mut fused_instances = 0usize;
    let mut paired_gathers = 0usize;
    for &opt in OPTS {
        let llvm = run(&compile(&dir, opt, false));
        let bridge_bin = compile(&dir, opt, true);
        let bridge = run(&bridge_bin);
        assert_eq!(llvm.0, Some(0), "LLVM -O{opt} exit");
        assert_eq!(llvm.1.len(), ROWS, "LLVM -O{opt} rows");
        assert_eq!(bridge.0, llvm.0, "bridge -O{opt} exit");
        let mismatched: Vec<String> = llvm
            .1
            .iter()
            .zip(&bridge.1)
            .filter(|(l, b)| l != b)
            .map(|(l, b)| format!("LLVM `{l}` bridge `{b}`"))
            .collect();
        assert!(
            mismatched.is_empty() && bridge.1.len() == ROWS,
            "-O{opt}: {} of {ROWS} rows differ (bridge printed {}):\n  {}",
            mismatched.len(),
            bridge.1.len(),
            mismatched.join("\n  ")
        );
        rows += ROWS;

        // Witnesses: the rewrites ran on this fixture's bridge binary.
        let xorshift = functions_named(&bridge_bin, "xorshift_pair");
        assert_eq!(
            xorshift.len(),
            XORSHIFT_INSTANCES,
            "-O{opt}: xorshift_pair instances in the bridge binary: {:?}",
            xorshift.keys().collect::<Vec<_>>()
        );
        for (symbol, asm) in &xorshift {
            assert!(
                count(asm, &["ubfx\t", "ubfiz\t"]) >= 1,
                "-O{opt}: {symbol} has no fused step pair (no UBFX/UBFIZ):\n{asm}"
            );
        }
        fused_instances += xorshift.len();
        size_offset_witnesses(&bridge_bin, opt);
        let gather = functions_named(&bridge_bin, "box_sum");
        assert_eq!(gather.len(), 1, "-O{opt}: one box_sum in the bridge binary");
        if opt == "3" {
            let asm = gather.values().next().expect("box_sum");
            assert!(
                asm.lines().any(|line| line.contains("ldp\tx")
                    && line.contains(", #0x10]")
                    && !line.contains("[sp")),
                "-O{opt}: box_sum loads no lane pair at #0x10 (LDP of X registers):\n{asm}"
            );
            paired_gathers += 1;
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    println!(
        "RUNTIME_PARITY_REWRITES rows={rows} matched={rows} opts=2,3 \
         fused_xorshift_instances={fused_instances} paired_gathers={paired_gathers}"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
