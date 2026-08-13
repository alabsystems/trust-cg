// crates/rustc-codegen-trust-cg/tests/opt_parity_x86.rs
//
// COMPLETE-12 — OPT-LEVEL PARITY SWEEP GATE.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHAT THIS IS
// ------------
// The bridge internally caps its own optimization at OptLevel::O1, but the
// FRONTEND (rustc) opt level still changes the *shape* of the MIR it hands the
// bridge: libcore inlining, aggregate scalarization, range-iterator expansion
// and bounds-check folding all differ between `-Copt-level=0` and `-O2/-O3`.
// That means the same source can take DIFFERENT bridge paths at different opt
// levels — and the audit found this is a real class:
//
//   * some programs COMPILE+MATCH at O0 but FAIL CLOSED at O2/O3
//     (e.g. array-by-value; static-mut RMW across a back-edge), and
//   * some go the other way — MaybeUninit write/read compiles at O0 only
//     (2ff5c58) — the O2/O3 inlined shape can fail closed instead.
//
// A fail-closed-at-one-level program is a SOUND completeness datum (it never
// runs, so it cannot miscompile). But a program whose bridge EXIT CODE differs
// across opt levels — while LLVM's exit code is stable — is a genuine
// opt-level-dependent MISCOMPILE (a real P0 soundness bug).
//
// THE SWEEP
// ---------
// For a set of in-envelope, exit-code-observable, panic=abort guests, compile
// each at rustc -Copt-level=0, 2 AND 3 through BOTH lanes (stock rustc/LLVM
// oracle and the trust-cg bridge), run them, and record the full
//   (program) x (O0,O2,O3) x (bridge,llvm)
// exit-code matrix. Then classify each program:
//
//   * PARITY-CLEAN : the bridge compiled+ran at all three levels, every bridge
//     exit code agrees with every other bridge exit code AND with LLVM at the
//     same level. (All 6 cells agree.)
//   * OPT-GAP : the bridge fail-closed at one or more levels, but EVERY level
//     where it did compile+run matched LLVM at that level. Sound — a
//     documented opt-parity COMPLETENESS gap (which level(s) fail-closed).
//   * MISCOMPILE : the bridge produced a WRONG or INCONSISTENT run result —
//     either (a) two bridge levels that both ran disagree with each other
//     while LLVM is stable, or (b) a bridge level that ran disagrees with LLVM
//     at that same level, or (c) an outcome-shape mismatch (one lane exits,
//     the other traps) at a level where the bridge ran. This is a P0
//     stop-the-line soundness event (fuzzer-finding doctrine applies).
//
// THE GATE (pass condition):
//   * MISCOMPILE count == 0                          (HARD — always).
//   * PARITY-CLEAN count >= PARITY_CLEAN_FLOOR       (ratchet — a
//     previously-clean program regressing to fail-closed at some level, or a
//     program that used to run at every level now not running, reds the gate).
//   OPT-GAP rows are NEVER failures; they are listed in the report as the
//   opt-parity completeness ledger.
//
// The floor is a const below (seeded at the first quiet-run measurement). RAISE
// it as opt-parity completeness fixes land; NEVER lower it to make the gate
// pass (soundness doctrine: a gate is never weakened in-run). LLVM is required
// to be opt-level-STABLE per program (deterministic source); a divergent LLVM
// exit across opt levels is a broken fixture and hard-fails loudly.
//
// Run (requires the target-bridge toolchain + x86_64-apple-darwin std, x86 host):
//     cd crates/rustc-codegen-trust-cg
//     cargo test --release --test opt_parity_x86 -- --nocapture
//
// (Plumbing mirrors tests/real_program_corpus_x86.rs and tests/vec_x86.rs —
// each bridge test target is its own crate, so the toolchain/dylib/run helpers
// are re-derived inline exactly like those harnesses.)
//
// ===========================================================================
// RESOLVED FINDING (found 2026-07-03 by this gate's first run; fixed same day) —
// P0 SILENT MISCOMPILE, now FAIL-CLOSED:
//   Iterator::step_by(N) on a Range was silently miscompiled at rustc -O0.
//   The bridge IGNORED THE STEP and iterated every element (as if step_by(1)).
//   * (0..80u64).step_by(3): iteration count LLVM=27, bridge=80 (all elems).
//   * (0..10usize).step_by(3): sum LLVM=18 (0+3+6+9), bridge=45 (0+1+..+9).
//   * step_by(1) matched (step 1 == identity, so the bug was invisible there).
//   ROOT CAUSE: the bridge intercepts the `.step_by(k)` CONSTRUCTOR and
//   synthesizes the StepBy slot in its OWN model (for the terminal
//   `emit_chain_next` driver used by `.sum()`/`.fold()`/`.collect()`), skipping
//   the specialized `<Range<uN> as SpecRangeSetup>::setup` (which rewrites
//   `iter.end` into a yield count). A bare `for` loop at -O0 instead lowers an
//   explicit real-core `<StepBy as Iterator>::next`, which reads that un-
//   preprocessed `end` and iterates as if `step == 1`. (At -O2/-O3 the shape is
//   inlined and either fail-closes or const-folds; only O0 ran the wrong loop.)
//   FIX (crates/rustc-codegen-trust-cg/src/lib.rs, `iter_chain_wraps_stepby`):
//   a real `next`/`into_iter` consuming any chain that WRAPS a StepBy adapter now
//   FAILS CLOSED [TCG-MIR-UNSUPPORTED] — doctrine: fail-closed beats miscompile.
//   The intercepted TERMINALS (`.step_by(k).sum()` etc.) are unaffected: they
//   drive the chain in the bridge's own step-correct model and never reach the
//   guard. So q06_ranges is now a sound OPT-GAP (fail-closed at all levels, LLVM
//   stable at 36), 0 MISCOMPILE.
//   Minimal repro (now fail-closed at O0, correct at O2/O3):
//     fn main(){let mut s:usize=0;for i in (0..10usize).step_by(3){s+=i;}
//               std::process::exit(s as i32);} // LLVM 18
//   NOTE (unchanged doctrine): MISCOMPILE stays a HARD P0 fail below; never
//   quarantine a program to turn the gate green.
// ===========================================================================

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";
// The three frontend opt levels whose MIR shapes diverge. -O1 is omitted on
// purpose: the bridge caps at its own O1 internally, and O2/O3 are the levels
// that produce the inlined/scalarized MIR shapes the audit flagged; O0 is the
// un-inlined baseline. (Add "1" here if a level-1-only shape is ever suspected.)
const OPT_LEVELS: [&str; 3] = ["0", "2", "3"];
const RUN_TIMEOUT: Duration = Duration::from_secs(60);

// Ratchet floor: the number of PARITY-CLEAN programs measured on a quiet x86
// host at the committing baseline. Seeded from the first measurement (see the
// report the test prints). Raise as completeness fixes land; never lower.
// Measured 2026-07-03 (x86_64-apple-darwin, HEAD e202f35): 14 programs ->
// 9 PARITY-CLEAN, 4 OPT-GAP, 1 MISCOMPILE (q06 step_by-at-O0, see header).
// After the step_by-O0 class-guard fix (this lane): 9 PARITY-CLEAN, 5 OPT-GAP,
// 0 MISCOMPILE (q06 moved MISCOMPILE -> OPT-GAP; parity-clean count unchanged,
// so the floor holds at 9).
const PARITY_CLEAN_FLOOR: usize = 9;

// ---------------------------------------------------------------------------
// Outcome model (mirror of tests/real_program_corpus_x86.rs)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum RunOutcome {
    Exited { code: i32 },
    Signalled { signal: i32 },
    /// rustc (compile+link in one invocation) failed — for the trust-cg lane
    /// this is the fail-closed shape (compile rejection OR an unemitted-symbol
    /// link error; both mean the program never runs, so it cannot miscompile).
    CompileError { stderr_tail: String, tcg_codes: Vec<String> },
    Timeout,
}

impl RunOutcome {
    fn short(&self) -> String {
        match self {
            RunOutcome::Exited { code } => format!("{code}"),
            RunOutcome::Signalled { signal } => format!("sig{signal}"),
            RunOutcome::CompileError { tcg_codes, .. } => {
                if tcg_codes.is_empty() {
                    "FAIL-CLOSED".to_string()
                } else {
                    format!("FC[{}]", tcg_codes.join(","))
                }
            }
            RunOutcome::Timeout => "TIMEOUT".to_string(),
        }
    }
    fn exit_code(&self) -> Option<i32> {
        match self {
            RunOutcome::Exited { code } => Some(*code),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    ParityClean,
    OptGap,
    Miscompile,
}

// ---------------------------------------------------------------------------
// Toolchain / dylib plumbing (mirror of tests/real_program_corpus_x86.rs)
// ---------------------------------------------------------------------------

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            let Some((_, value)) = raw_channel.split_once('=') else {
                continue;
            };
            return value.trim().trim_matches('"').to_owned();
        }
    }
    panic!("rust-toolchain.toml did not contain a channel");
}

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
    let name = dylib_name();
    let candidates = [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(
        status.success(),
        "cargo build failed; cannot run the opt-parity gate"
    );
    let built = target_dir.join("release").join(&name);
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn x86_64_std_available() -> bool {
    let output = Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output();
    match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line.trim() == TARGET),
        Err(_) => false,
    }
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_optparity_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Extract named `[TCG-*]`-style diagnostic codes from a trust-cg stderr, so
/// OPT-GAP rows carry the typed reason (the level-conditional gap ledger).
fn extract_tcg_codes(stderr: &str) -> Vec<String> {
    let mut codes: Vec<String> = Vec::new();
    let bytes = stderr.as_bytes();
    let mut i = 0;
    while let Some(pos) = stderr[i..].find("TCG-") {
        let start = i + pos;
        let mut end = start + 4;
        while end < bytes.len()
            && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'-' || bytes[end] == b'_')
        {
            end += 1;
        }
        let code = stderr[start..end].trim_end_matches(['-', '_']).to_string();
        if code.len() > 4 && !codes.contains(&code) {
            codes.push(code);
        }
        i = end;
    }
    codes
}

fn run_with_timeout(bin: &Path, timeout: Duration) -> RunOutcome {
    let mut child = Command::new(bin).spawn().expect("spawn compiled binary");
    let start = Instant::now();
    loop {
        match child.try_wait().expect("try_wait") {
            Some(status) => {
                if let Some(code) = status.code() {
                    return RunOutcome::Exited { code };
                }
                return RunOutcome::Signalled {
                    signal: signal_of(&status),
                };
            }
            None => {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return RunOutcome::Timeout;
                }
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }
}

/// Compile+link `src` with `dylib` (Some=trust-cg, None=LLVM oracle) via the
/// FULL rustc link at the given frontend opt level, run with a timeout,
/// classify. A rustc failure on the trust-cg lane (compile rejection or
/// unemitted-symbol link error) is the fail-closed shape: the program never
/// runs, so it cannot silently miscompile.
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> RunOutcome {
    let dir = workdir(&format!(
        "{stem}_o{opt}_{}",
        if dylib.is_some() { "tcg" } else { "llvm" }
    ));
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join("bin");

    let mut cmd = Command::new("rustup");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    // Typed diagnostics for the gap ledger (harmless if the bridge ignores it).
    cmd.env("TCG_DIAG_JSON", "1");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
    }
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("-o")
    .arg(&bin)
    .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        let _ = std::fs::remove_dir_all(&dir);
        return RunOutcome::CompileError {
            stderr_tail: stderr
                .lines()
                .rev()
                .take(6)
                .collect::<Vec<_>>()
                .join(" | "),
            tcg_codes: extract_tcg_codes(&stderr),
        };
    }

    let outcome = run_with_timeout(&bin, RUN_TIMEOUT);
    let _ = std::fs::remove_dir_all(&dir);
    outcome
}

#[cfg(unix)]
fn signal_of(status: &std::process::ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    status.signal().unwrap_or(-1)
}

#[cfg(not(unix))]
fn signal_of(_status: &std::process::ExitStatus) -> i32 {
    -1
}

// ---------------------------------------------------------------------------
// THE PROGRAM SET — in today's envelope, exit-code checksums (mod 251), no
// println, panic=abort-safe (inputs chosen so no panic path fires). Each
// program targets a shape whose MIR is known to change across frontend opt
// levels, so the sweep exercises the opt-conditional bridge paths.
// ---------------------------------------------------------------------------

struct Guest {
    name: &'static str,
    what: &'static str,
    src: &'static str,
}

fn program_set() -> Vec<Guest> {
    vec![
        Guest {
            name: "q01_int_arith",
            what: "integer arithmetic: add/sub/mul/div/rem/shift/bitops",
            src: r#"
fn main() {
    let mut a: u64 = 0x9e3779b97f4a7c15;
    let mut b: u64 = 0x1234_5678;
    let mut acc: u64 = 0;
    let mut i: u32 = 0;
    while i < 64 {
        a = a.wrapping_add(b).wrapping_mul(3);
        b = (b << 1) | (b >> 63);
        acc ^= (a & 0xff) | ((b % 97) << 8);
        acc = acc.wrapping_add(a / (b | 1)).wrapping_sub(a % (b | 3));
        acc = (acc >> 1) ^ (acc << 2);
        i += 1;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q02_struct_tuple_array",
            what: "structs + tuples + fixed arrays, field/element mutation",
            src: r#"
#[derive(Clone, Copy)]
struct Point { x: i64, y: i64 }

fn dist2(p: Point, q: Point) -> i64 {
    let dx = p.x - q.x;
    let dy = p.y - q.y;
    dx * dx + dy * dy
}

fn main() {
    let mut pts = [Point { x: 0, y: 0 }; 8];
    let mut i = 0i64;
    while i < 8 {
        pts[i as usize] = Point { x: i * 3 - 5, y: 7 - i * 2 };
        i += 1;
    }
    let mut total: i64 = 0;
    let mut pair = (0i64, 0i64);
    let mut j = 0usize;
    while j + 1 < 8 {
        let d = dist2(pts[j], pts[j + 1]);
        total = total.wrapping_add(d);
        pair = (pair.0 + d, pair.1 ^ (j as i64));
        j += 1;
    }
    let h = total.wrapping_mul(31).wrapping_add(pair.0).wrapping_add(pair.1);
    std::process::exit((h.rem_euclid(251)) as i32);
}
"#,
        },
        Guest {
            name: "q03_enum_match",
            what: "enum with data + match dispatch (tagged interpreter)",
            src: r#"
enum Op {
    Push(i64),
    Add,
    Mul,
    Neg,
    Dup,
}

fn main() {
    let prog = [
        Op::Push(3), Op::Push(4), Op::Add, Op::Dup, Op::Mul,
        Op::Push(2), Op::Neg, Op::Add, Op::Push(10), Op::Mul,
    ];
    let mut stack: [i64; 32] = [0; 32];
    let mut sp: usize = 0;
    for op in prog.iter() {
        match op {
            Op::Push(v) => { stack[sp] = *v; sp += 1; }
            Op::Add => { stack[sp - 2] = stack[sp - 2].wrapping_add(stack[sp - 1]); sp -= 1; }
            Op::Mul => { stack[sp - 2] = stack[sp - 2].wrapping_mul(stack[sp - 1]); sp -= 1; }
            Op::Neg => { stack[sp - 1] = -stack[sp - 1]; }
            Op::Dup => { stack[sp] = stack[sp - 1]; sp += 1; }
        }
    }
    let top = if sp > 0 { stack[sp - 1] } else { 0 };
    std::process::exit((top.rem_euclid(251)) as i32);
}
"#,
        },
        Guest {
            name: "q04_closures",
            what: "closures: FnMut accumulator + Fn combinator applied in a loop",
            src: r#"
fn apply<F: Fn(u64) -> u64>(f: F, x: u64) -> u64 {
    f(f(f(x)))
}

fn main() {
    let base: u64 = 0x2545f4914f6cdd1d;
    // FnMut closure captures its OWN state (not acc) by unique mutable borrow.
    let mut state: u64 = 0;
    let mut adder = |v: u64| -> u64 {
        state = state.wrapping_add(v).wrapping_mul(1103515245);
        state
    };
    let mut acc: u64 = 0;
    let mut i: u64 = 0;
    while i < 50 {
        let step = base.wrapping_mul(i + 1);
        let r = adder(step >> 20);
        let g = apply(|x| x.wrapping_mul(3).wrapping_add(7), r & 0xffff);
        acc ^= g;
        i += 1;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q05_nested_loops",
            what: "nested while loops with early break/continue",
            src: r#"
fn main() {
    let mut h: u64 = 1469598103934665603;
    let mut i: u64 = 1;
    while i < 60 {
        let mut j: u64 = 1;
        let mut inner: u64 = 0;
        while j < 60 {
            if (i * j) % 7 == 0 { j += 1; continue; }
            inner = inner.wrapping_add(i.wrapping_mul(j));
            if inner > 100_000 { break; }
            j += 2;
        }
        h = h.wrapping_mul(0x100000001b3) ^ inner;
        i += 1;
    }
    std::process::exit((h % 251) as i32);
}
"#,
        },
        Guest {
            // RESOLVED (see file header): the `.step_by(3)` loop below WAS a silent
            // O0 miscompile (bridge ignored the step and iterated every element,
            // exiting 96 vs LLVM 36). Fixed by the bridge's `iter_chain_wraps_stepby`
            // class guard — a bare `for` loop consuming a `.step_by(k)` chain now
            // FAILS CLOSED [TCG-MIR-UNSUPPORTED] at O0 (it already fails closed at
            // O2/O3), so this row is now a sound OPT-GAP (fail-closed at all levels,
            // LLVM stable at 36), never a miscompile.
            name: "q06_ranges",
            what: "for-range iteration (0..n, rev, step_by, inclusive) [step_by now fails closed at O0]",
            src: r#"
fn main() {
    let mut acc: u64 = 0;
    for i in 0..100u64 {
        acc = acc.wrapping_add(i.wrapping_mul(i));
    }
    for i in (0..50u64).rev() {
        acc ^= i << 1;
    }
    for i in (0..80u64).step_by(3) {
        acc = acc.wrapping_add(i);
    }
    for i in 1..=40u64 {
        acc = acc.wrapping_mul(31).wrapping_add(i);
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q07_multi_latch",
            what: "multi-latch dispatch loop w/ backward jumps (COMPLETE-6 shape)",
            src: r#"
fn main() {
    // A dispatch loop with several back-edges (one per opcode arm) into a
    // shared header — the multi-latch back-edge faithfulness shape.
    let prog: [u8; 14] = [2, 12, 0, 3, 1, 3, 4, 3, 0, 5, 3, 8, 4, 9];
    let mut acc: u64 = 1;
    let mut ctr: u64 = 0;
    let mut pc: usize = 0;
    let mut steps: u32 = 0;
    while pc < prog.len() && steps < 200_000 {
        steps += 1;
        match prog[pc] {
            0 => { acc = acc.wrapping_add(prog[pc + 1] as u64); pc += 2; }
            1 => { acc = acc.wrapping_mul(prog[pc + 1] as u64 | 1); pc += 2; }
            2 => { ctr = prog[pc + 1] as u64; pc += 2; }
            3 => {
                ctr = ctr.wrapping_sub(1);
                if ctr != 0 { pc = prog[pc + 1] as usize; } else { pc += 2; }
            }
            4 => { acc ^= ctr.wrapping_mul(0x9e37).wrapping_add(steps as u64); pc += 1; }
            _ => break,
        }
    }
    std::process::exit(((acc ^ steps as u64) % 251) as i32);
}
"#,
        },
        Guest {
            name: "q08_bounds_elim",
            what: "const-length array indexed over 0..N (OPT-6a bounds-check-elim shape)",
            src: r#"
fn main() {
    const N: usize = 256;
    let mut a = [0u32; N];
    for i in 0..N {
        a[i] = (i as u32).wrapping_mul(2654435761);
    }
    // Two more full-length in-bounds passes: the O2/O3 range analysis should
    // fold the bounds checks; O0 keeps them. Result must be identical.
    let mut acc: u64 = 0;
    for i in 0..N {
        acc = acc.wrapping_add(a[i] as u64);
    }
    for i in 0..N {
        let j = (a[i] as usize) % N;
        acc ^= a[j] as u64;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q09_if_convert_diamond",
            what: "pure value-select diamond in a loop (OPT-11 if-convert -> CMOV)",
            src: r#"
fn main() {
    // No stores inside the diamond — a pure value select the if-converter may
    // turn into CMOV at O2/O3 but leaves as a branch at O0. Same result.
    let mut acc: u64 = 0;
    let mut x: u64 = 0x243f6a8885a308d3;
    let mut i: u64 = 0;
    while i < 200 {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let hi = x >> 32;
        let lo = x & 0xffff_ffff;
        let m = if hi > lo { hi.wrapping_sub(lo) } else { lo.wrapping_sub(hi) };
        let sel = if (i & 1) == 0 { m } else { m ^ 0xdead_beef };
        let clamped = if sel > 1_000_000 { 1_000_000 } else { sel };
        acc = acc.wrapping_add(clamped);
        i += 1;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q10_wrapping_overflow",
            what: "wrapping / overflowing / checked / saturating arithmetic",
            src: r#"
fn main() {
    let mut acc: u64 = 0;
    let mut i: u32 = 0;
    while i < 120 {
        let a = (i as u64).wrapping_mul(0x9e3779b97f4a7c15);
        let b = (i as u64).wrapping_add(0xffff_ffff_0000_0000);
        let (s, o1) = a.overflowing_add(b);
        let (p, o2) = a.overflowing_mul(3);
        let c = a.checked_sub(b).unwrap_or(0);
        let sat = (i as u8).saturating_mul(200);
        acc = acc
            .wrapping_add(s)
            .wrapping_add(if o1 { 17 } else { 0 })
            .wrapping_add(p)
            .wrapping_add(if o2 { 31 } else { 0 })
            .wrapping_add(c)
            .wrapping_add(sat as u64);
        i += 1;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q11_vec_heap",
            what: "small Vec program (heap): push/index/len/pop/iter-sum",
            src: r#"
fn main() {
    let mut v: Vec<u64> = Vec::new();
    let mut x: u64 = 0x2545f4914f6cdd1d;
    let mut i = 0u32;
    while i < 64 {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1);
        v.push(x >> 40);
        i += 1;
    }
    let mut acc: u64 = 0;
    let mut j = 0usize;
    while j < v.len() {
        acc = acc.wrapping_add(v[j].wrapping_mul(j as u64 + 1));
        j += 1;
    }
    while let Some(top) = v.pop() {
        acc ^= top;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q12_array_byval",
            what: "fixed array passed BY VALUE to a fn (array-by-value opt shape)",
            src: r#"
fn fold(arr: [u64; 12], seed: u64) -> u64 {
    let mut h = seed;
    let mut i = 0usize;
    while i < 12 {
        h = h.wrapping_mul(31).wrapping_add(arr[i]);
        i += 1;
    }
    h
}

fn rotate(mut arr: [u64; 12]) -> [u64; 12] {
    let first = arr[0];
    let mut i = 0usize;
    while i < 11 {
        arr[i] = arr[i + 1];
        i += 1;
    }
    arr[11] = first;
    arr
}

fn main() {
    let mut a = [0u64; 12];
    let mut i = 0usize;
    while i < 12 {
        a[i] = (i as u64).wrapping_mul(2654435761).wrapping_add(1);
        i += 1;
    }
    let mut acc: u64 = 0;
    let mut round = 0;
    while round < 6 {
        acc = acc.wrapping_add(fold(a, acc ^ 0x9e37));
        a = rotate(a);
        round += 1;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q13_maybe_uninit",
            what: "MaybeUninit write/read (O0-only per 2ff5c58 — opt-gap candidate)",
            src: r#"
use std::mem::MaybeUninit;

fn main() {
    let mut acc: u64 = 0;
    let mut i: u64 = 0;
    while i < 32 {
        let mut m: MaybeUninit<u64> = MaybeUninit::uninit();
        let v = unsafe {
            m.as_mut_ptr().write(i.wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(1));
            m.assume_init()
        };
        acc = acc.wrapping_add(v ^ (v >> 29));
        i += 1;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
        Guest {
            name: "q14_recursion_option",
            what: "recursion returning Option/tuple, match on Option (Collatz-ish)",
            src: r#"
fn step(n: u64) -> Option<(u64, u64)> {
    if n <= 1 {
        None
    } else if n & 1 == 0 {
        Some((n / 2, 1))
    } else {
        Some((n.wrapping_mul(3).wrapping_add(1), 2))
    }
}

fn chain(start: u64) -> u64 {
    let mut n = start;
    let mut h: u64 = start;
    let mut guard = 0u32;
    while guard < 100_000 {
        guard += 1;
        match step(n) {
            None => break,
            Some((next, w)) => {
                h = h.wrapping_mul(31).wrapping_add(next).wrapping_add(w);
                n = next;
            }
        }
    }
    h
}

fn main() {
    let mut acc: u64 = 0;
    let mut s: u64 = 3;
    while s < 40 {
        acc ^= chain(s).wrapping_mul(s);
        s += 1;
    }
    std::process::exit((acc % 251) as i32);
}
"#,
        },
    ]
}

// ---------------------------------------------------------------------------
// THE GATE
// ---------------------------------------------------------------------------

#[test]
fn opt_level_parity_sweep_gate() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let started = Instant::now();

    // Per program: outcomes[opt_index] = (llvm, bridge).
    struct Row {
        name: &'static str,
        what: &'static str,
        cells: Vec<(RunOutcome, RunOutcome)>, // one per OPT_LEVELS entry
        class: Class,
        note: String,
    }

    let mut rows: Vec<Row> = Vec::new();
    let mut miscompiles: Vec<String> = Vec::new();

    for guest in program_set() {
        eprintln!("opt-parity guest {} — {}", guest.name, guest.what);
        let mut cells: Vec<(RunOutcome, RunOutcome)> = Vec::new();
        for opt in OPT_LEVELS {
            let reference = compile_link_run(guest.name, guest.src, opt, None);
            if let RunOutcome::CompileError { stderr_tail, .. } = &reference {
                panic!(
                    "FIXTURE BROKEN: LLVM could not compile `{}` (opt={opt}): {stderr_tail}",
                    guest.name
                );
            }
            let test = compile_link_run(guest.name, guest.src, opt, Some(&dylib));
            eprintln!(
                "  O{opt}: llvm={:<6} bridge={}",
                reference.short(),
                test.short()
            );
            cells.push((reference, test));
        }

        // ---- LLVM opt-stability check (broken-fixture guard) ----
        // A deterministic program must produce the same exit code at every LLVM
        // opt level. If not, the fixture is non-deterministic and any bridge
        // comparison is meaningless.
        let llvm_codes: Vec<Option<i32>> = cells.iter().map(|(r, _)| r.exit_code()).collect();
        let llvm_stable = {
            let mut it = llvm_codes.iter().filter_map(|c| *c);
            match it.next() {
                Some(first) => it.all(|c| c == first),
                None => true,
            }
        };
        assert!(
            llvm_stable,
            "FIXTURE BROKEN: LLVM exit code is not stable across opt levels for `{}`: {:?} — \
             the program is non-deterministic; pick a deterministic checksum.",
            guest.name, llvm_codes
        );

        // ---- Classify ----
        // Gather, per level, the (llvm_code, bridge_outcome).
        let mut bridge_ran_codes: Vec<(usize, i32)> = Vec::new(); // (opt_index, code)
        let mut bridge_failclosed_levels: Vec<usize> = Vec::new();
        let mut per_level_miscompile: Vec<String> = Vec::new();

        for (idx, (reference, test)) in cells.iter().enumerate() {
            let lvl = OPT_LEVELS[idx];
            match test {
                RunOutcome::Exited { code: bc } => {
                    bridge_ran_codes.push((idx, *bc));
                    // (b) bridge ran at this level — must match LLVM at this level.
                    if let Some(rc) = reference.exit_code() {
                        if *bc != rc {
                            per_level_miscompile.push(format!(
                                "O{lvl}: bridge_exit={bc} != llvm_exit={rc}"
                            ));
                        }
                    } else {
                        // LLVM did not plain-exit (trap/timeout) while bridge did.
                        per_level_miscompile.push(format!(
                            "O{lvl}: outcome-shape mismatch llvm={} bridge_exit={bc}",
                            reference.short()
                        ));
                    }
                }
                RunOutcome::CompileError { .. } => {
                    bridge_failclosed_levels.push(idx);
                }
                RunOutcome::Signalled { signal } => {
                    // Bridge trapped. If LLVM also trapped, agreement-in-trap is
                    // tolerated (mirrors the differential harness); otherwise a
                    // ran-but-diverged outcome-shape mismatch = miscompile.
                    match reference {
                        RunOutcome::Signalled { .. } => { /* agree-in-trap: ok */ }
                        _ => per_level_miscompile.push(format!(
                            "O{lvl}: bridge trapped (sig{signal}) while llvm={}",
                            reference.short()
                        )),
                    }
                }
                RunOutcome::Timeout => {
                    per_level_miscompile.push(format!(
                        "O{lvl}: bridge TIMEOUT while llvm={}",
                        reference.short()
                    ));
                }
            }
        }

        // (a) inconsistency ACROSS bridge levels that both ran (LLVM is stable,
        // proven above) — an opt-level-dependent miscompile.
        let mut cross_level_incoherent: Option<String> = None;
        if bridge_ran_codes.len() >= 2 {
            let first = bridge_ran_codes[0].1;
            if let Some((idx, bad)) = bridge_ran_codes.iter().find(|(_, c)| *c != first) {
                cross_level_incoherent = Some(format!(
                    "bridge exit differs across opt levels: O{}={} vs O{}={} (LLVM stable at {:?})",
                    OPT_LEVELS[bridge_ran_codes[0].0],
                    first,
                    OPT_LEVELS[*idx],
                    bad,
                    llvm_codes.iter().filter_map(|c| *c).next()
                ));
            }
        }

        let class;
        let mut note = String::new();
        if !per_level_miscompile.is_empty() || cross_level_incoherent.is_some() {
            class = Class::Miscompile;
            let mut detail = per_level_miscompile.join("; ");
            if let Some(ci) = cross_level_incoherent {
                if !detail.is_empty() {
                    detail.push_str("; ");
                }
                detail.push_str(&ci);
            }
            note = detail.clone();
            miscompiles.push(format!("{}: {detail}", guest.name));
        } else if bridge_failclosed_levels.is_empty() {
            // Compiled+ran at all levels, all matched LLVM, all coherent.
            class = Class::ParityClean;
        } else {
            class = Class::OptGap;
            let levels: Vec<String> = bridge_failclosed_levels
                .iter()
                .map(|i| format!("O{}", OPT_LEVELS[*i]))
                .collect();
            // Surface the typed diagnostic(s) for the ledger.
            let mut codes: Vec<String> = Vec::new();
            for i in &bridge_failclosed_levels {
                if let RunOutcome::CompileError { tcg_codes, .. } = &cells[*i].1 {
                    for c in tcg_codes {
                        if !codes.contains(c) {
                            codes.push(c.clone());
                        }
                    }
                }
            }
            note = if codes.is_empty() {
                format!("fail-closed at {}", levels.join(","))
            } else {
                format!("fail-closed at {} [{}]", levels.join(","), codes.join(","))
            };
            if bridge_ran_codes.is_empty() {
                note.push_str(" (all levels fail-closed — uniform completeness gap, not opt-conditional)");
            }
        }

        eprintln!("  => {:?}: {}", class, if note.is_empty() { "all 6 cells agree" } else { &note });
        rows.push(Row {
            name: guest.name,
            what: guest.what,
            cells,
            class,
            note,
        });
    }

    // ---- Report: the full matrix ----
    let parity_clean = rows.iter().filter(|r| r.class == Class::ParityClean).count();
    let opt_gap = rows.iter().filter(|r| r.class == Class::OptGap).count();
    let miscompile = rows.iter().filter(|r| r.class == Class::Miscompile).count();

    eprintln!("\n==================== COMPLETE-12 OPT-PARITY MATRIX ====================");
    eprintln!(
        "{:<24} | {:>16} | {:>16} | class",
        "program", "LLVM O0/O2/O3", "bridge O0/O2/O3"
    );
    eprintln!("{}", "-".repeat(78));
    for r in &rows {
        let llvm = r
            .cells
            .iter()
            .map(|(l, _)| l.short())
            .collect::<Vec<_>>()
            .join("/");
        let bridge = r
            .cells
            .iter()
            .map(|(_, b)| b.short())
            .collect::<Vec<_>>()
            .join("/");
        eprintln!(
            "{:<24} | {:>16} | {:>16} | {:?}",
            r.name, llvm, bridge, r.class
        );
    }
    eprintln!("{}", "-".repeat(78));
    eprintln!(
        "programs: {} | PARITY-CLEAN: {parity_clean} | OPT-GAP: {opt_gap} | MISCOMPILE: {miscompile}",
        rows.len()
    );
    eprintln!("PARITY-CLEAN floor: {PARITY_CLEAN_FLOOR}");

    // OPT-GAP ledger (opt-parity completeness data — which level fails closed).
    let gaps: Vec<&Row> = rows.iter().filter(|r| r.class == Class::OptGap).collect();
    if !gaps.is_empty() {
        eprintln!("\nOPT-GAP ledger (level-conditional completeness — sound, never a failure):");
        let mut by_reason: BTreeMap<String, u32> = BTreeMap::new();
        for r in &gaps {
            eprintln!("  {:<24} {} — {}", r.name, r.note, r.what);
            let key = r.note.clone();
            *by_reason.entry(key).or_insert(0) += 1;
        }
        eprintln!("  ranked:");
        let mut ranked: Vec<(&String, &u32)> = by_reason.iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(a.1));
        for (reason, count) in ranked {
            eprintln!("    {count:>2}x {reason}");
        }
    }

    // MISCOMPILE roll-up (P0).
    if !miscompiles.is_empty() {
        eprintln!("\n!!!! MISCOMPILE(S) — P0 STOP-THE-LINE !!!!");
        for m in &miscompiles {
            eprintln!("  {m}");
        }
    }
    eprintln!(
        "\nwall time: {:.1}s",
        started.elapsed().as_secs_f64()
    );
    eprintln!("======================================================================\n");

    // ---- The gate ----
    // (1) HARD: zero opt-level-dependent miscompiles. A bridge exit that
    // differs across opt levels (LLVM stable) or from LLVM at a level = a real
    // soundness bug (fuzzer-finding doctrine: close the class formally).
    assert!(
        miscompiles.is_empty(),
        "COMPLETE-12 P0: opt-level-dependent MISCOMPILE(S) — the bridge produced a wrong or \
         opt-level-inconsistent run result while LLVM was stable:\n{}",
        miscompiles.join("\n")
    );

    // (2) RATCHET: the PARITY-CLEAN count must not regress. A program that used
    // to run at every opt level now fail-closing at one level (or diverging)
    // drops this below the floor. Do NOT lower the floor to pass — investigate.
    assert!(
        parity_clean >= PARITY_CLEAN_FLOOR,
        "COMPLETE-12 parity regression: PARITY-CLEAN {parity_clean} < floor {PARITY_CLEAN_FLOOR}. \
         A previously opt-parity-clean program regressed to fail-closed at some level (or its \
         cells diverged). Find the regression; do NOT lower the floor."
    );
}
