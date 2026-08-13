// trust-cg-fuzz/src/bridge_diff.rs — P2 bridge differential harness core.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHY THIS EXISTS (the gap P2 closes)
// -----------------------------------
// The existing differential harness `src/jit_diff.rs` is structurally unable to
// catch *bridge* (rustc_codegen_trust_cg) bugs. Its oracle is
// `run_oracle_one` -> `trust_cg_codegen::interpreter::interpret_with_config`,
// i.e. the **trust-ir interpreter**. The bridge pipeline is:
//
//     Rust source --(rustc MIR)--> trust-ir-from-rustc-mir adapter --> trust-ir
//                 --> trust-cg lowering/opt/codegen --> machine code
//
// `jit_diff` only ever sees the *trust-ir* (it generates trust-ir directly, and
// compares the interpreter run of that trust-ir against the JIT run of the SAME
// trust-ir). Every bug in the MIR->trust-ir adapter (e.g. #71: a loop-carried
// scalarized aggregate field whose header phi was never emitted; #69: by-value
// mixed INT+SSE aggregate ABI; the `&mut`-to-join-local class) is INVISIBLE to
// it, because the adapter is UPSTREAM of the trust-ir the harness diffs, and the
// interpreter oracle is DOWNSTREAM of the adapter — both sides share the adapter
// output, so an adapter miscompile is in BOTH the oracle and the test side and
// cancels out. To catch a bridge bug you need an oracle that does NOT go through
// trust-cg at all: stock rustc/LLVM.
//
// This module is the toolchain-independent CORE of that harness: the outcome
// model, the comparison (diff) engine, the seed corpus, and the test-case
// reducer. All of it is PURE and unit-testable inside the workspace. The two
// actual compiler invocations (stock rustc/LLVM -> reference exe; trust-cg
// backend -> test exe) live behind the `BridgeCompiler` trait, whose real
// implementation (`real_compiler` / the bridge integration test) needs the
// nightly `target-bridge` toolchain and is therefore exercised out of workspace.

use std::fmt;

/// The observable result of running one compiled program. This is the unit the
/// diff engine compares: stock-rustc result vs trust-cg result.
///
/// We model both a clean exit (exit code, captured stdout) and an abnormal
/// termination (killed by a signal — a hardware trap such as SIGFPE on `idiv`
/// #DE, SIGSEGV on a bad load, SIGILL on `ud2`/`brk`). A *trap* on one backend
/// while the other produced a *value* is a real divergence (mirrors the
/// `Trapped`-vs-`Value` logic in `jit_diff::classify_outputs`). Both-trapped is
/// excused ONLY when the SAME signal fires on both backends — a SIGFPE on one
/// side vs a SIGSEGV on the other is a divergence, because the two faults are
/// not the same observable event (a branch-selection miscompile can make BOTH
/// arms fault for DIFFERENT reasons, masking the bug if any-trap-vs-any-trap
/// were excused).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunOutcome {
    /// Process exited normally. `code` is the byte-truncated exit status
    /// (0..=255), `stdout` is the captured standard output.
    Exited { code: i32, stdout: Vec<u8> },
    /// Process was terminated by `signal` (e.g. 8=SIGFPE, 11=SIGSEGV, 4=SIGILL,
    /// 6=SIGABRT). This is a hardware trap or abort, NOT a defined value.
    Signalled { signal: i32 },
    /// The compile step failed (the backend could not lower this program).
    /// Carries a short stderr tail. A *fail-closed* compile error on the
    /// trust-cg side is NOT a miscompile — the bridge refused rather than
    /// emitting wrong code. The diff engine treats it as `Skip`, never a finding.
    CompileError { stderr_tail: String },
    /// The run exceeded the per-program wall-clock deadline (genuine infinite
    /// loop, or a miscompile that turned a terminating loop into a hang).
    ///
    /// `deadline_ms` is the deadline the runner enforced and `elapsed_ms` is how
    /// long the process actually ran before being killed (which is `>= deadline`
    /// by construction). Both-timeout is only soundly excused when the REFERENCE
    /// itself genuinely hangs — i.e. the reference also hit the deadline with no
    /// margin — so the diff engine inspects these fields rather than treating any
    /// two `Timeout`s as agreement. A runner that does not track timing may use
    /// `RunOutcome::timeout(deadline)` (elapsed==deadline), which is the
    /// conservative "reference genuinely hung" reading.
    Timeout { deadline_ms: u64, elapsed_ms: u64 },
}

impl RunOutcome {
    /// Convenience constructor for a clean exit with no stdout (the common
    /// `std::process::exit(N)` corpus shape).
    pub fn exit(code: i32) -> Self {
        RunOutcome::Exited {
            code,
            stdout: Vec::new(),
        }
    }

    /// Convenience constructor for a timeout where the process ran right up to
    /// the deadline (elapsed == deadline). This is the conservative reading: the
    /// run is treated as a genuine hang that hit the wall-clock with no margin.
    pub fn timeout(deadline_ms: u64) -> Self {
        RunOutcome::Timeout {
            deadline_ms,
            elapsed_ms: deadline_ms,
        }
    }
}

/// One backend's identity, used only for human-readable finding messages.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Backend {
    /// Stock rustc with the default LLVM codegen backend — the ORACLE.
    LlvmReference,
    /// rustc with `-Zcodegen-backend=<librustc_codegen_trust_cg>` — UNDER TEST.
    TrustCg,
}

impl fmt::Display for Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Backend::LlvmReference => write!(f, "llvm"),
            Backend::TrustCg => write!(f, "trust-cg"),
        }
    }
}

/// Optimization level the program is compiled at on BOTH backends. A bridge bug
/// that only manifests under trust-cg's own opt passes (e.g. the #64 splitter
/// join, or #71 only-at-O0) is caught by diffing across these.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OptLevel {
    O0,
    O1,
    O2,
    O3,
}

impl OptLevel {
    /// The `-Copt-level=` value passed to `rustc`.
    pub fn rustc_flag(self) -> &'static str {
        match self {
            OptLevel::O0 => "0",
            OptLevel::O1 => "1",
            OptLevel::O2 => "2",
            OptLevel::O3 => "3",
        }
    }

    /// The opt levels a default campaign sweeps. O0 is non-negotiable: the
    /// memory-model bug class (#71, the &mut-to-join-local class) is O0-only.
    pub fn campaign_default() -> [OptLevel; 3] {
        [OptLevel::O0, OptLevel::O2, OptLevel::O3]
    }
}

/// Verdict of comparing the reference (LLVM) outcome against the test (trust-cg)
/// outcome for a single (program, opt-level) pair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiffVerdict {
    /// The two backends agree: same exit+stdout, or both trapped with the SAME
    /// signal (a value-independent fault), or both genuinely hung (the reference
    /// itself reached the deadline with margin). No defect.
    Agree,
    /// trust-cg failed closed (compile error) while LLVM compiled. The bridge
    /// REFUSED to emit code; this is the safe outcome, not a miscompile. Carries
    /// the stderr tail so a corpus entry that is supposed to compile can assert
    /// it does (see `expect_compile` on a corpus entry).
    TrustCgFailedClosed(String),
    /// LLVM itself could not compile the program (bad fixture). Reported as a
    /// corpus error, never as a trust-cg finding.
    ReferenceCompileError(String),
    /// A genuine divergence: the trust-cg-compiled program is observably wrong
    /// relative to the LLVM-compiled program. `kind` classifies it.
    Divergence {
        kind: DivergenceKind,
        detail: String,
    },
}

/// The shape of a divergence, mirroring `jit_diff`'s "crash" / "miscompile" /
/// "timeout" taxonomy but oriented around the trust-cg-vs-LLVM axis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DivergenceKind {
    /// Both backends exited cleanly but with different exit codes / stdout.
    /// This is the classic silent miscompile (#51, #54, #69, #71, ...).
    WrongValue,
    /// LLVM returned a value but trust-cg trapped (or vice versa). e.g. #67:
    /// `overflowing_mul(_, 0)` SIGFPE'd on trust-cg while LLVM returned (0,false).
    TrapMismatch,
    /// One backend terminated within the deadline and the other hung. A loop
    /// the bridge turned non-terminating.
    HangMismatch,
}

/// Compare a reference (LLVM) outcome with a test (trust-cg) outcome.
///
/// This is the heart of the harness and is a PURE function: every campaign
/// finding flows through here, and every unit test pins a historical bug shape
/// onto it. The asymmetry between the two backends is deliberate:
///   * trust-cg `CompileError`  => `TrustCgFailedClosed` (safe, never a finding)
///   * LLVM `CompileError`      => `ReferenceCompileError` (bad fixture)
///   * trap-vs-value / hang-vs-exit / wrong-value => `Divergence`
pub fn diff_outcomes(reference: &RunOutcome, test: &RunOutcome) -> DiffVerdict {
    // A reference (LLVM) compile error means the fixture is malformed; we cannot
    // form an oracle, so this is never a trust-cg finding.
    if let RunOutcome::CompileError { stderr_tail } = reference {
        return DiffVerdict::ReferenceCompileError(stderr_tail.clone());
    }
    // trust-cg failing closed (refusing to lower) is the SAFE outcome. The
    // bridge emitted no wrong code. Surface it distinctly so a corpus entry that
    // expects compilation can flag a regression, but it is NOT a miscompile.
    if let RunOutcome::CompileError { stderr_tail } = test {
        return DiffVerdict::TrustCgFailedClosed(stderr_tail.clone());
    }

    match (reference, test) {
        // Both ran to a clean exit: compare exit code AND captured stdout.
        (
            RunOutcome::Exited {
                code: rc,
                stdout: rs,
            },
            RunOutcome::Exited {
                code: tc,
                stdout: ts,
            },
        ) => {
            if rc == tc && rs == ts {
                DiffVerdict::Agree
            } else {
                DiffVerdict::Divergence {
                    kind: DivergenceKind::WrongValue,
                    detail: format!(
                        "llvm_exit={} trust_cg_exit={}{}",
                        rc,
                        tc,
                        stdout_detail(rs, ts),
                    ),
                }
            }
        }

        // Both trapped: excused ONLY when the SAME signal fired on both sides.
        //
        // SOUNDNESS: "a trap is a trap" is WRONG as an excusal rule. A trap is
        // value-independent only when it is the SAME trap. Consider a
        // branch-selection miscompile where the reference takes arm A (which
        // divides by zero -> SIGFPE) and trust-cg wrongly takes arm B (which
        // dereferences null -> SIGSEGV): both "trap", but the bridge ran the
        // WRONG code. Blanket both-trap excusal masks that miscompile. Requiring
        // signal equality keeps the only case that is genuinely value-independent
        // (the program faults the SAME way regardless of backend) as Agree, and
        // surfaces every differing-fault as a TrapMismatch divergence.
        (RunOutcome::Signalled { signal: rsig }, RunOutcome::Signalled { signal: tsig }) => {
            if rsig == tsig {
                DiffVerdict::Agree
            } else {
                DiffVerdict::Divergence {
                    kind: DivergenceKind::TrapMismatch,
                    detail: format!(
                        "llvm=TRAP(sig={}) trust_cg=TRAP(sig={}) (both trapped but with \
                         DIFFERENT signals — not a value-independent fault)",
                        rsig, tsig
                    ),
                }
            }
        }

        // LLVM produced a value, trust-cg trapped: real divergence (#67 shape).
        (RunOutcome::Exited { code, .. }, RunOutcome::Signalled { signal }) => {
            DiffVerdict::Divergence {
                kind: DivergenceKind::TrapMismatch,
                detail: format!("llvm_exit={} trust_cg=TRAP(sig={})", code, signal),
            }
        }
        // trust-cg produced a value, LLVM trapped: also a divergence (trust-cg
        // computed a value where the program should fault — e.g. #59 saturation
        // vs trap, or a missed overflow check).
        (RunOutcome::Signalled { signal }, RunOutcome::Exited { code, .. }) => {
            DiffVerdict::Divergence {
                kind: DivergenceKind::TrapMismatch,
                detail: format!("llvm=TRAP(sig={}) trust_cg_exit={}", signal, code),
            }
        }

        // Both timed out: excused ONLY when the REFERENCE genuinely hung — i.e.
        // the reference (LLVM) run itself reached the deadline with no margin.
        //
        // SOUNDNESS: both-timeout is NOT automatically agreement. The deadline is
        // a harness artifact, not a program property. If the REFERENCE terminates
        // well under the deadline but the harness still recorded a `Timeout` for
        // it (a flaky/over-tight run), then a trust-cg `Timeout` would be silently
        // excused even though the reference proves the program TERMINATES — that
        // is exactly the terminating->hang miscompile the harness must catch. We
        // only excuse when the reference's own wall-clock shows it hit the
        // deadline with margin (elapsed >= deadline), i.e. the reference is itself
        // a genuine hang and the deadline is value-independent across backends.
        (
            RunOutcome::Timeout {
                deadline_ms: rdl,
                elapsed_ms: rel,
            },
            RunOutcome::Timeout { .. },
        ) => {
            if rel >= rdl {
                // The reference genuinely ran to the deadline: a real hang on
                // both sides. Value-independent; excused.
                DiffVerdict::Agree
            } else {
                // The reference did NOT actually reach the deadline — we cannot
                // claim the program hangs, so a trust-cg timeout is unexcused.
                DiffVerdict::Divergence {
                    kind: DivergenceKind::HangMismatch,
                    detail: format!(
                        "llvm=TIMEOUT(elapsed={}ms<deadline={}ms — reference did NOT genuinely \
                         hang) trust_cg=TIMEOUT — cannot excuse both-timeout",
                        rel, rdl
                    ),
                }
            }
        }
        // A timeout on exactly one side is a hang divergence.
        (RunOutcome::Timeout { .. }, _) => DiffVerdict::Divergence {
            kind: DivergenceKind::HangMismatch,
            detail: format!("llvm=TIMEOUT trust_cg={}", describe(test)),
        },
        (_, RunOutcome::Timeout { .. }) => DiffVerdict::Divergence {
            kind: DivergenceKind::HangMismatch,
            detail: format!("llvm={} trust_cg=TIMEOUT", describe(reference)),
        },

        // CompileError pairs are handled by the early returns above; this arm is
        // unreachable for them, but the match must be exhaustive.
        (RunOutcome::CompileError { .. }, _) | (_, RunOutcome::CompileError { .. }) => {
            unreachable!("compile-error outcomes handled before the value match")
        }
    }
}

fn describe(o: &RunOutcome) -> String {
    match o {
        RunOutcome::Exited { code, .. } => format!("exit={}", code),
        RunOutcome::Signalled { signal } => format!("TRAP(sig={})", signal),
        RunOutcome::Timeout {
            deadline_ms,
            elapsed_ms,
        } => format!(
            "TIMEOUT(elapsed={}ms/deadline={}ms)",
            elapsed_ms, deadline_ms
        ),
        RunOutcome::CompileError { .. } => "COMPILE_ERROR".to_string(),
    }
}

/// Append a stdout-diff note only when stdout actually differs (most corpus
/// entries emit nothing and communicate purely via exit code).
fn stdout_detail(reference: &[u8], test: &[u8]) -> String {
    if reference == test {
        String::new()
    } else {
        format!(
            " llvm_stdout={:?} trust_cg_stdout={:?}",
            String::from_utf8_lossy(reference),
            String::from_utf8_lossy(test)
        )
    }
}

/// What kind of campaign finding this is. A campaign reports not just observable
/// divergences but also CORPUS-POLICY violations, because the corpus encodes
/// intent (`CompileExpectation`) that the differential alone cannot check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FindingKind {
    /// The two backends observably diverged (the classic differential finding).
    Divergence(DivergenceKind),
    /// A `MustCompile` corpus entry FAILED CLOSED on trust-cg. Failing closed is
    /// the SAFE outcome in general, but for an entry the corpus asserts must
    /// compile, a fail-closed is a REGRESSION: the bridge used to lower this
    /// shape and now refuses (or the entry was mis-marked). Either way the
    /// differential for that shape is no longer being exercised, so it must be
    /// surfaced rather than silently treated as "safe".
    FailedClosedRegression,
    /// A `MayFailClosed` tripwire entry SILENTLY started compiling (and agreeing)
    /// on trust-cg. This is NOT a miscompile, but it IS an alert: a shape we kept
    /// refused-until-differentially-verified now compiles, so it must be promoted
    /// to a `MustCompile` differential entry before we trust its codegen. Leaving
    /// it `MayFailClosed` would mean we ship un-differentially-verified codegen.
    FailClosedTripwireFired,
}

/// A finding: a single (corpus entry, opt level) pair on which the campaign
/// observed either a divergence or a corpus-policy violation. Campaign output is
/// a `Vec<Finding>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Finding {
    pub program_name: String,
    pub opt: OptLevel,
    pub kind: FindingKind,
    pub detail: String,
    /// The exact Rust source that produced the finding (post-reduction, if the
    /// finding is a reducible divergence; otherwise the original source).
    pub source: String,
}

/// True if a verdict is a real *differential* finding (a divergence). Fail-closed
/// / reference errors / agreement are not divergence findings (the corpus-policy
/// findings — fail-closed regressions and tripwire-fires — are raised by
/// `run_campaign` against the entry's `CompileExpectation`, not by this predicate
/// over a single verdict).
pub fn is_finding(verdict: &DiffVerdict) -> bool {
    matches!(verdict, DiffVerdict::Divergence { .. })
}

// ---------------------------------------------------------------------------
// Seed corpus
// ---------------------------------------------------------------------------

/// What a corpus entry asserts about its own compilation, independent of the
/// differential. Most entries MUST compile on both backends (a fail-closed there
/// is itself a regression). A few intentionally exercise fail-closed paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompileExpectation {
    /// Both backends must compile this; trust-cg failing closed is a regression.
    MustCompile,
    /// trust-cg is allowed to fail closed (a known-unsupported shape kept in the
    /// corpus to detect when it SILENTLY starts compiling — at which point it
    /// must be promoted to `MustCompile` and differentially checked).
    MayFailClosed,
}

/// One seed program. The full Rust source is `source`; the harness wraps nothing
/// — each entry is a complete crate so the corpus doubles as human-readable
/// repro files (see `corpus/*.rs`). `bug_ref` names the historical bug the entry
/// guards; that string is the lock-in documentation.
#[derive(Debug, Clone)]
pub struct CorpusEntry {
    pub name: &'static str,
    pub bug_ref: &'static str,
    pub source: &'static str,
    pub expect: CompileExpectation,
}

/// The seed corpus. Every entry is a COMPLETE `#![no_std] #![no_main]` program
/// exposing `pub extern "C" fn main() -> i32` (so the bridge compiles `main`
/// directly and we avoid the std `lang_start` entry path — matching the
/// established `m51_signed_narrow_x86.rs` pattern), with `black_box` defeating
/// const-folding so the bug-relevant ops are materialized at every opt level.
///
/// Each program is deterministic (no inputs): its exit code is fixed, so the
/// differential is "trust-cg exit == LLVM exit". The `bug_ref` strings are the
/// lock-in: each shape is one of the bridge bug classes from MEMORY.md.
pub fn seed_corpus() -> Vec<CorpusEntry> {
    vec![
        // -------------------------------------------------------------------
        // #71 — loop-carried scalarized aggregate field. `q.a += 1` inside a
        // loop. The bridge scalarizes the struct into per-field SSA values; the
        // ORIGINAL bug was that the header phi for a PROJECTED field value
        // (`q.a`) was never emitted, so the field reverted to its entry value
        // each iteration while plain scalars (`z1`/`z2`) updated correctly — a
        // silent WrongValue miscompile.
        //
        // CURRENT STATUS (commit e172b77 "bridge: fail closed on loop-carried
        // scalarized-aggregate field mutation"): the bridge no longer
        // miscompiles this shape — it FAILS CLOSED (`loop_carried_aggregate_error`
        // raises a hard unsupported-MIR error; full memory-backed support is
        // future work). So against the REAL bridge this entry compiles-errors on
        // trust-cg, never reaching the WrongValue differential. It is therefore a
        // `MayFailClosed` TRIPWIRE, NOT a `MustCompile` differential: the
        // tripwire assertion is "stays fail-closed until aggregate loop-carry is
        // actually implemented and differentially verified". The day it silently
        // starts compiling, the campaign raises `FailClosedTripwireFired` so it
        // gets promoted to a differential MustCompile (and the WrongValue path is
        // re-armed) rather than shipping an unverified aggregate loop-carry.
        // The WrongValue *shape* itself is still pinned end-to-end by the
        // MockCompiler-driven unit tests (`campaign_reports_and_reduces_a_wrong_
        // value_finding`) and by `diff_outcomes` directly.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "m71_loop_carried_aggregate_field",
            bug_ref: "#71 loop-carried scalarized aggregate field (fail-closed since e172b77; tripwire until memory-backed loop-carry is differentially verified)",
            source: SRC_M71_LOOP_CARRIED_AGG,
            expect: CompileExpectation::MayFailClosed,
        },
        // -------------------------------------------------------------------
        // #69 — by-value aggregate with a MIXED INT+SSE eightbyte. A
        // `struct{a:i64, x:f64}` is one INTEGER eightbyte and one SSE eightbyte
        // under SysV; passed by value it must go in {rdi (or stack), xmm0}. The
        // bug class is mis-placing the SSE half into a GPR (or vice versa),
        // corrupting the float on the callee side.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "m69_byval_mixed_int_sse_aggregate",
            bug_ref: "#69 by-value aggregate mixed INT+SSE eightbyte ABI placement",
            source: SRC_M69_MIXED_INT_SSE,
            expect: CompileExpectation::MustCompile,
        },
        // -------------------------------------------------------------------
        // c6 / "&mut-to-join-local" — a `&mut` of a local that is live across a
        // control-flow join (an `if/else` that both write through the reference).
        // The address-taken local must be slot-backed and the mutation observed
        // after the join; the bug dropped the write on one arm. O0-specific.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "c6_mut_ref_to_join_local",
            bug_ref: "c6 &mut-to-join-local (address-taken local mutated across a CF join, O0)",
            source: SRC_C6_MUT_REF_JOIN_LOCAL,
            expect: CompileExpectation::MustCompile,
        },
        // -------------------------------------------------------------------
        // #54 — multi-arg call parallel-move. A call whose arguments form a
        // cyclic move (arg registers must be permuted: f(b, a) where a,b are in
        // each other's target registers). A naive sequential move clobbers one.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "m54_call_arg_parallel_move",
            bug_ref: "#54 multi-arg call parallel-move (cyclic argument register permutation)",
            source: SRC_M54_PARALLEL_MOVE,
            expect: CompileExpectation::MustCompile,
        },
        // -------------------------------------------------------------------
        // #55 — by-ref capture in a closure. A closure capturing a local by
        // mutable reference and mutating it; the mutation must be visible to the
        // enclosing frame after the closure runs.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "m55_byref_closure_capture",
            bug_ref: "#55 by-ref closure capture (mutation through captured &mut visible after call)",
            source: SRC_M55_BYREF_CLOSURE,
            expect: CompileExpectation::MustCompile,
        },
        // -------------------------------------------------------------------
        // #56 — narrow-representation enum. An enum lowered to a narrow (i8)
        // discriminant carrier; reading the discriminant must re-extend (the
        // dirty-high-carrier invariant, sibling to #51/#66). Match on it.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "m56_narrow_repr_enum",
            bug_ref: "#56 narrow-representation enum discriminant (dirty high carrier on i8 tag)",
            source: SRC_M56_NARROW_ENUM,
            expect: CompileExpectation::MustCompile,
        },
        // -------------------------------------------------------------------
        // #72 — nested-closure wrapping_shl. A closure inside a closure whose
        // body does a wrapping shift; the inner shift count carrier and the
        // nested environment lowering interacted to drop a wrap. (Listed in the
        // prompt's bug set alongside #54/#55/#56/#69/#71.)
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "m72_nested_closure_wrapping_shl",
            bug_ref: "#72 nested-closure wrapping_shl (inner shift in a doubly-nested closure)",
            source: SRC_M72_NESTED_CLOSURE_SHL,
            expect: CompileExpectation::MustCompile,
        },
        // -------------------------------------------------------------------
        // #51 — signed-narrow SAR from a narrowing cast. `(-100i8) >> 1`. The
        // narrow carrier is zero-extended by `select_trunc`; a signed SAR must
        // sign-extend it first. Kept as a regression anchor in the bridge corpus
        // even though it already has a dedicated test, because it is the simplest
        // shape and validates the harness's WrongValue path against a known sign.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "m51_signed_narrow_sar",
            bug_ref: "#51 signed-narrow SAR from narrowing cast (dirty carrier needs sign-ext)",
            source: SRC_M51_SIGNED_NARROW_SAR,
            expect: CompileExpectation::MustCompile,
        },
        // -------------------------------------------------------------------
        // #67 — overflow expansion trap. `5i32.overflowing_mul(0)` SIGFPE'd on
        // x86 (IDIV-based overflow check by zero) while LLVM returns (0,false).
        // This is the TrapMismatch shape: trust-cg traps, LLVM has a value.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "m67_overflowing_mul_by_zero",
            bug_ref: "#67 overflowing_mul by zero (x86 IDIV-by-0 trap vs LLVM value) — TrapMismatch",
            source: SRC_M67_OVERFLOW_MUL_ZERO,
            expect: CompileExpectation::MustCompile,
        },
        // -------------------------------------------------------------------
        // FAIL-CLOSED tripwire: an i128 by-value extern "C" parameter. The
        // bridge fails closed on the i128 scalar ABI today (see rustc.rs
        // UI_FIXTURES `extern-c-i128-scalar-abi-fail-closed`). Kept in the corpus
        // so the day it SILENTLY starts compiling, the harness flags that it must
        // be promoted to a differential MustCompile entry rather than shipping an
        // unverified i128 ABI.
        // -------------------------------------------------------------------
        CorpusEntry {
            name: "i128_byval_abi_fail_closed_tripwire",
            bug_ref: "i128 scalar ABI fail-closed tripwire (must stay refused until differentially verified)",
            source: SRC_I128_BYVAL_FAIL_CLOSED,
            expect: CompileExpectation::MayFailClosed,
        },
    ]
}

// ---------------------------------------------------------------------------
// Test-case reducer
// ---------------------------------------------------------------------------

/// A side-effect-free predicate the reducer queries: "does this candidate source
/// still reproduce the divergence?". The campaign supplies a closure over the
/// real `BridgeCompiler`; unit tests supply a pure stand-in (e.g. "still
/// contains the marker line"). The reducer NEVER inspects compiler internals; it
/// only asks this oracle, so it is fully testable in-workspace.
pub trait ReductionOracle {
    /// True iff `candidate` still triggers the divergence of interest.
    fn still_diverges(&mut self, candidate: &str) -> bool;
}

/// Blanket impl so a plain `FnMut(&str) -> bool` is a `ReductionOracle`. Lets
/// tests (and the real campaign) pass a closure directly.
impl<F: FnMut(&str) -> bool> ReductionOracle for F {
    fn still_diverges(&mut self, candidate: &str) -> bool {
        self(candidate)
    }
}

/// Line-granularity delta-style reducer. Greedily drops contiguous chunks of
/// lines (ddmin-style: chunk sizes halve from n/2 down to 1) as long as the
/// reduced candidate STILL diverges per `oracle`. Returns the minimal source it
/// could reach. Deterministic and pure (its only effect is calling the oracle).
///
/// This is intentionally line-based, not token-based: the corpus programs are
/// line-structured `no_std`/`no_main` crates, and line reduction collapses a
/// fuzzed multi-statement `main` down to the minimal diverging statement set —
/// e.g. peeling everything but the `q.a += 1` loop body that reproduces #71 —
/// without needing a Rust parser in-workspace.
pub fn reduce(source: &str, oracle: &mut impl ReductionOracle) -> String {
    let mut lines: Vec<String> = source.lines().map(|l| l.to_string()).collect();

    // Sanity: the full input must diverge, else there is nothing to reduce
    // toward. If it does not, return it unchanged (the caller mis-used us).
    if !oracle.still_diverges(&join(&lines)) {
        return source.to_string();
    }

    let mut chunk = (lines.len() / 2).max(1);
    while chunk >= 1 {
        let mut start = 0;
        while start < lines.len() {
            let end = (start + chunk).min(lines.len());
            // Candidate with the [start, end) window removed.
            let mut candidate: Vec<String> = Vec::with_capacity(lines.len() - (end - start));
            candidate.extend_from_slice(&lines[..start]);
            candidate.extend_from_slice(&lines[end..]);
            if !candidate.is_empty() && oracle.still_diverges(&join(&candidate)) {
                // Accept the removal; do not advance `start` (the window now
                // covers the lines that had followed the removed block).
                lines = candidate;
            } else {
                start += chunk;
            }
        }
        if chunk == 1 {
            break;
        }
        chunk /= 2;
    }

    join(&lines)
}

fn join(lines: &[String]) -> String {
    let mut s = lines.join("\n");
    s.push('\n');
    s
}

// ---------------------------------------------------------------------------
// Compiler abstraction (the boundary between in-workspace and target-bridge)
// ---------------------------------------------------------------------------

/// The two-compiler boundary. The PURE logic above (diff + reduce + corpus)
/// never touches a compiler; it only ever sees `RunOutcome`s. A real campaign
/// implements this by shelling out to `rustup run <nightly> rustc ...` (see the
/// bridge integration test `bridge_differential_x86.rs`), which requires the
/// `target-bridge` toolchain. Unit tests implement it with canned outcomes.
pub trait BridgeCompiler {
    /// Compile `source` with the given backend at `opt`, run the resulting
    /// binary, and return its outcome. Must never panic on a compile failure —
    /// return `RunOutcome::CompileError` instead.
    fn compile_and_run(&self, source: &str, backend: Backend, opt: OptLevel) -> RunOutcome;
}

/// Run the whole corpus through a `BridgeCompiler` at the default opt sweep and
/// collect findings. PURE w.r.t. the compiler: all compiler interaction is via
/// the `BridgeCompiler` trait, so this driver is itself unit-testable with a
/// mock compiler (see tests). Each finding is reduced before being returned.
pub fn run_campaign<C: BridgeCompiler>(compiler: &C, corpus: &[CorpusEntry]) -> Vec<Finding> {
    let mut findings = Vec::new();
    for entry in corpus {
        for opt in OptLevel::campaign_default() {
            let reference = compiler.compile_and_run(entry.source, Backend::LlvmReference, opt);
            let test = compiler.compile_and_run(entry.source, Backend::TrustCg, opt);
            let verdict = diff_outcomes(&reference, &test);
            match &verdict {
                DiffVerdict::Divergence { kind, detail } => {
                    // Reduce: shrink to the minimal source that still reproduces
                    // the SPECIFIC divergence (not merely the same KIND) at this
                    // opt level — see the oracle below.
                    let target = verdict.clone();
                    // SOUNDNESS (reducer oracle): the oracle must preserve the
                    // EXACT divergence we are reducing, not just its `kind`. A
                    // kind-only oracle can reduce AWAY the real bug and keep an
                    // UNRELATED same-kind trigger that happens to remain in the
                    // file (e.g. two independent WrongValue ops; the reducer
                    // deletes the one we found and the surviving one still makes
                    // it "a WrongValue"). We therefore compare the FULL
                    // `DiffVerdict`, whose `detail` carries the exact exit
                    // codes / signals / stdout-diff — so the candidate must
                    // diverge the same way on the same values.
                    let mut reduce_oracle = |candidate: &str| {
                        let r = compiler.compile_and_run(candidate, Backend::LlvmReference, opt);
                        let t = compiler.compile_and_run(candidate, Backend::TrustCg, opt);
                        diff_outcomes(&r, &t) == target
                    };
                    let reduced = reduce(entry.source, &mut reduce_oracle);
                    findings.push(Finding {
                        program_name: entry.name.to_string(),
                        opt,
                        kind: FindingKind::Divergence(*kind),
                        detail: detail.clone(),
                        source: reduced,
                    });
                }
                // CORPUS-POLICY check: honour the entry's `CompileExpectation`.
                // `diff_outcomes` alone cannot see intent — a fail-closed always
                // looks "safe" to it — so the policy is enforced HERE.
                DiffVerdict::TrustCgFailedClosed(tail) => match entry.expect {
                    // A shape the corpus asserts must compile that now fails
                    // closed is a regression: the differential for it is no
                    // longer exercised. Emit it as a finding.
                    CompileExpectation::MustCompile => {
                        findings.push(Finding {
                            program_name: entry.name.to_string(),
                            opt,
                            kind: FindingKind::FailedClosedRegression,
                            detail: format!("MustCompile entry failed closed on trust-cg: {tail}"),
                            source: entry.source.to_string(),
                        });
                    }
                    // The expected case for a tripwire entry: still refused. No
                    // finding — the tripwire is holding.
                    CompileExpectation::MayFailClosed => {}
                },
                // A `MayFailClosed` tripwire entry that COMPILED (and agreed, or
                // diverged) is no longer failing closed: the tripwire fired. This
                // is an alert (the shape must be promoted to a differentially
                // verified MustCompile), even when the outcome was `Agree`.
                DiffVerdict::Agree => {
                    if entry.expect == CompileExpectation::MayFailClosed {
                        findings.push(Finding {
                            program_name: entry.name.to_string(),
                            opt,
                            kind: FindingKind::FailClosedTripwireFired,
                            detail:
                                "MayFailClosed tripwire entry now COMPILES and agrees with LLVM \
                                 — promote it to a MustCompile differential entry before trusting \
                                 its codegen"
                                    .to_string(),
                            source: entry.source.to_string(),
                        });
                    }
                }
                // The reference fixture is broken; not a trust-cg finding. (The
                // out-of-workspace driver panics on this; here we leave it out of
                // the findings list — a bad fixture is a corpus-maintenance issue,
                // not a bridge defect.)
                DiffVerdict::ReferenceCompileError(_) => {}
            }
        }
    }
    findings
}

// ---------------------------------------------------------------------------
// Corpus source fixtures (also written to corpus/*.rs as standalone repros)
// ---------------------------------------------------------------------------
//
// Every fixture is `#![no_std] #![no_main]` with a `#[panic_handler]` and a
// `#[no_mangle] pub extern "C" fn main() -> i32`, mirroring the established
// `m51_signed_narrow_x86.rs` differential shape. `black_box` is `core::hint`.

/// #71 — loop-carried scalarized aggregate field.
pub const SRC_M71_LOOP_CARRIED_AGG: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
struct Q { a: i64, b: i64 }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut q = Q { a: black_box(0), b: black_box(0) };
    let mut z1: i64 = black_box(0);
    let mut z2: i64 = black_box(0);
    let mut i: i64 = 0;
    while i < black_box(10) {
        q.a += 1;
        q.b += 2;
        z1 += 1;
        z2 += 2;
        i += 1;
    }
    // If the q.a/q.b header phis are dropped, q.a==q.b==0 while z1==10,z2==20.
    // Correct: 10 + 20 + 10 + 20 = 60.
    ((q.a + q.b + z1 + z2) & 0xff) as i32
}
"#;

/// #69 — by-value aggregate, mixed INT+SSE eightbyte.
pub const SRC_M69_MIXED_INT_SSE: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
struct Mixed { a: i64, x: f64 }
#[inline(never)]
fn use_mixed(m: Mixed) -> i64 {
    // a is the INTEGER eightbyte, x the SSE eightbyte. If the SSE half is
    // mis-placed into a GPR, x is garbage and the result diverges.
    m.a + (m.x as i64)
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let m = Mixed { a: black_box(7), x: black_box(35.0_f64) };
    (use_mixed(m) & 0xff) as i32
}
"#;

/// c6 — &mut to a local live across a control-flow join.
pub const SRC_C6_MUT_REF_JOIN_LOCAL: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[inline(never)]
fn bump(p: &mut i64, by: i64) { *p += by; }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: i64 = black_box(0);
    let cond = black_box(1i64);
    let r = &mut acc;
    if cond > 0 {
        bump(r, black_box(40));
    } else {
        bump(r, black_box(2));
    }
    // After the join, acc must reflect the taken arm's write. Correct: 40.
    (acc & 0xff) as i32
}
"#;

/// #54 — multi-arg call parallel-move (cyclic register permutation).
pub const SRC_M54_PARALLEL_MOVE: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[inline(never)]
fn sub4(a: i64, b: i64, c: i64, d: i64) -> i64 { a * 27 + b * 9 + c * 3 + d }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = black_box(1i64);
    let b = black_box(2i64);
    let c = black_box(3i64);
    let d = black_box(4i64);
    // Permute the arguments so the call needs a cyclic parallel move:
    // pass them in reverse, forcing register swaps among rdi/rsi/rdx/rcx.
    (sub4(d, c, b, a) & 0xff) as i32
}
"#;

/// #55 — by-ref closure capture, mutation visible after the call.
pub const SRC_M55_BYREF_CLOSURE: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: i64 = black_box(0);
    let mut add = |v: i64| { acc += v; };
    add(black_box(11));
    add(black_box(31));
    // The closure captured `acc` by &mut; both adds must persist. Correct: 42.
    (acc & 0xff) as i32
}
"#;

/// #56 — narrow-representation enum discriminant.
pub const SRC_M56_NARROW_ENUM: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[repr(i8)]
enum Tag { A = -3, B = 5, C = 17 }
#[inline(never)]
fn pick(sel: i64) -> Tag {
    match sel { 0 => Tag::A, 1 => Tag::B, _ => Tag::C }
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let t = pick(black_box(1));
    let v = match t { Tag::A => 100i64, Tag::B => 42, Tag::C => 200 };
    // If the i8 discriminant carrier is read with a dirty high carrier, the
    // match mis-selects. Correct: 42.
    (v & 0xff) as i32
}
"#;

/// #72 — nested closure with a wrapping shift.
pub const SRC_M72_NESTED_CLOSURE_SHL: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let base = black_box(3u64);
    let outer = |shift: u32| {
        let inner = |v: u64| v.wrapping_shl(shift);
        inner(base)
    };
    // wrapping_shl masks the shift to 0..63; 3 << 4 = 48. A dropped wrap or a
    // mis-nested environment would corrupt this. Correct: 48.
    (outer(black_box(4u32)) & 0xff) as i32
}
"#;

/// #51 — signed-narrow SAR from a narrowing cast (regression anchor).
pub const SRC_M51_SIGNED_NARROW_SAR: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let x: i8 = black_box(-100i32) as i8;
    let r: i8 = x >> 1;
    // -100 >> 1 = -50; (-50i8 as u8) = 206. Zero-extended carrier would give 78.
    (r as u8) as i32
}
"#;

/// #67 — overflowing_mul by zero (TrapMismatch shape).
pub const SRC_M67_OVERFLOW_MUL_ZERO: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = black_box(5i32);
    let b = black_box(0i32);
    let (v, o) = a.overflowing_mul(b);
    // Correct: (0, false) -> 0. The pre-fix bridge SIGFPE'd (IDIV-by-0 in the
    // x86 overflow check). A trust-cg trap vs an LLVM value is a TrapMismatch.
    ((v + o as i32) & 0xff) as i32
}
"#;

/// i128 by-value extern "C" param — fail-closed tripwire (NOT a differential).
pub const SRC_I128_BYVAL_FAIL_CLOSED: &str = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
#[no_mangle]
pub extern "C" fn takes_i128(v: i128) -> i128 { v.wrapping_add(1) }
#[no_mangle]
pub extern "C" fn main() -> i32 {
    takes_i128(0) as i32
}
"#;
