// trust-cg-fuzz/tests/bridge_diff.rs — in-workspace unit tests for the P2 bridge
// differential harness CORE (diff engine + reducer + corpus + campaign driver).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These tests need NO compiler and NO target-bridge toolchain: they exercise the
// pure functions only, driving the compiler boundary with a `MockCompiler`. Each
// test states which historical bug or invariant it locks in.
//
// Run in-workspace with:  cargo test -p trust-cg-fuzz --test bridge_diff

use std::collections::HashMap;

use trust_cg_fuzz::bridge_diff::{
    Backend, BridgeCompiler, CompileExpectation, DiffVerdict, DivergenceKind, Finding, FindingKind,
    OptLevel, RunOutcome, diff_outcomes, is_finding, reduce, run_campaign, seed_corpus,
};

// ---------------------------------------------------------------------------
// diff_outcomes — the comparison engine
// ---------------------------------------------------------------------------

/// LOCKS IN: the core invariant — two backends agreeing on exit code AND stdout
/// is NOT a finding. (Sanity for the whole harness.)
#[test]
fn agree_when_exit_and_stdout_match() {
    let a = RunOutcome::Exited {
        code: 42,
        stdout: b"hi".to_vec(),
    };
    let b = RunOutcome::Exited {
        code: 42,
        stdout: b"hi".to_vec(),
    };
    assert_eq!(diff_outcomes(&a, &b), DiffVerdict::Agree);
    assert!(!is_finding(&diff_outcomes(&a, &b)));
}

/// LOCKS IN: #51/#54/#56/#69/#71 — the silent WrongValue miscompile. The whole
/// reason the bridge harness exists: a trust-cg binary that exits with a
/// DIFFERENT code than the LLVM binary on the same source is a miscompile. This
/// is the class the interpreter-oracle `jit_diff` cannot see (the adapter bug is
/// in both its oracle and its test side and cancels out).
#[test]
fn wrong_exit_code_is_a_miscompile_finding() {
    // #71 shape: LLVM computes 60, trust-cg (dropped header phi) computes 30.
    let llvm = RunOutcome::exit(60);
    let trust = RunOutcome::exit(30);
    let v = diff_outcomes(&llvm, &trust);
    match v {
        DiffVerdict::Divergence { kind, .. } => assert_eq!(kind, DivergenceKind::WrongValue),
        other => panic!("expected WrongValue divergence, got {other:?}"),
    }
    assert!(is_finding(&diff_outcomes(&llvm, &trust)));
}

/// LOCKS IN: stdout divergence with equal exit codes is still a finding (catches
/// a miscompile that corrupts a printed value but not the exit status).
#[test]
fn diverging_stdout_with_equal_exit_is_a_finding() {
    let llvm = RunOutcome::Exited {
        code: 0,
        stdout: b"55\n".to_vec(),
    };
    let trust = RunOutcome::Exited {
        code: 0,
        stdout: b"54\n".to_vec(),
    };
    let v = diff_outcomes(&llvm, &trust);
    assert!(matches!(
        v,
        DiffVerdict::Divergence {
            kind: DivergenceKind::WrongValue,
            ..
        }
    ));
}

/// LOCKS IN: #67 — overflowing_mul(_, 0) SIGFPE on trust-cg while LLVM returns a
/// value. A trap on ONE side while the other has a value is a TrapMismatch
/// finding (mirrors `jit_diff::trap_vs_value`).
#[test]
fn trust_cg_trap_while_llvm_has_value_is_trapmismatch() {
    let llvm = RunOutcome::exit(0); // (0, false) -> 0
    let trust = RunOutcome::Signalled { signal: 8 }; // SIGFPE on IDIV-by-0
    let v = diff_outcomes(&llvm, &trust);
    assert!(matches!(
        v,
        DiffVerdict::Divergence {
            kind: DivergenceKind::TrapMismatch,
            ..
        }
    ));
}

/// LOCKS IN: #59 — trust-cg computed a value where the program must FAULT (LLVM
/// trapped). The symmetric TrapMismatch: a trap that the bridge wrongly turned
/// into a value (e.g. saturation where Rust requires a panic/trap).
#[test]
fn llvm_trap_while_trust_cg_has_value_is_trapmismatch() {
    let llvm = RunOutcome::Signalled { signal: 6 }; // SIGABRT (overflow panic)
    let trust = RunOutcome::exit(7);
    let v = diff_outcomes(&llvm, &trust);
    assert!(matches!(
        v,
        DiffVerdict::Divergence {
            kind: DivergenceKind::TrapMismatch,
            ..
        }
    ));
}

/// LOCKS IN: the trap-excusal rule is SIGNAL-SPECIFIC. BOTH backends trapping
/// with the SAME signal (a value-independent fault, e.g. an unguarded
/// divide-by-zero that SIGFPEs on both) is NOT a finding — both honour the same
/// observable "no value" event. This prevents false-flagging programs that
/// legitimately fault.
#[test]
fn both_trapped_with_same_signal_is_excused() {
    let llvm = RunOutcome::Signalled { signal: 8 };
    let trust = RunOutcome::Signalled { signal: 8 };
    assert_eq!(diff_outcomes(&llvm, &trust), DiffVerdict::Agree);
}

/// LOCKS IN (SOUNDNESS, reviewer finding #1): BOTH backends trapping with
/// DIFFERENT signals is a TrapMismatch DIVERGENCE, NOT agreement. The previous
/// blanket "a trap is a trap" excusal masked a branch-selection miscompile: a bug
/// that makes the reference take a SIGFPE arm while trust-cg takes a SIGSEGV arm
/// would slip through as "both trapped -> Agree". The fault is value-INdependent
/// only when it is the SAME fault, so a differing signal pair must be flagged.
#[test]
fn both_trapped_with_different_signals_is_a_trapmismatch_divergence() {
    let llvm = RunOutcome::Signalled { signal: 8 }; // SIGFPE (e.g. div-by-zero arm)
    let trust = RunOutcome::Signalled { signal: 11 }; // SIGSEGV (e.g. null-deref arm)
    let v = diff_outcomes(&llvm, &trust);
    assert!(
        matches!(
            v,
            DiffVerdict::Divergence {
                kind: DivergenceKind::TrapMismatch,
                ..
            }
        ),
        "different-signal both-trap must be a TrapMismatch divergence, got {v:?}"
    );
    assert!(is_finding(&diff_outcomes(&llvm, &trust)));
}

/// LOCKS IN: trust-cg failing closed (refusing to lower) is the SAFE outcome and
/// must NEVER be reported as a miscompile. The bridge emitted no wrong code. This
/// is the single most important asymmetry: a fail-closed compile error is not a
/// finding (it surfaces as `TrustCgFailedClosed`, distinct from `Divergence`).
#[test]
fn trust_cg_compile_error_is_failed_closed_not_a_finding() {
    let llvm = RunOutcome::exit(0);
    let trust = RunOutcome::CompileError {
        stderr_tail: "failing closed: unsupported i128 scalar ABI".to_string(),
    };
    let v = diff_outcomes(&llvm, &trust);
    assert!(matches!(v, DiffVerdict::TrustCgFailedClosed(_)));
    assert!(!is_finding(&v));
}

/// LOCKS IN: an LLVM (reference) compile error means the fixture is malformed —
/// it is a corpus error, never a trust-cg finding.
#[test]
fn reference_compile_error_is_not_a_trust_cg_finding() {
    let llvm = RunOutcome::CompileError {
        stderr_tail: "error[E0425]: cannot find value".to_string(),
    };
    let trust = RunOutcome::exit(0);
    let v = diff_outcomes(&llvm, &trust);
    assert!(matches!(v, DiffVerdict::ReferenceCompileError(_)));
    assert!(!is_finding(&v));
}

/// LOCKS IN: a hang on exactly one backend (a loop the bridge made
/// non-terminating) is a HangMismatch; both-timeout where the REFERENCE genuinely
/// reached the deadline is excused.
#[test]
fn one_sided_timeout_is_hang_mismatch_genuine_both_is_excused() {
    let exit = RunOutcome::exit(0);
    // A timeout that ran right up to the deadline (genuine hang).
    let to = RunOutcome::timeout(5000);
    assert!(matches!(
        diff_outcomes(&exit, &to),
        DiffVerdict::Divergence {
            kind: DivergenceKind::HangMismatch,
            ..
        }
    ));
    assert!(matches!(
        diff_outcomes(&to, &exit),
        DiffVerdict::Divergence {
            kind: DivergenceKind::HangMismatch,
            ..
        }
    ));
    // Both genuinely hung (reference elapsed == deadline): excused.
    assert_eq!(diff_outcomes(&to, &to), DiffVerdict::Agree);
}

/// LOCKS IN (SOUNDNESS, reviewer finding #1): both-timeout is NOT excused when the
/// REFERENCE did not actually reach the deadline (elapsed < deadline). The
/// previous blanket "both Timeout -> Agree" masked a terminating->hang miscompile:
/// if the reference TERMINATES well under the deadline but the harness still
/// records a Timeout for it (flaky/over-tight run), a trust-cg Timeout would be
/// wrongly excused even though the reference proves the program terminates. We
/// require the reference's own wall-clock to show a genuine deadline hit.
#[test]
fn both_timeout_unexcused_when_reference_did_not_genuinely_hang() {
    // Reference "timed out" but actually only ran 12ms against a 5000ms deadline:
    // it did NOT genuinely hang. trust-cg also timed out (a real hang).
    let ref_flaky = RunOutcome::Timeout {
        deadline_ms: 5000,
        elapsed_ms: 12,
    };
    let trust_hang = RunOutcome::Timeout {
        deadline_ms: 5000,
        elapsed_ms: 5000,
    };
    let v = diff_outcomes(&ref_flaky, &trust_hang);
    assert!(
        matches!(
            v,
            DiffVerdict::Divergence {
                kind: DivergenceKind::HangMismatch,
                ..
            }
        ),
        "both-timeout with a reference that did not genuinely hang must be a \
         HangMismatch, got {v:?}"
    );
    assert!(is_finding(&v));
}

// ---------------------------------------------------------------------------
// reduce — the test-case reducer
// ---------------------------------------------------------------------------

/// LOCKS IN: the reducer shrinks a multi-line program down to the minimal set of
/// lines that still trigger the divergence, querying ONLY the oracle. Here the
/// "divergence" oracle is "still contains the load-bearing marker line", so the
/// reducer must peel away every non-marker line.
#[test]
fn reducer_peels_to_the_minimal_diverging_lines() {
    let src = "line_a\nMARKER\nline_c\nline_d\nline_e\n";
    let mut oracle = |candidate: &str| candidate.contains("MARKER");
    let reduced = reduce(src, &mut oracle);
    assert!(reduced.contains("MARKER"));
    assert!(!reduced.contains("line_a"));
    assert!(!reduced.contains("line_c"));
    // Minimal: only the marker line survives.
    assert_eq!(reduced.trim(), "MARKER");
}

/// LOCKS IN: the reducer preserves a divergence that needs TWO co-occurring
/// lines (e.g. #71 needs both the `q.a += 1` write AND the read of `q.a`). It
/// must not over-reduce past a multi-line trigger.
#[test]
fn reducer_keeps_co_dependent_lines() {
    let src = "noise1\nWRITE_QA\nnoise2\nREAD_QA\nnoise3\n";
    // Divergence requires BOTH the write and the read to remain.
    let mut oracle = |c: &str| c.contains("WRITE_QA") && c.contains("READ_QA");
    let reduced = reduce(src, &mut oracle);
    assert!(reduced.contains("WRITE_QA"));
    assert!(reduced.contains("READ_QA"));
    assert!(!reduced.contains("noise1"));
    assert!(!reduced.contains("noise2"));
    assert!(!reduced.contains("noise3"));
}

/// LOCKS IN: if the input does not diverge to begin with, the reducer returns it
/// unchanged (it never invents a reduction).
#[test]
fn reducer_no_op_when_input_does_not_diverge() {
    let src = "a\nb\nc\n";
    let mut oracle = |_c: &str| false;
    assert_eq!(reduce(src, &mut oracle), src.to_string());
}

/// LOCKS IN (reviewer finding #4): the reducer must preserve the SPECIFIC bug,
/// and an OR-shaped (kind-only) oracle does NOT — it lets the reducer delete the
/// real bug line and keep an UNRELATED same-kind trigger. This test contrasts the
/// two oracles on the same source so the danger and the fix are both pinned.
///
/// `REAL_BUG` and `OTHER_BUG` each independently "diverge" (here: each line, on
/// its own, satisfies the kind-only oracle — modelling two independent WrongValue
/// ops in one fuzzed program). A kind-only oracle ("contains EITHER") is happy to
/// drop `REAL_BUG` as long as `OTHER_BUG` survives, so the reduced repro can lose
/// the bug we were chasing. A SPECIFIC oracle ("the divergence is still the REAL
/// one") keeps `REAL_BUG`.
#[test]
fn reducer_or_oracle_can_drop_the_real_bug_but_specific_oracle_keeps_it() {
    let src = "prelude\nREAL_BUG\nmiddle\nOTHER_BUG\ntail\n";

    // KIND-ONLY (OR) oracle: any same-kind trigger counts. This is the UNSOUND
    // shape — it accepts a candidate that has dropped REAL_BUG so long as
    // OTHER_BUG remains.
    let mut kind_only = |c: &str| c.contains("REAL_BUG") || c.contains("OTHER_BUG");
    let reduced_kind_only = reduce(src, &mut kind_only);
    // The reducer is free to (and does) reduce to JUST the unrelated trigger,
    // losing the real bug — demonstrating exactly why a kind-only oracle is
    // unsound for reduction.
    assert!(
        !reduced_kind_only.contains("REAL_BUG"),
        "kind-only oracle should have let the reducer drop REAL_BUG: <<<{reduced_kind_only}>>>"
    );
    assert!(reduced_kind_only.contains("OTHER_BUG"));

    // SPECIFIC oracle: the divergence of interest requires the REAL_BUG line.
    // This is what the campaign's full-`DiffVerdict` comparison achieves (the
    // exact exit codes / signals / detail uniquely identify the bug we found).
    let mut specific = |c: &str| c.contains("REAL_BUG");
    let reduced_specific = reduce(src, &mut specific);
    assert!(
        reduced_specific.contains("REAL_BUG"),
        "specific oracle must keep the real bug line: <<<{reduced_specific}>>>"
    );
    assert_eq!(reduced_specific.trim(), "REAL_BUG");
}

// ---------------------------------------------------------------------------
// seed_corpus — corpus invariants
// ---------------------------------------------------------------------------

/// LOCKS IN: every corpus entry is a complete `no_std`/`no_main` crate with the
/// `extern "C" fn main` entry shape and a panic handler (so the bridge compiles
/// `main` directly, matching the `m51_signed_narrow_x86.rs` pattern). A
/// malformed fixture would silently never reach the differential.
#[test]
fn corpus_entries_are_well_formed_no_main_crates() {
    for e in seed_corpus() {
        assert!(
            e.source.contains("#![no_main]"),
            "{} is not no_main",
            e.name
        );
        assert!(e.source.contains("#![no_std]"), "{} is not no_std", e.name);
        assert!(
            e.source.contains("pub extern \"C\" fn main() -> i32"),
            "{} lacks the extern C main entry",
            e.name
        );
        assert!(
            e.source.contains("#[panic_handler]"),
            "{} lacks a panic handler",
            e.name
        );
        assert!(!e.bug_ref.is_empty(), "{} has no bug_ref lock-in", e.name);
    }
}

/// LOCKS IN: the corpus actually covers the bridge bug classes named in the P2
/// brief (#54/#55/#56/#69/#71/#72) plus the &mut-to-join-local class and the
/// #67 TrapMismatch. If someone deletes a shape, this fails.
#[test]
fn corpus_covers_the_named_bridge_bug_classes() {
    let names: Vec<&str> = seed_corpus().iter().map(|e| e.name).collect();
    for required in [
        "m71_loop_carried_aggregate_field",
        "m69_byval_mixed_int_sse_aggregate",
        "c6_mut_ref_to_join_local",
        "m54_call_arg_parallel_move",
        "m55_byref_closure_capture",
        "m56_narrow_repr_enum",
        "m72_nested_closure_wrapping_shl",
        "m67_overflowing_mul_by_zero",
    ] {
        assert!(
            names.contains(&required),
            "corpus is missing required bug shape {required}"
        );
    }
}

/// LOCKS IN (reviewer finding #3): EXACTLY the known-fail-closed shapes are
/// marked `MayFailClosed` — the i128 scalar ABI AND #71 (which fails closed
/// against the real bridge since commit e172b77). Every OTHER entry is
/// `MustCompile`. A shape that the bridge currently REFUSES must NOT be marked
/// `MustCompile`: that contradiction would make the campaign emit a spurious
/// `FailedClosedRegression` against a known-unsupported shape, and (the original
/// sin) would document a WrongValue differential that the real bridge never
/// actually exercises end-to-end.
#[test]
fn exactly_the_known_fail_closed_shapes_may_fail_closed() {
    let may_fail_closed: Vec<&str> = seed_corpus()
        .iter()
        .filter(|e| e.expect == CompileExpectation::MayFailClosed)
        .map(|e| e.name)
        .collect();
    let mut expected = vec![
        "i128_byval_abi_fail_closed_tripwire",
        "m71_loop_carried_aggregate_field",
    ];
    let mut got = may_fail_closed.clone();
    got.sort_unstable();
    expected.sort_unstable();
    assert_eq!(
        got, expected,
        "MayFailClosed set must be exactly the known fail-closed shapes"
    );
}

// ---------------------------------------------------------------------------
// run_campaign — the corpus driver (with a MockCompiler)
// ---------------------------------------------------------------------------

/// A deterministic mock compiler keyed on (source-marker, backend, opt). It lets
/// us drive `run_campaign` end-to-end (including the reducer) with NO real
/// compiler. The map key is a substring that must be present in the source.
struct MockCompiler {
    /// (marker_substring, backend, opt) -> outcome. The marker is matched as a
    /// `contains` so reduced candidates that retain the marker keep diverging.
    table: HashMap<(&'static str, Backend, OptLevel), RunOutcome>,
    /// Default outcome when no marker matches (both backends agree on exit 0).
    default: RunOutcome,
}

impl BridgeCompiler for MockCompiler {
    fn compile_and_run(&self, source: &str, backend: Backend, opt: OptLevel) -> RunOutcome {
        // DETERMINISTIC selection: when several markers match the same source
        // (e.g. two triggers in one fuzzed program, as in the OR-oracle test),
        // pick the MOST SPECIFIC (longest) marker, tie-breaking lexicographically.
        // HashMap iteration order is unspecified, so a first-match-wins scan would
        // make such tests flaky; longest-marker-wins is well-defined and, for the
        // common unique-marker case, identical to first-match.
        let mut best: Option<(&'static str, &RunOutcome)> = None;
        for ((marker, b, o), outcome) in &self.table {
            if *b == backend && *o == opt && source.contains(marker) {
                let better = match best {
                    None => true,
                    Some((bm, _)) => (marker.len(), *marker) > (bm.len(), bm),
                };
                if better {
                    best = Some((marker, outcome));
                }
            }
        }
        match best {
            Some((_, outcome)) => outcome.clone(),
            None => self.default.clone(),
        }
    }
}

/// Build a mock whose DEFAULT behaviour mirrors the real bridge for the corpus:
/// every `MustCompile` shape compiles+agrees (exit 0 both sides), and the two
/// `MayFailClosed` tripwire shapes (#71 since e172b77, and the i128 ABI) FAIL
/// CLOSED on trust-cg at every opt level (so they raise neither a divergence nor
/// a tripwire alert). Tests then perturb specific (marker, backend, opt) cells to
/// inject the scenario under test. This keeps the campaign tests honest: a
/// MayFailClosed entry that silently "agrees" by accident would otherwise trip
/// the new `FailClosedTripwireFired` alert.
fn baseline_corpus_mock() -> MockCompiler {
    let mut table = HashMap::new();
    for opt in OptLevel::campaign_default() {
        // #71 tripwire: LLVM compiles (exit 60), trust-cg fails closed. Keyed on
        // the m71-UNIQUE marker `q.a` (so tests can override individual O0/O2/O3
        // cells by re-inserting the same key — `q.a` matches ONLY the #71 source,
        // avoiding any HashMap-order ambiguity with another marker in the same
        // file).
        table.insert(("q.a", Backend::LlvmReference, opt), RunOutcome::exit(60));
        table.insert(
            ("q.a", Backend::TrustCg, opt),
            RunOutcome::CompileError {
                stderr_tail: "fail-closed: loop-carried scalarized aggregate field (#71)"
                    .to_string(),
            },
        );
        // i128 tripwire: LLVM compiles (exit 1), trust-cg fails closed.
        table.insert(
            ("takes_i128", Backend::LlvmReference, opt),
            RunOutcome::exit(1),
        );
        table.insert(
            ("takes_i128", Backend::TrustCg, opt),
            RunOutcome::CompileError {
                stderr_tail: "fail-closed: i128 scalar ABI".to_string(),
            },
        );
    }
    MockCompiler {
        table,
        default: RunOutcome::exit(0),
    }
}

/// LOCKS IN: the campaign driver actually FLAGS a #71-style WrongValue
/// divergence end-to-end (corpus -> diff -> reduce -> Finding), and that the
/// finding is attributed to the right program and the reduced source still
/// carries the load-bearing marker (`q.a`). This is the integration of all the
/// pure pieces.
///
/// Even though the REAL bridge fails closed on #71 today (so this divergence is
/// only reachable via the mock), the WrongValue *shape* must stay pinned
/// end-to-end: if aggregate loop-carry is ever implemented, this is the exact
/// path that must catch a regression.
#[test]
fn campaign_reports_and_reduces_a_wrong_value_finding() {
    let mut compiler = baseline_corpus_mock();
    // Override the #71 entry at O0 to a WrongValue: LLVM exits 60, trust-cg
    // exits 30 (as if aggregate loop-carry were implemented but miscompiling).
    // The marker "q.a" is present in the source and survives reduction down to
    // the loop body, so the divergence persists through the reducer. Re-inserting
    // the same ("q.a", _, O0) keys replaces the baseline's fail-closed cells at
    // O0 only; O2/O3 stay fail-closed.
    compiler.table.insert(
        ("q.a", Backend::LlvmReference, OptLevel::O0),
        RunOutcome::exit(60),
    );
    compiler.table.insert(
        ("q.a", Backend::TrustCg, OptLevel::O0),
        RunOutcome::exit(30),
    );

    let corpus = seed_corpus();
    let findings = run_campaign(&compiler, &corpus);

    // Exactly one finding (only #71 at O0 diverges; O2/O3 #71 + i128 stay
    // fail-closed, so no tripwire alerts fire).
    assert_eq!(findings.len(), 1, "findings: {:#?}", findings);
    let f = &findings[0];
    assert_eq!(f.program_name, "m71_loop_carried_aggregate_field");
    assert_eq!(f.opt, OptLevel::O0);
    assert_eq!(f.kind, FindingKind::Divergence(DivergenceKind::WrongValue));
    // The reducer kept the load-bearing `q.a` line.
    assert!(
        f.source.contains("q.a"),
        "reduced source dropped the q.a marker: <<<{}>>>",
        f.source
    );
}

/// LOCKS IN: a `MayFailClosed` entry that ACTUALLY fails closed produces NO
/// campaign finding (the tripwire holding is the expected, quiet state). With the
/// real-bridge-shaped baseline (both tripwire entries fail closed, every
/// MustCompile entry agrees), the findings list is empty.
#[test]
fn campaign_does_not_flag_a_holding_tripwire() {
    let compiler = baseline_corpus_mock();
    let findings = run_campaign(&compiler, &seed_corpus());
    assert!(
        findings.is_empty(),
        "a holding fail-closed tripwire must not be a finding: {findings:#?}"
    );
}

/// LOCKS IN (reviewer finding #2): a `MustCompile` entry that FAILS CLOSED on
/// trust-cg is a `FailedClosedRegression` finding — NOT silently treated as the
/// "safe" outcome. The corpus `expect` field was dead (run_campaign ignored it);
/// this proves it is now honoured. A regression here means the bridge stopped
/// lowering a shape it must lower, so its differential is no longer exercised.
#[test]
fn campaign_flags_must_compile_entry_that_fails_closed() {
    let mut compiler = baseline_corpus_mock();
    // Make a MustCompile entry (#54 parallel-move, marker "sub4") fail closed on
    // trust-cg at every opt while LLVM still compiles it.
    for opt in OptLevel::campaign_default() {
        compiler
            .table
            .insert(("sub4", Backend::LlvmReference, opt), RunOutcome::exit(40));
        compiler.table.insert(
            ("sub4", Backend::TrustCg, opt),
            RunOutcome::CompileError {
                stderr_tail: "regressed: refuses to lower call parallel-move".to_string(),
            },
        );
    }
    let findings = run_campaign(&compiler, &seed_corpus());
    // One FailedClosedRegression per opt level for the #54 entry, and nothing
    // else (the two tripwire entries are still fail-closed).
    let regressions: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.kind == FindingKind::FailedClosedRegression)
        .collect();
    assert_eq!(
        regressions.len(),
        OptLevel::campaign_default().len(),
        "expected one FailedClosedRegression per opt for the MustCompile entry: {findings:#?}"
    );
    for r in &regressions {
        assert_eq!(r.program_name, "m54_call_arg_parallel_move");
    }
    // No OTHER kind of finding leaked in.
    assert!(
        findings
            .iter()
            .all(|f| f.kind == FindingKind::FailedClosedRegression),
        "unexpected non-regression finding: {findings:#?}"
    );
}

/// LOCKS IN (reviewer finding #2/#3): a `MayFailClosed` tripwire entry that
/// SILENTLY starts COMPILING and AGREEING raises a `FailClosedTripwireFired`
/// alert. This is the exact #71 promotion guard: the day aggregate loop-carry is
/// implemented, the #71 tripwire stops failing closed and we MUST notice (so it
/// gets promoted to a differentially verified MustCompile) rather than shipping
/// un-differentially-verified codegen.
#[test]
fn campaign_alerts_when_tripwire_entry_silently_compiles() {
    let mut compiler = baseline_corpus_mock();
    // Make the #71 tripwire (marker "q.a") COMPILE and AGREE on both backends at
    // every opt (exit 60 == exit 60): the tripwire has fired.
    for opt in OptLevel::campaign_default() {
        compiler
            .table
            .insert(("q.a", Backend::LlvmReference, opt), RunOutcome::exit(60));
        compiler
            .table
            .insert(("q.a", Backend::TrustCg, opt), RunOutcome::exit(60));
    }
    let findings = run_campaign(&compiler, &seed_corpus());
    let tripwires: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.kind == FindingKind::FailClosedTripwireFired)
        .collect();
    assert_eq!(
        tripwires.len(),
        OptLevel::campaign_default().len(),
        "expected one tripwire alert per opt for the now-compiling #71 entry: {findings:#?}"
    );
    for t in &tripwires {
        assert_eq!(t.program_name, "m71_loop_carried_aggregate_field");
    }
    // The i128 tripwire is still fail-closed, so no extra alert for it.
    assert!(
        findings
            .iter()
            .all(|f| f.program_name == "m71_loop_carried_aggregate_field"),
        "only the #71 tripwire should have fired: {findings:#?}"
    );
}

/// LOCKS IN (reviewer finding #4, end-to-end): the campaign's reduction oracle
/// preserves the SPECIFIC divergence, not merely its KIND. We give the #54 entry
/// TWO independent same-kind (WrongValue) triggers:
///   * the call line `sub4(d, c, b, a)` -> the REAL bug, LLVM 142 vs trust-cg 130
///   * the fn-body line `a * 27`        -> an UNRELATED bug, LLVM 50 vs trust-cg 60
///     A kind-only oracle (the OLD `kind == kind` check) would let the reducer delete
///     the real call line and keep the unrelated `a * 27` trigger (still "a
///     WrongValue"), producing a repro for the WRONG bug. The fixed oracle compares
///     the full `DiffVerdict` (whose detail carries `llvm_exit=142 trust_cg_exit=130`),
///     so deleting the call line — which would change the divergence to 50-vs-60 — is
///     REJECTED. The reduced repro therefore keeps the real bug line and the finding
///     detail stays the real one.
#[test]
fn campaign_reducer_preserves_specific_divergence_not_just_kind() {
    let mut compiler = baseline_corpus_mock();
    // Longest-marker-wins in the mock: when both lines are present, the longer
    // `sub4(d, c, b, a)` marker dominates and yields the REAL 142/130 divergence.
    // Once the reducer removes that line, only `a * 27` remains -> 50/60.
    compiler.table.insert(
        ("sub4(d, c, b, a)", Backend::LlvmReference, OptLevel::O0),
        RunOutcome::exit(142),
    );
    compiler.table.insert(
        ("sub4(d, c, b, a)", Backend::TrustCg, OptLevel::O0),
        RunOutcome::exit(130),
    );
    compiler.table.insert(
        ("a * 27", Backend::LlvmReference, OptLevel::O0),
        RunOutcome::exit(50),
    );
    compiler.table.insert(
        ("a * 27", Backend::TrustCg, OptLevel::O0),
        RunOutcome::exit(60),
    );

    let findings = run_campaign(&compiler, &seed_corpus());
    // Exactly one divergence finding: the #54 entry at O0 (the unrelated 50/60
    // trigger never becomes a SEPARATE finding because while the call line is
    // present it shadows `a * 27`; at O2/O3 the #54 entry agrees).
    let divergences: Vec<&Finding> = findings
        .iter()
        .filter(|f| matches!(f.kind, FindingKind::Divergence(_)))
        .collect();
    assert_eq!(divergences.len(), 1, "findings: {findings:#?}");
    let f = divergences[0];
    assert_eq!(f.program_name, "m54_call_arg_parallel_move");
    assert_eq!(f.opt, OptLevel::O0);
    assert_eq!(f.kind, FindingKind::Divergence(DivergenceKind::WrongValue));
    // The finding is the REAL divergence (142 vs 130), not the unrelated one.
    assert!(
        f.detail.contains("llvm_exit=142") && f.detail.contains("trust_cg_exit=130"),
        "finding kept the wrong divergence detail: {}",
        f.detail
    );
    // The reducer KEPT the real bug's call line and did NOT reduce down to the
    // unrelated `a * 27` trigger.
    assert!(
        f.source.contains("sub4(d, c, b, a)"),
        "reducer dropped the REAL bug line: <<<{}>>>",
        f.source
    );
}
