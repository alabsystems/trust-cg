// trust-cg-verify/tests/proof_gate_strict.rs - Strict formal-proof gate test (P0)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the fail-closed external-SMT gate. The full-database test fails when
// no solver is present, when a solver finds a counterexample or errors, or if
// any result falls back to statistical evaluation. Timeout/unknown results are
// explicit solver-capacity PENDING entries: they are reported but are neither
// proofs nor soundness failures. Only the narrow audited allowlist below may
// remain pending; a new timeout/unknown fails the full-database floor closed.
//
// The always-on tests assert the gate contract without requiring a solver.
// `representative_arithmetic_is_formally_verified` is a six-obligation smoke.
// `scripts/check_proof_gate.sh` defaults to the full-database zero-soundness /
// no-statistical-fallback floor and prints the verified/pending split.
//
// Run the full database directly (external solver lane):
//   TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 \
//     cargo test -p trust-cg-verify --test proof_gate_strict \
//       full_database_is_formally_verified -- --test-threads=1
//
// v0.1.0 exposes only the external AY subprocess lane. There is no
// native-AY Cargo feature in this release.
//
// The solver-gated bodies use an explicit
// `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1` qualification gate, so the plain
// `cargo test -p trust-cg-verify --tests` lane does not require a solver. The
// default package-lane contract (no solver => fail closed, never a downgrade)
// is asserted by the always-on `gate_fails_closed_*` / `strict_gate_*` tests.
//
// Historical bugs this locks in (all OUTSIDE the per-instruction SMT core, but
// the gate makes the SMT core itself the mandatory floor and removes the
// statistical-downgrade escape hatch that let them ship):
//   - The select_auto_mode() silent downgrade to MockOnly (the P0 gap itself).
//   - #51 / #66 carrier hygiene (SAR/IDIV sign-ext, SHR/unsigned-DIV zero-ext):
//     the division/shift obligations are discharged formally, not sampled.
//   - #68-fneg (select_fneg emitted 0.0-x with no proof): the FP-lowering
//     obligations now MUST be formally Verified, so an unproven encoder change
//     surfaces as a gate failure rather than a statistical near-miss.
//   - #67 overflow / INT_MIN edge cases: a 64-bit edge that 100K random samples
//     can miss is now decided by the solver.
//
// Reference: crates/trust-cg-verify/src/proof_gate.rs,
//            crates/trust-cg-verify/src/proof_database.rs,
//            crates/trust-cg-verify/src/ay_bridge.rs

use trust_cg_verify::ay_bridge::{AYConfig, z3_available};
use trust_cg_verify::proof_database::{
    GENUINE_IDENTITY_ALLOWLIST, KNOWN_DEGENERATE_PENDING_FIX, ProofDatabase,
};
use trust_cg_verify::proof_gate::{
    FailureClass, GateConfig, GateError, GateReport, native_ay_compiled,
};

/// Run `f` on a 64 MiB stack so `ProofDatabase::new()` does not overflow the
/// default 8 MiB test-thread stack (proof_database.rs #205).
fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("universal-gate".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack universal-gate thread")
        .join()
        .expect("universal-gate thread panicked")
}

const FORMAL_PROOF_TEST_ENV: &str = "TRUST_CG_RUN_FORMAL_PROOF_TESTS";

/// Audited full-database obligations that may remain formally PENDING because
/// their bit-blasts exceed the strict gate's current solver budget. This is an
/// upper bound, not a claim that they must time out: an entry that AY proves is
/// credited as `Verified`, while any pending name outside this list fails the
/// gate. Keep exact registered names so a rename cannot silently inherit debt.
const SOLVER_CAPACITY_PENDING_ALLOWLIST: &[&str] = &[
    "x86_64: Sdiv_I32 -> IDIV r32 (quotient)",
    "x86_64: Sdiv_I64 -> IDIV r64 (quotient)",
    "x86_64: Srem_I32 -> IDIV r32 (remainder)",
    "x86_64: Srem_I64 -> IDIV r64 (remainder)",
    "x86_64: V2I64 even-dword widening Umul -> PMULUDQ xmm,xmm",
];

/// Exact static corpus cardinality after removing duplicate registrations.
/// A change requires auditing both the capacity allowlist and the documented
/// full-gate scope; silently shrinking the database is not a green gate.
const EXPECTED_STATIC_PROOF_OBLIGATION_COUNT: usize = 1_869;

#[test]
fn solver_capacity_pending_allowlist_is_narrow_unique_and_live() {
    on_large_stack(|| {
        use std::collections::HashSet;

        assert_eq!(
            SOLVER_CAPACITY_PENDING_ALLOWLIST.len(),
            5,
            "capacity debt may change only through an explicit audit"
        );
        let unique: HashSet<&str> = SOLVER_CAPACITY_PENDING_ALLOWLIST.iter().copied().collect();
        assert_eq!(
            unique.len(),
            SOLVER_CAPACITY_PENDING_ALLOWLIST.len(),
            "capacity-pending allowlist contains duplicate names"
        );

        let db = ProofDatabase::new();
        assert_eq!(
            db.len(),
            EXPECTED_STATIC_PROOF_OBLIGATION_COUNT,
            "static proof corpus changed; audit the strict-gate scope and capacity allowlist"
        );
        let registered: HashSet<&str> = db
            .all()
            .iter()
            .map(|proof| proof.obligation.name.as_str())
            .collect();
        assert_eq!(
            registered.len(),
            db.len(),
            "registered static proof names must be globally unique because capacity authority is name-bound"
        );
        let ambiguous_or_dead: Vec<(&str, usize)> = SOLVER_CAPACITY_PENDING_ALLOWLIST
            .iter()
            .copied()
            .map(|name| {
                let registrations = db
                    .all()
                    .iter()
                    .filter(|proof| proof.obligation.name == name)
                    .count();
                (name, registrations)
            })
            .filter(|(_, registrations)| *registrations != 1)
            .collect();
        assert!(
            ambiguous_or_dead.is_empty(),
            "each name-bound capacity exception must identify exactly one registered proof: \
             {ambiguous_or_dead:?}"
        );
    });
}

/// Keep external-solver proof campaigns out of the ordinary hermetic test lane
/// without hiding them from libtest. The opt-in must be the exact value `1`;
/// every other value is a visible, deterministic no-op.
fn formal_proof_test_enabled(test_name: &str) -> bool {
    if matches!(std::env::var(FORMAL_PROOF_TEST_ENV).as_deref(), Ok("1")) {
        true
    } else {
        eprintln!(
            "{test_name}: external-solver campaign not requested; \
             set {FORMAL_PROOF_TEST_ENV}=1 to run"
        );
        false
    }
}

// ---------------------------------------------------------------------------
// (i) No silent downgrade: the gate fails closed without a solver.
//
// These run on EVERY lane (no solver required) because they assert the
// *contract*: absent a solver, `discharge` returns Err, never a downgraded Ok.
// ---------------------------------------------------------------------------

#[test]
fn gate_fails_closed_when_no_solver() {
    // ALWAYS-ON, deterministic on EVERY machine: inject `available = false` into
    // the testable core so the single most important P0 guarantee — no solver =>
    // Err(NoSolver), never a downgraded Ok — is asserted unconditionally, even
    // on a normal dev/CI box that has a solver installed. Passing `false`
    // short-circuits before any solver call, so no real solver is invoked.
    //
    // (The previous version of this test early-returned whenever a solver was
    // present, so on every normal machine this guarantee was NEVER asserted.)
    let db = ProofDatabase::new();
    let result = GateConfig::strict().discharge_with_availability(&db, false);
    match result {
        Err(GateError::NoSolver { .. }) => {
            // Correct: refused to downgrade to statistical mock.
        }
        Err(other) => panic!("expected NoSolver, got a different gate error: {}", other),
        Ok(_) => panic!(
            "STRICT GATE REGRESSION: discharge_with_availability(.., false) returned Ok. \
             This is exactly the P0 silent-downgrade bug — the gate must fail closed \
             when no solver is available."
        ),
    }
}

/// A non-strict gate (require_solver = false) must NOT fail closed on absence of
/// a solver — it is the explicit opt-out. This pins that `discharge_with_
/// availability` keys the NoSolver decision on `require_solver`, so the always-on
/// test above is genuinely testing the strict path's fail-closed behaviour and
/// not a blanket reject.
#[test]
fn non_strict_gate_does_not_fail_closed_on_no_solver() {
    let gate = GateConfig {
        ay_config: AYConfig::default(),
        require_solver: false,
    };
    // Empty DB so we don't actually invoke a solver; the point is only that the
    // NoSolver branch is NOT taken when require_solver = false even with
    // available = false. We therefore expect EmptyDatabase, never NoSolver.
    let db = ProofDatabase::from_proofs(vec![]);
    match gate.discharge_with_availability(&db, false) {
        Err(GateError::EmptyDatabase) => {}
        Err(GateError::NoSolver { .. }) => panic!(
            "non-strict gate must not return NoSolver: require_solver = false is the opt-out"
        ),
        other => panic!("expected EmptyDatabase for non-strict empty-DB gate, got {other:?}"),
    }
}

#[test]
fn strict_gate_requires_solver_flag_is_set() {
    // The strict constructor must request a solver. If this flips, the whole
    // gate degrades to the old auto-mode behaviour.
    assert!(
        GateConfig::strict().require_solver,
        "GateConfig::strict() must set require_solver = true"
    );
    assert!(
        GateConfig::default().require_solver,
        "GateConfig::default() must be strict"
    );
}

/// Real-environment smoke (always on, no solver required): when this machine
/// genuinely has NO solver, the PUBLIC `discharge()` (which probes the real
/// environment) must itself fail closed — a final guard that the production
/// entry point, not just the injected core, honours the contract. When a solver
/// IS present this is a no-op (the formal smoke / full-DB tests below cover the
/// solver path). The injected-core test above is the deterministic guarantee;
/// this confirms `discharge()` delegates to it faithfully.
#[test]
fn real_discharge_fails_closed_when_environment_has_no_solver() {
    if native_ay_compiled() || z3_available() {
        eprintln!(
            "solver present; real-environment no-solver branch is a no-op here \
             (deterministic contract covered by gate_fails_closed_when_no_solver)"
        );
        return;
    }
    let db = ProofDatabase::new();
    match GateConfig::strict().discharge(&db) {
        Err(GateError::NoSolver { .. }) => {}
        Ok(_) => {
            panic!("STRICT GATE REGRESSION: real discharge() returned Ok with no solver present")
        }
        Err(other) => panic!("expected NoSolver from real discharge(), got: {}", other),
    }
}

// ---------------------------------------------------------------------------
// (ii) + (iii) Formal discharge of the FULL database.
//
// This is the substantive gate. It requires an `ay`/`z3` binary on PATH (CLI
// formal path). Its explicit environment qualification keeps the plain
// `cargo test -p trust-cg-verify --tests` lane hermetic; the CI wrapper
// (scripts/check_proof_gate.sh) enables the campaign.
// ---------------------------------------------------------------------------

#[test]
fn full_database_is_formally_verified() {
    if !formal_proof_test_enabled("full_database_is_formally_verified") {
        return;
    }

    // (i) A solver MUST be present. If not, this is a hard failure, not a skip:
    //     the whole point of the gate is "no solver => no pass".
    let gate = GateConfig::strict();
    assert!(
        gate.solver_available(),
        "STRICT GATE: no SMT solver available (native ay compiled: {}, z3_available: {}). \
         Install an ay/z3 binary on PATH.",
        native_ay_compiled(),
        z3_available(),
    );

    let db = ProofDatabase::new();
    assert!(!db.is_empty(), "proof database must be non-empty");

    let report = match gate.discharge(&db) {
        Ok(report) => report, // all verified — the ideal outcome
        Err(GateError::NotAllVerified(report)) => report,
        Err(GateError::NoSolver { detail, .. }) => {
            panic!(
                "STRICT GATE FAILED: no solver at discharge time: {}",
                detail
            )
        }
        Err(GateError::EmptyDatabase) => panic!("STRICT GATE FAILED: empty database"),
    };

    // THE ENFORCED GUARANTEE: ZERO soundness failures. A counterexample (the
    // solver DISPROVED the obligation) or an Error (could not even run it) is a
    // hard, non-negotiable fail — that is the only thing that can indicate a
    // miscompile. This is what every push must satisfy.
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "STRICT GATE FAILED (SOUNDNESS): {} obligation(s) the solver DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );

    // PROOF AUTHORITY: solver `unsat` is only a candidate. A proof-bearing
    // success gate must separately require every such candidate to have an
    // exact, hole-free Alethe proof accepted by the independent checker.
    let evidence = report.proof_evidence_summary();
    println!(
        "STRICT PROOF EVIDENCE: checked={} artifacts_emitted={} holey={} \
         checker_rejected={} missing={} solver_unsat_uncertified={} \
         capacity_or_other_pending={}",
        evidence.checked_accepted,
        evidence.artifacts_emitted(),
        evidence.holey,
        evidence.checker_rejected,
        evidence.missing,
        evidence.solver_unsat_uncertified,
        evidence.capacity_or_other_pending,
    );
    assert_eq!(
        evidence.failures(),
        0,
        "STRICT GATE FAILED (PROOF EVIDENCE): holey/rejected/missing/uncertified \
         UNSAT artifacts are never Formal/Certified authority: {evidence:?}"
    );

    // No obligation passed via anything but a formal `Verified`.
    assert_no_statistical_fallback(&report);

    // Solver-capacity PENDING (Timeout/Unknown) is REPORTED, never a pass. The
    // five audited wide x86 bit-vector rows may remain pending; any NEW pending
    // row is a gate failure. A known row may graduate to `Verified`, so the
    // observed pending set may be a subset of the allowlist, never a superset.
    // This preserves load tolerance without letting solver/checker regressions
    // silently widen the formal floor.
    let pending = report.failures_in_class(FailureClass::SolverCapacity);
    let unexpected: Vec<_> = pending
        .iter()
        .copied()
        .filter(|result| !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(&result.name.as_str()))
        .collect();
    assert!(
        unexpected.is_empty(),
        "STRICT GATE FAILED (UNALLOWLISTED PENDING): {} new timeout/unknown obligation(s):\n{}",
        unexpected.len(),
        unexpected
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    if pending.is_empty() {
        assert_eq!(report.verified(), report.total());
        println!(
            "STRICT GATE OK: all {} obligations formally Verified (0 soundness failures).",
            report.total()
        );
    } else {
        println!(
            "STRICT GATE OK: {}/{} formally Verified, 0 soundness failures; \
             {} solver-capacity PENDING (timeouts/unknown — reported, not a pass; \
             audited allowlist only):\n{}",
            report.verified(),
            report.total(),
            pending.len(),
            report.pending_summary(),
        );
    }
}

/// Assert no result counts as a pass via anything but a formal `Verified`.
///
/// The strict gate never calls the statistical mock evaluator, so this can only
/// fail if the gate implementation regresses to admit a non-formal outcome as
/// passing. It is the explicit lock for requirement (iii).
fn assert_no_statistical_fallback(report: &GateReport) {
    // The strict gate counts an obligation as passing ONLY when it is formally
    // `Verified` (never a statistical-mock pass). Lock that property in a way that
    // is compatible with allowlisted solver-capacity PENDING obligations: the
    // number of formally-valid results must equal the reported verified count
    // (nothing non-formal is counted as a pass), and every non-verified result
    // must carry a real failure outcome rather than a silent pass.
    let formally_valid = report
        .results
        .iter()
        .filter(|r| r.is_formally_valid())
        .count();
    assert_eq!(
        formally_valid,
        report.verified(),
        "strict gate counted a non-formal result as verified (statistical-mock fallback?)"
    );
    for r in &report.results {
        assert!(
            r.is_formally_valid() || r.failure_kind().is_some(),
            "obligation '{}' is neither formally Verified nor a recognized failure outcome \
             (possible non-formal pass): {}",
            r.name,
            r.detail(),
        );
    }
}

// ---------------------------------------------------------------------------
// Smaller formal lane: discharge a representative subset so a solver-equipped
// dev box gets fast signal without the full-database wall-clock cost.
// It shares the explicit external-solver qualification used by the full lane.
// ---------------------------------------------------------------------------

#[test]
fn representative_arithmetic_is_formally_verified() {
    if !formal_proof_test_enabled("representative_arithmetic_is_formally_verified") {
        return;
    }

    use trust_cg_verify::proof_database::{CategorizedProof, ProofCategory};

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no solver for representative smoke"
    );

    let full = ProofDatabase::new();
    let subset: Vec<CategorizedProof> = full
        .by_category(ProofCategory::Arithmetic)
        .into_iter()
        .take(6)
        .cloned()
        .collect();
    assert!(!subset.is_empty(), "no arithmetic proofs to discharge");
    let db = ProofDatabase::from_proofs(subset);

    let report = gate
        .discharge(&db)
        .unwrap_or_else(|e| panic!("representative arithmetic gate failed: {}", e));
    assert!(report.all_verified());
    assert_no_statistical_fallback(&report);
}

/// FORMAL floor for the #1111 newly-WIRED opcode->proof bindings: every proof
/// that the coverage gate now demands for a freshly-wired packed-int / CSEL /
/// FP-trio opcode is discharged FORMALLY through z3 with ZERO soundness
/// failures. This is the targeted analogue of `full_database_is_formally_
/// verified` for exactly the obligations whose BINDING this change introduced
/// (no new obligations were authored — these were already registered — so the
/// full-DB gate content is unchanged; this test pins that the SPECIFIC bound
/// proofs discharge formally, not merely statistically).
#[test]
fn wired_packed_csel_fp_bindings_are_formally_verified() {
    if !formal_proof_test_enabled("wired_packed_csel_fp_bindings_are_formally_verified") {
        return;
    }

    use trust_cg_verify::proof_database::CategorizedProof;

    // The EXACT proof-name substrings the coverage gate / verifiers now bind for
    // the newly-wired opcodes. Width/lane-exact, single-instruction lowerings.
    let wired_names: &[&str] = &[
        // x86 bitwise.
        "V128 Band -> PAND xmm,xmm",
        "V128 Bor -> POR xmm,xmm",
        // x86 lane-exact add/sub.
        "V16I8Add -> PADDB",
        "V8I16Add -> PADDW",
        "V4I32Add -> PADDD",
        "V2I64Add -> PADDQ",
        "V16I8Sub -> PSUBB",
        "V8I16Sub -> PSUBW",
        "V4I32Sub -> PSUBD",
        "V2I64Sub -> PSUBQ",
        // x86 lane-exact eq/sgt compare masks.
        "V16I8Icmp_Eq -> PCMPEQB",
        "V8I16Icmp_Eq -> PCMPEQW",
        "V4I32Icmp_Eq -> PCMPEQD",
        "V16I8Icmp_Sgt -> PCMPGTB",
        "V8I16Icmp_Sgt -> PCMPGTW",
        "V4I32Icmp_Sgt -> PCMPGTD",
        // x86 uniform-immediate dword shifts.
        "V4I32 Ishl uniform immediate -> PSLLD",
        "V4I32 Ushr uniform immediate -> PSRLD",
        "V4I32 Sshr uniform immediate -> PSRAD",
        // x86 uniform-immediate qword shifts + the PMULUDQ faithful lane model
        // (the SSE2 vectorizer's packed 64-bit multiply compose).
        "V2I64 Ishl uniform immediate -> PSLLQ",
        "V2I64 Ushr uniform immediate -> PSRLQ",
        "V2I64 even-dword widening Umul -> PMULUDQ",
        // AArch64 conditional selects (64-bit form bound by the verifier).
        "diamond CSEL — if(cond) a else b ≡ CSEL x, a, b, cond (64-bit)",
        "CSINC — if(cond) a else b+1 ≡ CSINC x, a, b, cond (64-bit)",
        "CSNEG — if(cond) a else -b ≡ CSNEG x, a, b, cond (64-bit)",
        // AArch64 FP trio, BOTH widths.
        "Fabs_F32 -> FABS Sd",
        "Fabs_F64 -> FABS Dd",
        "Fsqrt_F32 -> FSQRT Sd",
        "Fsqrt_F64 -> FSQRT Dd",
        "Fdiv_F32 -> FDIV Sd",
        "Fdiv_F64 -> FDIV Dd",
    ];

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no SMT solver for the #1111 wired-bindings formal floor"
    );

    let full = ProofDatabase::new();
    let all = full.all();
    let mut subset: Vec<CategorizedProof> = Vec::with_capacity(wired_names.len());
    for want in wired_names {
        let found = all
            .iter()
            .find(|p| p.obligation.name.contains(want))
            .unwrap_or_else(|| {
                panic!("#1111 wired binding {want:?} resolves to NO registered proof")
            });
        subset.push((*found).clone());
    }
    assert_eq!(
        subset.len(),
        wired_names.len(),
        "every wired binding must resolve to exactly one registered obligation"
    );

    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("#1111 wired-bindings gate errored: {e}"),
    };

    // ZERO soundness failures — a counterexample on any wired proof would mean
    // the binding admits a miscompiled packed/select/FP op (the cardinal sin).
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "#1111 WIRED-BINDINGS SOUNDNESS FAILURE: {} obligation(s) z3 DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    // These are all small, fast obligations: every one should formally verify.
    assert_eq!(
        report.verified(),
        report.total(),
        "every #1111 wired binding must FORMALLY verify (no solver-capacity pending expected)"
    );
}

/// FORMAL floor for the AArch64 16-byte scalar-pair aggregate eightbyte
/// placement proof (added 2026-06-23). The obligation discharges THROUGH the
/// symbolic byte-array memory model (store the two eightbytes at offsets 0/8,
/// re-load into X0/X1, assert reassembly), so it must verify FORMALLY via AY —
/// not merely statistically — with ZERO soundness failures. This pins that the
/// eightbyte→register placement and the `+8` offset are genuinely proven (a
/// wrong/swapped offset refutes), unlike the retracted degenerate pair identity.
#[test]
fn aggregate_placement_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aggregate_placement_proofs_are_formally_verified") {
        return;
    }

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the aggregate-placement formal floor"
    );

    // Both memory-model aggregate-placement proofs: GPR scalar-pair (X0/X1) and
    // FP HFA lanes (S0..S3). Each discharges THROUGH the symbolic byte-array.
    let wanted: &[&str] = &[
        "16-byte aggregate scalar-pair eightbyte placement",
        "4xF32 HFA lane placement",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<_> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!("aggregate placement proof {want:?} resolves to NO registered proof")
                })
                .clone()
        })
        .collect();
    let db = ProofDatabase::from_proofs(subset);

    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("aggregate-placement gate errored: {e}"),
    };

    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AGGREGATE-PLACEMENT SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both aggregate placement proofs (scalar-pair + HFA) must FORMALLY verify via AY"
    );
}

/// FORMAL floor for the AArch64 Mach-O DATA relocation selection proofs
/// (ARM64_RELOC_PAGE21 / ARM64_RELOC_PAGEOFF12 for the local global read,
/// ARM64_RELOC_GOT_LOAD_PAGE21 / ARM64_RELOC_GOT_LOAD_PAGEOFF12 for the
/// function-pointer / extern-symbol GOT load, ARM64_RELOC_UNSIGNED in both its
/// extern abs64 form — compact-unwind / FDE / TLS-descriptor / data slots —
/// and its section-based DWARF-debug rebase form, and the
/// ARM64_RELOC_SUBTRACTOR+UNSIGNED difference pair) added for symbolic
/// data-relocation emission on aarch64-apple-darwin. These obligations encode
/// the LINKER-applied + runtime ADRP/ADD/LDR page arithmetic (resp. the
/// linker's in-place slot application) and assert it equals the intended
///   address (`S + A` for the global / abs64 slot, `G + A` — the GOT slot
///   address — for the GOT rows, `SectFinal + off` for the section-based
///   rebase, `(A + ADDEND) - B` for the difference pair), so they must verify
///   FORMALLY via AY (not merely statistically) with ZERO soundness failures.
///   A wrong relocation row miscompiles EVERY global / fn-pointer access — the
///   cardinal sin — so this pins that each row form is genuinely proven. The
///   negative controls (each row with the wrong r_pcrel / a missing section
///   base / swapped SUBTRACTOR operand roles) must be REFUTED by AY, witnessing
///   that the positive proofs are real equivalences and not tautologies.
#[test]
fn aarch64_macho_data_reloc_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_macho_data_reloc_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_macho_data_reloc_proofs::{
        aarch64_macho_data_relocation_negative_controls, aarch64_macho_data_relocation_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the AArch64 Mach-O data-reloc formal floor"
    );

    // (a) The 7 positive obligations must FORMALLY verify through the strict gate
    //     (resolved by name from the registered ProofDatabase — confirms they are
    //     actually wired into the DB the coverage gate consumes).
    let wanted: &[&str] = &[
        "ARM64_RELOC_PAGE21 ADRP == page(S+A)",
        "ARM64_RELOC_PAGEOFF12 ADRP+ADD == S+A",
        "ARM64_RELOC_GOT_LOAD_PAGE21 ADRP == page(G+A)",
        "ARM64_RELOC_GOT_LOAD_PAGEOFF12 ADRP+LDR == G+A",
        "ARM64_RELOC_UNSIGNED == S + A (extern abs64 pointer slot)",
        "SECTION-BASED ARM64_RELOC_UNSIGNED rebase == SectFinal + off",
        "ARM64_RELOC_SUBTRACTOR(B)+UNSIGNED(A) == A - B",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!(
                        "AArch64 Mach-O data-reloc proof {want:?} resolves to NO registered proof"
                    )
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every AArch64 Mach-O data-reloc proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("AArch64 Mach-O data-reloc gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AARCH64 MACHO DATA-RELOC SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "all AArch64 Mach-O data-reloc proofs (PAGE21 + PAGEOFF12 + GOT_LOAD_PAGE21 + \
         GOT_LOAD_PAGEOFF12 + extern UNSIGNED + section-based UNSIGNED rebase + \
         SUBTRACTOR+UNSIGNED pair) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (a malformed relocation row
    //     with the wrong r_pcrel) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_macho_data_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "AArch64 Mach-O data-reloc NEGATIVE control '{}' returned {}; \
             a wrong encoding must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 7 we discharged.
    assert_eq!(aarch64_macho_data_relocation_proofs().len(), 7);
}

/// FORMAL floor for the AArch64 Mach-O CALL (BRANCH26) relocation proof added for
/// symbolic direct-call emission on aarch64-apple-darwin. The obligation encodes
/// the LINKER-applied + runtime PC-relative branch displacement and asserts it
/// equals the intended call target `S + A`, so it must verify FORMALLY via AY (not
/// merely statistically) with ZERO soundness failures. A wrong call-relocation row
/// miscompiles EVERY direct extern call (drop's `__rust_dealloc`,
/// `_Unwind_Resume`/personality) — so this pins the formal-evidence lane. It does
/// not promote the production inventory row; the negative control (a BRANCH26
/// with the wrong r_pcrel, i.e. an absolute row) must be REFUTED by AY.
#[test]
fn aarch64_macho_call_reloc_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_macho_call_reloc_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_macho_call_reloc_proofs::{
        aarch64_macho_call_relocation_negative_controls, aarch64_macho_call_relocation_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the AArch64 Mach-O call-reloc formal floor"
    );

    // (a) The positive obligation must FORMALLY verify through the strict gate,
    //     resolved by name from the registered ProofDatabase (confirms it is wired
    //     into the DB the coverage gate consumes).
    let want = "ARM64_RELOC_BRANCH26 BL == S+A";
    let full = ProofDatabase::new();
    let all = full.all();
    let found = all
        .iter()
        .find(|p| p.obligation.name.contains(want))
        .unwrap_or_else(|| {
            panic!("AArch64 Mach-O call-reloc proof {want:?} resolves to NO registered proof")
        });
    let db = ProofDatabase::from_proofs(vec![found.clone()]);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("AArch64 Mach-O call-reloc gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AARCH64 MACHO CALL-RELOC SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "the AArch64 Mach-O BRANCH26 call-reloc proof must FORMALLY verify via AY"
    );

    // (b) Soundness witness: the NEGATIVE control (an absolute, wrong-r_pcrel
    //     BRANCH26 row) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_macho_call_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "AArch64 Mach-O call-reloc NEGATIVE control '{}' returned {}; \
             a wrong (absolute) encoding must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 1 we discharged.
    assert_eq!(aarch64_macho_call_relocation_proofs().len(), 1);
}

/// FORMAL floor for the AArch64 Mach-O TLVP (thread-local descriptor) relocation
/// proofs added for the Darwin TLV-descriptor access on aarch64-apple-darwin.
/// These obligations encode the LINKER-applied + runtime ADRP/LDR page arithmetic
/// for the `ARM64_RELOC_TLVP_LOAD_PAGE21` / `ARM64_RELOC_TLVP_LOAD_PAGEOFF12`
/// rows and assert it equals the intended `tlv_descriptor` slot address `D + A`,
/// so they must verify FORMALLY via AY (not merely statistically) with ZERO
/// soundness failures. The negative controls (a TLVP PAGE21 with the wrong
/// r_pcrel, a TLVP PAGEOFF12 with the wrong r_pcrel) must be REFUTED by AY,
/// witnessing the positive proofs are real equivalences and not tautologies.
///
/// NOTE: these proofs certify the relocation ADDRESS ARITHMETIC. The FULL Darwin
/// TLV access is now ALSO emitted by the backend (the `select_tls_ref` TLV
/// sequence — ADRP/LDR to the `tlv_descriptor`, load the thunk, `BLR` through it —
/// plus the `__thread_data`/`__thread_vars` section emission with the
/// `__tlv_bootstrap`/init `ARM64_RELOC_UNSIGNED` relocations), verified
/// end-to-end by link+run
/// (`e2e_aarch64_thread_local_read_is_correct_and_per_thread`). Those are formal
/// evidence and regression coverage, not production Certified authority: this
/// floor pins the page+pageoff arithmetic only. The production relocation
/// registry stays empty until an independently checked gate report is bound to
/// the exact emitted object.
#[test]
fn aarch64_macho_tlvp_reloc_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_macho_tlvp_reloc_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_macho_tlvp_reloc_proofs::{
        aarch64_macho_tlvp_relocation_negative_controls, aarch64_macho_tlvp_relocation_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the AArch64 Mach-O TLVP-reloc formal floor"
    );

    // (a) The 2 positive obligations must FORMALLY verify through the strict gate
    //     (resolved by name from the registered ProofDatabase — confirms they are
    //     actually wired into the DB the coverage gate consumes).
    let wanted: &[&str] = &[
        "ARM64_RELOC_TLVP_LOAD_PAGE21 ADRP == page(D+A)",
        "ARM64_RELOC_TLVP_LOAD_PAGEOFF12 ADRP+LDR == D+A",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!(
                        "AArch64 Mach-O TLVP-reloc proof {want:?} resolves to NO registered proof"
                    )
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every AArch64 Mach-O TLVP-reloc proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("AArch64 Mach-O TLVP-reloc gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AARCH64 MACHO TLVP-RELOC SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both AArch64 Mach-O TLVP-reloc proofs (TLVP_LOAD_PAGE21 + TLVP_LOAD_PAGEOFF12) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (a malformed TLVP relocation
    //     row with the wrong r_pcrel) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_macho_tlvp_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "AArch64 Mach-O TLVP-reloc NEGATIVE control '{}' returned {}; \
             a wrong encoding must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 2 we discharged.
    assert_eq!(aarch64_macho_tlvp_relocation_proofs().len(), 2);
}

/// FORMAL evidence lane for the AArch64 ELF TLS local-exec (TLSLE) relocation
/// obligations. These obligations encode the LINKER-patched +
/// runtime ADD arithmetic for the `R_AARCH64_TLSLE_ADD_TPREL_HI12` (first ADD,
/// `LSL #12`) / `R_AARCH64_TLSLE_ADD_TPREL_LO12_NC` (second ADD) rows and assert
/// the `MRS; ADD; ADD` local-exec sequence reconstructs the thread-local address
/// `TP + TPREL(S+A)`, so they must verify FORMALLY via AY (not merely
/// statistically) with ZERO soundness failures. A wrong bit-field placement /
/// dropped `LSL #12` / dropped ABI range check miscompiles EVERY local-exec
/// thread-local access — so this pins the two TLSLE rows (and the two TLSIE
/// GOT-indirect rows, whose wrong page/scale/alignment likewise miscompiles
/// every initial-exec access) as solver-backed formal evidence. They do not
/// promote production Certified inventory rows: AY is in this lane's trusted
/// computing base, and the current inventory cannot represent that authority
/// distinction or bind this report to an emitted object. The negative controls
/// (dropped `LSL #12`, wrong low slice,
/// missing range check, dropped PC-page subtraction, dropped slot alignment)
/// must be REFUTED by AY.
#[test]
fn aarch64_elf_tls_reloc_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_elf_tls_reloc_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_elf_tls_reloc_proofs::{
        aarch64_elf_tls_relocation_negative_controls, aarch64_elf_tls_relocation_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the AArch64 ELF TLSLE-reloc formal floor"
    );

    // (a) The 5 positive obligations must FORMALLY verify through the strict gate
    //     (resolved by name from the registered ProofDatabase — confirms they are
    //     actually wired into the DB the coverage gate consumes).
    let wanted: &[&str] = &[
        "R_AARCH64_TLSLE_ADD_TPREL_HI12 ADD(LSL#12)",
        "R_AARCH64_TLSLE_ADD_TPREL_LO12_NC ADD;ADD",
        "TLSLE local-exec MRS;ADD;ADD == TP + TPREL(S+A)",
        "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21 ADRP == page(G+A)",
        "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC ADRP+LDR == G+A",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!("AArch64 ELF TLSLE-reloc proof {want:?} resolves to NO registered proof")
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every AArch64 ELF TLSLE-reloc proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("AArch64 ELF TLSLE-reloc gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AARCH64 ELF TLSLE-RELOC SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "all AArch64 ELF TLS-reloc proofs (TLSLE HI12 + LO12_NC + exact-address-under-range, \
         TLSIE GOTTPREL page + slot address) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (dropped LSL#12, wrong low
    //     slice, missing ABI range check) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_elf_tls_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "AArch64 ELF TLSLE-reloc NEGATIVE control '{}' returned {}; \
             a wrong encoding / dropped range check must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 5 we discharged
    //     (3 TLSLE + 2 TLSIE).
    assert_eq!(aarch64_elf_tls_relocation_proofs().len(), 5);
}

/// FORMAL floor for the coroutine-suspend (yield) frame save/restore proofs. The
/// `Inst::CoroSuspend` lowering macro-expands to "store i64 next_state into
/// frame[state_slot]; return value". These obligations discharge THROUGH the
/// symbolic byte-array memory model (QF_ABV) — the state store at byte offset
/// `state_slot*8` reloads `next_state`, and the state store preserves the
/// independently-yielded return `value` (disjoint slot) — so they must verify
/// FORMALLY via AY (not merely statistically) with ZERO soundness failures. A
/// wrong store offset (`state_slot*4`) or an aliasing value placement REFUTES, so
/// this pins the suspend glue wires the resume-state and yielded value correctly.
#[test]
fn coroutine_frame_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("coroutine_frame_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::coroutine_frame_proofs::{
        all_coroutine_frame_proofs, coroutine_frame_negative_controls,
    };
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the coroutine-frame formal floor"
    );

    // (a) The 2 positive obligations must FORMALLY verify through the strict gate
    //     (resolved by name from the registered ProofDatabase — confirms they are
    //     wired into the DB the coverage gate consumes).
    let wanted: &[&str] = &[
        "CoroSuspend: state store at frame[state_slot] (offset slot*8) reloads next_state",
        "CoroSuspend: state store preserves the yielded value (disjoint slot)",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!("coroutine-frame proof {want:?} resolves to NO registered proof")
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every coroutine-frame proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("coroutine-frame gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "COROUTINE-FRAME SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both coroutine-frame proofs (state save + value independence) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (a wrong store offset, an
    //     aliasing value placement) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in coroutine_frame_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "coroutine-frame NEGATIVE control '{}' returned {}; a wrong placement must \
             produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 2 we discharged.
    assert_eq!(all_coroutine_frame_proofs().len(), 2);
}

/// FORMAL floor for the Darwin aarch64 TLV thunk-call (indirect descriptor
/// resolver) proof. The emitted `select_tls_ref` Tlv sequence loads the resolver
/// from the materialized descriptor and invokes it with the descriptor address;
/// this obligation proves the emitted sequence passes the CORRECT descriptor
/// argument (the ADRP/LDR page+pageoff reconstruction of `D`) through the
/// argument-sensitive thunk model `thunk(arg) = arg + thunk_off`, so it must
/// verify FORMALLY via AY with ZERO soundness failures. The negative controls (a
/// wrong call argument `D+8`, a dropped indirection returning `D`) must be REFUTED
/// by AY, witnessing the positive proof is a real equivalence (not a tautology).
/// This complements the TLVP relocation lane (which proves the address arithmetic
/// that materializes `D`).
#[test]
fn aarch64_tlv_thunk_proof_is_formally_verified() {
    if !formal_proof_test_enabled("aarch64_tlv_thunk_proof_is_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_tlv_thunk_proofs::{
        aarch64_tlv_thunk_negative_controls, aarch64_tlv_thunk_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the TLV thunk-call formal floor"
    );

    // (a) The positive obligation must FORMALLY verify through the strict gate,
    //     resolved by name from the registered ProofDatabase.
    let want = "TLV thunk-call: emitted ADRP/LDR/LDR/BLR computes thunk(D) == &var";
    let full = ProofDatabase::new();
    let all = full.all();
    let found = all
        .iter()
        .find(|p| p.obligation.name.contains(want))
        .unwrap_or_else(|| panic!("TLV thunk-call proof {want:?} resolves to NO registered proof"));
    let db = ProofDatabase::from_proofs(vec![found.clone()]);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("TLV thunk-call gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "TLV THUNK-CALL SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "the TLV thunk-call proof must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (wrong call argument, missing
    //     indirection) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_tlv_thunk_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "TLV thunk-call NEGATIVE control '{}' returned {}; a wrong indirection must \
             produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 1 we discharged.
    assert_eq!(aarch64_tlv_thunk_proofs().len(), 1);
}

/// FORMAL floor for the aarch64 LSDA EH call-site / catch-all dispatch encoding
/// proofs. For a `catch(...)` landing pad, the personality dispatches an in-range
/// exception to the landing pad ONLY with a POSITIVE type filter (match-any NULL
/// TType slot), and a PC past the half-open call-site range does NOT dispatch.
/// These obligations encode the personality's range/dispatch reconstruction and
/// must verify FORMALLY via AY with ZERO soundness failures. The negative controls
/// (a cleanup `type_filter=0` catch-all that does NOT dispatch, a closed-range
/// over-claim at the boundary) must be REFUTED by AY — witnessing the
/// catch-vs-cleanup type-filter distinction and the half-open range bound are
/// load-bearing (a wrong encoding silently drops the catch and terminates).
#[test]
fn aarch64_eh_lsda_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_eh_lsda_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_eh_lsda_proofs::{
        aarch64_eh_lsda_negative_controls, aarch64_eh_lsda_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the LSDA EH formal floor"
    );

    // (a) The 2 positive obligations must FORMALLY verify through the strict gate.
    let wanted: &[&str] = &[
        "LSDA EH: catch(...) in-range dispatch lands on func_start+landing_pad",
        "LSDA EH: out-of-range PC (region end) does not dispatch (half-open range)",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| panic!("LSDA EH proof {want:?} resolves to NO registered proof"))
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every LSDA EH proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("LSDA EH gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "LSDA EH SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both LSDA EH proofs (catch-all dispatch + out-of-range non-dispatch) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (cleanup type-filter, closed
    //     range over-claim) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_eh_lsda_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "LSDA EH NEGATIVE control '{}' returned {}; a wrong encoding must produce a \
             CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 2 we discharged.
    assert_eq!(aarch64_eh_lsda_proofs().len(), 2);
}

/// FORMAL floor for the aarch64 LSDA EH call-site TABLE COVERAGE / PARTITION
/// proofs — the invariant the abstract dispatch proof
/// (`aarch64_eh_lsda_proofs_are_formally_verified`) ASSUMES and that
/// `resolve_eh_offsets` filler synthesis (pipeline.rs:6720-6802) establishes.
/// The resolved call-site table covers `[0, code_len)` EXACTLY ONCE (no gap =>
/// the personality never `std::terminate()`s on an in-flight PC; no overlap =>
/// `scan_eh_table` selects a single record), and an Invoke PC maps to a region
/// carrying the Invoke's own landing pad (not a filler's 0). These obligations
/// encode the reconstructed HEAD/explicit/TAIL table over a bounded `forall pc`
/// and MUST verify FORMALLY via AY with ZERO soundness failures and NO
/// statistical fallback. The negative controls (a dropped tail filler leaving a
/// gap; a zero-pad filler over the Invoke PC) MUST be REFUTED by AY — witnessing
/// the filler coverage and the explicit-region-pad-wins invariants are
/// load-bearing (the real cleanup-PC-terminate bug `resolve_eh_offsets` fixes).
#[test]
fn aarch64_eh_coverage_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_eh_coverage_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_eh_coverage_proofs::{
        aarch64_eh_coverage_negative_controls, aarch64_eh_coverage_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no AY solver for the LSDA EH coverage formal floor"
    );

    // (a) The 2 positive obligations must FORMALLY verify through the strict gate.
    let wanted: &[&str] = &[
        "LSDA EH: resolved call-site table covers [0,code_len) exactly once (partition)",
        "LSDA EH: Invoke PC maps to region with the Invoke's landing pad (not 0)",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!("LSDA EH coverage proof {want:?} resolves to NO registered proof")
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every LSDA EH coverage proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("LSDA EH coverage gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "LSDA EH coverage SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both LSDA EH coverage proofs (total coverage/partition + Invoke->pad mapping) must \
         FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (dropped tail filler => gap;
    //     zero-pad filler over the Invoke PC => selects 0) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_eh_coverage_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "LSDA EH coverage NEGATIVE control '{}' returned {}; a wrong table (gap / zero-pad \
             filler over an Invoke PC) must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 2 we discharged.
    assert_eq!(aarch64_eh_coverage_proofs().len(), 2);
}

/// FORMAL floor for the #67 checked-overflow DETECTION obligations, at HONEST
/// per-strength granularity (ZERO soundness failures everywhere):
///   - the 4 add/sub i64 obligations (AddsRR/SubsRR carriers) discharge FORMALLY
///     and fast via ay/z3 — verified()==total();
///   - the 2 mul i64 obligations carry a GENUINE (non-degenerate) 64-bit
///     equivalence theorem that is SMT-hard (128-bit bvmul) — every non-verified
///     one is SolverCapacity PENDING (timeout/unknown), NEVER a 64-bit formal
///     claim and NEVER a counterexample;
///   - the 2 width-8 mul-equivalence anchors discharge FORMALLY at width-8,
///     witnessing the honest "exhaustive/formal at w=8, 64-bit pending" claim
///     that backs the Smulh/Umulh allowlist reason.
///     All obligations are asserted structurally non-degenerate (X != X-side). Run
///     with `AY_SOLVER_PATH` pointed at the improved ay binary.
#[test]
fn wired_checked_overflow_bindings_are_formally_verified() {
    if !formal_proof_test_enabled("wired_checked_overflow_bindings_are_formally_verified") {
        return;
    }

    use trust_cg_verify::proof_database::CategorizedProof;

    // HONEST per-strength split (#67). Each obligation packs `overflow_b1 ::
    // value_iN` and models the real AArch64 flag predicate; all are
    // non-degenerate (trust_ir_expr != aarch64_expr).
    //
    //  - FORMAL_NAMES: the 4 add/sub i64 obligations. These discharge FORMALLY
    //    via ay and fast (no multiply hardness) — they MUST verify==total.
    //  - MUL_I64_NAMES: the 2 mul i64 obligations. The genuine 64-bit
    //    equivalence theorem is SMT-hard (128-bit bvmul times out). They carry
    //    ZERO soundness failures, but their FORMAL discharge is capacity-pending
    //    — we EXPECT them in FailureClass::SolverCapacity and do NOT claim a
    //    64-bit formal proof.
    //  - MUL_I8_ANCHOR_NAMES: the 2 width-8 mul-equivalence proofs. These are the
    //    HONEST mul evidence and MUST formally verify at width-8.
    let formal_names: &[&str] = &[
        "CheckedSadd_I64 -> ADDS+CSET_VS",
        "CheckedSsub_I64 -> SUBS+CSET_VS",
        "CheckedUadd_I64 -> ADDS+CSET_HS",
        "CheckedUsub_I64 -> SUBS+CSET_LO",
    ];
    let mul_i64_names: &[&str] = &[
        "CheckedSmul_I64 -> MUL+SMULH+ASR+CMP+CSET_NE",
        "CheckedUmul_I64 -> MUL+UMULH+CMP0+CSET_NE",
    ];
    let mul_i8_anchor_names: &[&str] = &[
        "CheckedSmul_I8 exact product overflow",
        "CheckedUmul_I8 exact product overflow",
    ];

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    assert!(
        gate.solver_available(),
        "no SMT solver for the #67 wired checked-overflow formal floor"
    );

    let full = ProofDatabase::new();
    let all = full.all();
    let resolve = |want: &str| -> CategorizedProof {
        all.iter()
            .find(|p| p.obligation.name.contains(want))
            .unwrap_or_else(|| {
                panic!(
                    "#67 wired checked-overflow binding {want:?} resolves to NO registered proof"
                )
            })
            .clone()
    };

    // STRUCTURAL NON-DEGENERACY (f81e45b / X==X guard) over EVERY checked-overflow
    // obligation involved here — add/sub AND mul, i64 AND i8 — so an X==X can
    // never silently pass for any of them regardless of which gate binds them.
    for want in formal_names
        .iter()
        .chain(mul_i64_names)
        .chain(mul_i8_anchor_names)
    {
        let p = resolve(want);
        assert_ne!(
            p.obligation.trust_ir_expr, p.obligation.aarch64_expr,
            "#67 DEGENERATE (X==X) checked-overflow proof {want:?}: proves nothing"
        );
    }

    // (1) add/sub i64: MUST formally verify, verified()==total(), zero pending.
    let formal_subset: Vec<CategorizedProof> = formal_names.iter().map(|w| resolve(w)).collect();
    let formal_report = match gate.discharge(&ProofDatabase::from_proofs(formal_subset)) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("#67 add/sub checked-overflow gate errored: {e}"),
    };
    assert!(
        formal_report.soundness_failures().is_empty(),
        "#67 ADD/SUB SOUNDNESS FAILURE: {}",
        formal_report
            .soundness_failures()
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&formal_report);
    assert_eq!(
        formal_report.verified(),
        formal_report.total(),
        "every #67 add/sub checked-overflow binding MUST formally verify (they are not SMT-hard)"
    );

    // (2) mul i64: ZERO soundness failures, but FORMAL discharge is capacity-
    //     pending (timeout/unknown). We require NO counterexample, and that every
    //     non-verified mul is SolverCapacity PENDING — NOT a 64-bit formal claim.
    let mul_subset: Vec<CategorizedProof> = mul_i64_names.iter().map(|w| resolve(w)).collect();
    let mul_report = match gate.discharge(&ProofDatabase::from_proofs(mul_subset)) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("#67 mul checked-overflow gate errored: {e}"),
    };
    assert!(
        mul_report.soundness_failures().is_empty(),
        "#67 MUL SOUNDNESS FAILURE (counterexample/error — NOT mere capacity): {}",
        mul_report
            .soundness_failures()
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&mul_report);
    let mul_pending = mul_report.failures_in_class(FailureClass::SolverCapacity);
    // Every mul i64 that did not formally verify must be SolverCapacity PENDING
    // (timeout/unknown), never a silent pass. Empirically both time out, but we
    // tolerate a faster machine formally verifying them too — what we forbid is
    // counting them as a 64-bit formal claim when they are merely capacity-bound.
    assert_eq!(
        mul_report.verified() + mul_pending.len(),
        mul_report.total(),
        "#67 mul i64: every non-verified obligation must be SolverCapacity PENDING, \
         never a silent/non-formal pass"
    );

    // (3) width-8 mul-equivalence anchor: MUST formally verify.
    let anchor_subset: Vec<CategorizedProof> =
        mul_i8_anchor_names.iter().map(|w| resolve(w)).collect();
    let anchor_report = match gate.discharge(&ProofDatabase::from_proofs(anchor_subset)) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("#67 width-8 mul-anchor gate errored: {e}"),
    };
    assert!(
        anchor_report.soundness_failures().is_empty(),
        "#67 WIDTH-8 MUL-ANCHOR SOUNDNESS FAILURE: {}",
        anchor_report
            .soundness_failures()
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&anchor_report);
    assert_eq!(
        anchor_report.verified(),
        anchor_report.total(),
        "the width-8 mul-equivalence anchor MUST formally verify (exhaustive/formal at w=8)"
    );
}

// ===========================================================================
// UNIVERSAL NON-DEGENERACY GATE (Strategy C, task #53)
// ===========================================================================
//
// Generalizes the per-family `assert_ne` guards (the #67 checked-overflow
// family above, and the RISC-V comparison idioms in coverage_gate_tests.rs)
// to EVERY proof in `ProofDatabase::new()`.
//
// A lowering proof whose `trust_ir_expr` is STRUCTURALLY identical to its
// machine (`aarch64_expr`) side (`SmtExpr` derives `PartialEq`) proves nothing
// — the f81e45b X==X lie — UNLESS the lowering genuinely IS a 1:1 identity
// built by INDEPENDENT encoders (e.g. `Iadd -> ADD`: both independently denote
// `bvadd`; a wrong opcode `Iadd -> SUB` would yield `bvadd == bvsub` and
// refute). Those audited genuine identities live on
// `GENUINE_IDENTITY_ALLOWLIST`; the audited SUSPICIOUS self-equalities that
// still need a faithful re-derivation live on the SHRINKING debt ledger
// `KNOWN_DEGENERATE_PENDING_FIX` (which is NOT a genuineness claim).
//
// The gate is FAIL-CLOSED: a degenerate proof on NEITHER list is a violation
// and FAILS the build, so a FUTURE degenerate proof can never silently
// register.

/// Pinned length of the genuine-identity allowlist. Bump deliberately ONLY when
/// a new audited genuine 1:1 identity lowering is added (and never to silence a
/// suspicious self-equality — those go on the debt ledger, or better, get
/// fixed).
///
/// HONESTY (task #61): lowered 461 -> 433. The auditor found 28 MIS-FILED entries
/// that were never genuine independent-encoder identities — the 16 CAS/atomic-RMW
/// "returns old value" self-equalities (both sides via `encode_load_le` => X==X)
/// and the 12 scalar shift proofs (`bvshl==bvshl` / `bvlshr==bvlshr` /
/// `bvashr==bvashr`; the #57 precondition is added identically to both sides and
/// is cosmetic). They were moved to the DEBT ledger below, where they belong.
// +6 (2026-06-27): the AArch64 FRINT round-to-integral family — Ffloor/Fceil/
// Ftrunc x {F32,F64} -> FRINTM/FRINTP/FRINTZ. Single-instruction 1:1 identities
// in the same audited category as Fneg/Fabs/Fsqrt (machine side opcode-keyed via
// encode_frint{m,p,z}); on-host execution proves the lowerings bit-exact.
// -20 (2026-06-28): the scalar-FP gap closure made encode_fcmp FAITHFUL (FCMP→
// NZCV then CSET reading from_floatcc(cond), via the nzcv flag table). The 20
// Fcmp conditions whose CSET flag-reading is STRUCTURALLY DISTINCT from the
// source predicate — GE/GT/LE/Ord and ALL the Unordered-* forms x {F32,F64} —
// became GENUINELY PROVEN (no longer X==X) and were removed from the allowlist.
// Only the 8 that read a single flag equal to the source (Eq/NE/LT/Uno x
// {F32,F64}) remain as audited 1:1 identities.
// +1 (419 -> 420): SLICE 3 -- "x86_64: SeqCst fence -> MFENCE single-thread
// identity". MFENCE's single-thread semantics IS the (register, memory) identity
// (writes no register / no memory), so its faithful obligation is necessarily
// structurally degenerate -- the same audited class as AtomicLoad/reg-reg copy,
// witnessed non-vacuous by refuting clobber-register / clobber-memory negative
// controls. NOT the retracted #62 encoding tautology.
// +2 (420 -> 422): the Faulhaber closed-form BASE CASES "ClosedForm: sum_i m=1"
// and "ClosedForm: sum_i2 m=1" (9736a62 registered them unclassified and the
// non-degeneracy gate correctly FIRED red). At m=1 both sides fold to `x + 0`,
// structurally X==X -- but only because s1_of(1)/s2_of(1) are CORRECT (a wrong
// constant would have produced distinct sides and refuted at registration);
// the m>=2 siblings carry the family's genuine refutability. Audited-genuine,
// same footing as the MFENCE / AtomicLoad identities.
// -2 (422 -> 420): the two Faulhaber m=1 base cases were RETRACTED from the
// allowlist because their obligations are now GENUINELY non-degenerate. The
// closed-form side of `proof_sum_i`/`proof_sum_i2` is now the EXPRESSION TREE
// `s1_expr`/`s2_expr` (`m(m-1)/2`, `m(m-1)(2m-1)/6`) instead of a pre-folded
// constant, so even at m=1 (`x + (1·0 >> 1)`) it is structurally distinct from
// the loop fold and refutes a wrong closed form -- it no longer belongs on the
// degenerate-identity allowlist.
// -4 (420 -> 416): Sdiv_I32/I64 -> SDIVWrr/Xrr and Udiv_I32/I64 -> UDIVWrr/Xrr
// removed 2026-07-12. Their AArch64 division-lowering proofs are no longer
// degenerate (a genuine machine model, not an X==X identity), so the four
// identity exemptions were DEAD and masking a possible regression per
// genuine_allowlist_is_tight_and_live. Coverage of those opcodes still holds
// through the now-genuine proofs.
const GENUINE_ALLOWLIST_LEN: usize = 416;

/// Pinned UPPER BOUND on the known-degenerate debt ledger. This is a RATCHET:
/// the ledger may only SHRINK as suspicious proofs are given faithful
/// independent-encoder obligations (task #53 follow-up). It must NEVER grow to
/// admit a NEW degenerate proof — fix the proof instead.
///
/// HONESTY (task #61): raised 440 -> 468 ONCE, to absorb a RECLASSIFICATION
/// (not new debt) of 28 mis-filed entries removed from GENUINE_IDENTITY_ALLOWLIST.
///
/// CAPSTONE (task #62): lowered 468 -> 0. Every degenerate-debt proof has now been
/// RETRACTED — the non-lowering vacuous families were DELETED from the proof
/// builders, and the reconstruction-superseded static lowerings were removed
/// because operand reconstruction is the genuine coverage. The debt ledger is
/// EMPTY: the database contains zero degenerate-debt proofs. The ratchet now pins
/// it at zero — a new degenerate proof can never be admitted; it must be given a
/// faithful independent-encoder obligation instead.
const DEBT_LEDGER_MAX_LEN: usize = 0;

/// THE universal non-degeneracy gate. Iterates EVERY registered proof and
/// requires each to be EITHER non-degenerate (`trust_ir_expr != aarch64_expr`,
/// so a wrong machine choice would refute) OR classified — on
/// `GENUINE_IDENTITY_ALLOWLIST` (audited genuine identity) or on the disclosed,
/// shrinking `KNOWN_DEGENERATE_PENDING_FIX` debt ledger. An unclassified
/// degenerate proof FAILS (fail-closed).
#[test]
fn universal_non_degeneracy_gate() {
    let violations = on_large_stack(|| {
        ProofDatabase::new()
            .non_degeneracy_violations()
            .into_iter()
            .map(|v| v.name)
            .collect::<Vec<_>>()
    });
    assert!(
        violations.is_empty(),
        "UNIVERSAL NON-DEGENERACY GATE FAILED (Strategy C, task #53): {} degenerate \
         proof(s) have trust_ir_expr STRUCTURALLY identical to their machine side and are \
         on NEITHER the audited GENUINE_IDENTITY_ALLOWLIST NOR the KNOWN_DEGENERATE_PENDING_FIX \
         debt ledger. A degenerate proof proves nothing (the f81e45b X==X lie) unless the \
         lowering is a genuine independent-encoder 1:1 identity. FIX each by giving it a \
         faithful independent machine-side obligation (so a wrong opcode/instruction/placement \
         refutes); do NOT add a self-equality to the genuine allowlist. Offending proofs:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

/// The genuine allowlist must be TIGHT and LIVE: every name on it must be (a)
/// actually registered in the database and (b) actually degenerate. A name that
/// is non-degenerate (or absent) is a DEAD entry — it would mask a future
/// regression where that proof silently becomes a degenerate X==X yet still
/// "passes" because it is pre-allowlisted. Dead entries must be removed.
#[test]
fn genuine_allowlist_is_tight_and_live() {
    use std::collections::HashSet;
    let degen: HashSet<String> = on_large_stack(|| {
        ProofDatabase::new()
            .degenerate_proof_names()
            .into_iter()
            .collect()
    });

    assert_eq!(
        GENUINE_IDENTITY_ALLOWLIST.len(),
        GENUINE_ALLOWLIST_LEN,
        "GENUINE_IDENTITY_ALLOWLIST length changed; update GENUINE_ALLOWLIST_LEN \
         deliberately (only for a genuinely-audited new 1:1 identity)."
    );

    // No duplicate names within the allowlist.
    let unique: HashSet<&&str> = GENUINE_IDENTITY_ALLOWLIST.iter().collect();
    assert_eq!(
        unique.len(),
        GENUINE_IDENTITY_ALLOWLIST.len(),
        "GENUINE_IDENTITY_ALLOWLIST contains duplicate names"
    );

    let dead: Vec<&str> = GENUINE_IDENTITY_ALLOWLIST
        .iter()
        .copied()
        .filter(|n| !degen.contains(*n))
        .collect();
    assert!(
        dead.is_empty(),
        "GENUINE_IDENTITY_ALLOWLIST has {} DEAD entr(y/ies) — either not registered or no longer \
         degenerate (so the exemption is masking a possible regression). Remove them:\n{}",
        dead.len(),
        dead.join("\n")
    );
}

/// The debt ledger is a RATCHET that may only shrink, must be disjoint from the
/// genuine allowlist (a suspicious proof can never be silently reclassified as
/// genuine), and must be LIVE (every entry actually registered and degenerate).
#[test]
fn debt_ledger_is_disjoint_shrinking_and_live() {
    use std::collections::HashSet;
    let degen: HashSet<String> = on_large_stack(|| {
        ProofDatabase::new()
            .degenerate_proof_names()
            .into_iter()
            .collect()
    });

    assert!(
        KNOWN_DEGENERATE_PENDING_FIX.len() == DEBT_LEDGER_MAX_LEN,
        "KNOWN_DEGENERATE_PENDING_FIX GREW to {} (cap {}). The debt ledger is a fail-closed \
         RATCHET: it may only shrink as suspicious proofs are made non-degenerate. Raising the \
         cap to admit a new degenerate proof is forbidden — fix the proof instead.",
        KNOWN_DEGENERATE_PENDING_FIX.len(),
        DEBT_LEDGER_MAX_LEN
    );

    // No duplicates within the ledger.
    let ledger: HashSet<&&str> = KNOWN_DEGENERATE_PENDING_FIX.iter().collect();
    assert_eq!(
        ledger.len(),
        KNOWN_DEGENERATE_PENDING_FIX.len(),
        "KNOWN_DEGENERATE_PENDING_FIX contains duplicate names"
    );

    // Disjoint from the genuine allowlist: a suspicious proof must never be
    // dressed up as a genuine identity.
    let genuine: HashSet<&&str> = GENUINE_IDENTITY_ALLOWLIST.iter().collect();
    let overlap: Vec<&str> = KNOWN_DEGENERATE_PENDING_FIX
        .iter()
        .copied()
        .filter(|n| genuine.contains(&n))
        .collect();
    assert!(
        overlap.is_empty(),
        "name(s) appear on BOTH GENUINE_IDENTITY_ALLOWLIST and KNOWN_DEGENERATE_PENDING_FIX — a \
         suspicious proof must never be silently reclassified as genuine:\n{}",
        overlap.join("\n")
    );

    // Live: every ledger entry must be a currently-registered, degenerate proof.
    let dead: Vec<&str> = KNOWN_DEGENERATE_PENDING_FIX
        .iter()
        .copied()
        .filter(|n| !degen.contains(*n))
        .collect();
    assert!(
        dead.is_empty(),
        "KNOWN_DEGENERATE_PENDING_FIX has {} DEAD entr(y/ies) — fixed or removed proofs must be \
         deleted from the ledger (and DEBT_LEDGER_MAX_LEN lowered):\n{}",
        dead.len(),
        dead.join("\n")
    );
}

/// PROVES THE GATE HAS TEETH (fail-closed): inject a synthetic degenerate proof
/// (`X == X`) whose name is on NEITHER list and confirm the universal gate
/// reports it as a violation. This is the negative test that locks in that a
/// future degenerate proof cannot silently slip through.
#[test]
fn universal_gate_fails_closed_on_injected_degenerate_proof() {
    use trust_cg_verify::lowering_proof::ProofObligation;
    use trust_cg_verify::proof_database::{CategorizedProof, ProofCategory};
    use trust_cg_verify::smt::SmtExpr;

    let x = SmtExpr::var("x", 64);
    let injected = CategorizedProof {
        obligation: ProofObligation {
            machine_side_provenance:
                trust_cg_verify::lowering_proof::MachineSideProvenance::StaticDb,
            name: "INJECTED degenerate X==X (must fail the gate)".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x, // structurally identical -> degenerate, no independent model
            inputs: vec![("x".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        },
        category: ProofCategory::Arithmetic,
    };

    let db = on_large_stack(|| {
        let mut proofs: Vec<CategorizedProof> = ProofDatabase::new().all().to_vec();
        proofs.push(injected);
        ProofDatabase::from_proofs(proofs)
    });

    let violations: Vec<String> = db
        .non_degeneracy_violations()
        .into_iter()
        .map(|v| v.name)
        .collect();
    assert_eq!(
        violations,
        vec!["INJECTED degenerate X==X (must fail the gate)".to_string()],
        "the universal gate must report EXACTLY the injected degenerate proof as a violation \
         (and nothing else): otherwise the gate is not fail-closed, or the real registry \
         regressed. Got: {violations:?}"
    );
}
