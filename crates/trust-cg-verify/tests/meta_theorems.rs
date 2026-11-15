// trust-cg-verify/tests/meta_theorems.rs — DELIVERABLE 1 of task #54 (D engine).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// PROPERTIES, NOT VALUES — universal invariant meta-theorems.
// ===========================================================================
//
// Each test here asserts a UNIVERSAL PROPERTY quantified over the WHOLE proof
// database / gate / opcode universe — never an incidental value. The point of D
// is that these invariants must be IMPOSSIBLE TO SATISFY VACUOUSLY: break the
// underlying gate (A fail-closed classifier, C non-degeneracy gate, the
// reconstruction credit rule, the fsym deref-coverage invariant) and one of
// these meta-theorems MUST go red. The companion `mutation_catalog.rs` provides
// the constructive negative side (inject a fault, a NAMED gate rejects it); this
// file provides the universally-quantified positive side.
//
// The invariants asserted (one per `(a)`..`(e)` requirement of task #54):
//   (a) NO registered proof is degenerate-and-unclassified (X==X with no audited
//       reason): `forall p in DB. !degenerate(p) || classified(p)`.
//   (b) EVERY emittable opcode of EVERY backend is CLASSIFIED — the four
//       `classify_<arch>` matches are total (wildcard-free): no opcode falls
//       through to a fail-open default. Asserted by classifying every member of
//       each `ALL_<arch>_OPCODES` universe and requiring a typed `OpcodeClass`.
//   (c) EVERY coverage credit is keyed on `is_reconstructed() && Valid` (or an
//       explicit non-degenerate discharged DB proof) — a static-DB X==X can
//       NEVER be credited: `forall covered emittable row. its credit came from a
//       NON-degenerate obligation`.
//   (d) EVERY deref/memory obligation is accounted-for or fails closed (the fsym
//       A-invariant): a report carrying ANY `FsymCoverageError` is rejected by
//       `has_coverage_error()`; an empty list passes. The gate decision keys on
//       the coverage-error list, not on silence.
//   (e) removed: the per-backend coverage pins live with their named RED
//       lists in coverage_gate_tests (`aarch64_emittable_coverage_is_honest_under_strict`,
//       `x86_emittable_coverage_is_honest_under_strict`,
//       `riscv_inventory_pins_accepted_and_deferred_rows`,
//       `wasm_inventory_pins_accepted_and_deferred_rows`) and the wasm
//       sub-inventory gates (`wasm_value_domain_gate`, `wasm_cfg_structural_gate`,
//       `wasm_abi_proofs_gate`).

use std::collections::HashSet;

use trust_cg_ir::{AArch64Opcode, RiscVOpcode, WasmOpcode, X86Opcode};

use trust_cg_verify::coverage_gate::{
    ALL_AARCH64_OPCODES, ALL_RISCV_OPCODES, ALL_WASM_OPCODES, ALL_X86_OPCODES, CoverageGate,
    GateArch, OpcodeClass, classify_aarch64, classify_riscv, classify_wasm, classify_x86,
};
use trust_cg_verify::fsym_trust_ir::{FsymCoverageError, FsymTrustIrReport};
use trust_cg_verify::lowering_proof::MachineSideProvenance;
use trust_cg_verify::proof_database::{
    ProofDatabase, is_genuine_identity, is_known_degenerate_debt,
};

// ---------------------------------------------------------------------------
// `ProofDatabase::new()` materializes thousands of obligations; do it on a big
// scratch thread to match the rest of the gate suites (proof_gate_strict.rs).
// ---------------------------------------------------------------------------
fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("meta-theorems".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn scratch thread")
        .join()
        .expect("scratch thread panicked")
}

// ===========================================================================
// (a) META-THEOREM: every registered proof is non-degenerate OR audited.
// ===========================================================================
//
// INVARIANT: `forall p in ProofDatabase. is_genuinely_proven(p) OR
//             is_genuine_identity(p.name) OR is_known_degenerate_debt(p.name)`.
//
// This is the C non-degeneracy gate, re-stated as a universal property and
// re-derived HERE (not by calling `non_degeneracy_violations`, so the test has
// independent teeth): we iterate the WHOLE DB and re-check the disjunction. A
// new degenerate proof that proves nothing (X==X) and is on neither audited list
// fails this — exactly the f81e45b lie the gate exists to forbid.
#[test]
fn meta_a_no_proof_is_degenerate_and_unclassified() {
    let offenders = on_large_stack(|| {
        let db = ProofDatabase::new();
        db.all()
            .iter()
            .filter_map(|cp| {
                let o = &cp.obligation;
                // degenerate (X==X) AND on NEITHER audited list -> a violation.
                let degenerate = o.trust_ir_expr == o.aarch64_expr;
                let classified = is_genuine_identity(&o.name) || is_known_degenerate_debt(&o.name);
                if degenerate && !classified {
                    Some(o.name.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
    });
    assert!(
        offenders.is_empty(),
        "META-THEOREM (a) VIOLATED: {} registered proof(s) are DEGENERATE (trust_ir_expr == \
         aarch64_expr, an X==X self-equality that proves nothing) yet on NEITHER the audited \
         GENUINE_IDENTITY_ALLOWLIST NOR the KNOWN_DEGENERATE_PENDING_FIX ledger. A degenerate \
         proof can never refute a wrong lowering. Offenders:\n{}",
        offenders.len(),
        offenders.join("\n")
    );

    // Cross-check the property against the gate's own enumeration: the universal
    // re-derivation above must agree with `non_degeneracy_violations`. If these
    // ever diverge, one of them is not measuring what it claims.
    let gate_violations = on_large_stack(|| {
        ProofDatabase::new()
            .non_degeneracy_violations()
            .into_iter()
            .map(|v| v.name)
            .collect::<HashSet<_>>()
    });
    assert!(
        gate_violations.is_empty(),
        "the gate's own non_degeneracy_violations() disagrees with the re-derived invariant: {:?}",
        gate_violations
    );

    // TEETH (anti-fail-open): the gate must be ALIVE, not stubbed to always-empty.
    // Inject a degenerate X==X proof and confirm `non_degeneracy_violations`
    // actually REPORTS it. A fail-open mutation (e.g. `return Vec::new()`) returns
    // empty here and breaks this — so the meta-theorem has teeth against BOTH a
    // fail-closed regression (the re-derivation above) AND a fail-open gate stub.
    let reports_injected = on_large_stack(|| {
        use trust_cg_verify::ProofObligation;
        use trust_cg_verify::proof_database::{CategorizedProof, ProofCategory};
        use trust_cg_verify::smt::SmtExpr;
        let x = SmtExpr::var("x", 64);
        let injected = CategorizedProof {
            obligation: ProofObligation {
                name: "META-A teeth probe degenerate X==X".to_string(),
                trust_ir_expr: x.clone(),
                aarch64_expr: x,
                inputs: vec![("x".to_string(), 64)],
                preconditions: vec![],
                fp_inputs: vec![],
                category: None,
                machine_side_provenance: MachineSideProvenance::StaticDb,
            },
            category: ProofCategory::Arithmetic,
        };
        let mut proofs = ProofDatabase::new().all().to_vec();
        proofs.push(injected);
        ProofDatabase::from_proofs(proofs)
            .non_degeneracy_violations()
            .into_iter()
            .map(|v| v.name)
            .collect::<Vec<_>>()
    });
    assert_eq!(
        reports_injected,
        vec!["META-A teeth probe degenerate X==X".to_string()],
        "TEETH: the non-degeneracy gate must REPORT an injected degenerate proof (it is alive, \
         not stubbed to always-empty). If this is empty the gate fails OPEN."
    );
}

// ===========================================================================
// (b) META-THEOREM: every emittable opcode of every backend is CLASSIFIED.
// ===========================================================================
//
// INVARIANT: `forall arch. forall op in ALL_<arch>_OPCODES.
//             classify_<arch>(op) in {EmittableNeedsProof, PseudoOrTrap,
//             FailClosedAllowlisted{..}}` — i.e. the classifier is TOTAL, the
// match is wildcard-free, and EVERY opcode lands in a typed class (never a
// silent fail-open default).
//
// The wildcard-freedom is enforced at COMPILE TIME (the source `match`es have no
// `_` arm — a new variant breaks the build). What this test adds at RUN TIME is
// the COMPLEMENTARY property: the enumeration `ALL_<arch>_OPCODES` is complete
// (no duplicates) and EVERY listed opcode actually classifies (the function is
// total over the universe the gate iterates), and a FailClosedAllowlisted arm
// always carries a non-empty reason (an exception is never silent).
#[test]
fn meta_b_every_opcode_is_classified_total_classifier() {
    fn check_total<O: Copy + std::fmt::Debug + std::hash::Hash + Eq>(
        arch: &str,
        universe: &[O],
        classify: impl Fn(O) -> OpcodeClass,
    ) {
        let mut seen = HashSet::new();
        for &op in universe {
            assert!(
                seen.insert(op),
                "{arch}: ALL_<arch>_OPCODES has a DUPLICATE ({op:?}) — the universe must be a set"
            );
            // The classifier is total: this call cannot panic and returns a typed
            // class (the match has no fail-open wildcard).
            match classify(op) {
                OpcodeClass::EmittableNeedsProof | OpcodeClass::PseudoOrTrap => {}
                OpcodeClass::FailClosedAllowlisted { reason } => {
                    assert!(
                        !reason.trim().is_empty(),
                        "{arch}: opcode {op:?} is fail-closed allowlisted with an EMPTY reason — \
                         an exception out of the proof requirement must always be auditable"
                    );
                }
            }
        }
        assert!(
            !universe.is_empty(),
            "{arch}: opcode universe is empty — the gate would be vacuous"
        );
    }

    check_total("aarch64", ALL_AARCH64_OPCODES, classify_aarch64);
    check_total("x86_64", ALL_X86_OPCODES, classify_x86);
    check_total("riscv", ALL_RISCV_OPCODES, classify_riscv);
    check_total("wasm", ALL_WASM_OPCODES, classify_wasm);
}

// ===========================================================================
// (c) META-THEOREM: every coverage credit comes from a NON-degenerate obligation.
// ===========================================================================
//
// INVARIANT: `forall arch. forall covered emittable row r in audit(arch).
//             r was credited because EITHER its representative reconstruction
//             discharged Valid (is_reconstructed() && Valid) OR a NON-degenerate
//             DB proof matched and discharged Valid`. A static-DB X==X
// self-equality can NEVER be the reason a row is green.
//
// We assert this STRUCTURALLY at the credit source: for every backend, every
// covered (emittable, finding==None) row's note must record a genuine credit
// path (a reconstruction credit, a discharged genuine proof, or a width-poly
// genuine discharge) — NEVER a degenerate match. The audit path routes
// degenerate matches to `CoverageFinding::DegenerateProof` (a RED finding), so a
// covered row can only exist via the reconstruction / genuine-discharge paths.
// We additionally assert the converse for the reconstruction-credited rows: that
// the note names "[reconstruction]" (the provenance-keyed credit), proving the
// 100% headlines rest on `is_reconstructed() && Valid`, not on X==X.
#[test]
fn meta_c_every_credit_is_genuine_never_static_degenerate() {
    // The flag is whether RECONSTRUCTION is a credit path for the arch at all.
    // It is for every opcode-keyed inventory and for the wasm ABI family, whose
    // frame obligations rebuild their machine side from the emitted prologue /
    // alloca / epilogue bytes. It is NOT for the wasm CFG-structural family:
    // that family's credit unit is a REFUTATION of a deliberately-wrong module,
    // not a rebuilt expression, so demanding a reconstruction credit there would
    // demand a credit path it deliberately does not have. The no-DEGENERATE
    // clause still applies to it — it applies to every arch.
    let archs = [
        (GateArch::AArch64, true),
        (GateArch::X86_64, true),
        (GateArch::RiscV, true),
        (GateArch::Wasm, true),
        (GateArch::WasmValueDomain, true),
        (GateArch::WasmAbi, true),
        (GateArch::WasmCfgStructural, false),
    ];
    for (arch, expects_reconstruction_credit) in archs {
        let report = on_large_stack(move || CoverageGate::new().audit(arch));
        let mut reconstruction_credits = 0usize;
        for row in &report.rows {
            // We only reason about emittable rows that were CREDITED (no finding).
            if row.class != OpcodeClass::EmittableNeedsProof || row.finding.is_some() {
                continue;
            }
            // A credited row's note records WHY it is covered. The audit code
            // never emits a "DEGENERATE" note on a covered (finding==None) row —
            // a degenerate match always produces a `DegenerateProof` finding
            // (RED). Assert that load-bearing property structurally.
            assert!(
                !row.note.contains("DEGENERATE"),
                "{arch}: covered row {} is credited via a DEGENERATE (X==X) proof — a static-DB \
                 self-equality must NEVER count as coverage (it proves nothing). Note: {}",
                row.opcode_display,
                row.note
            );
            if row.note.contains("[reconstruction]") {
                reconstruction_credits += 1;
                assert!(
                    row.note.contains("RECONSTRUCTED"),
                    "{arch}: a [reconstruction] credit must name the real opcode it was rebuilt \
                     from: {}",
                    row.note
                );
            }
        }
        // RISC-V and wasm are 100% reconstruction-credited; AArch64/x86 are a mix
        // of reconstruction + genuine DB discharge. In every backend the genuine
        // emittable surface is reconstruction-dominated, so there must be at least
        // one reconstruction credit (the credit path is exercised, not dead).
        if expects_reconstruction_credit {
            assert!(
                reconstruction_credits > 0,
                "{arch}: NOT A SINGLE covered row was credited via reconstruction — the \
                 `is_reconstructed() && Valid` credit path is dead, so the headline cannot rest \
                 on it",
            );
        } else {
            assert_eq!(
                reconstruction_credits, 0,
                "{arch}: declared as having no reconstruction credit path, yet a row claims one \
                 — the declaration and the audit have drifted apart",
            );
        }
    }
}

// ===========================================================================
// (c'') META-THEOREM: the credit predicate itself rejects a static-DB X==X.
// ===========================================================================
//
// Independent of the audit walk, assert the load-bearing predicates directly:
//   * a degenerate (X==X) obligation is `is_degenerate()` and NOT
//     `is_genuinely_proven()` regardless of name;
//   * a `StaticDb`-provenance obligation is NOT `is_reconstructed()`, so it can
//     never satisfy the `is_reconstructed() && Valid` reconstruction credit rule.
// These are the two structural facts the whole credit story rests on.
#[test]
fn meta_c2_credit_predicates_reject_static_x_eq_x() {
    use trust_cg_verify::smt::SmtExpr;
    use trust_cg_verify::verify::VerificationResult;
    use trust_cg_verify::{ProofObligation, verify_by_evaluation};

    let x = SmtExpr::var("x", 64);
    let static_xx = ProofObligation {
        name: "static X==X (model consistency only)".to_string(),
        trust_ir_expr: x.clone(),
        aarch64_expr: x.clone(),
        inputs: vec![("x".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };

    // It evaluates Valid (a tautology) — the precise trap the gate must not fall
    // into: Valid does NOT imply coverage.
    assert!(
        matches!(verify_by_evaluation(&static_xx), VerificationResult::Valid),
        "an X==X obligation trivially evaluates Valid — that is exactly why Valid is not the \
         credit criterion"
    );
    // Yet it is degenerate, not genuinely proven, and not reconstructed: it can
    // satisfy NEITHER credit rule.
    assert!(static_xx.is_degenerate());
    assert!(!static_xx.is_genuinely_proven());
    assert!(
        !static_xx.is_reconstructed(),
        "a StaticDb-provenance obligation is never reconstructed, so it can never satisfy the \
         is_reconstructed() && Valid credit rule"
    );
}

// ===========================================================================
// (d) META-THEOREM: the fsym deref-coverage gate keys on the error list.
// ===========================================================================
//
// INVARIANT: a scanner report fails closed IFF it carries any coverage error:
//   `report.has_coverage_error() <=> !report.coverage_errors.is_empty()`.
//
// This is the A fail-closed deref-coverage invariant (task #49/#50): a reachable
// memory access that records NO verdict is an UNACCOUNTED obligation, recorded as
// an `FsymCoverageError`, and `has_coverage_error()` — the gate the build wires
// — must return true for it. The deep negative (force-drop a verdict and watch
// the invariant fire) lives in the in-crate unit test
// `deref_coverage_invariant_fails_closed_on_dropped_verdict`; here we assert the
// PUBLIC gate DECISION is driven by the error list and nothing else, so a future
// refactor that silences the list (failing open) breaks this.
#[test]
fn meta_d_fsym_deref_coverage_gate_keys_on_error_list() {
    // An empty report passes the gate (no unaccounted deref).
    let clean = FsymTrustIrReport::default();
    assert!(
        !clean.has_coverage_error(),
        "a report with no coverage errors must pass the deref-coverage gate"
    );

    // A report carrying a single unaccounted-deref error FAILS the gate — the
    // dropped obligation is surfaced, not silently treated as safe.
    let dropped = FsymCoverageError {
        module: "m".to_string(),
        function: "f".to_string(),
        block: 2,
        inst_index: 0,
        opcode: "Load",
        detail: "reachable Load recorded no verdict (INJECTED dropped obligation)".to_string(),
    };
    let mut failing = FsymTrustIrReport::default();
    failing.coverage_errors.push(dropped.clone());
    assert!(
        failing.has_coverage_error(),
        "a report carrying an FsymCoverageError must FAIL the deref-coverage gate (fail-closed): \
         a reachable deref with no verdict is an unaccounted obligation, never an implicit pass"
    );

    // The gate decision is EXACTLY `!coverage_errors.is_empty()` — equivalence,
    // not mere implication, so neither a false pass nor a false fail is possible.
    assert_eq!(
        failing.has_coverage_error(),
        !failing.coverage_errors.is_empty(),
        "has_coverage_error() must be exactly the non-emptiness of the coverage-error list"
    );
    assert_eq!(
        clean.has_coverage_error(),
        !clean.coverage_errors.is_empty(),
        "the gate must agree with the error list for the clean case too"
    );

    // The surfaced error carries the dropped site (module/function/block/inst/
    // opcode) so the failure is actionable, not opaque.
    let rendered = dropped.render(None);
    assert!(
        rendered.contains("deref-coverage invariant violated")
            && rendered.contains("Load")
            && rendered.contains("no verdict"),
        "the coverage error must render the dropped-obligation site: {rendered}"
    );
}

// ===========================================================================
// META-THEOREM (cross-cut): the headline rests on a NON-empty emittable surface.
// ===========================================================================
//
// A coverage gate over an EMPTY emittable set is vacuously 100% — the classic way
// to fake a green wall (allowlist everything OUT of the denominator). Assert the
// emittable surface is non-trivially large for every backend, so "100%" is a
// claim about real opcodes, not an empty denominator.
#[test]
fn meta_headline_denominator_is_nonvacuous() {
    for (arch, floor) in [
        (GateArch::AArch64, 40usize),
        (GateArch::RiscV, 10usize),
        (GateArch::Wasm, 80usize),
        (GateArch::WasmValueDomain, 20usize),
        // The two P4 families. The CFG floor is small BY CONSTRUCTION — its
        // denominator is a battery of mutants plus five deferrals, not an opcode
        // table — so the floor states only that the battery is non-empty and the
        // deferrals are counted, which is what makes its 6/13 a real ratio
        // rather than a vacuous one.
        (GateArch::WasmCfgStructural, 10usize),
        (GateArch::WasmAbi, 50usize),
        (GateArch::X86_64, 100usize),
    ] {
        let report = on_large_stack(move || CoverageGate::new().audit(arch));
        assert!(
            report.emittable_count() >= floor,
            "{arch}: emittable denominator is only {} (< {floor}) — a near-empty denominator makes \
             the 100% headline vacuous",
            report.emittable_count()
        );
    }
}

// Touch the opcode types so an unused-import regression in this enum surface is
// caught (the meta-theorems quantify over these universes).
#[test]
fn meta_opcode_universes_are_typed() {
    let _a: AArch64Opcode = ALL_AARCH64_OPCODES[0];
    let _x: X86Opcode = ALL_X86_OPCODES[0];
    let _r: RiscVOpcode = ALL_RISCV_OPCODES[0];
    let _w: WasmOpcode = ALL_WASM_OPCODES[0];
}
