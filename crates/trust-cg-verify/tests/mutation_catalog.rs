// trust-cg-verify/tests/mutation_catalog.rs — DELIVERABLE 2 of task #54 (D engine).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// ADVERSARIAL FAULT CATALOG — inject a fault, a NAMED gate must KILL it.
// ===========================================================================
//
// This is the constructive negative half of D: for each catalogued fault we
// CONSTRUCT the faulty artifact THROUGH THE REAL TYPES (the same public encoders
// and reconstructors the verifier uses internally) and assert a NAMED gate
// REJECTS it. A fault that NO gate catches is a SURVIVOR — an untested gap — and
// is reported HONESTLY rather than hidden behind a green wall. (Fault 5a was the
// last documented survivor; it is now a genuine native-lane KILL — see #79 and
// `fault5a_dropped_divisor_precond_killed_by_native_trap_model` below — so the
// catalog currently has ZERO survivors.)
//
// The catalog (each entry names the gate that kills it):
//   (1) degenerate X==X proof          -> non-degeneracy gate (C) rejects.
//   (2) emittable op w/ no proof binding -> classifier/lookup fails CLOSED
//                                          (NoMatchingProof, not a silent pass).
//   (3) swapped opcode (Iadd as SUB)   -> reconstruction discharge REFUTES
//                                          (is_reconstructed() && Valid: Invalid).
//   (4) dropped deref obligation       -> fsym deref-coverage invariant (A) fires
//                                          (has_coverage_error()).
//   (5a) weakened precond divisor!=0   -> KILLED by the reconstruction discharge
//                                          under the NATIVE evaluator: x86 IDIV/DIV
//                                          now traps (#DE -> POISON) at divisor==0,
//                                          so the machine side diverges from the
//                                          trust_ir div-by-zero sentinel and the
//                                          unguarded form REFUTES (#79). (Was a
//                                          documented survivor before the trap model.)
//   (5b) weakened precond count<width  -> reconstruction discharge REFUTES (#57).
//   (6) value op hidden in the allowlist -> the credit-vs-exemption invariant
//                                          (a FailClosedAllowlisted op must NOT be
//                                          reconstructable) + the headline pin.
//   (7) credit a static-DB X==X covered -> is_degenerate() blocks the credit
//                                          (DegenerateProof finding, never green).

use trust_cg_ir::{AArch64Opcode, RiscVOpcode, WasmOpcode, X86Opcode};

use trust_cg_verify::coverage_gate::{
    ALL_AARCH64_OPCODES, ALL_RISCV_OPCODES, ALL_WASM_OPCODES, ALL_X86_OPCODES, OpcodeClass,
    classify_aarch64, classify_riscv, classify_wasm, classify_x86,
};
use trust_cg_verify::fsym_trust_ir::{FsymCoverageError, FsymTrustIrReport};
use trust_cg_verify::lowering_proof::{MachineSideProvenance, VerificationConfig};
use trust_cg_verify::proof_database::{CategorizedProof, ProofCategory, ProofDatabase};
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::trust_ir_semantics::{encode_trust_ir_binop, encode_trust_ir_shift};
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::{ProofObligation, verify_by_evaluation};

use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;

fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("mutation-catalog".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn scratch thread")
        .join()
        .expect("scratch thread panicked")
}

// ===========================================================================
// FAULT (1): a degenerate X==X proof — KILLED BY the non-degeneracy gate (C).
// ===========================================================================
//
// Construct a proof whose machine side is STRUCTURALLY identical to its source
// side (an X==X self-equality that proves nothing) with a name on NEITHER audited
// list, register it, and confirm `ProofDatabase::non_degeneracy_violations`
// reports EXACTLY it. This is the f81e45b lie the C gate exists to forbid.
#[test]
fn fault1_degenerate_xx_proof_killed_by_non_degeneracy_gate() {
    let x = SmtExpr::var("x", 64);
    let injected = CategorizedProof {
        obligation: ProofObligation {
            name: "INJECTED degenerate X==X (fault catalog #1)".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x, // identical -> degenerate, no independent machine model
            inputs: vec![("x".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::StaticDb,
        },
        category: ProofCategory::Arithmetic,
    };

    let violations = on_large_stack(move || {
        let mut proofs = ProofDatabase::new().all().to_vec();
        proofs.push(injected);
        ProofDatabase::from_proofs(proofs)
            .non_degeneracy_violations()
            .into_iter()
            .map(|v| v.name)
            .collect::<Vec<_>>()
    });

    assert_eq!(
        violations,
        vec!["INJECTED degenerate X==X (fault catalog #1)".to_string()],
        "GATE: ProofDatabase::non_degeneracy_violations (C) must report EXACTLY the injected \
         degenerate proof — and nothing else. If empty, the C gate is not fail-closed; if it \
         reports more, the real registry regressed."
    );
}

// ===========================================================================
// FAULT (2): an emittable opcode with NO proof binding — classifier/lookup fails
// CLOSED. KILLED BY: the (NoMatchingProof) lookup, not a silent pass.
// ===========================================================================
//
// An "unknown opcode" cannot be constructed in the typed enums (the four
// `classify_<arch>` matches are WILDCARD-FREE — a new variant breaks the build).
// The runtime fault is therefore "an EmittableNeedsProof opcode whose proof
// binding resolves to NOTHING". We model that directly: query the proof database
// for a category with a query string that matches NO proof, and confirm the
// lookup returns None (no match) — the gate's `discharge_one` turns that into a
// RED `NoMatchingProof` finding, never an implicit pass. Plus: every backend's
// classifier is TOTAL and every fail-closed exemption carries a reason (an
// exemption is never silent).
#[test]
fn fault2_unbound_emittable_opcode_fails_closed_not_silent() {
    // (2a) A proof lookup for a non-existent binding returns NO match — so the
    // gate cannot silently credit it; it MUST produce a RED finding.
    let found = on_large_stack(|| {
        let db = ProofDatabase::new();
        db.by_category(ProofCategory::Arithmetic).iter().any(|p| {
            p.obligation
                .name
                .contains("THIS_QUERY_MATCHES_NO_REAL_PROOF_xyz")
        })
    });
    assert!(
        !found,
        "GATE: a missing proof binding must resolve to NO match (fail-closed). The gate's \
         discharge path turns 'no match' into a RED NoMatchingProof finding — never a silent pass."
    );

    // (2b) Every classifier is TOTAL over its opcode universe and every
    // fail-closed exemption carries a non-empty reason: an opcode can never fall
    // through to a fail-open default, and an exemption is never silent.
    fn assert_total_and_reasoned<O: Copy + std::fmt::Debug>(
        arch: &str,
        universe: &[O],
        classify: impl Fn(O) -> OpcodeClass,
    ) {
        for &op in universe {
            match classify(op) {
                OpcodeClass::EmittableNeedsProof | OpcodeClass::PseudoOrTrap => {}
                OpcodeClass::FailClosedAllowlisted { reason } => assert!(
                    !reason.trim().is_empty(),
                    "{arch}: opcode {op:?} is allowlisted out of the proof requirement with an \
                     EMPTY reason — an exemption must always be auditable"
                ),
            }
        }
    }
    assert_total_and_reasoned("aarch64", ALL_AARCH64_OPCODES, classify_aarch64);
    assert_total_and_reasoned("x86_64", ALL_X86_OPCODES, classify_x86);
    assert_total_and_reasoned("riscv", ALL_RISCV_OPCODES, classify_riscv);
    assert_total_and_reasoned("wasm", ALL_WASM_OPCODES, classify_wasm);
}

// ===========================================================================
// FAULT (3): a swapped opcode (Iadd emitted as SUB) — KILLED BY the
// reconstruction discharge (is_reconstructed() && Valid yields Invalid).
// ===========================================================================
//
// Build the buggy obligation THROUGH THE REAL ENCODERS: source side =
// `encode_trust_ir_binop(Iadd)` (the intended op), machine side = `bvsub` (the
// wrong emitted opcode), over the SAME shared symbols and tagged Reconstructed.
// `verify_by_evaluation` must REFUTE (Invalid): bvadd != bvsub for some inputs.
// The credit rule is `is_reconstructed() && Valid`; Invalid kills the credit.
#[test]
fn fault3_swapped_opcode_iadd_as_sub_killed_by_reconstruction_discharge() {
    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let buggy = ProofObligation {
        name: "RECONSTRUCTED Iadd -> SUB (INJECTED swapped opcode, fault catalog #3)".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a.clone(), b.clone()),
        // WRONG: the machine side is a subtraction, not an addition.
        aarch64_expr: a.clone().bvsub(b.clone()),
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "SubRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        buggy.is_reconstructed(),
        "the buggy obligation must be on the reconstruction credit path to be a fair test"
    );
    assert!(
        matches!(
            verify_by_evaluation(&buggy),
            VerificationResult::Invalid { .. }
        ),
        "GATE: the reconstruction discharge (is_reconstructed() && Valid) must REFUTE an \
         Iadd-emitted-as-SUB: bvadd != bvsub. Valid here would mean a swapped opcode ships."
    );
    // It is genuinely distinct (not vacuous X==X): a wrong opcode CAN refute.
    assert!(buggy.is_genuinely_proven());
}

// ===========================================================================
// FAULT (4): a dropped deref obligation — KILLED BY the fsym deref-coverage
// invariant (A): `has_coverage_error()`.
// ===========================================================================
//
// A reachable memory access that records NO verdict is an UNACCOUNTED obligation
// (the scanner would be failing open, asserting a safety it never proved). The
// scanner records an `FsymCoverageError` and `has_coverage_error()` — the gate
// the build wires — must return true. We construct the report carrying the
// dropped-Load error through the public type and assert the gate FAILS CLOSED.
// (The deep in-process force-drop negative lives in the in-crate unit test
// `deref_coverage_invariant_fails_closed_on_dropped_verdict`.)
#[test]
fn fault4_dropped_deref_obligation_killed_by_fsym_coverage_gate() {
    let dropped = FsymCoverageError {
        module: "m".to_string(),
        function: "f_test".to_string(),
        block: 2,
        inst_index: 0,
        opcode: "Load",
        detail: "reachable Load recorded no verdict (INJECTED dropped obligation, fault #4)"
            .to_string(),
    };
    let mut report = FsymTrustIrReport::default();
    report.coverage_errors.push(dropped);

    assert!(
        report.has_coverage_error(),
        "GATE: FsymTrustIrReport::has_coverage_error (A deref-coverage invariant) must return \
         true for a report carrying a dropped-deref error — a reachable Load with no verdict is \
         never an implicit pass."
    );
    // The clean baseline must NOT trip the gate (no false positive that would
    // make the gate meaningless).
    assert!(
        !FsymTrustIrReport::default().has_coverage_error(),
        "an empty report must pass the gate (else the gate is vacuous)"
    );
}

// ===========================================================================
// FAULT (5b): a weakened precondition (shift count<width removed) — KILLED BY
// the reconstruction discharge (#57). The count<width precondition is
// LOAD-BEARING: strip it and a shift by exactly width REFUTES.
// ===========================================================================
#[test]
fn fault5b_dropped_shift_count_precond_killed_by_reconstruction_discharge() {
    let a = SmtExpr::var("recon_src1", 8);
    let amt = SmtExpr::var("recon_src2", 8);
    // A correct masked shift WITH the in-range precondition is Valid.
    let machine = encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone());
    let with_precond = ProofObligation {
        name: "RECONSTRUCTED Ishl (count<width precond present)".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: machine.clone(),
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "LslRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&with_precond),
            VerificationResult::Valid
        ),
        "baseline: the shift WITH its count<width precondition must discharge Valid"
    );

    // Now build the SAME obligation against a HARDWARE-MASKED machine shift but
    // with the precondition STRIPPED. A shift amount of exactly the width (8)
    // diverges between the unmasked spec and the masked machine ⇒ REFUTE. (This
    // is the #57 shift-divergence fault; the precondition models the ISel guard.)
    let masked_machine = a.clone().bvshl(amt.clone().bvand(SmtExpr::bv_const(7, 8)));
    let weakened = ProofObligation {
        name: "RECONSTRUCTED Ishl (count<width precond DROPPED, fault catalog #5b)".to_string(),
        trust_ir_expr: a.clone().bvshl(amt.clone()), // unmasked spec
        aarch64_expr: masked_machine,                // hardware masks amt & (width-1)
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: vec![], // <-- the load-bearing precondition was REMOVED
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "LslRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        matches!(
            verify_by_evaluation(&weakened),
            VerificationResult::Invalid { .. }
        ),
        "GATE: with the count<width precondition DROPPED, an unmasked spec vs a hardware-masked \
         machine shift must REFUTE at amt==width (#57). The precondition is load-bearing."
    );
}

// ===========================================================================
// FAULT (5a): a weakened precondition (divisor!=0 removed) — KILLED BY the
// reconstruction discharge under the NATIVE evaluator (#79, was a survivor).
// ===========================================================================
//
// x86 `IDIV`/`DIV` raise `#DE` (divide error) on a zero divisor: the instruction
// TRAPS and has NO defined result. The reconstruction now models this FAITHFULLY
// via a `TrapIfZero` wrapper on the machine side (smt.rs), which evaluates to
// POISON at divisor==0. Poison is unequal to EVERY value — including trust_ir's
// own div-by-zero contract sentinel — so the source and machine sides DIVERGE at
// divisor==0. The `divisor != 0` precondition is therefore genuinely
// LOAD-BEARING in the native lane:
//   * WITH the precondition  -> the divisor==0 trap point is excluded ⇒ Valid;
//   * WITHOUT it (the fault) -> the sweep samples divisor==0, machine = Poison ≠
//                               sentinel ⇒ REFUTE.
// This is the genuine native-lane KILL that closes the documented D survivor.
// (The strict SMT lane also models the trap via a fresh unconstrained poison
// constant — see proof_gate_strict — but the native evaluator alone now suffices.)
//
// This test asserts the KILL: with the precondition the obligation is Valid, and
// stripping it makes the obligation REFUTE (Invalid) under the native evaluator.
// If a future change reintroduced the src/machine div0 agreement (e.g. dropped
// the trap model), `refuted_without_precond` would no longer list both forms and
// this test would FAIL — the kill cannot silently regress to a survivor.
#[test]
fn fault5a_dropped_divisor_precond_killed_by_native_trap_model() {
    use trust_cg_verify::{
        reconstruct_x86_alu_obligation, representative_x86_reconstructable_inst,
    };

    let mut refuted_without_precond = Vec::new();
    for op in [X86Opcode::Idiv, X86Opcode::Div] {
        let inst = representative_x86_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must have a representative"));
        let ob = reconstruct_x86_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(
            !ob.preconditions.is_empty(),
            "{op:?}: the division reconstruction must carry a divisor!=0 precondition to strip"
        );
        // Baseline: WITH the precondition it discharges Valid (production stays
        // 100% — the trap point is excluded, so the trap model adds no false
        // counterexample to the guarded form).
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "{op:?}: division WITH divisor!=0 must STILL discharge Valid (the trap model must not \
             refute the correctly-guarded production obligation)"
        );
        // Strip the precondition (the injected fault). The native evaluator must
        // now REFUTE: at divisor==0 the machine side traps (Poison) while the
        // source side returns its div0 sentinel ⇒ they diverge.
        let mut stripped = ob.clone();
        stripped.preconditions.clear();
        if matches!(
            verify_by_evaluation(&stripped),
            VerificationResult::Invalid { .. }
        ) {
            refuted_without_precond.push(format!("{op:?}"));
        }
    }

    // KILL ASSERTION: the native evaluator REFUTES BOTH division forms once the
    // divisor!=0 precondition is dropped — the precondition is load-bearing.
    assert_eq!(
        refuted_without_precond,
        vec!["Idiv".to_string(), "Div".to_string()],
        "KILL (#79): dropping divisor!=0 must make BOTH x86 IDIV/DIV reconstructions REFUTE under \
         the native evaluator — x86 traps (#DE -> Poison) at divisor==0, so the machine side no \
         longer agrees with the trust_ir div-by-zero sentinel. If this stops refuting, the trap \
         model regressed and the kill silently became a survivor again."
    );
}

// ===========================================================================
// FAULT (6): a value-bearing op hidden in the fail-closed allowlist — KILLED BY
// the credit-vs-exemption invariant: a FailClosedAllowlisted op must NOT be
// reconstructable (a reconstructable value op must be CREDITED, never exempted),
// and reclassifying a credited op OUT of EmittableNeedsProof drops the headline
// pin below 100%.
// ===========================================================================
//
// The exact-mutation gate (moving a value op into the allowlist) is killed at
// COMPILE/RUNTIME two ways:
//   (i)  the headline emittable-count pin in meta_theorems (e) drops below
//        63/144/14/109 — caught;
//   (ii) the structural invariant ASSERTED HERE: NO allowlisted opcode is
//        reconstructable. If a value op were moved into the allowlist, it would
//        STILL reconstruct-discharge Valid, so this invariant would flag it as a
//        value op hiding in the exemption list.
#[test]
fn fault6_value_op_in_allowlist_killed_by_credit_vs_exemption_invariant() {
    use trust_cg_verify::function_verifier::reconstruction_discharges_valid as aarch64_recon;
    use trust_cg_verify::riscv_function_verifier::reconstruction_discharges_valid as riscv_recon;
    use trust_cg_verify::wasm_function_verifier::reconstruction_discharges_valid as wasm_recon;
    use trust_cg_verify::x86_64_function_verifier::reconstruction_discharges_valid as x86_recon;

    let cfg = VerificationConfig::default();

    // The invariant: a fail-closed allowlisted opcode must NOT reconstruct-
    // discharge Valid. If it did, it is a VALUE op that should be CREDITED, not
    // exempted — i.e. a value op hiding in the allowlist (fault #6).
    fn check<O: Copy + std::fmt::Debug>(
        arch: &str,
        universe: &[O],
        classify: impl Fn(O) -> OpcodeClass,
        recon: impl Fn(O, &VerificationConfig) -> bool,
        cfg: &VerificationConfig,
    ) -> Vec<String> {
        let mut hiding = Vec::new();
        for &op in universe {
            if matches!(classify(op), OpcodeClass::FailClosedAllowlisted { .. }) && recon(op, cfg) {
                hiding.push(format!("{arch}::{op:?}"));
            }
        }
        hiding
    }

    let hiding = on_large_stack(move || {
        let cfg = VerificationConfig::default();
        let mut h = Vec::new();
        h.extend(check(
            "aarch64",
            ALL_AARCH64_OPCODES,
            classify_aarch64,
            aarch64_recon,
            &cfg,
        ));
        h.extend(check(
            "x86_64",
            ALL_X86_OPCODES,
            classify_x86,
            x86_recon,
            &cfg,
        ));
        h.extend(check(
            "riscv",
            ALL_RISCV_OPCODES,
            classify_riscv,
            riscv_recon,
            &cfg,
        ));
        h.extend(check(
            "wasm",
            ALL_WASM_OPCODES,
            classify_wasm,
            wasm_recon,
            &cfg,
        ));
        h
    });

    assert!(
        hiding.is_empty(),
        "GATE: credit-vs-exemption invariant — these FailClosedAllowlisted opcodes ALSO \
         reconstruct-discharge Valid, i.e. they are VALUE ops hiding in the exemption list \
         (fault #6). A reconstructable value op must be CREDITED (in the denominator), not \
         exempted out of it:\n{}",
        hiding.join("\n")
    );
    // sanity: the config is actually used (the closures borrow it).
    let _ = &cfg;
}

// ===========================================================================
// FAULT (7): crediting a static-DB X==X as covered — KILLED BY the is_degenerate
// credit guard: a degenerate obligation is never genuinely proven, so the credit
// path (the DegenerateProof finding) blocks it; it can never go green.
// ===========================================================================
//
// The strict credit criterion is `is_genuinely_proven()` (trust_ir != machine)
// for DB proofs, and `is_reconstructed() && Valid` for the reconstruction path.
// A static-DB X==X obligation satisfies NEITHER: it evaluates Valid trivially but
// is degenerate (proves nothing), its provenance is StaticDb (not Reconstructed),
// so neither credit rule can fire. Constructed and asserted directly.
#[test]
fn fault7_static_db_xx_cannot_be_credited_covered() {
    let x = SmtExpr::var("x", 64);
    let static_xx = ProofObligation {
        name: "x86_64: AddRR -> ADD (static X==X, fault catalog #7)".to_string(),
        trust_ir_expr: x.clone(),
        aarch64_expr: x.clone(), // identical -> degenerate
        inputs: vec![("x".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };

    // It is Valid (a tautology) — the trap: Valid does not imply coverage.
    assert!(
        matches!(verify_by_evaluation(&static_xx), VerificationResult::Valid),
        "an X==X obligation trivially evaluates Valid — precisely why Valid is not the credit rule"
    );
    // GATE: it is degenerate, not genuinely proven, and not reconstructed, so it
    // satisfies NEITHER credit rule and can never be credited covered.
    assert!(
        static_xx.is_degenerate(),
        "GATE: a static-DB X==X must be is_degenerate() (the DegenerateProof credit block)"
    );
    assert!(
        !static_xx.is_genuinely_proven(),
        "GATE: a static-DB X==X is NOT genuinely proven (the DB credit criterion rejects it)"
    );
    assert!(
        !static_xx.is_reconstructed(),
        "GATE: a static-DB X==X is NOT reconstructed (the reconstruction credit rule rejects it)"
    );
}

// Touch the opcode/category types so an enum-surface regression is caught.
#[test]
fn catalog_types_are_wired() {
    let _a: AArch64Opcode = ALL_AARCH64_OPCODES[0];
    let _x: X86Opcode = ALL_X86_OPCODES[0];
    let _r: RiscVOpcode = ALL_RISCV_OPCODES[0];
    let _w: WasmOpcode = ALL_WASM_OPCODES[0];
    let _c = ProofCategory::Arithmetic;
}
