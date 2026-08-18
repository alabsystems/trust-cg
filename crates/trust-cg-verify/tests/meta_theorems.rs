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
//   (e) The 4 headline coverage numbers are pinned exactly. Every uncovered row
//       must be an explicit `DeferredUnfaithfulModel`, never a wiring gap.
//       AArch64 is 155/248 with 93 explicit model gaps; x86-64 is 163/192
//       with 29; RISC-V is 14/17 with 3; wasm is 109/111 with 2.

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
    let archs = [
        GateArch::AArch64,
        GateArch::X86_64,
        GateArch::RiscV,
        GateArch::Wasm,
    ];
    for arch in archs {
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
        assert!(
            reconstruction_credits > 0,
            "{arch}: NOT A SINGLE covered row was credited via reconstruction — the \
             `is_reconstructed() && Valid` credit path is dead, so the headline cannot rest on it",
        );
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
// (e) META-THEOREM: the 4 headline numbers are pinned AND each gate is honest.
// ===========================================================================
//
// INVARIANT: for each backend, `emittable == EMITTABLE-PIN AND covered ==
// COVERED-PIN AND every uncovered row is an HONESTLY-DEFERRED
// `DeferredUnfaithfulModel` (never a NoProofMapping / NoMatchingProof /
// ProofNotDischarged / DegenerateProof wiring gap)`. Phrased as a single
// universal over the four backends with their pins, so a regression in ANY of
// them (an opcode losing coverage, the denominator drifting, a wiring-gap RED
// row appearing, a deferral silently multiplying) fails this one meta-theorem.
// Named deferred debt is permitted; any unknown finding class or count drift
// fails this theorem.
#[test]
fn meta_e_headline_coverage_is_pinned_and_honest() {
    use trust_cg_verify::coverage_gate::CoverageFinding;

    // (arch, pinned emittable, pinned covered).
    // AArch64: 110 = the prior 105 (98 + 7 NEON popcount-fold/abs/dot-product/byte-extract/
    // add-long-pairwise/bitwise-insert ops CntV, UaddlpV, AbsV, UdotV, ExtV, SaddlpV,
    // BitV) + the 5 NEON FP vector ops FaddV/FsubV/FmulV/FdivV/FcmgtV credited by the 30
    // per-lane FP LANE-PLUMBING obligations (both .4S and .2D demanded; see the honesty
    // note in neon_lowering_proofs::all_neon_fp_lanewise_proofs — lane wiring / op /
    // width selection genuinely proven, FP-circuit semantic weight on the shared QF_FP
    // model + the silicon-validated B-aarch64-neon-fp bridge).
    // 110 -> 111: NeonStpQPost (paired NEON vector store, b2834cc) joins the
    // proven NEON post-index family (same coverage arm as NeonLdpQPost); that
    // landing added the opcode + classification but not this denominator bump
    // (meta_c already certifies the credit is genuine, so only the pin drifted).
    // 111 -> 112: + the scalar FUSED multiply-add FMADD (FmaddRR), the
    // `llvm.fmuladd`/`llvm.fma` lowering, EmittableNeedsProof and reconstruction-
    // covered by the single-rounding `fp.fma` obligation (round-once vs round-twice
    // refutes; see reconstruction_fp_div_madd::fmadd_*).
    // 112/112 -> 122/122 (UNIVERSE BACKFILL + neon_fpred lane proofs): 28 enum
    // variants that existed OUTSIDE `ALL_AARCH64_OPCODES` joined the audit — the
    // 18 exact-ordering LSE/CAS/SWP forms are allowlisted like their base/AL
    // siblings; +5 covered (FmaxnmRR/FminnmRR via the FpBinary Fmax/Fmin
    // reconstruction, Frintm/Frintp/FrintzRR via the unary-FP reconstruction);
    // +5 covered `.2D`-vectorizer NEON ops (NeonFmlaV/FmlsV (fused single-
    // rounding fp.fma), NeonUcvtfV/ScvtfV (per-lane int->FP), NeonDupScalarD
    // (64-bit lane->scalar copy)) via their 10 faithful per-lane obligations
    // (both .2D lanes; FMLA<->FMLS / accumulator-miswire / sign-confusion /
    // wrong-lane refute controls) — back to covered == emittable. See
    // coverage_gate_tests::aarch64_emittable_coverage_is_honest_under_strict.
    // 122/122 -> 124/124 (two independent landings): UMOV EXTRACT — NeonUmovGen
    // moved allowlisted -> emittable, covered via its 30 faithful per-(size,lane)
    // obligations (all_neon_umov_proofs, `.16B`/`.8H`/`.4S`/`.2D`; wrong-lane /
    // wrong-size refute controls); and TLS GOT-TPREL — LdrGottprel -> emittable,
    // covered via aarch64_elf_tls_reloc_proofs — still covered == emittable.
    // 124/124 -> 126/126 (one landing, TWO opcodes): FCVTL/FCVTL2 — NeonFcvtlV /
    // NeonFcvtl2V (vector f32->f64 widening convert emitted by neon_farray for
    // the widening dot) -> emittable, covered via their 4 faithful per-lane
    // obligations (all_neon_fcvtl_proofs, {FCVTL low, FCVTL2 high} x `.2D` 2 lanes;
    // wrong-half / wrong-lane refute controls) — still covered == emittable.
    // 126/126 -> 127/127 (EorRRShift): the rotate-fusion peephole's shifted-
    // register EOR-ROR (EOR Rd,Rn,Rm,ROR #k) -> emittable, covered via its
    // faithful rotate-XOR obligations (all_eor_ror_shift_proofs, W+X; wrong-amount
    // / wrong-shift-kind / operand-swap refute controls) — still covered == emittable.
    // 127/127 -> 128/128 (FcselRR): the FP-Select isel path's scalar FP
    // conditional select (FCSEL Sd/Dd,Sn,Sm,cc) -> emittable, covered via its
    // faithful bit-preserving-mux obligations (all_fcsel_proofs, S+D; inverted-cond
    // / operand-swap refute controls) — still covered == emittable.
    // 128/128 -> 129/129 (NeonFmlaLaneV): the NEON FP fused multiply-accumulate BY
    // ELEMENT (FMLA Vd.T,Vn.T,Vm.Ts[lane]) the elementwise-FP vectorizer emits for
    // y[i]+=da*x[i] (da broadcast from a lane, no DUP) -> emittable, covered via
    // its 20 faithful per-(arrangement,dest,selector) obligations
    // (all_neon_fmla_lane_proofs, .4S+.2D; wrong-lane-selector / FMLA<->FMLS polarity
    // / accumulator-miswire refute controls) — still covered == emittable.
    // 129/129 -> 131/131 (AddRRShift, SubRRShift): the shift-ALU fusion peephole's
    // shifted-register ADD/SUB (ADD/SUB Rd,Rn,Rm,LSL #k) -> emittable, each covered
    // via its faithful ring obligations (all_add_sub_lsl_shift_proofs, W+X; source
    // base +/- src*2^k (bvmul) == machine base +/- (src<<k) (bvshl); wrong-amount /
    // ADD-vs-SUB / SUB operand-swap refute controls) — still covered == emittable.
    // 131/131 -> 135/135 (NeonSmlalV/NeonSmlal2V/NeonUmlalV/NeonUmlal2V): the NEON
    // widening multiply-accumulate-long (SMLAL/SMLAL2/UMLAL/UMLAL2 .4S -> .2D) the
    // neon_array widening-dot vectorizer emits for `s(i64) += ext(a_i32[i]) *
    // ext(b_i32[i])` -> emittable, each covered via its faithful D-pair accumulate
    // obligation (all_neon_smlal_proofs; source acc_j + EXT64(n_s)*EXT64(m_s) ==
    // machine encode_neon_smlal; sign-confusion / no-accumulate / wrong-half /
    // truncating-mul refute controls) — still covered == emittable.
    // 135/135 -> 137/137 (NeonUaddwV/NeonUaddw2V): the NEON widening add-wide
    // (UADDW/UADDW2 .4S -> .2D) the neon_array widening abs-sum vectorizer
    // (TRACK D) emits for `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))` ->
    // emittable, each covered via its faithful D-pair obligation
    // (all_neon_uaddw_proofs; source addend_j + zext64(m_s) == machine
    // encode_neon_uaddw; sign-confusion / no-addend / wrong-half /
    // truncating-add refute controls) — still covered == emittable.
    // 137/137 -> 139/139 (NeonSaddwV/NeonSaddw2V): the NEON SIGNED widening
    // add-wide (SADDW/SADDW2 .4S -> .2D) the neon_predsum widening i64-acc
    // condsum emits for `s(i64) += (a_i32[iv] as i64) [if pred]` -> emittable,
    // each covered via its faithful D-pair obligation (all_neon_saddw_proofs;
    // source addend_j + sext64(m_s) == machine encode_neon_saddw;
    // zext-confusion [SADDW-as-UADDW] / no-addend / wrong-half /
    // truncating-add refute controls) — still covered == emittable.
    // 141/141 -> 143/143 (NeonMlaV + NeonUadalpV): the NEON vector
    // multiply-accumulate (MLA.4S, the neon_predsum MLA-by-mask condsum
    // accumulate — NEGATED-sum accumulators folded by one wrapping SubRR) and
    // pairwise widening accumulate (UADALP .4S -> .2D, the neon_array TRACK D
    // abs-sum accumulate — a pure mod-2^64 reassociation of the UADDW/UADDW2
    // terms under the both-lanes drain) -> emittable, each covered via its
    // faithful D-pair obligation (all_neon_mla_proofs; source acc_i + n_i*m_i
    // mod 2^32 == machine encode_neon_mla; MLS-confusion / MUL-no-accumulate /
    // lane-swap refute controls; all_neon_uadalp_proofs; source acc_j +
    // zext64(n_2j) + zext64(n_2j+1) == machine encode_neon_uadalp;
    // SADALP-sign-confusion / UADDLP-no-accumulate / wrong-pairing refute
    // controls) — still covered == emittable.
    // 143/143 -> 144 covered of 144 at that stage (NeonRbitV): the NEON
    // per-byte 8-bit reverse (RBIT.16B)
    // the neon-bitrev vectorizer emits for `a[i].reverse_bits()` over `[u8; N]`
    // -> emittable, covered via its faithful D-pair obligation
    // (all_neon_rbit_proofs; source per-bit within-byte mirror == machine
    // encode_neon_rbit_16b SWAR; identity / byte-swap [REV16.8B] /
    // 16-bit-lane-reverse [wrong-width] refute controls) — still covered ==
    // emittable. Publication re-audit then withdrew opcode-wide MOVN/MOVK
    // credit. The publication audit then restored all emitted value/effect
    // forms to the denominator, yielding 145/238. Six subsequently added
    // volatile load/store forms leave 93 explicit RED rows at 151/244;
    // EorRRLsl/EorRRLsr add two reconstructed shifted-source forms, yielding
    // 153/246. Umull then leaves the deferred set (faithful single-form
    // zext64*zext64 widening obligation, proof_umull_rr), yielding 154/246;
    // complete packed-NZCV TST authority then yields 155/246 with 91 RED rows.
    // StrbRO/StrhRO add two honest memory-effect gaps to the audited universe,
    // producing the current 155/248 with 93 RED rows.
    let pins = [
        // EorRRLsl/EorRRLsr reached 153/246; the independent UMULL widening
        // theorem and the width-complete packed-NZCV TST theorem each remove
        // one RED row, yielding 155/246 before the two narrow register-offset
        // store rows extend the current denominator to 248.
        (GateArch::AArch64, 248usize, 155usize),
        (GateArch::RiscV, 17usize, 14usize),
        (GateArch::Wasm, 111usize, 109usize),
        // 149 -> 151 (OPT-7): MovRMSib/MovMRSib SIB memory MOVs flip
        // FailClosedAllowlisted -> EmittableNeedsProof, covered by the same
        // reconstructed Load_I64/Store_I64 effective-address proofs as MovRM/MovMR.
        // 151 -> 154 (OPT-12 / VEC-Q): PSLLQ/PSRLQ (new i64x2 uniform-immediate
        // shifts, static-DB proofs parallel to PSLLD/PSRLD) and PMULUDQ
        // (FailClosedAllowlisted -> EmittableNeedsProof; faithful same-width
        // i64x2 `lo32(a)*lo32(b)` lane model, refuting negatives) — the packed
        // 64-bit multiply compose emitted by the SSE2 vectorizer.
        // 154 -> 157 (X9 slice 3 + X10): ImulRMSib (memory-operand IMUL, the
        // RM-fusion peephole) and MovRM32Sib/MovMR32Sib (32-bit SIB loads/
        // stores, the width-extended address folds) -> emittable, covered by
        // their effective-address/RM-fusion obligations landed with the same
        // commits (884d0b9c, d60553ac) — still covered == emittable.
        // 157 -> 158: Psadbw (horizontal byte sum-of-absolute-differences, the
        // byte-sum vectorizer tier) -> EmittableNeedsProof, covered by the
        // PsadbwByteSad reconstruction — still covered == emittable. (Pin
        // reconciled with the old 158/158 pin. Publication audit then restored
        // 13 emitted former exclusions and 16 volatile memory forms to the
        // denominator as named RED debt.)
        (GateArch::X86_64, 192usize, 163usize),
    ];
    for (arch, emittable_pin, covered_pin) in pins {
        let report = on_large_stack(move || CoverageGate::new().audit(arch));
        assert_eq!(
            report.emittable_count(),
            emittable_pin,
            "META-THEOREM (e): {arch} emittable (denominator) drifted from the pinned \
             {emittable_pin}",
        );
        assert_eq!(
            report.covered_count(),
            covered_pin,
            "META-THEOREM (e): {arch} covered drifted from the pinned {covered_pin}:\n{}",
            report.audit_log()
        );
        // Every uncovered row must be an HONESTLY-DEFERRED value op with a true
        // reason. A wiring-gap finding class here is the #68-fneg regression
        // this meta-theorem exists to catch. (Zero uncovered rows == the old
        // `is_clean()` check, verbatim.)
        let failures = report.failures();
        for row in &failures {
            assert!(
                matches!(
                    row.finding,
                    Some(CoverageFinding::DeferredUnfaithfulModel { .. })
                ),
                "META-THEOREM (e): {arch} uncovered row {} is a WIRING GAP, not an honest \
                 deferral: {:?}\n{}",
                row.opcode_display,
                row.finding,
                report.failure_summary()
            );
        }
        assert_eq!(
            failures.len(),
            emittable_pin - covered_pin,
            "META-THEOREM (e): {arch} uncovered-row count drifted from the pinned \
             emittable - covered",
        );
        assert!(
            (report.coverage_percent() - (covered_pin as f64 / emittable_pin as f64 * 100.0)).abs()
                < 0.01,
            "META-THEOREM (e): {arch} coverage_percent drifted from the pinned honest ratio",
        );
    }
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
