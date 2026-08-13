// guard_kernel_gate_e2e.rs — End-to-end proof of kernel-gated bounds-check elimination
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Sentinel — the integration proof that public trust-ir proof metadata cannot authorize
//! bounds-check elimination.
//!
//! This test drives the REAL lowering path (trust-ir adapter + AArch64 instruction selection) and
//! then exercises the kernel gate exactly as the optimizer would:
//!
//! 1. Build a trust-ir [`Module`] with a function doing an array access (`Inst::ExtractElement`) on
//!    an `Array(_, N)` value, annotated with BOTH [`ProofAnnotation::InBounds`] (the upstream safety
//!    proof) and [`ProofAnnotation::ProofRef(ProofId(oid))`] (binding the carrier to a module
//!    obligation), plus a `ProofObligation(oid, MemorySafety, Discharged)` in
//!    `module.proof_obligations`.
//! 2. Lower it to a [`MachFunction`] via `translate_function` (adapter) + AArch64 `InstructionSelector`.
//! 3. Re-derive the carrier's operand fingerprint and confirm the report-only `ProofRef` binding
//!    survives lowering.
//! 4. Confirm `build_discharged_evidence_table` does not promote public `Discharged` status into
//!    optimization authority, then run [`ProofOptimization`] and assert the runtime carrier stays.
//! 5. Repeat with `Pending`, and with a bare `InBounds` annotation, to cover every former
//!    metadata-only admission path.
//!
//! `InBounds`, `ProofRef`, and `ProofStatus` are report/runtime-carrier metadata, not replayed proof
//! authority. Until an exact proof rechecker supplies an entry, the evidence table is empty and the
//! fail-closed kernel must keep the runtime check.

use std::collections::HashMap;

use trust_cg_ir::{AArch64GuardTarget, AArch64Opcode, GuardTarget, InstId, MachFunction};
use trust_cg_lower::isel::InstructionSelector;
use trust_cg_lower::{Function as LirFunction, Proof, ProofContext as LirProofContext};
use trust_cg_opt::pass_manager::MachinePass;
use trust_cg_opt::proof_opts::ProofOptimization;

use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

/// The obligation id used to bind the guard carrier to its module obligation. The adapter folds
/// `ProofRef(ProofId(oid))` to `oid` (the proof index). That binding remains useful for reporting,
/// but the public status does not populate the authoritative evidence table.
const OBLIGATION_ID: u32 = 7;

/// Array length / exact bound for the access.
const ARRAY_LEN: u64 = 8;

/// Build a trust-ir module whose single function does `array[index]` (ExtractElement) on an
/// `Array(I64, ARRAY_LEN)` parameter, carrying `InBounds` + `ProofRef(ProofId(OBLIGATION_ID))`, with
/// a single module proof obligation of the given `status`.
fn build_module(status: ProofStatus) -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_e2e");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "proven_extract", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: ValueId::new(0),
                index: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::InBounds)
            .with_proof(ProofAnnotation::ProofRef(ProofId::new(OBLIGATION_ID))),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];

    // Reported status for the carrier's obligation; deliberately not proof authority.
    module.proof_obligations.push(ProofObligation::new(
        ProofId::new(OBLIGATION_ID),
        ObligationKind::MemorySafety,
        status,
        "array index is in bounds",
    ));

    module.add_function(func.clone());
    (module, func)
}

/// Lower a single trust-ir function to a MachFunction via the real adapter + AArch64 ISel,
/// mirroring the codegen pipeline's `run_isel`. Returns the MachFunction (with stable `InstId`s),
/// the ISel-recorded carrier→obligation bindings (`guard_obligations`), and the obligation ids the
/// adapter's (necessarily empty) synthesized-authority list.
fn lower_to_machfunction(
    func: &TrustIrFunction,
    module: &Module,
) -> (MachFunction, HashMap<u128, u64>, Vec<u64>) {
    let (lir_func, proof_ctx): (LirFunction, LirProofContext) =
        trust_cg_lower::translate_function(func, module).expect("adapter translate");

    let sig = trust_cg_lower::function::Signature {
        params: lir_func.signature.params.clone(),
        returns: lir_func.signature.returns.clone(),
    };
    let mut isel = InstructionSelector::new(lir_func.name.clone(), sig.clone());
    isel.set_stack_slots(lir_func.stack_slots.clone());
    isel.seed_value_types(&lir_func.value_types);
    isel.seed_pure_callees(&lir_func.pure_callees);
    isel.seed_iconst_origins(
        lir_func
            .blocks
            .values()
            .map(|bb| bb.instructions.as_slice()),
    );
    isel.lower_formal_arguments(&sig, lir_func.entry_block)
        .expect("lower formal arguments");

    for block_ref in lir_func.layout_order() {
        let basic_block = &lir_func.blocks[&block_ref];
        if block_ref != lir_func.entry_block && !basic_block.params.is_empty() {
            isel.define_block_params(&basic_block.params);
        }
        let trust_ir_origins = lir_func
            .trust_ir_origins
            .get(&block_ref)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        isel.select_block_with_provenance(
            block_ref,
            &basic_block.instructions,
            &basic_block.source_locs,
            trust_ir_origins,
        )
        .expect("select block");
    }

    // The adapter records the `ExactInBounds` proof in `proof_ctx.value_proofs` keyed by the index
    // value; the carrier itself carries the InBounds proof in the real pipeline via Phase 2.5
    // (`apply_guard_proof_annotations`). We assert the proof made it across the adapter boundary so
    // this fixture stays honest about what InBounds asserts, then mirror that Phase-2.5 stamping
    // below (the pipeline-private matcher is not exported).
    assert!(
        proof_ctx
            .value_proofs
            .values()
            .flatten()
            .any(|p| matches!(p, Proof::ExactInBounds { .. } | Proof::InBounds { .. })),
        "adapter must record the InBounds proof for the array access"
    );

    let synthesized_discharged = proof_ctx.synthesized_discharged.clone();
    let isel_func = isel.finalize();
    let guard_obligations = isel_func.guard_obligations.clone();
    let mut mach_func = isel_func.to_ir_func();

    // Phase 2.5 (mirrors `pipeline::apply_guard_proof_annotations`): the real pipeline stamps the
    // `InBounds` annotation onto the exact bounds-check carrier so the proof-consuming optimizer's
    // legacy admission (`proof == Some(InBounds)`) reaches the carrier. The kernel gate then refines
    // that admission. The pipeline matcher is module-private; for a single proven array access the
    // only `TrapBoundsCheckExact` carrier is exactly the one the InBounds proof is about, so this
    // local stamping reproduces its effect faithfully.
    for inst in mach_func.insts.iter_mut() {
        if inst.opcode == AArch64Opcode::TrapBoundsCheckExact && inst.proof.is_none() {
            inst.proof = Some(trust_cg_ir::ProofAnnotation::InBounds);
        }
    }

    (mach_func, guard_obligations, synthesized_discharged)
}

/// Build the carrier→obligation map the kernel gate consumes: for every `TrapBoundsCheckExact`
/// carrier in the MachFunction, compute its operand fingerprint exactly as the kernel does
/// (`AArch64GuardTarget::operand_identity`) and look the obligation id up in the ISel-recorded
/// `guard_obligations` (keyed by that same fingerprint). This is the seam that crosses the ISel
/// boundary without a new MachInst field.
fn build_carrier_obligation_map(
    func: &MachFunction,
    guard_obligations: &HashMap<u128, u64>,
) -> HashMap<InstId, (u128, Option<u128>)> {
    let target = AArch64GuardTarget;
    let mut map = HashMap::new();
    for (idx, inst) in func.insts.iter().enumerate() {
        let Some(kind) = target.classify_carrier(inst) else {
            continue;
        };
        // The binding key folds in the carrier's GuardKind (defense-in-depth, Item B).
        let identity = target.operand_identity(inst);
        let fp = trust_cg_ir::fingerprint_for_kind(kind, &identity.operands);
        if let Some(&oid) = guard_obligations.get(&fp) {
            map.insert(InstId(idx as u32), (oid as u128, None));
        }
    }
    map
}

/// Count the `TrapBoundsCheckExact` carriers still referenced by the function's blocks (the optimizer
/// deletes by removing the InstId from its block, not by mutating the flat `insts` vec).
fn live_bounds_carriers(func: &MachFunction) -> usize {
    let mut count = 0;
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            if func.inst(inst_id).opcode == AArch64Opcode::TrapBoundsCheckExact {
                count += 1;
            }
        }
    }
    count
}

#[test]
fn kernel_gate_keeps_report_only_discharged_bounds_check_end_to_end() {
    let (module, func) = build_module(ProofStatus::Discharged);
    let (mut mach_func, guard_obligations, synthesized) = lower_to_machfunction(&func, &module);
    assert!(
        synthesized.is_empty(),
        "the carrier has an explicit ProofRef, so no obligation is synthesized"
    );

    // The carrier must exist after real lowering, and the ISel must have recorded its obligation.
    assert_eq!(
        live_bounds_carriers(&mach_func),
        1,
        "real lowering must emit exactly one bounds-check carrier"
    );
    assert_eq!(
        guard_obligations.len(),
        1,
        "ISel must preserve the report-only ProofRef binding by fingerprint"
    );

    // Public Discharged status is report-only. It must not mint optimization authority.
    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "public Discharged/ProofRef metadata must not populate the authoritative evidence table"
    );

    // Carrier→obligation map re-derived from the live MachFunction.
    let carrier_map = build_carrier_obligation_map(&mach_func, &guard_obligations);
    assert_eq!(
        carrier_map.len(),
        1,
        "fingerprint round-trip: the kernel's fingerprint must match the ISel-recorded one, so the \
         carrier resolves to its obligation"
    );

    // Run the gated optimizer.
    let mut pass = ProofOptimization::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    let changed = pass.run(&mut mach_func);

    assert!(
        !changed,
        "report-only proof metadata must not authorize elimination"
    );
    assert_eq!(
        live_bounds_carriers(&mach_func),
        1,
        "the runtime bounds-check carrier must survive without replayed proof authority"
    );
    assert_eq!(pass.stats().bounds_checks_eliminated, 0);
    assert_eq!(
        pass.kernel_eliminations().len(),
        0,
        "no kernel-authorized elimination may be recorded"
    );
    assert!(
        pass.recheck_kernel_eliminations().is_ok(),
        "nothing eliminated, so the independent re-check remains vacuously sound"
    );
}

#[test]
fn kernel_gate_keeps_pending_bounds_check_end_to_end() {
    // NEGATIVE case: obligation is Pending, so it is NOT in the evidence table => fail-safe Keep.
    let (module, func) = build_module(ProofStatus::Pending);
    let (mut mach_func, guard_obligations, _synthesized) = lower_to_machfunction(&func, &module);

    assert_eq!(
        live_bounds_carriers(&mach_func),
        1,
        "real lowering must emit exactly one bounds-check carrier"
    );

    // Evidence table excludes Pending obligations (fail-safe).
    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "Pending obligation must NOT appear in the evidence table"
    );

    // The carrier→obligation map still binds the carrier (the ProofRef is present); the kernel keeps
    // it solely because the obligation is not discharged in the evidence table.
    let carrier_map = build_carrier_obligation_map(&mach_func, &guard_obligations);

    let mut pass = ProofOptimization::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    pass.run(&mut mach_func);

    assert_eq!(
        live_bounds_carriers(&mach_func),
        1,
        "the bounds-check carrier MUST be KEPT: the obligation is not discharged (fail-safe)"
    );
    assert_eq!(pass.stats().bounds_checks_eliminated, 0);
    assert_eq!(
        pass.kernel_eliminations().len(),
        0,
        "no elimination should be authorized when the obligation is undischarged"
    );
    assert!(
        pass.recheck_kernel_eliminations().is_ok(),
        "nothing eliminated => re-check is trivially ok"
    );
}

/// Build a trust-ir module whose function does `array[index]` carrying ONLY `InBounds` (no
/// ProofRef) — the ordinary `getelementptr inbounds` shape. The adapter must not synthesize proof
/// authority from this report-only annotation.
fn build_inbounds_only_module() -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_e2e_synth");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func =
        TrustIrFunction::new(FuncId::new(0), "inbounds_only_extract", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), Ty::I64)],
        body: vec![
            // InBounds but NO ProofRef or independently replayable certificate.
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: ValueId::new(0),
                index: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::InBounds),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (module, func)
}

#[test]
fn kernel_gate_keeps_inbounds_annotation_without_replayed_authority() {
    // A bare InBounds annotation must retain its runtime carrier. In particular, it must not create
    // a synthetic discharge that can bypass exact proof replay.
    let (module, func) = build_inbounds_only_module();
    let (mut mach_func, guard_obligations, synthesized) = lower_to_machfunction(&func, &module);

    assert_eq!(live_bounds_carriers(&mach_func), 1);
    assert!(
        synthesized.is_empty(),
        "InBounds must not synthesize proof authority"
    );
    assert_eq!(
        guard_obligations.len(),
        0,
        "without ProofRef or replayed authority, no obligation is bound to the carrier"
    );

    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "no replayed proof authority exists in this fixture"
    );

    let carrier_map = build_carrier_obligation_map(&mach_func, &guard_obligations);
    assert!(
        carrier_map.is_empty(),
        "no synthetic obligation may resolve through the fingerprint"
    );

    let mut pass = ProofOptimization::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    let changed = pass.run(&mut mach_func);

    assert!(!changed);
    assert_eq!(
        live_bounds_carriers(&mach_func),
        1,
        "the InBounds runtime carrier must survive without replayed proof authority"
    );
    assert_eq!(pass.stats().bounds_checks_eliminated, 0);
    assert_eq!(pass.kernel_eliminations().len(), 0);
    assert!(pass.recheck_kernel_eliminations().is_ok());
}
