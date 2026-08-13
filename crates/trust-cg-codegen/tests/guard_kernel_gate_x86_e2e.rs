// guard_kernel_gate_x86_e2e.rs — Fail-closed bounds-check authority tests on x86-64
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fail-closed x86-64 integration coverage for bounds-check carriers.
//!
//! Public proof annotations, `ProofRef`, obligation status, and adapter-synthesized ids are report
//! metadata, not deletion authority. An explicit `ProofRef` may preserve an identifier binding for
//! reporting, but the replay-only evidence table remains empty; annotation-only input creates neither
//! a synthesized id nor a binding. The production compiler therefore retains its hardware guard.
//! This suite exercises the real adapter, x86 selector, kernel, and object pipeline to lock in that
//! policy. Both legacy environment values are deliberately non-authoritative.
//!
//! The fingerprint checks remain valuable: they prove the carrier has a stable identity while also
//! proving that identity is intentionally absent from the authority map.

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_ir::{GuardKind, GuardOperandRef, X86GuardTarget, X86Opcode};
use trust_cg_lower::x86_64_isel::{
    X86CallAbi, X86ISelFunction, X86ISelInst, X86InstructionSelector,
};
use trust_cg_lower::{Function as LirFunction, ProofContext as LirProofContext};
use trust_cg_opt::x86_proof_opts::X86ProofGuardElimination;

use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

const OBLIGATION_ID: u32 = 7;
const ARRAY_LEN: u64 = 8;

/// Build a trust-ir module whose single function does `array[index]` on an `Array(I64, ARRAY_LEN)`
/// parameter, carrying `InBounds` (+ `ProofRef(OBLIGATION_ID)` when `with_proof_ref`), with a single
/// module obligation of the given `status`.
fn build_module(status: ProofStatus, with_proof_ref: bool) -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_x86_e2e");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "proven_extract_x86", ft, BlockId::new(0));
    let mut node = InstrNode::new(Inst::ExtractElement {
        ty: Ty::I64,
        array: ValueId::new(0),
        index: ValueId::new(1),
    })
    .with_result(ValueId::new(2))
    .with_proof(ProofAnnotation::InBounds);
    if with_proof_ref {
        node = node.with_proof(ProofAnnotation::ProofRef(ProofId::new(OBLIGATION_ID)));
    }
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), Ty::I64)],
        body: vec![
            node,
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];

    if with_proof_ref {
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(OBLIGATION_ID),
            ObligationKind::MemorySafety,
            status,
            "array index is in bounds",
        ));
    }

    module.add_function(func.clone());
    (module, func)
}

/// Lower a single trust-ir function to an x86 ISel function via the real adapter + x86 ISel,
/// mirroring `Compiler::compile_x86_64`'s ISel phase. Returns the X86ISelFunction (with the
/// ISel-recorded carrier->obligation bindings) and the adapter's synthesized-id report. Production
/// policy requires the report to remain empty for public annotations.
fn lower_to_x86_isel(func: &TrustIrFunction, module: &Module) -> (X86ISelFunction, Vec<u64>) {
    let (lir_func, proof_ctx): (LirFunction, LirProofContext) =
        trust_cg_lower::translate_function(func, module).expect("adapter translate");

    let sig = trust_cg_lower::function::Signature {
        params: lir_func.signature.params.clone(),
        returns: lir_func.signature.returns.clone(),
    };
    let mut isel =
        X86InstructionSelector::with_abi(lir_func.name.clone(), sig.clone(), X86CallAbi::SystemV);
    isel.set_stack_slots(lir_func.stack_slots.clone());
    isel.seed_value_types(&lir_func.value_types);
    isel.seed_function_value_use_counts(&lir_func);

    let block_order = lir_func.layout_order();
    for block_ref in &block_order {
        isel.ensure_block(*block_ref);
    }
    isel.lower_formal_arguments(&sig, lir_func.entry_block)
        .expect("lower formal arguments");
    for block_ref in &block_order {
        let basic_block = &lir_func.blocks[block_ref];
        if *block_ref != lir_func.entry_block && !basic_block.params.is_empty() {
            isel.define_block_params(&basic_block.params);
        }
        isel.select_block(*block_ref, &basic_block.instructions)
            .expect("select block");
    }

    (isel.finalize(), proof_ctx.synthesized_discharged.clone())
}

/// Count the live x86 bounds-check carriers in the function.
fn live_x86_carriers(func: &X86ISelFunction) -> usize {
    func.block_order
        .iter()
        .filter_map(|b| func.blocks.get(b))
        .flat_map(|b| b.insts.iter())
        .filter(|i: &&X86ISelInst| i.opcode == X86Opcode::TrapBoundsCheckExact)
        .count()
}

/// Build the carrier->obligation map the x86 gate consumes: re-derive each carrier's operand
/// fingerprint exactly as the kernel does (`X86GuardTarget::operand_identity`) and look the
/// obligation up in the ISel-recorded `guard_obligations` (keyed by that same fingerprint).
fn build_carrier_obligation_map(func: &X86ISelFunction) -> HashMap<u128, (u128, Option<u128>)> {
    let target = X86GuardTarget;
    let mut map = HashMap::new();
    for block in func.block_order.iter().filter_map(|b| func.blocks.get(b)) {
        for inst in &block.insts {
            let Some(kind) = target.classify_carrier(inst.opcode) else {
                continue;
            };
            let refs: Vec<GuardOperandRef> = inst
                .operands
                .iter()
                .filter_map(|op| match op {
                    trust_cg_lower::X86ISelOperand::VReg(v) => Some(GuardOperandRef::Reg(v.id)),
                    trust_cg_lower::X86ISelOperand::Imm(i) => Some(GuardOperandRef::Imm(*i)),
                    _ => None,
                })
                .collect();
            let identity = target.operand_identity(&refs);
            let fp = trust_cg_ir::fingerprint_for_kind(kind, &identity.operands);
            if let Some(&oid) = func.guard_obligations.get(&fp) {
                map.insert(fp, (oid as u128, None));
            }
        }
    }
    map
}

#[test]
fn x86_kernel_gate_rejects_discharged_status_as_bounds_authority() {
    let (module, func) = build_module(ProofStatus::Discharged, true);
    let (mut isel_func, synthesized) = lower_to_x86_isel(&func, &module);
    assert!(
        synthesized.is_empty(),
        "the carrier has an explicit ProofRef, so no obligation is synthesized"
    );

    // Real x86 lowering emits the carrier and may preserve the explicit identifier for reporting.
    assert_eq!(
        live_x86_carriers(&isel_func),
        1,
        "real x86 lowering must emit exactly one bounds-check carrier"
    );
    assert_eq!(
        isel_func.guard_obligations.len(),
        1,
        "explicit ProofRef remains traceable even though it is not deletion authority"
    );

    // The production evidence builder is replay-only. A public Discharged row is insufficient.
    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "Discharged status without exact replay must be ignored"
    );

    let carrier_map = build_carrier_obligation_map(&isel_func);
    assert_eq!(
        carrier_map.len(),
        1,
        "the explicit identifier binding remains available for reporting"
    );

    // Run the gated x86 pass.
    let mut pass = X86ProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    let changed = pass.run_on_function(&mut isel_func);

    assert!(
        !changed,
        "empty replay authority must reject the elimination"
    );
    assert_eq!(
        live_x86_carriers(&isel_func),
        1,
        "the x86 bounds-check carrier must be retained without exact replay authority"
    );
    assert_eq!(pass.stats().guards_eliminated, 0);
    assert!(pass.kernel_eliminations().is_empty());
    assert!(pass.recheck_kernel_eliminations().is_ok());
}

#[test]
fn x86_kernel_gate_keeps_pending_bounds_check_end_to_end() {
    // NEGATIVE: obligation is Pending, so it is NOT in the evidence table => fail-safe Keep.
    let (module, func) = build_module(ProofStatus::Pending, true);
    let (mut isel_func, _synthesized) = lower_to_x86_isel(&func, &module);

    assert_eq!(live_x86_carriers(&isel_func), 1);

    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "Pending obligation must NOT appear in the evidence table"
    );

    let carrier_map = build_carrier_obligation_map(&isel_func);

    let mut pass = X86ProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    pass.run_on_function(&mut isel_func);

    assert_eq!(
        live_x86_carriers(&isel_func),
        1,
        "the x86 carrier MUST be KEPT: the obligation is not discharged (fail-safe)"
    );
    assert_eq!(pass.stats().guards_eliminated, 0);
    assert_eq!(pass.kernel_eliminations().len(), 0);
    assert!(pass.recheck_kernel_eliminations().is_ok());
}

#[test]
fn x86_kernel_gate_rejects_synthesized_inbounds_authority_end_to_end() {
    // An InBounds annotation without exact replay must not mint an id, evidence, or binding.
    let (module, func) = build_module(ProofStatus::Discharged, false);
    let (mut isel_func, synthesized) = lower_to_x86_isel(&func, &module);

    assert_eq!(live_x86_carriers(&isel_func), 1);
    assert_eq!(
        synthesized.len(),
        0,
        "public InBounds annotations must not synthesize deletion authority"
    );
    assert!(isel_func.guard_obligations.is_empty());

    // Replay evidence is empty, as are the adapter's synthesized ids.
    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(evidence.is_empty(), "no module obligations in this fixture");

    let carrier_map = build_carrier_obligation_map(&isel_func);
    assert!(carrier_map.is_empty());

    let mut pass = X86ProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    let changed = pass.run_on_function(&mut isel_func);

    assert!(!changed);
    assert_eq!(
        live_x86_carriers(&isel_func),
        1,
        "the x86 InBounds carrier must be kept without replayed validator authority"
    );
    assert_eq!(pass.stats().guards_eliminated, 0);
    assert!(pass.recheck_kernel_eliminations().is_ok());
}

/// Independent duplicate control for the annotation-only path: no synthesized authority may leak
/// through either the evidence table or the carrier map.
#[test]
fn x86_annotation_only_bounds_check_has_empty_authority_inputs() {
    let (module, func) = build_module(ProofStatus::Discharged, false);
    let (mut isel_func, synthesized) = lower_to_x86_isel(&func, &module);

    assert_eq!(live_x86_carriers(&isel_func), 1);
    assert!(synthesized.is_empty());

    // Evidence WITHOUT the synthesized id (empty here).
    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(evidence.is_empty());

    let carrier_map = build_carrier_obligation_map(&isel_func);
    assert!(
        carrier_map.is_empty(),
        "annotation-only carrier must remain unbound"
    );

    let mut pass = X86ProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    pass.run_on_function(&mut isel_func);

    assert_eq!(
        live_x86_carriers(&isel_func),
        1,
        "empty authority inputs keep the guard fail-closed"
    );
    assert_eq!(pass.kernel_eliminations().len(), 0);
}

/// Count UD2 (0F 0B) occurrences in raw object bytes. A surviving x86 bounds-check carrier expands
/// to a synthetic UD2 trap block, so UD2 presence is the observable for "guard kept"; its absence
/// in these tiny functions, so this is a faithful runtime-guard observable.
fn ud2_count(bytes: &[u8]) -> usize {
    bytes.windows(2).filter(|w| w == b"\x0F\x0B").count()
}

fn compile_x86_object(module: &Module) -> Vec<u8> {
    let spec = TargetSpec::parse("x86_64-apple-darwin").expect("parse x86_64-apple-darwin");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        spec,
    );
    let result = compiler.compile(module).expect("x86 compile");
    result.object_code
}

/// Full-pipeline refutation: neither legacy environment value may turn public annotation/status
/// metadata into deletion authority. Both compilations retain the same hardware trap.
#[test]
fn x86_kernel_gate_env_values_cannot_bypass_empty_authority() {
    let (module, _func) = build_module(ProofStatus::Discharged, false);

    // Both old spellings are ignored by the unconditional fail-closed production policy.
    let (off_ud2, on_ud2) = env_lock::with_env_edits(|env| {
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "0");
        let off = compile_x86_object(&module);
        let off_ud2 = ud2_count(&off);
        assert!(
            off_ud2 >= 1,
            "legacy value 0 must keep the UD2 bounds-check trap"
        );

        env.set("TRUST_CG_GUARD_KERNEL_GATE", "1");
        let on = compile_x86_object(&module);
        let on_ud2 = ud2_count(&on);
        (off_ud2, on_ud2)
    });

    assert!(
        on_ud2 >= 1,
        "legacy value 1 must keep the UD2 bounds-check trap"
    );
    assert_eq!(
        on_ud2, off_ud2,
        "environment values must not alter guard retention"
    );
}

/// The fingerprint and explicit identifier binding remain deterministic for reporting, but a public
/// Discharged row still does not supply replay evidence and therefore cannot authorize deletion.
#[test]
fn x86_carrier_fingerprint_binding_is_non_authoritative_without_replay() {
    let (module, func) = build_module(ProofStatus::Discharged, true);
    let (isel_func, _) = lower_to_x86_isel(&func, &module);

    let carrier = isel_func
        .block_order
        .iter()
        .filter_map(|b| isel_func.blocks.get(b))
        .flat_map(|b| b.insts.iter())
        .find(|i| i.opcode == X86Opcode::TrapBoundsCheckExact)
        .expect("carrier present");

    let refs: Vec<GuardOperandRef> = carrier
        .operands
        .iter()
        .filter_map(|op| match op {
            trust_cg_lower::X86ISelOperand::VReg(v) => Some(GuardOperandRef::Reg(v.id)),
            trust_cg_lower::X86ISelOperand::Imm(i) => Some(GuardOperandRef::Imm(*i)),
            _ => None,
        })
        .collect();
    // The binding key folds in the carrier's GuardKind (defense-in-depth, Item B).
    let fp = trust_cg_ir::fingerprint_for_kind(GuardKind::BoundsCheck, &refs);
    assert_eq!(
        fp,
        trust_cg_ir::fingerprint_for_kind(GuardKind::BoundsCheck, &refs)
    );
    assert!(
        isel_func.guard_obligations.contains_key(&fp),
        "explicit id binding is traceable"
    );
    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "traceable identity is not replay authority"
    );
}
