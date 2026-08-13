// guard_kernel_gate_x86_null_e2e.rs — Fail-closed NULL-check authority tests on x86-64
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Public `NotNull` annotations and synthesized ids are non-authoritative. The real adapter must
//! report no synthesized discharge, the selector must leave the carrier unbound, and the compiler
//! must retain the hardware null guard for both legacy gate environment values.
//!
//! The stable single-operand fingerprint is still checked, but its reproducibility is explicitly not
//! treated as proof authority.

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

use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

/// Build a trust-ir module whose single function does `i64 deref(i64* p) { return *p; }` with the
/// load's pointer carrying the public `NotNull` annotation.
fn build_not_null_module() -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_x86_null_e2e");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "proven_deref_x86", ft, BlockId::new(0));
    let load = InstrNode::new(Inst::Load {
        ty: Ty::I64,
        ptr: ValueId::new(0),
        volatile: false,
        align: Some(8),
    })
    .with_result(ValueId::new(1))
    .with_proof(ProofAnnotation::NotNull);
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            load,
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (module, func)
}

/// Lower a single trust-ir function to an x86 ISel function via the real adapter + x86 ISel, mirroring
/// `Compiler::compile_x86_64`'s ISel phase. Returns the X86ISelFunction (with the ISel-recorded
/// carrier->obligation bindings) and the adapter's synthesized-id report.
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

/// Count the live x86 null-check carriers in the function.
fn live_x86_null_carriers(func: &X86ISelFunction) -> usize {
    func.block_order
        .iter()
        .filter_map(|b| func.blocks.get(b))
        .flat_map(|b| b.insts.iter())
        .filter(|i: &&X86ISelInst| i.opcode == X86Opcode::TrapNullIfZeroExact)
        .count()
}

/// Build the carrier->obligation map the x86 gate consumes: re-derive each carrier's operand
/// fingerprint exactly as the kernel does (`X86GuardTarget::operand_identity`) and look the obligation
/// up in the ISel-recorded `guard_obligations` (keyed by that same fingerprint).
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
fn x86_kernel_gate_rejects_not_null_annotation_as_authority() {
    let (module, func) = build_not_null_module();
    let (mut isel_func, synthesized) = lower_to_x86_isel(&func, &module);

    assert!(
        synthesized.is_empty(),
        "public NotNull annotation must not synthesize deletion authority"
    );

    // The carrier survives lowering and remains deliberately unbound.
    assert_eq!(
        live_x86_null_carriers(&isel_func),
        1,
        "real x86 lowering must emit exactly one null-check carrier"
    );
    assert_eq!(
        isel_func.guard_obligations.len(),
        0,
        "annotation-only null carrier must not receive an authority binding"
    );

    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(evidence.is_empty(), "no module obligations in this fixture");

    let carrier_map = build_carrier_obligation_map(&isel_func);
    assert_eq!(
        carrier_map.len(),
        0,
        "no exact replay means no carrier-to-obligation authority map"
    );

    // Run the gated x86 pass.
    let mut pass = X86ProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    let changed = pass.run_on_function(&mut isel_func);

    assert!(!changed, "empty replay authority must reject elimination");
    assert_eq!(
        live_x86_null_carriers(&isel_func),
        1,
        "the x86 null-check carrier must be retained without replay authority"
    );
    assert!(pass.kernel_eliminations().is_empty());
    assert!(pass.recheck_kernel_eliminations().is_ok());
}

/// Duplicate control proving the adapter and evidence builder both remain empty for annotation-only
/// input.
#[test]
fn x86_annotation_only_null_check_has_empty_authority_inputs() {
    let (module, func) = build_not_null_module();
    let (mut isel_func, synthesized) = lower_to_x86_isel(&func, &module);

    assert_eq!(live_x86_null_carriers(&isel_func), 1);
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
        live_x86_null_carriers(&isel_func),
        1,
        "empty authority inputs keep the null guard fail-closed"
    );
    assert_eq!(pass.kernel_eliminations().len(), 0);
}

/// Count UD2 (0F 0B) occurrences in raw object bytes. A surviving x86 null-check carrier expands to a
/// synthetic UD2 trap block, so UD2 presence is the observable for "guard kept".
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

/// Full-pipeline refutation: neither legacy environment value may authorize null-guard deletion.
#[test]
fn x86_null_kernel_gate_env_values_keep_hardware_guard() {
    let (module, _func) = build_not_null_module();

    let (off, on, off_ud2, on_ud2) = env_lock::with_env_edits(|env| {
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "0");
        let off = compile_x86_object(&module);
        let off_ud2 = ud2_count(&off);
        assert!(
            off_ud2 >= 1,
            "legacy value 0 must keep the UD2 null-check trap"
        );

        env.set("TRUST_CG_GUARD_KERNEL_GATE", "1");
        let on = compile_x86_object(&module);
        let on_ud2 = ud2_count(&on);
        (off, on, off_ud2, on_ud2)
    });

    assert!(
        on_ud2 >= 1,
        "legacy value 1 must keep the UD2 null-check trap"
    );
    assert_eq!(
        on_ud2, off_ud2,
        "environment values must not alter guard retention"
    );

    // Both objects remain non-empty real functions and have identical guarded code size.
    assert!(!off.is_empty() && !on.is_empty());
    assert_eq!(on.len(), off.len());
}

/// The null fingerprint remains deterministic, but the public annotation must not bind it.
#[test]
fn x86_null_carrier_fingerprint_is_stable_but_unbound_without_replay() {
    let (module, func) = build_not_null_module();
    let (isel_func, _) = lower_to_x86_isel(&func, &module);

    let carrier = isel_func
        .block_order
        .iter()
        .filter_map(|b| isel_func.blocks.get(b))
        .flat_map(|b| b.insts.iter())
        .find(|i| i.opcode == X86Opcode::TrapNullIfZeroExact)
        .expect("null carrier present");

    let refs: Vec<GuardOperandRef> = carrier
        .operands
        .iter()
        .filter_map(|op| match op {
            trust_cg_lower::X86ISelOperand::VReg(v) => Some(GuardOperandRef::Reg(v.id)),
            trust_cg_lower::X86ISelOperand::Imm(i) => Some(GuardOperandRef::Imm(*i)),
            _ => None,
        })
        .collect();
    assert_eq!(
        refs.len(),
        1,
        "null carrier fingerprints over a single [ptr] operand"
    );
    // The binding key folds in GuardKind::NullPtr (defense-in-depth, Item B).
    let fp = trust_cg_ir::fingerprint_for_kind(GuardKind::NullPtr, &refs);
    assert_eq!(
        fp,
        trust_cg_ir::fingerprint_for_kind(GuardKind::NullPtr, &refs)
    );
    assert!(
        !isel_func.guard_obligations.contains_key(&fp),
        "identity is not authority"
    );
}
