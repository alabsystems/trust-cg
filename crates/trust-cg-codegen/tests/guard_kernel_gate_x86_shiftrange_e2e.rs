// guard_kernel_gate_x86_shiftrange_e2e.rs — Fail-closed SHIFT-RANGE authority tests on x86-64
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Public `ShiftInRange` annotations and adapter-synthesized ids are non-authoritative. The real
//! adapter reports no synthesized discharge, the selector leaves the carrier unbound, and the
//! compiler retains the hardware range guard for both legacy gate environment values.
//!
//! Fingerprint coverage remains load-bearing: the shift width participates in identity, while the
//! suite separately proves that stable identity alone is not deletion authority.

mod common;

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
    BinOp, Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module, ProofAnnotation, Ty, ValueId,
};

/// Build a trust-ir module whose single function does `i64 shl(i64 a, i64 b) { return a << b; }` with
/// the shift carrying the public `ShiftInRange` annotation.
fn build_shift_in_range_module() -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_x86_shiftrange_e2e");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "proven_shl_x86", ft, BlockId::new(0));
    let shl = InstrNode::new(Inst::BinOp {
        op: BinOp::Shl,
        ty: Ty::I64,
        lhs: ValueId::new(0),
        rhs: ValueId::new(1),
    })
    .with_result(ValueId::new(2))
    .with_proof(ProofAnnotation::ShiftInRange);
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            shl,
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
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

/// Count the live x86 shift-range-check carriers in the function.
fn live_x86_shift_range_carriers(func: &X86ISelFunction) -> usize {
    func.block_order
        .iter()
        .filter_map(|b| func.blocks.get(b))
        .flat_map(|b| b.insts.iter())
        .filter(|i: &&X86ISelInst| i.opcode == X86Opcode::TrapShiftRangeExact)
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
fn x86_kernel_gate_rejects_shift_in_range_annotation_as_authority() {
    let (module, func) = build_shift_in_range_module();
    let (mut isel_func, synthesized) = lower_to_x86_isel(&func, &module);

    assert!(
        synthesized.is_empty(),
        "public ShiftInRange annotation must not synthesize deletion authority"
    );

    // Real x86 lowering emits exactly one carrier and deliberately leaves it unbound.
    assert_eq!(
        live_x86_shift_range_carriers(&isel_func),
        1,
        "real x86 lowering must emit exactly one shift-range-check carrier"
    );
    assert_eq!(
        isel_func.guard_obligations.len(),
        0,
        "annotation-only shift carrier must not receive an authority binding"
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
        live_x86_shift_range_carriers(&isel_func),
        1,
        "the x86 shift-range carrier must be retained without replay authority"
    );
    assert!(pass.kernel_eliminations().is_empty());
    assert!(pass.recheck_kernel_eliminations().is_ok());
}

/// Duplicate control proving the annotation-only path has empty authority inputs.
#[test]
fn x86_annotation_only_shift_range_has_empty_authority_inputs() {
    let (module, func) = build_shift_in_range_module();
    let (mut isel_func, synthesized) = lower_to_x86_isel(&func, &module);

    assert_eq!(live_x86_shift_range_carriers(&isel_func), 1);
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
        live_x86_shift_range_carriers(&isel_func),
        1,
        "empty authority inputs keep the shift-range guard fail-closed"
    );
    assert_eq!(pass.kernel_eliminations().len(), 0);
}

/// Count UD2 (0F 0B) occurrences in raw object bytes. A surviving x86 shift-range-check carrier expands
/// to a synthetic UD2 trap block, so UD2 presence is the observable for "guard kept".
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

/// Full-pipeline refutation: neither legacy environment value may authorize guard deletion. The shift
/// and the runtime range trap remain present in both objects.
#[test]
fn x86_shift_range_kernel_gate_env_values_keep_hardware_guard() {
    use common::disasm::{disassemble_x86_text, has_objdump};

    let (module, _func) = build_shift_in_range_module();

    let (off, on, off_ud2, on_ud2) = env_lock::with_env_edits(|env| {
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "0");
        let off = compile_x86_object(&module);
        let off_ud2 = ud2_count(&off);
        assert!(
            off_ud2 >= 1,
            "legacy value 0 must keep the UD2 shift-range trap"
        );

        env.set("TRUST_CG_GUARD_KERNEL_GATE", "1");
        let on = compile_x86_object(&module);
        let on_ud2 = ud2_count(&on);
        (off, on, off_ud2, on_ud2)
    });

    assert!(
        on_ud2 >= 1,
        "legacy value 1 must keep the UD2 shift-range trap"
    );
    assert_eq!(
        on_ud2, off_ud2,
        "environment values must not alter guard retention"
    );

    // The shift survives in both real functions.
    assert!(!off.is_empty() && !on.is_empty());
    assert_eq!(on.len(), off.len());

    // SEMANTIC object-level oracle (when objdump is available on the host): decode the actual emitted
    // x86 stream and assert the shift and runtime trap are present under both legacy values.
    if has_objdump() {
        let off_insns = disassemble_x86_text(&off).expect("objdump decodes gate-off object");
        let on_insns = disassemble_x86_text(&on).expect("objdump decodes gate-on object");

        // A variable shift lowers to `shl`/`sal`/`shlx` (left-shift) on x86-64.
        let has_shift = |insns: &[common::disasm::DisasmInsn]| {
            insns
                .iter()
                .any(|i| i.mnemonic.starts_with("shl") || i.mnemonic.starts_with("sal"))
        };
        assert!(
            has_shift(&off_insns),
            "gate OFF: the shift (shl/sal/shlx) must be present — the operation is never removed"
        );
        assert!(
            has_shift(&on_insns),
            "legacy value 1: the shift (shl/sal/shlx) must still be present"
        );

        let ud2s = |insns: &[common::disasm::DisasmInsn]| {
            insns.iter().filter(|i| i.mnemonic == "ud2").count()
        };
        assert!(
            ud2s(&off_insns) >= 1,
            "gate OFF: the kept shift-range carrier expands to a real ud2 trap"
        );
        assert!(
            ud2s(&on_insns) >= 1,
            "legacy value 1 keeps the shift-range trap"
        );
    }
}

/// The fingerprint is stable and width-sensitive, but must remain unbound without exact replay.
#[test]
fn x86_shift_range_fingerprint_is_width_sensitive_but_unbound() {
    let (module, func) = build_shift_in_range_module();
    let (isel_func, _) = lower_to_x86_isel(&func, &module);

    let carrier = isel_func
        .block_order
        .iter()
        .filter_map(|b| isel_func.blocks.get(b))
        .flat_map(|b| b.insts.iter())
        .find(|i| i.opcode == X86Opcode::TrapShiftRangeExact)
        .expect("shift-range carrier present");

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
        2,
        "shift-range carrier fingerprints over [amount, Imm(bitwidth)]"
    );
    // The width must be 64 for an i64 shift — it is operand 1 of the carrier.
    assert_eq!(refs[1], GuardOperandRef::Imm(64));
    // The binding key folds in GuardKind::ShiftRange (defense-in-depth, Item B).
    let fp = trust_cg_ir::fingerprint_for_kind(GuardKind::ShiftRange, &refs);
    assert!(
        !isel_func.guard_obligations.contains_key(&fp),
        "identity is not authority"
    );

    // SOUNDNESS: a narrower (width-32) proof's binding key differs, so it cannot discharge this guard.
    let amount_ref = refs[0];
    let fp_width_32 = trust_cg_ir::fingerprint_for_kind(
        GuardKind::ShiftRange,
        &[amount_ref, GuardOperandRef::Imm(32)],
    );
    assert_ne!(
        fp, fp_width_32,
        "the width is part of the binding key: a 32-bit proof cannot discharge a 64-bit shift guard"
    );
    assert!(!isel_func.guard_obligations.contains_key(&fp_width_32));
}
