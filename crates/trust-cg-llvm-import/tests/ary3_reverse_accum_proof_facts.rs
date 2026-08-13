#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / ary3_reverse_accum_proof_facts.rs
//
// Imported-O0 ary3 reverse-accumulation proof-fact coverage for #935.

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::aarch64_regs::preg_class;
use trust_cg_ir::{AArch64Opcode, MachFunction, MachOperand, RegClass};
use trust_cg_llvm_import::import_text;
use trust_ir::{Inst, ProofAnnotation, Ty};

const ARY3_REVERSE_ACCUM_LL: &str = include_str!("fixtures/ary3_reverse_accum_clang_o0.ll");

fn opcode_count(func: &MachFunction, opcode: AArch64Opcode) -> usize {
    func.block_order
        .iter()
        .flat_map(|&block_id| func.block(block_id).insts.iter().copied())
        .filter(|&inst_id| func.inst(inst_id).opcode == opcode)
        .count()
}

fn q_pair_opcode_count(func: &MachFunction, opcode: AArch64Opcode) -> usize {
    fn is_fpr128(operand: &MachOperand) -> bool {
        match operand {
            MachOperand::VReg(vreg) => vreg.class == RegClass::Fpr128,
            MachOperand::PReg(preg) => preg_class(*preg) == RegClass::Fpr128,
            _ => false,
        }
    }

    func.block_order
        .iter()
        .flat_map(|&block_id| func.block(block_id).insts.iter().copied())
        .filter(|&inst_id| {
            let inst = func.inst(inst_id);
            inst.opcode == opcode
                && inst.operands.len() >= 2
                && is_fpr128(&inst.operands[0])
                && is_fpr128(&inst.operands[1])
        })
        .count()
}

fn has_scalar_reverse_accumulate_chain(func: &MachFunction) -> bool {
    func.block_order.iter().any(|&block_id| {
        func.block(block_id).insts.windows(4).any(|window| {
            let first_load = func.inst(window[0]);
            let second_load = func.inst(window[1]);
            let add = func.inst(window[2]);
            let store = func.inst(window[3]);
            if first_load.opcode != AArch64Opcode::LdrRO
                || second_load.opcode != AArch64Opcode::LdrRO
                || add.opcode != AArch64Opcode::AddRR
                || store.opcode != AArch64Opcode::StrRO
                || first_load.operands.len() != 4
                || second_load.operands.len() != 4
                || add.operands.len() != 3
                || store.operands.len() != 4
            {
                return false;
            }

            let add_reads_both_loads = (add.operands[1] == first_load.operands[0]
                && add.operands[2] == second_load.operands[0])
                || (add.operands[2] == first_load.operands[0]
                    && add.operands[1] == second_load.operands[0]);
            let store_writes_add = store.operands[0] == add.operands[0];
            let store_reuses_loaded_destination = store.operands[1..] == first_load.operands[1..]
                || store.operands[1..] == second_load.operands[1..];

            add_reads_both_loads && store_writes_add && store_reuses_loaded_destination
        })
    })
}

fn dump_function_shape(func: &MachFunction) {
    for &block_id in &func.block_order {
        eprintln!(
            "bb{} preds={:?} succs={:?}",
            block_id.0,
            func.block(block_id).preds,
            func.block(block_id).succs
        );
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            eprintln!("  i{} {:?} {:?}", inst_id.0, inst.opcode, inst.operands);
        }
    }
}

#[test]
fn imported_o0_ary3_reverse_accum_preserves_allocator_gep_facts() {
    let module =
        import_text(ARY3_REVERSE_ACCUM_LL, "ary3_reverse_accum_clang_o0").expect("import fixture");
    let run_case = module
        .functions
        .iter()
        .find(|function| function.name == "run_case")
        .expect("run_case function");

    let mut allocator_calls_with_facts = 0;
    let mut pointer_slot_loads_with_facts = 0;
    let mut noalias_inbounds_geps = 0;

    for block in &run_case.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Call { .. } => {
                    if node.proofs.contains(&ProofAnnotation::NoAlias)
                        && node.proofs.contains(&ProofAnnotation::Aligned(16))
                    {
                        allocator_calls_with_facts += 1;
                    }
                }
                Inst::Load { ty: Ty::Ptr, .. } => {
                    if node.proofs.contains(&ProofAnnotation::NoAlias)
                        && node.proofs.contains(&ProofAnnotation::Aligned(16))
                    {
                        pointer_slot_loads_with_facts += 1;
                    }
                }
                Inst::GEP { .. }
                    if node.proofs.contains(&ProofAnnotation::InBounds)
                        && node.proofs.contains(&ProofAnnotation::NoAlias) =>
                {
                    noalias_inbounds_geps += 1;
                }
                _ => {}
            }
        }
    }

    assert_eq!(
        allocator_calls_with_facts, 2,
        "both calloc results should import allocator NoAlias/Aligned facts"
    );
    assert!(
        pointer_slot_loads_with_facts >= 5,
        "O0 pointer-slot loads should preserve allocator facts, got {pointer_slot_loads_with_facts}"
    );
    assert!(
        noalias_inbounds_geps >= 3,
        "reverse/check GEPs should carry NoAlias plus InBounds, got {noalias_inbounds_geps}"
    );
}

#[test]
fn imported_o0_ary3_reverse_accum_o2_fails_closed_without_replay_authority() {
    let module =
        import_text(ARY3_REVERSE_ACCUM_LL, "ary3_reverse_accum_clang_o0").expect("import fixture");
    let lowered = trust_cg_lower::translate_module(&module).expect("lower imported fixture");
    let (run_case, proof_ctx) = lowered
        .iter()
        .find(|(function, _)| function.name == "run_case")
        .expect("lowered run_case function");
    assert!(
        proof_ctx
            .value_facts
            .values()
            .any(|facts| facts.contains(&trust_cg_lower::ProofFact::InBounds)),
        "lowering must retain imported InBounds facts for report-only metadata"
    );
    assert!(
        proof_ctx
            .value_facts
            .values()
            .any(|facts| facts.contains(&trust_cg_lower::ProofFact::NoAlias)),
        "lowering must retain imported NoAlias facts for report-only metadata"
    );
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    });
    let (optimized, _metrics) = pipeline
        .prepare_function_with_metrics(run_case, Some(proof_ctx))
        .expect("prepare run_case through real O2 pipeline");
    if std::env::var_os("TRUST_CG_ARY3_REVERSE_DIAG").is_some() {
        dump_function_shape(&optimized);
    }

    assert!(
        !trust_cg_lower::guard_evidence::validator_guard_replay_authority_available(),
        "update this production-boundary test when exact validator replay authority is wired"
    );
    assert_eq!(
        q_pair_opcode_count(&optimized, AArch64Opcode::LdpRI),
        0,
        "report-only imported facts must not authorize pair loads in production"
    );
    assert_eq!(
        opcode_count(&optimized, AArch64Opcode::NeonAddV),
        0,
        "report-only imported facts must not authorize vector addition in production"
    );
    assert_eq!(
        q_pair_opcode_count(&optimized, AArch64Opcode::StpRI),
        0,
        "report-only imported facts must not authorize pair stores in production"
    );
    assert!(
        has_scalar_reverse_accumulate_chain(&optimized),
        "the fail-closed production path must retain a same-block scalar load/load/add/store \
         chain whose add consumes both loads and whose store writes the loaded destination"
    );
}
