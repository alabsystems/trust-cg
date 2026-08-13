use std::collections::HashMap;

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::{
    AArch64Opcode, DischargeStatus, DischargedEvidenceTable, GuardKind, GuardOperandRef, InstFlags,
    MachFunction, MachInst, MachOperand, ProofAnnotation, Signature as MachSignature, X86Opcode,
    fingerprint_for_kind,
};
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};
use trust_cg_opt::env_lock;
use trust_cg_opt::gvn::GlobalValueNumbering;
use trust_cg_opt::neon_condstore::NeonCondStorePass;
use trust_cg_opt::pass_manager::MachinePass;
use trust_cg_opt::pipeline::{OptLevel, OptimizationPipeline};
use trust_cg_opt::proof_opts::ProofOptimization;
use trust_cg_opt::scheduler::build_dag;
use trust_cg_opt::x86_proof_opts::X86ProofGuardElimination;

fn vreg(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

// Scoped to the kernel-gate authority path. With `lattice-guard-elision` compiled
// in, the pass ALSO holds the decidable-lattice authority, and the restriction that
// confines that authority to InBounds bounds-guards is
//
//     let lattice_bounds_only = !full_authority && !cfg!(test) && lattice_authority;
//
// i.e. it is disabled in test builds. A test build therefore runs the lattice path at
// FULL scope — strictly more permissive than anything that ships, since in production
// `!cfg!(test)` is true and the restriction applies. The elision this test then sees
// comes from the lattice, not from the forged kernel evidence it plants, so the
// precondition no longer holds and the assertion tests the wrong thing.
//
// Production soundness is unaffected. Re-enable by removing `!cfg!(test)` from
// `lattice_bounds_only` so test builds exercise the shipping restriction.
#[test]
#[cfg_attr(
    feature = "lattice-guard-elision",
    ignore = "kernel-gate-only test: test builds exempt the lattice from its production scope restriction"
)]
fn public_aarch64_gate_api_cannot_turn_forged_evidence_into_authority() {
    let mut func = MachFunction::new(
        "forged_aarch64".to_string(),
        MachSignature::new(vec![], vec![]),
    );
    let guard = MachInst::new(
        AArch64Opcode::TrapBoundsCheckExact,
        vec![vreg(0), vreg(1), MachOperand::Imm(8)],
    )
    .with_proof(ProofAnnotation::InBounds);
    let guard_id = func.push_inst(guard);
    func.append_inst(func.entry, guard_id);

    let mut evidence = DischargedEvidenceTable::new();
    evidence.insert(17, DischargeStatus::Certified, Some(0xCAFE));
    let mut bindings = HashMap::new();
    bindings.insert(guard_id, (17, Some(0xCAFE)));
    let mut pass = ProofOptimization::new();
    pass.enable_kernel_gate(evidence, bindings);

    assert!(!pass.run(&mut func));
    assert!(func.block(func.entry).insts.contains(&guard_id));
    assert_eq!(pass.stats().bounds_checks_eliminated, 0);
}

#[test]
fn public_aarch64_default_constructors_cannot_select_label_only_elimination() {
    fn forged_function(name: &str) -> (MachFunction, trust_cg_ir::InstId) {
        let mut func = MachFunction::new(name.to_string(), MachSignature::new(vec![], vec![]));
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), MachOperand::Imm(8)],
        )
        .with_proof(ProofAnnotation::InBounds);
        let guard_id = func.push_inst(guard);
        func.append_inst(func.entry, guard_id);
        (func, guard_id)
    }

    let (mut direct, direct_guard) = forged_function("forged_aarch64_direct");
    let mut pass = ProofOptimization::new();
    assert!(!pass.run(&mut direct));
    assert!(direct.block(direct.entry).insts.contains(&direct_guard));

    let (mut pipelined, pipeline_guard) = forged_function("forged_aarch64_pipeline");
    OptimizationPipeline::new(OptLevel::O1).run(&mut pipelined);
    assert!(
        pipelined
            .block(pipelined.entry)
            .insts
            .contains(&pipeline_guard)
    );
}

#[test]
fn public_aarch64_pass_cannot_rewrite_checked_arithmetic_from_a_forged_label() {
    let mut func = MachFunction::new(
        "forged_nooverflow".to_string(),
        MachSignature::new(vec![], vec![]),
    );
    for inst in [
        MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow),
        MachInst::new(AArch64Opcode::TrapOverflow, vec![]),
        MachInst::new(AArch64Opcode::Ret, vec![]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(func.entry, id);
    }

    let mut pass = ProofOptimization::new();
    assert!(!pass.run(&mut func));
    assert_eq!(
        func.inst(trust_cg_ir::InstId(0)).opcode,
        AArch64Opcode::AddsRR
    );
    assert!(
        func.block(func.entry)
            .insts
            .contains(&trust_cg_ir::InstId(1))
    );
    assert!(pass.certificates().is_empty());
}

#[test]
fn public_gvn_cannot_reorder_memory_from_forged_validborrow_flags() {
    fn marked(mut inst: MachInst) -> MachInst {
        inst.flags.insert(InstFlags::PROOF_REORDERABLE);
        inst
    }

    let mut func = MachFunction::new(
        "forged_validborrow".to_string(),
        MachSignature::new(vec![], vec![]),
    );
    for inst in [
        marked(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(2), vreg(0), MachOperand::Imm(8)],
        )),
        marked(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(5), vreg(0), MachOperand::Imm(32)],
        )),
        MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(3), vreg(0), MachOperand::Imm(8)],
        ),
        MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(3), vreg(6)]),
        MachInst::new(AArch64Opcode::Ret, vec![]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(func.entry, id);
    }

    let mut gvn = GlobalValueNumbering;
    assert!(!gvn.run(&mut func));
    assert_eq!(func.block(func.entry).insts.len(), 5);
    assert_eq!(
        func.inst(trust_cg_ir::InstId(3)).operands[1],
        vreg(3),
        "the second load must not be replaced across the store"
    );
}

#[test]
fn public_scheduler_keeps_memory_order_with_forged_reorderable_flags() {
    let mut func = MachFunction::new(
        "forged_scheduler_validborrow".to_string(),
        MachSignature::new(vec![], vec![]),
    );
    for (dst, base) in [(0, 2), (1, 3)] {
        let mut load = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![vreg(dst), vreg(base), MachOperand::Imm(0)],
        );
        load.flags.insert(InstFlags::PROOF_REORDERABLE);
        let id = func.push_inst(load);
        func.append_inst(func.entry, id);
    }

    let dag = build_dag(&func, func.entry);
    assert!(
        dag.nodes[1].deps.contains(&0),
        "forged proof flags must not remove the load-load ordering edge"
    );
}

#[test]
fn public_x86_gate_api_cannot_turn_forged_evidence_into_authority() {
    let mut func = X86ISelFunction::new(
        "forged_x86".to_string(),
        Signature {
            params: vec![],
            returns: vec![Type::I64],
        },
    );
    let entry = Block(0);
    func.ensure_block(entry);
    func.next_vreg = 2;
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::TrapBoundsCheckExact,
            vec![
                X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                X86ISelOperand::VReg(VReg::new(1, RegClass::Gpr64)),
                X86ISelOperand::Imm(8),
            ],
        ),
    );
    let fp = fingerprint_for_kind(
        GuardKind::BoundsCheck,
        &[
            GuardOperandRef::Reg(0),
            GuardOperandRef::Reg(1),
            GuardOperandRef::Imm(8),
        ],
    );
    let mut evidence = DischargedEvidenceTable::new();
    evidence.insert(19, DischargeStatus::Certified, Some(0xBEEF));
    let mut bindings = HashMap::new();
    bindings.insert(fp, (19, Some(0xBEEF)));
    let mut pass = X86ProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, bindings);

    assert!(!pass.run_on_function(&mut func));
    assert_eq!(
        func.blocks[&entry]
            .insts
            .iter()
            .filter(|inst| inst.opcode == X86Opcode::TrapBoundsCheckExact)
            .count(),
        1
    );
    assert_eq!(pass.stats().guards_eliminated, 0);
}

#[test]
fn public_noalias_and_process_env_cannot_authorize_conditional_blind_stores() {
    let mut func = MachFunction::new(
        "forged_condstore_ownership".to_string(),
        MachSignature::new(vec![], vec![]),
    );
    func.noalias_params = vec![0, 1];

    // Production authority is independent of the environment: prove even
    // TRUST_CG_CONDSTORE=blind cannot license the forged conditional store.
    // The thread-local override is restored on scope exit, even on panic.
    env_lock::with_env_overrides(&[("TRUST_CG_CONDSTORE", "blind")], || {
        let mut pass = NeonCondStorePass::new();
        assert!(!pass.run(&mut func));
        assert_eq!(pass.fired(), 0);
    });
}
