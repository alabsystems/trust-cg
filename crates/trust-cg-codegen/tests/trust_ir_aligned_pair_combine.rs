// Producer-owned alignment facts are report metadata until an independent
// replay capability is wired.  These integration tests ensure the public pass
// cannot turn constructible sidecar facts into behavior authority.

use trust_cg_codegen::pipeline::ir_to_regalloc;
use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, ProofFact, RegClass, Signature,
    VReg,
    regs::{X0, X1, X2},
};
use trust_cg_opt::addr_mode::AddrModeEarlyFormation;
use trust_cg_opt::pass_manager::MachinePass;
use trust_cg_opt::proof_opts::ProofOptimization;

fn vreg(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn preg(reg: trust_cg_ir::PReg) -> MachOperand {
    MachOperand::PReg(reg)
}

#[test]
fn explicit_ldpri_vreg_operands_expose_two_regalloc_defs() {
    let mut func = MachFunction::new(
        "trust_ir_aligned_ldp_classification".to_string(),
        Signature::new(vec![], vec![]),
    );
    let pair_id = func.push_inst(MachInst::new(
        AArch64Opcode::LdpRI,
        vec![vreg(0), vreg(1), vreg(2), imm(0)],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, pair_id);
    func.append_inst(func.entry, ret);

    let ra_func = ir_to_regalloc(&func).expect("explicit LDP must adapt to regalloc");
    let ra_pair = &ra_func.insts[pair_id.0 as usize];
    assert_eq!(ra_pair.defs.len(), 2);
    assert_eq!(ra_pair.uses.len(), 2);
    assert_eq!(
        ra_pair.defs[0].as_vreg(),
        Some(VReg::new(0, RegClass::Gpr64))
    );
    assert_eq!(
        ra_pair.defs[1].as_vreg(),
        Some(VReg::new(1, RegClass::Gpr64))
    );
    assert_eq!(
        ra_pair.uses[0].as_vreg(),
        Some(VReg::new(2, RegClass::Gpr64))
    );
}

#[test]
fn aligned_pre_ra_vreg_store_pair_fact_is_report_only() {
    let mut func = MachFunction::new(
        "trust_ir_aligned_pair_combine".to_string(),
        Signature::new(vec![], vec![]),
    );
    let str0 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![vreg(0), vreg(2), imm(0)],
    ));
    let str1 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![vreg(1), vreg(2), imm(8)],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, str0);
    func.append_inst(func.entry, str1);
    func.append_inst(func.entry, ret);

    let mut pass = ProofOptimization::new();
    pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
    pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

    assert!(!pass.run(&mut func));
    assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    assert!(pass.certificates().is_empty());
    assert_eq!(func.block(func.entry).insts, vec![str0, str1, ret]);
    assert_eq!(func.inst(str0).opcode, AArch64Opcode::StrRI);
    assert_eq!(func.inst(str1).opcode, AArch64Opcode::StrRI);
    ir_to_regalloc(&func).expect("unchanged scalar stores must adapt to regalloc");
}

#[test]
fn aligned_store_pair_spill_fact_cannot_mint_pair_certificate() {
    let mut func = MachFunction::new(
        "trust_ir_aligned_pair_combine_spill_fixture".to_string(),
        Signature::new(vec![], vec![]),
    );
    let str0 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![vreg(0), vreg(2), imm(0)],
    ));
    let str1 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![vreg(1), vreg(2), imm(8)],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, str0);
    func.append_inst(func.entry, str1);
    func.append_inst(func.entry, ret);

    let mut pass = ProofOptimization::new();
    pass.set_inst_proof_facts(str0, vec![ProofFact::Aligned(16)]);
    pass.set_inst_proof_facts(str1, vec![ProofFact::Aligned(16)]);

    assert!(!pass.run(&mut func));
    assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    assert!(pass.certificates().is_empty());
    assert_eq!(func.block(func.entry).insts, vec![str0, str1, ret]);
    ir_to_regalloc(&func).expect("unchanged scalar stores must adapt to regalloc");
}

#[test]
fn unaligned_store_pair_spill_fixture_does_not_form_pair_op_or_citation() {
    let mut func = MachFunction::new(
        "trust_ir_unaligned_pair_combine_spill_fixture".to_string(),
        Signature::new(vec![], vec![]),
    );
    let str0 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![vreg(0), vreg(2), imm(0)],
    ));
    let str1 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![vreg(1), vreg(2), imm(8)],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, str0);
    func.append_inst(func.entry, str1);
    func.append_inst(func.entry, ret);

    let mut pass = ProofOptimization::new();

    assert!(!pass.run(&mut func));
    assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    assert_eq!(pass.stats().total_certificates, 0);
    assert!(pass.certificates().is_empty());
    assert_eq!(func.block(func.entry).insts, vec![str0, str1, ret]);
    assert_eq!(func.inst(str0).opcode, AArch64Opcode::StrRI);
    assert_eq!(func.inst(str1).opcode, AArch64Opcode::StrRI);
    assert!(
        func.block(func.entry)
            .insts
            .iter()
            .all(|inst_id| func.inst(*inst_id).opcode != AArch64Opcode::StpRI)
    );
}

#[test]
fn aligned_pre_ra_vreg_load_pair_fact_is_report_only_after_addrmode() {
    let mut func = MachFunction::new(
        "trust_ir_aligned_vreg_load_pair_addri".to_string(),
        Signature::new(vec![], vec![]),
    );
    let add0 = func.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![vreg(3), vreg(2), imm(0)],
    ));
    let ldr0 = func.push_inst(MachInst::new(
        AArch64Opcode::LdrRI,
        vec![vreg(0), vreg(3), imm(0)],
    ));
    let add1 = func.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![vreg(4), vreg(2), imm(8)],
    ));
    let ldr1 = func.push_inst(MachInst::new(
        AArch64Opcode::LdrRI,
        vec![vreg(1), vreg(4), imm(0)],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, add0);
    func.append_inst(func.entry, ldr0);
    func.append_inst(func.entry, add1);
    func.append_inst(func.entry, ldr1);
    func.append_inst(func.entry, ret);

    let mut addrmode = AddrModeEarlyFormation;
    assert!(addrmode.run(&mut func));
    assert_eq!(func.block(func.entry).insts, vec![ldr0, ldr1, ret]);
    assert_eq!(func.inst(ldr0).operands, vec![vreg(0), vreg(2), imm(0)]);
    assert_eq!(func.inst(ldr1).operands, vec![vreg(1), vreg(2), imm(8)]);

    let mut pass = ProofOptimization::new();
    pass.set_inst_proof_facts(ldr0, vec![ProofFact::Aligned(16)]);

    assert!(!pass.run(&mut func));
    assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    assert!(pass.certificates().is_empty());
    assert_eq!(func.block(func.entry).insts, vec![ldr0, ldr1, ret]);
    assert_eq!(func.inst(ldr0).opcode, AArch64Opcode::LdrRI);
    assert_eq!(func.inst(ldr1).opcode, AArch64Opcode::LdrRI);
    ir_to_regalloc(&func).expect("unchanged scalar loads must adapt to regalloc");
}

#[test]
fn aligned_physical_store_pair_fact_is_report_only() {
    let mut func = MachFunction::new(
        "trust_ir_aligned_physical_pair_combine".to_string(),
        Signature::new(vec![], vec![]),
    );
    let str0 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![preg(X0), preg(X2), imm(0)],
    ));
    let str1 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![preg(X1), preg(X2), imm(8)],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, str0);
    func.append_inst(func.entry, str1);
    func.append_inst(func.entry, ret);

    let mut pass = ProofOptimization::new();
    pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);

    assert!(!pass.run(&mut func));
    assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    assert!(pass.certificates().is_empty());
    assert_eq!(func.block(func.entry).insts, vec![str0, str1, ret]);
    assert_eq!(func.inst(str0).opcode, AArch64Opcode::StrRI);
    assert_eq!(func.inst(str1).opcode, AArch64Opcode::StrRI);
    ir_to_regalloc(&func).expect("unchanged physical stores must adapt to regalloc");
}
