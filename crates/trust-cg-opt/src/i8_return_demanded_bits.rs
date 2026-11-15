//! Demanded-bits simplification for an exact narrow AArch64 return shape.
//!
//! An `I8` function result observes only bits 7:0 of the value placed in W0.
//! Therefore the terminal sequence
//!
//! ```text
//! masked = AndRI source, #255
//! narrow = Uxtb masked
//! Copy W0, narrow
//! Ret X30                     ; implicit-use W0
//! ```
//!
//! may feed the return copy directly from `source`: both the mask and `Uxtb`
//! preserve exactly those eight observable bits.  The producer instructions
//! are deliberately left in place.  Ordinary DCE removes them only when they
//! have no other users, so a 32-bit consumer continues to see the fully masked
//! value.
//!
//! This is a contextual equivalence, not a full-W-register identity.  The pass
//! consequently fails closed unless the function signature, ABI register,
//! terminal `Ret`, register widths, immediate, and same-block instruction order
//! all establish the exact I8-return observation.

use trust_cg_ir::{
    AArch64Opcode, MachFunction, MachOperand, PassId, ProvenanceMap, RegClass, Type, VReg,
    regs::{W0, X30},
};

use crate::pass_manager::{AnalysisCache, MachinePass};

/// Stable pass identity used by the optimization pipeline.
pub const I8_RETURN_DEMANDED_BITS_PASS_NAME: &str = "i8-return-demanded-bits";
/// Stable semantic obligation bound into the transform provenance.
pub const I8_RETURN_DEMANDED_BITS_PROOF_ID: &str = "trust-cg.opt.i8-return-and255-low8.v1";
/// Width of the W-register value consumed by the exact return suffix.
pub const I8_RETURN_DEMANDED_BITS_CONTAINER_BITS: u32 = 32;
/// Only these low bits are observable through an `I8` return.
pub const I8_RETURN_DEMANDED_BITS_OBSERVED_BITS: u32 = 8;
/// Exact `AndRI` immediate admitted by the shared optimization/proof schema.
pub const I8_RETURN_DEMANDED_BITS_MASK: i64 = (1_i64 << I8_RETURN_DEMANDED_BITS_OBSERVED_BITS) - 1;

fn proof_bound_pass_id() -> PassId {
    PassId::new(format!(
        "{I8_RETURN_DEMANDED_BITS_PASS_NAME}@{I8_RETURN_DEMANDED_BITS_PROOF_ID}"
    ))
}

/// Bypass an exact `AndRI #255` + `Uxtb` chain only at a terminal I8 ABI
/// return copy.
pub struct I8ReturnDemandedBits;

impl MachinePass for I8ReturnDemandedBits {
    fn name(&self) -> &str {
        I8_RETURN_DEMANDED_BITS_PASS_NAME
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_pass(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_pass(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_pass(func, Some(provenance))
    }
}

fn gpr32_vreg(operand: &MachOperand) -> Option<VReg> {
    let MachOperand::VReg(vreg) = operand else {
        return None;
    };
    (vreg.class == RegClass::Gpr32).then_some(*vreg)
}

fn run_pass(func: &mut MachFunction, mut provenance: Option<&mut ProvenanceMap>) -> bool {
    if func.signature.returns.as_slice() != [Type::I8] {
        return false;
    }

    let mut rewrite_sites = Vec::new();

    for &block_id in &func.block_order {
        let inst_ids = &func.block(block_id).insts;
        if inst_ids.len() < 4 {
            continue;
        }

        // RET is a terminator, so requiring this exact four-instruction suffix
        // also proves that none of the bypassed source registers is redefined
        // between the AND and the return copy.  It remains sound in non-SSA
        // MachIR without relying on a global single-definition assumption.
        let suffix = &inst_ids[inst_ids.len() - 4..];
        let and_id = suffix[0];
        let uxtb_id = suffix[1];
        let copy_id = suffix[2];
        let ret_id = suffix[3];

        let and = func.inst(and_id);
        let uxtb = func.inst(uxtb_id);
        let copy = func.inst(copy_id);
        let ret = func.inst(ret_id);

        if and.opcode != AArch64Opcode::AndRI
            || and.operands.len() != 3
            || !and.implicit_defs.is_empty()
            || !and.implicit_uses.is_empty()
            || !matches!(
                and.operands.get(2),
                Some(MachOperand::Imm(I8_RETURN_DEMANDED_BITS_MASK))
            )
            || uxtb.opcode != AArch64Opcode::Uxtb
            || uxtb.operands.len() != 2
            || !uxtb.implicit_defs.is_empty()
            || !uxtb.implicit_uses.is_empty()
            || copy.opcode != AArch64Opcode::Copy
            || copy.operands.len() != 2
            || !copy.implicit_defs.is_empty()
            || !copy.implicit_uses.is_empty()
            || copy.operands[0] != MachOperand::PReg(W0)
            || ret.opcode != AArch64Opcode::Ret
            || ret.operands != [MachOperand::PReg(X30)]
            || !ret.implicit_defs.is_empty()
            || ret.implicit_uses != [W0]
        {
            continue;
        }

        let Some(and_dst) = gpr32_vreg(&and.operands[0]) else {
            continue;
        };
        let Some(source) = gpr32_vreg(&and.operands[1]) else {
            continue;
        };
        let Some(uxtb_dst) = gpr32_vreg(&uxtb.operands[0]) else {
            continue;
        };
        let Some(uxtb_src) = gpr32_vreg(&uxtb.operands[1]) else {
            continue;
        };
        let Some(copy_src) = gpr32_vreg(&copy.operands[1]) else {
            continue;
        };

        if uxtb_src != and_dst
            || copy_src != uxtb_dst
            || source == and_dst
            || source == uxtb_dst
            || and_dst == uxtb_dst
        {
            continue;
        }

        rewrite_sites.push((copy_id, source));
    }

    if rewrite_sites.is_empty() {
        return false;
    }

    for (copy_id, source) in rewrite_sites {
        // Rewrite only the narrow observer.  The AND/UXTB definitions and all
        // their other uses remain byte-for-byte untouched.
        func.inst_mut(copy_id).operands[1] = MachOperand::VReg(source);
        if let Some(provenance) = provenance.as_deref_mut() {
            provenance.record_in_place_transform(copy_id, proof_bound_pass_id());
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{MachInst, Signature, TrustIrInstId, regs::W1};

    static RETURN_W0: &[trust_cg_ir::PReg] = &[W0];

    fn vreg(id: u32, class: RegClass) -> MachOperand {
        MachOperand::VReg(VReg::new(id, class))
    }

    fn v32(id: u32) -> MachOperand {
        vreg(id, RegClass::Gpr32)
    }

    fn exact_chain(signature_return: Type) -> (MachFunction, [trust_cg_ir::InstId; 4]) {
        let mut func = MachFunction::new(
            "i8_return_bits".into(),
            Signature::new(vec![Type::I32], vec![signature_return]),
        );
        let block = func.entry;
        let insts = [
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![
                    v32(1),
                    v32(0),
                    MachOperand::Imm(I8_RETURN_DEMANDED_BITS_MASK),
                ],
            ),
            MachInst::new(AArch64Opcode::Uxtb, vec![v32(2), v32(1)]),
            MachInst::new(AArch64Opcode::Copy, vec![MachOperand::PReg(W0), v32(2)]),
            MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)])
                .with_implicit_uses(RETURN_W0),
        ];
        let mut ids = Vec::new();
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
            ids.push(id);
        }
        (func, ids.try_into().expect("four fixture instructions"))
    }

    #[test]
    fn exact_i8_return_bypasses_mask_chain_at_the_consumer_only() {
        let (mut func, [and_id, uxtb_id, copy_id, _]) = exact_chain(Type::I8);

        assert!(I8ReturnDemandedBits.run(&mut func));
        assert_eq!(
            func.inst(copy_id).operands,
            vec![MachOperand::PReg(W0), v32(0)]
        );
        assert_eq!(func.inst(and_id).opcode, AArch64Opcode::AndRI);
        assert_eq!(func.inst(and_id).operands[1], v32(0));
        assert_eq!(func.inst(uxtb_id).opcode, AArch64Opcode::Uxtb);
        assert_eq!(func.inst(uxtb_id).operands[1], v32(1));
        assert!(
            !I8ReturnDemandedBits.run(&mut func),
            "pass must be idempotent"
        );
    }

    #[test]
    fn provenance_binds_the_rewrite_to_the_shared_proof_id() {
        let (mut func, [_, _, copy_id, _]) = exact_chain(Type::I8);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(7), &[copy_id], PassId::new("isel"));

        assert!(I8ReturnDemandedBits.run_with_provenance(&mut func, &mut provenance));
        let entry = provenance
            .get_entry(copy_id)
            .expect("return copy provenance must remain present");
        let transform = entry.transforms.last().expect("rewrite transform record");
        assert_eq!(
            transform.pass.name(),
            format!("{I8_RETURN_DEMANDED_BITS_PASS_NAME}@{I8_RETURN_DEMANDED_BITS_PROOF_ID}")
        );
    }

    #[test]
    fn non_i8_signatures_never_authorize_the_contextual_rewrite() {
        for ty in [Type::I16, Type::I32, Type::B1] {
            let (mut func, [_, _, copy_id, _]) = exact_chain(ty.clone());
            assert!(
                !I8ReturnDemandedBits.run(&mut func),
                "unexpected {ty:?} rewrite"
            );
            assert_eq!(func.inst(copy_id).operands[1], v32(2));
        }
    }

    #[test]
    fn wrong_mask_width_or_return_contract_fails_closed() {
        let (mut wrong_mask, [and_id, _, _, _]) = exact_chain(Type::I8);
        wrong_mask.inst_mut(and_id).operands[2] = MachOperand::Imm(511);
        assert!(!I8ReturnDemandedBits.run(&mut wrong_mask));

        let (mut wrong_width, [and_id, _, _, _]) = exact_chain(Type::I8);
        wrong_width.inst_mut(and_id).operands[1] = vreg(0, RegClass::Gpr64);
        assert!(!I8ReturnDemandedBits.run(&mut wrong_width));

        let (mut wrong_preg, [_, _, copy_id, _]) = exact_chain(Type::I8);
        wrong_preg.inst_mut(copy_id).operands[0] = MachOperand::PReg(W1);
        assert!(!I8ReturnDemandedBits.run(&mut wrong_preg));

        let (mut no_liveout, [_, _, _, ret_id]) = exact_chain(Type::I8);
        no_liveout.inst_mut(ret_id).implicit_uses = &[];
        assert!(!I8ReturnDemandedBits.run(&mut no_liveout));

        let (mut wrong_ret_target, [_, _, _, ret_id]) = exact_chain(Type::I8);
        wrong_ret_target.inst_mut(ret_id).operands[0] = MachOperand::PReg(W1);
        assert!(!I8ReturnDemandedBits.run(&mut wrong_ret_target));

        let (mut extra_ret_target, [_, _, _, ret_id]) = exact_chain(Type::I8);
        extra_ret_target
            .inst_mut(ret_id)
            .operands
            .push(MachOperand::PReg(W1));
        assert!(!I8ReturnDemandedBits.run(&mut extra_ret_target));

        let (mut ret_def, [_, _, _, ret_id]) = exact_chain(Type::I8);
        ret_def.inst_mut(ret_id).implicit_defs = &[W1];
        assert!(!I8ReturnDemandedBits.run(&mut ret_def));
    }

    #[test]
    fn nonlocal_or_redefined_source_fails_closed() {
        let (mut nonlocal, [and_id, uxtb_id, copy_id, ret_id]) = exact_chain(Type::I8);
        let other = nonlocal.create_block();
        let entry = nonlocal.entry;
        nonlocal.block_mut(entry).insts = vec![and_id];
        nonlocal.block_mut(other).insts = vec![uxtb_id, copy_id, ret_id];
        assert!(!I8ReturnDemandedBits.run(&mut nonlocal));

        let (mut redefined, [and_id, uxtb_id, copy_id, ret_id]) = exact_chain(Type::I8);
        let redefine = redefined.push_inst(MachInst::new(
            AArch64Opcode::MovI,
            vec![v32(0), MachOperand::Imm(7)],
        ));
        let entry = redefined.entry;
        redefined.block_mut(entry).insts = vec![and_id, redefine, uxtb_id, copy_id, ret_id];
        assert!(!I8ReturnDemandedBits.run(&mut redefined));
    }

    #[test]
    fn other_32bit_consumers_remain_on_the_masked_values() {
        let (mut func, [_, _, copy_id, _]) = exact_chain(Type::I8);
        let consumer_block = func.create_block();
        let consumer = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![v32(9), v32(1), MachOperand::Imm(1)],
        ));
        func.append_inst(consumer_block, consumer);

        assert!(I8ReturnDemandedBits.run(&mut func));
        assert_eq!(func.inst(copy_id).operands[1], v32(0));
        assert_eq!(
            func.inst(consumer).operands[1],
            v32(1),
            "a 32-bit consumer must continue reading the masked result"
        );
    }
}
