// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Copy erasure leaves inert arena slots, not new proof or ABI authority.

use super::*;
use trust_cg_ir::InstFlags;
use trust_cg_ir::function::Type;
use trust_cg_ir::inst::{ProofAnnotation, SourceLoc};
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId, TrustIrInstId};
use trust_cg_ir::regs::{W0, W1, X0, X1, X9, X30};

fn function() -> IrMachFunction {
    let mut func = IrMachFunction::new(
        "copy_retirement".into(),
        IrSignature::new(vec![Type::I64; 2], vec![Type::I64]),
    );
    for _ in 0..10 {
        func.alloc_vreg();
    }
    func
}

fn add(func: &mut IrMachFunction, inst: IrMachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(func.entry, id);
    id
}

fn copy(dst: IrOperand, src: IrOperand) -> IrMachInst {
    IrMachInst::new(IrOpcode::Copy, vec![dst, src])
}

fn attributed(inst: IrMachInst) -> IrMachInst {
    inst.with_proof(ProofAnnotation::Pure)
        .with_source_loc(SourceLoc {
            file: 2,
            line: 19,
            col: 4,
        })
}

fn attribution(index: u32) -> LoweringProvenance {
    LoweringProvenance::SourceInst {
        id: SourceInstId { block: 0, index },
        digest: SourceInstDigest::compute("Copy", 1, 1),
        trust_ir_inst: Some(TrustIrInstId(index)),
    }
}

fn assert_retired(func: &IrMachFunction, id: InstId) {
    let inst = func.inst(id);
    assert_eq!(inst.opcode, IrOpcode::Nop);
    assert_eq!(inst.flags, InstFlags::IS_PSEUDO);
    assert!(inst.operands.is_empty());
    assert!(inst.implicit_defs.is_empty());
    assert!(inst.implicit_uses.is_empty());
    assert!(inst.proof.is_none());
    assert!(inst.source_loc.is_none());
}

fn assert_same(after: &IrMachInst, before: &IrMachInst) {
    assert_eq!(after.opcode, before.opcode);
    assert_eq!(after.operands, before.operands);
    assert_eq!(after.flags, before.flags);
    assert_eq!(after.implicit_defs, before.implicit_defs);
    assert_eq!(after.implicit_uses, before.implicit_uses);
    assert_eq!(after.proof, before.proof);
    assert_eq!(after.source_loc, before.source_loc);
}

#[test]
fn exact_erased_ids_retire_without_attached_credit_or_lost_source_history() {
    for flags in [InstFlags::EMPTY, InstFlags::IS_PSEUDO] {
        let mut func = function();
        let dead_virtual = add(
            &mut func,
            attributed(IrMachInst::with_flags(
                IrOpcode::Copy,
                vec![
                    IrOperand::VReg(VReg::new(0, RegClass::Gpr32)),
                    IrOperand::VReg(VReg::new(1, RegClass::Gpr32)),
                ],
                flags,
            )),
        );
        let dead_formal = add(
            &mut func,
            attributed(IrMachInst::with_flags(
                IrOpcode::Copy,
                vec![
                    IrOperand::VReg(VReg::new(2, RegClass::Gpr64)),
                    IrOperand::PReg(X1),
                ],
                flags,
            )),
        );
        let identity = add(
            &mut func,
            attributed(IrMachInst::with_flags(
                IrOpcode::Copy,
                vec![IrOperand::PReg(X9), IrOperand::PReg(X9)],
                flags,
            )),
        );
        let body = add(
            &mut func,
            attributed(IrMachInst::new(
                IrOpcode::AddRI,
                vec![IrOperand::PReg(X0), IrOperand::PReg(X0), IrOperand::Imm(1)],
            )),
        );
        let ret = add(
            &mut func,
            IrMachInst::new(IrOpcode::Ret, vec![IrOperand::PReg(X30)]).with_implicit_uses(&[X0]),
        );
        for id in [dead_virtual, dead_formal, identity, body] {
            func.set_inst_lowering_provenance(id, attribution(id.0));
        }
        let before = func.clone();
        lower_copies(&mut func).unwrap();
        for id in [dead_virtual, dead_formal] {
            assert_retired(&func, id);
            assert_eq!(
                func.inst_lowering_provenance(id),
                before.inst_lowering_provenance(id)
            );
        }
        let mut identity_marker = before.inst(identity).clone();
        identity_marker.opcode = IrOpcode::Nop;
        assert_same(func.inst(identity), &identity_marker);
        assert_eq!(
            func.inst_lowering_provenance(identity),
            before.inst_lowering_provenance(identity)
        );
        assert_eq!(func.insts.len(), before.insts.len());
        assert_eq!(func.block_order, before.block_order);
        assert_eq!(
            func.block(func.entry).insts,
            before.block(before.entry).insts
        );
        assert_same(func.inst(body), before.inst(body));
        assert_same(func.inst(ret), before.inst(ret));
        ensure_no_unresolved_vregs(&func, "copy-retirement test").unwrap();
        let once = format!("{func:?}");
        lower_copies(&mut func).unwrap();
        assert_eq!(format!("{func:?}"), once);
    }
}

#[test]
fn malformed_or_effectful_erasure_candidates_fail_without_becoming_tombstones() {
    for virtual_source in [false, true] {
        for mutation in 0..15 {
            let mut func = function();
            let source = if virtual_source {
                IrOperand::VReg(VReg::new(1, RegClass::Gpr64))
            } else {
                IrOperand::PReg(X1)
            };
            let mut inst = attributed(copy(IrOperand::VReg(VReg::new(0, RegClass::Gpr64)), source));
            match mutation {
                0 => inst.operands.push(IrOperand::Imm(0)),
                1 => inst.operands.push(IrOperand::PReg(X9)),
                2 => inst.operands[1] = IrOperand::Imm(0),
                3 => inst.flags.insert(InstFlags::HAS_SIDE_EFFECTS),
                4 => inst.flags.insert(InstFlags::READS_MEMORY),
                5 => inst.flags.insert(InstFlags::WRITES_MEMORY),
                6 => inst.flags.insert(InstFlags::IS_CALL),
                7 => inst.flags.insert(InstFlags::IS_BRANCH),
                8 => inst.flags.insert(InstFlags::IS_RETURN),
                9 => inst.flags.insert(InstFlags::IS_TERMINATOR),
                10 => inst.flags.insert(InstFlags::PROOF_REORDERABLE),
                11 => inst.flags.insert(InstFlags::SPILL_SLOT_ACCESS),
                12 => inst.implicit_defs = &[X9],
                13 => inst.implicit_uses = &[X9],
                14 => inst.flags.insert(InstFlags::IS_PHI),
                _ => unreachable!(),
            }
            let id = add(&mut func, inst);
            func.set_inst_lowering_provenance(id, attribution(5));
            let before = func.clone();
            let mut direct = before.inst(id).clone();
            let error = retire_erased_copy(&mut direct, &func.name, id.0 as usize, func.next_vreg)
                .expect_err("the retirement helper must reject every malformed candidate");
            assert!(
                matches!(error, PipelineError::Encoding(ref reason) if reason.contains("cannot erase noncanonical or effectful Copy"))
            );
            assert_same(&direct, before.inst(id));
            if matches!(mutation, 5..=8) {
                // Memory-write/call/branch/return flags make every operand a
                // use. The public pass sees a live destination and must not
                // attempt retirement; the next ordinary gate still refuses.
                lower_copies(&mut func).unwrap();
                ensure_no_unresolved_vregs(&func, "preserved flagged virtual Copy")
                    .expect_err("a retained live virtual copy must not reach encoding");
            } else {
                lower_copies(&mut func).expect_err("an attempted noncanonical erasure must refuse");
            }
            assert_same(func.inst(id), before.inst(id));
            assert_eq!(func.lowering_provenance, before.lowering_provenance);
            assert_eq!(
                func.block(func.entry).insts,
                before.block(before.entry).insts
            );
        }
    }
}

#[test]
fn invalid_virtual_arenas_classes_and_widths_remain_refusals() {
    for mutation in 0..11 {
        let mut func = function();
        let mut inst = copy(
            IrOperand::VReg(VReg::new(0, RegClass::Gpr64)),
            IrOperand::PReg(X1),
        );
        match mutation {
            0 => func.next_vreg = 0,
            1 => inst.operands[0] = IrOperand::VReg(VReg::new(10, RegClass::Gpr64)),
            2 => inst.operands[0] = IrOperand::VReg(VReg::new(u32::MAX, RegClass::Gpr64)),
            3 => inst.operands[1] = IrOperand::VReg(VReg::new(10, RegClass::Gpr64)),
            4 => inst.operands[0] = IrOperand::VReg(VReg::new(0, RegClass::Fpr8)),
            5 => inst.operands[0] = IrOperand::VReg(VReg::new(0, RegClass::System)),
            6 => inst.operands[1] = IrOperand::VReg(VReg::new(1, RegClass::Fpr64)),
            7 => inst.operands[1] = IrOperand::PReg(trust_cg_ir::regs::D9),
            8 => inst.operands[1] = IrOperand::PReg(PReg::new(u16::MAX)),
            9 => {
                inst.operands[0] = IrOperand::VReg(VReg::new(0, RegClass::Fpr64));
                inst.operands[1] = IrOperand::PReg(trust_cg_ir::regs::S0);
            }
            10 => {
                inst.operands[0] = IrOperand::VReg(VReg::new(0, RegClass::Fpr64));
                inst.operands[1] = IrOperand::VReg(VReg::new(1, RegClass::Fpr32));
            }
            _ => unreachable!(),
        }
        let id = add(&mut func, attributed(inst));
        let before = func.inst(id).clone();
        lower_copies(&mut func).expect_err("invalid register custody must not be erased");
        assert_same(func.inst(id), &before);
    }
}

#[test]
fn dead_gpr_copies_keep_existing_destination_selected_width_aliases() {
    for (class, incoming) in [
        (RegClass::Gpr32, IrOperand::PReg(X1)),
        (RegClass::Gpr64, IrOperand::PReg(W1)),
        (
            RegClass::Gpr32,
            IrOperand::VReg(VReg::new(1, RegClass::Gpr64)),
        ),
        (
            RegClass::Gpr64,
            IrOperand::VReg(VReg::new(1, RegClass::Gpr32)),
        ),
    ] {
        let mut func = function();
        let id = add(
            &mut func,
            attributed(copy(IrOperand::VReg(VReg::new(0, class)), incoming)),
        );
        func.set_inst_lowering_provenance(id, attribution(4));
        lower_copies(&mut func).unwrap();
        assert_retired(&func, id);
        assert_eq!(func.inst_lowering_provenance(id), attribution(4));
    }
    // Width aliases overlap, but only exact PReg equality is redundant.
    // W0 <- X0 must retain the real W write that clears X0's high bits.
    let mut func = function();
    let id = add(&mut func, copy(IrOperand::PReg(W0), IrOperand::PReg(X0)));
    lower_copies(&mut func).unwrap();
    assert_eq!(func.inst(id).opcode, IrOpcode::MOVWrr);
    assert_eq!(
        func.inst(id).operands,
        [IrOperand::PReg(W0), IrOperand::PReg(X0)]
    );
    assert_eq!(encode_ir_inst(func.inst(id)).unwrap(), 0x2a00_03e0);
}

#[test]
fn actual_formal_identity_liveins_and_hidden_x8_metadata_survive() {
    use trust_cg_lower::function::{AbiSretParam, Signature};
    use trust_cg_lower::isel::InstructionSelector;
    for variant in [AArch64AbiVariant::Darwin, AArch64AbiVariant::Aapcs64] {
        for hidden_sret in [false, true] {
            let signature = Signature {
                params: vec![LowerType::I64; 4],
                returns: vec![],
            };
            let mut selector =
                InstructionSelector::new("formal_identity".into(), signature.clone());
            selector.set_abi_variant(variant);
            if hidden_sret {
                selector
                    .seed_sret_param(Some(AbiSretParam { param_index: 0 }))
                    .unwrap();
            }
            selector
                .lower_formal_arguments(&signature, trust_cg_lower::instructions::Block(0))
                .unwrap();
            let mut func = selector.finalize().to_ir_func();
            let ids = func.block(func.entry).insts.clone();
            assert_eq!(ids.len(), 4);
            // Model actual allocator coalescing onto each incoming register.
            // The live-in metadata is supplied by the real formal producer,
            // not reconstructed from the signature (which lacks sret facts).
            for &id in &ids {
                let inst = func.inst_mut(id);
                assert_eq!(inst.opcode, IrOpcode::Copy);
                assert!(matches!(
                    inst.operands.as_slice(),
                    [IrOperand::VReg(_), IrOperand::PReg(_)]
                ));
                inst.operands[0] = inst.operands[1].clone();
            }
            let before = func.clone();
            assert_eq!(
                before.inst(ids[0]).operands[1],
                IrOperand::PReg(if hidden_sret {
                    trust_cg_ir::regs::X8
                } else {
                    X0
                })
            );
            assert!(!before.inst(ids[0]).implicit_uses.is_empty());
            lower_copies(&mut func).unwrap();
            for id in ids {
                let mut expected = before.inst(id).clone();
                expected.opcode = IrOpcode::Nop;
                assert_same(func.inst(id), &expected);
                assert_eq!(
                    func.inst_lowering_provenance(id),
                    before.inst_lowering_provenance(id)
                );
            }
        }
    }
}

#[test]
fn live_virtual_copies_and_existing_nops_are_not_reinterpreted() {
    let mut func = function();
    let v0 = VReg::new(0, RegClass::Gpr64);
    let live = add(
        &mut func,
        attributed(copy(IrOperand::VReg(v0), IrOperand::PReg(X1))),
    );
    let use_id = add(
        &mut func,
        IrMachInst::new(
            IrOpcode::AddRR,
            vec![
                IrOperand::PReg(X0),
                IrOperand::PReg(X0),
                IrOperand::VReg(v0),
            ],
        ),
    );
    let nop = add(
        &mut func,
        attributed(IrMachInst::new(
            IrOpcode::Nop,
            vec![IrOperand::VReg(VReg::new(9, RegClass::Gpr32))],
        )),
    );
    let before = func.clone();
    lower_copies(&mut func).unwrap();
    for id in [live, use_id, nop] {
        assert_same(func.inst(id), before.inst(id));
    }
    ensure_no_unresolved_vregs(&func, "copy-retirement live control")
        .expect_err("live VReg and old malformed NOP remain subject to ordinary refusal");
}

#[test]
fn exact_call_argument_identity_metadata_still_reaches_the_final_abi_validator() {
    let mut func = function();
    let mut marker = attributed(copy(IrOperand::PReg(X1), IrOperand::PReg(X1)));
    marker.flags.insert(InstFlags::IS_CALL_ARG_SETUP);
    let id = add(&mut func, marker);
    let call = add(
        &mut func,
        IrMachInst::new(IrOpcode::Bl, vec![IrOperand::Symbol("_callee".into())])
            .with_implicit_uses(&[X1]),
    );
    func.set_inst_lowering_provenance(id, attribution(8));
    let before = func.clone();
    lower_copies(&mut func).unwrap();
    let mut expected = before.inst(id).clone();
    expected.opcode = IrOpcode::Nop;
    assert_same(func.inst(id), &expected);
    assert_eq!(func.inst_lowering_provenance(id), attribution(8));
    assert_same(func.inst(call), before.inst(call));
    verify_aarch64_final_call_argument_sequence(
        &func.name,
        func.block(func.entry).insts.iter().map(|&id| func.inst(id)),
    )
    .expect("the retained identity marker must validate the resident argument");
}

#[test]
fn canonical_zero_register_sources_do_not_add_special_register_admission() {
    for (class, zero) in [(RegClass::Gpr32, WZR), (RegClass::Gpr64, XZR)] {
        let mut func = function();
        let id = add(
            &mut func,
            copy(IrOperand::VReg(VReg::new(0, class)), IrOperand::PReg(zero)),
        );
        lower_copies(&mut func).unwrap();
        assert_retired(&func, id);
    }
    for source in [
        trust_cg_ir::regs::SpecialReg::SP,
        trust_cg_ir::regs::SpecialReg::XZR,
        trust_cg_ir::regs::SpecialReg::WZR,
    ] {
        let mut func = function();
        let id = add(
            &mut func,
            copy(
                IrOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                IrOperand::Special(source),
            ),
        );
        let before = func.inst(id).clone();
        lower_copies(&mut func).expect_err("retirement does not legalize special operands");
        assert_same(func.inst(id), &before);
    }
}

#[test]
fn retired_copies_preserve_actual_words_and_exact_removed_ids() {
    for (dst, src, mov, expected_word) in [
        (X0, X1, IrOpcode::MOVXrr, 0xaa01_03e0),
        (W0, W1, IrOpcode::MOVWrr, 0x2a01_03e0),
    ] {
        let mut func = function();
        let live = add(&mut func, copy(IrOperand::PReg(dst), IrOperand::PReg(src)));
        let dead = add(
            &mut func,
            attributed(copy(
                IrOperand::VReg(VReg::new(0, preg_class(dst))),
                IrOperand::VReg(VReg::new(1, preg_class(dst))),
            )),
        );
        let identity = add(&mut func, copy(IrOperand::PReg(dst), IrOperand::PReg(dst)));
        let ret = add(
            &mut func,
            IrMachInst::new(IrOpcode::Ret, vec![IrOperand::PReg(X30)]).with_implicit_uses(&[X0]),
        );
        // Historical post-prune oracle: remove only the two known erased
        // copies from the block stream, preserving the original arena slots.
        let mut historical = func.clone();
        historical.inst_mut(live).opcode = mov;
        historical.inst_mut(live).flags.remove(InstFlags::IS_PSEUDO);
        historical.block_mut(historical.entry).insts = vec![live, ret];
        lower_copies(&mut func).unwrap();
        assert_retired(&func, dead);
        let mut expected_identity = historical.inst(identity).clone();
        expected_identity.opcode = IrOpcode::Nop;
        assert_same(func.inst(identity), &expected_identity);
        assert_eq!(func.block(func.entry).insts, [live, dead, identity, ret]);
        let code = encode_function(&func).unwrap();
        assert_eq!(code, encode_function(&historical).unwrap());
        assert_eq!(code, encode_function_with_fixups(&func).unwrap().0);
        for block in &mut func.blocks {
            block.insts.retain(|id| ![dead, identity].contains(id));
        }
        assert_eq!(func.block(func.entry).insts, [live, ret]);
        assert_eq!(encode_function(&func).unwrap(), code);
        assert_eq!(func.insts.len(), historical.insts.len());
        let words: Vec<_> = code
            .as_chunks::<4>()
            .0
            .iter()
            .map(|word| u32::from_le_bytes(*word))
            .collect();
        assert_eq!(words, [expected_word, 0xd65f_03c0]);
    }
}
