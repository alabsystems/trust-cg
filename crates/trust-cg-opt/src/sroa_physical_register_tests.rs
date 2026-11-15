// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Architectural store sources must be captured before later clobbers.

use super::*;
use trust_cg_ir::{Signature, SourceLoc, StackSlot, TransformKind, TrustIrInstId};

fn reg(id: u32, class: RegClass) -> MachOperand {
    MachOperand::VReg(VReg::new(id, class))
}

fn push(func: &mut MachFunction, inst: MachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(func.entry, id);
    id
}

fn fixture(source: PReg, load_class: RegClass, size: u32) -> (MachFunction, [InstId; 3]) {
    let mut func = MachFunction::new("physical_store".into(), Signature::new(vec![], vec![]));
    func.next_vreg = 20;
    let slot = func.alloc_stack_slot(StackSlot::new(size, 8));
    let root = push(
        &mut func,
        MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                reg(10, RegClass::Gpr64),
                MachOperand::PReg(regs::SP),
                MachOperand::StackSlot(slot),
            ],
        ),
    );
    let store = push(
        &mut func,
        MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(source),
                reg(10, RegClass::Gpr64),
                MachOperand::Imm(0),
            ],
        ),
    );
    let load = push(
        &mut func,
        MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                reg(2, load_class),
                reg(10, RegClass::Gpr64),
                MachOperand::Imm(0),
            ],
        ),
    );
    (func, [root, store, load])
}

fn unchanged(mut func: MachFunction) {
    let before = format!("{func:?}");
    assert!(!ScalarReplacementOfAggregates.run(&mut func));
    assert_eq!(format!("{func:?}"), before);
}

#[test]
fn physical_gpr_sources_keep_exact_width_and_original_store_point() {
    for (source, class) in [
        (regs::X0, RegClass::Gpr64),
        (regs::X30, RegClass::Gpr64),
        (regs::W0, RegClass::Gpr32),
        (regs::W30, RegClass::Gpr32),
    ] {
        let (mut func, [root, store, load]) = fixture(source, class, 8);
        assert!(ScalarReplacementOfAggregates.run(&mut func));
        assert_eq!(func.block(func.entry).insts, [store, load]);
        assert!(!func.block(func.entry).insts.contains(&root));
        let captured = func.inst(store).operands[0].clone();
        assert!(matches!(&captured, MachOperand::VReg(value) if value.class == class));
        assert_eq!(func.inst(store).operands[1], MachOperand::PReg(source));
        assert_eq!(func.inst(load).operands, [reg(2, class), captured]);
        for id in [store, load] {
            assert_eq!(func.inst(id).opcode, AArch64Opcode::MovR);
            assert_eq!(func.inst(id).flags, AArch64Opcode::MovR.default_flags());
            assert!(func.inst(id).implicit_defs.is_empty());
            assert!(func.inst(id).implicit_uses.is_empty());
            assert!(func.inst(id).proof.is_none());
        }
        // The slot keeps its id (no operand is renumbered), but a fully
        // promoted slot that nothing addresses any more reserves no bytes.
        assert_eq!(func.stack_slots.len(), 1);
        assert_eq!(func.stack_slots[0].fixed_size(), Some(0));
    }
}

#[test]
fn physical_return_pair_is_captured_before_a_later_call_clobbers_both_registers() {
    let (mut func, [root, store0, load0]) = fixture(regs::X0, RegClass::Gpr64, 16);
    let store1 = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![
            MachOperand::PReg(regs::X1),
            reg(10, RegClass::Gpr64),
            MachOperand::Imm(8),
        ],
    ));
    let mut call = MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("overwrite_pair".into())],
    );
    call.implicit_defs = &[regs::X0, regs::X1];
    let call_before = format!("{call:?}");
    let call = func.push_inst(call);
    let load1 = func.push_inst(MachInst::new(
        AArch64Opcode::LdrRI,
        vec![
            reg(3, RegClass::Gpr64),
            reg(10, RegClass::Gpr64),
            MachOperand::Imm(8),
        ],
    ));
    func.block_mut(func.entry).insts = vec![root, store0, store1, call, load0, load1];
    assert!(ScalarReplacementOfAggregates.run(&mut func));
    assert_eq!(
        func.block(func.entry).insts,
        [store0, store1, call, load0, load1]
    );
    assert_eq!(format!("{:?}", func.inst(call)), call_before);
    let captures = [store0, store1].map(|id| func.inst(id).operands[0].clone());
    assert_ne!(captures[0], captures[1]);
    for (lane, (store, load, source)) in [(store0, load0, regs::X0), (store1, load1, regs::X1)]
        .into_iter()
        .enumerate()
    {
        assert_eq!(func.inst(store).opcode, AArch64Opcode::MovR);
        assert_eq!(
            func.inst(store).operands,
            [captures[lane].clone(), MachOperand::PReg(source)]
        );
        assert_eq!(func.inst(load).opcode, AArch64Opcode::MovR);
        assert_eq!(func.inst(load).operands[1], captures[lane]);
        assert!(matches!(&captures[lane], MachOperand::VReg(_)));
    }
}

#[test]
fn physical_store_sources_refuse_special_register_aliases_and_non_gpr_banks() {
    for source in [
        regs::SP,
        PReg::new(63),
        PReg::new(160),
        PReg::new(161),
        regs::V0,
        regs::D0,
        regs::S0,
        regs::NZCV,
        PReg::new(u16::MAX),
    ] {
        unchanged(fixture(source, RegClass::Gpr64, 8).0);
    }
}

#[test]
fn physical_store_slots_keep_width_bounds_overlap_and_reaching_store_refusals() {
    unchanged(fixture(regs::W0, RegClass::Gpr64, 8).0);
    unchanged(fixture(regs::X0, RegClass::Gpr32, 8).0);
    unchanged(fixture(regs::X0, RegClass::Gpr64, 4).0);
    let (mut func, [root, store, load]) = fixture(regs::X0, RegClass::Gpr64, 8);
    func.block_mut(func.entry).insts = vec![root, load, store];
    unchanged(func);
    let (mut func, [_, store, load]) = fixture(regs::W0, RegClass::Gpr32, 8);
    func.inst_mut(store).opcode = AArch64Opcode::StrbRI;
    func.inst_mut(store).flags = AArch64Opcode::StrbRI.default_flags();
    func.inst_mut(load).opcode = AArch64Opcode::LdrbRI;
    func.inst_mut(load).flags = AArch64Opcode::LdrbRI.default_flags();
    unchanged(func);
    let (mut func, _) = fixture(regs::X0, RegClass::Gpr64, 16);
    push(
        &mut func,
        MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(regs::X1),
                reg(10, RegClass::Gpr64),
                MachOperand::Imm(4),
            ],
        ),
    );
    unchanged(func);
}

#[test]
fn physical_store_slots_refuse_escape_and_unrepresented_instruction_effects() {
    for pure in [false, true] {
        let (mut func, _) = fixture(regs::X0, RegClass::Gpr64, 8);
        push(
            &mut func,
            MachInst::new(
                AArch64Opcode::Copy,
                vec![MachOperand::PReg(regs::X0), reg(10, RegClass::Gpr64)],
            ),
        );
        let mut call = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("escape".into())],
        );
        if pure {
            call.proof = Some(ProofAnnotation::Pure);
        }
        push(&mut func, call);
        unchanged(func);
    }
    let (mut func, [root, _, _]) = fixture(regs::X0, RegClass::Gpr64, 8);
    func.inst_mut(root).operands[1] = MachOperand::PReg(regs::X0);
    unchanged(func);
    for site in 0..3 {
        for mutation in 0..4 {
            let (mut func, ids) = fixture(regs::X0, RegClass::Gpr64, 8);
            let inst = func.inst_mut(ids[site]);
            match mutation {
                0 => inst.flags = inst.flags.union(InstFlags::IS_CALL),
                1 => inst.implicit_defs = &[regs::X9],
                2 => inst.implicit_uses = &[regs::X9],
                3 => inst.proof = Some(ProofAnnotation::Pure),
                _ => unreachable!(),
            }
            unchanged(func);
        }
    }
}

#[test]
fn physical_store_rewrite_retains_access_and_address_provenance() {
    let (mut func, [root, store, load]) = fixture(regs::X0, RegClass::Gpr64, 8);
    let location = SourceLoc {
        file: 0,
        line: 42,
        col: 7,
    };
    func.inst_mut(store).source_loc = Some(location);
    let mut provenance = ProvenanceMap::new();
    for (origin, id) in [
        (TrustIrInstId(100), root),
        (TrustIrInstId(101), store),
        (TrustIrInstId(102), load),
    ] {
        provenance.record_lowering(origin, &[id], PassId::new("isel"));
    }
    assert!(ScalarReplacementOfAggregates.run_with_provenance(&mut func, &mut provenance));
    assert_eq!(func.inst(store).source_loc, Some(location));
    let entry = provenance.get_entry(store).unwrap();
    assert!(entry.is_active());
    assert!(entry.trust_ir_origins.contains(&TrustIrInstId(100)));
    assert!(entry.trust_ir_origins.contains(&TrustIrInstId(101)));
    assert_eq!(entry.transforms.last().unwrap().pass, PassId::new("sroa"));
    assert!(matches!(&entry.transforms.last().unwrap().kind,
        TransformKind::Merged { sources } if sources.contains(&root) && sources.contains(&store)));
    for origin in [TrustIrInstId(100), TrustIrInstId(101)] {
        assert_eq!(provenance.get_mach_insts(origin), Some(&[store][..]));
    }
    assert_eq!(
        provenance.get_mach_insts(TrustIrInstId(102)),
        Some(&[load][..])
    );
    assert!(!func.block(func.entry).insts.contains(&root));
}

#[test]
fn physical_capture_keeps_memcpy_call_and_arguments_in_same_or_other_slot() {
    for (same_slot, physical) in [
        (false, regs::X0),
        (false, regs::X1),
        (true, regs::X0),
        (true, regs::X1),
    ] {
        let (mut func, [capture_root, store, load]) = fixture(physical, RegClass::Gpr64, 8);
        let (fill_root, fill_address) = if same_slot {
            (capture_root, reg(10, RegClass::Gpr64))
        } else {
            let slot = func.alloc_stack_slot(StackSlot::new(8, 8));
            let id = func.push_inst(MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    reg(11, RegClass::Gpr64),
                    MachOperand::PReg(regs::SP),
                    MachOperand::StackSlot(slot),
                ],
            ));
            (id, reg(11, RegClass::Gpr64))
        };
        let source = func.push_inst(MachInst::new(
            AArch64Opcode::Copy,
            vec![reg(1, RegClass::Gpr64), MachOperand::PReg(regs::X4)],
        ));
        let size = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![reg(4, RegClass::Gpr64), MachOperand::Imm(8)],
        ));
        let arguments = [
            (regs::X0, fill_address.clone()),
            (regs::X1, reg(1, RegClass::Gpr64)),
            (regs::X2, reg(4, RegClass::Gpr64)),
        ]
        .map(|(destination, value)| {
            func.push_inst(MachInst::new(
                AArch64Opcode::Copy,
                vec![MachOperand::PReg(destination), value],
            ))
        });
        // The `bl memcpy` instruction selection makes for a LIR `Memcpy`, the
        // only one the fill reads.
        let mut library_memcpy = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol(
                trust_cg_lower::RuntimeSymbol::Memcpy.name().into(),
            )],
        );
        library_memcpy.flags.insert(InstFlags::LIBRARY_ROUTINE_CALL);
        let call = func.push_inst(library_memcpy);
        let fill_load = func.push_inst(MachInst::new(
            AArch64Opcode::LdrRI,
            vec![reg(5, RegClass::Gpr64), fill_address, MachOperand::Imm(0)],
        ));
        let gap = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![reg(6, RegClass::Gpr64), MachOperand::Imm(99)],
        ));
        let mut order = vec![source, capture_root];
        if !same_slot {
            order.push(fill_root);
        }
        order.push(size);
        order.extend(arguments);
        order.extend([call, gap, store, load, fill_load]);
        func.block_mut(func.entry).insts = order;

        // The actual matcher must refuse delayed X0 AND non-X0 consumers.
        let (definitions, multiple) = build_def_map_and_multidef(&func);
        assert!(match_memcpy_fill(&func, &definitions, &multiple, arguments[0]).is_none());
        // Non-vacuity: the otherwise identical virtual-only case admits and
        // deletes the fill; the pre-call physical source copy is harmless.
        let mut virtual_control = func.clone();
        virtual_control.inst_mut(store).operands[0] = reg(1, RegClass::Gpr64);
        let (definitions, multiple) = build_def_map_and_multidef(&virtual_control);
        assert!(
            match_memcpy_fill(&virtual_control, &definitions, &multiple, arguments[0]).is_some()
        );
        assert!(ScalarReplacementOfAggregates.run(&mut virtual_control));
        assert!(
            !virtual_control
                .block(virtual_control.entry)
                .insts
                .contains(&call)
        );
        let retained: Vec<_> = arguments
            .into_iter()
            .chain([call, fill_root])
            .map(|id| (id, format!("{:?}", func.inst(id))))
            .collect();
        if same_slot {
            unchanged(func);
        } else {
            assert!(ScalarReplacementOfAggregates.run(&mut func));
            assert_eq!(func.inst(store).opcode, AArch64Opcode::MovR);
            assert_eq!(func.inst(store).operands[1], MachOperand::PReg(physical));
            assert_eq!(func.inst(load).opcode, AArch64Opcode::MovR);
            assert_eq!(func.inst(fill_load).opcode, AArch64Opcode::LdrRI);
            for (id, original) in retained {
                assert!(func.block(func.entry).insts.contains(&id));
                assert_eq!(format!("{:?}", func.inst(id)), original);
            }
            let order = &func.block(func.entry).insts;
            assert!(
                order.iter().position(|id| *id == call).unwrap()
                    < order.iter().position(|id| *id == store).unwrap()
            );
            // O3 runs SROA again. Its output is now MovR, not a physical STR;
            // a one-pass candidate guard would wrongly delete the call here.
            let after_first = format!("{func:?}");
            for _ in 0..2 {
                assert!(!ScalarReplacementOfAggregates.run(&mut func));
                assert_eq!(format!("{func:?}"), after_first);
            }
        }
    }
}

#[test]
fn memcpy_fill_post_call_gpr_guard_covers_successors_backedges_and_unknown_edges() {
    for mutation in 0..11 {
        let mut func =
            MachFunction::new("fill_control_flow".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        push(
            &mut func,
            MachInst::new(
                AArch64Opcode::Copy,
                vec![reg(0, RegClass::Gpr64), MachOperand::PReg(regs::X4)],
            ),
        );
        push(
            &mut func,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol(
                    trust_cg_lower::RuntimeSymbol::Memcpy.name().into(),
                )],
            ),
        );
        let tail = push(&mut func, MachInst::new(AArch64Opcode::Ret, vec![]));
        assert!(memcpy_fill_gpr_uses_are_dead(&func, entry, 1));
        if mutation == 3 {
            // An actual backedge must rescan the pre-call input capture.
            *func.inst_mut(tail) = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(entry)]);
        } else if mutation == 5 {
            func.block_mut(entry)
                .succs
                .push(trust_cg_ir::BlockId(u32::MAX));
        } else if mutation == 6 {
            *func.inst_mut(tail) =
                MachInst::new(AArch64Opcode::Br, vec![MachOperand::PReg(PReg::new(160))]);
        } else {
            let successor = func.create_block();
            let mut read = MachInst::new(
                AArch64Opcode::MovR,
                vec![reg(1, RegClass::Gpr64), MachOperand::PReg(regs::X1)],
            );
            if mutation == 4 {
                read = MachInst::new(AArch64Opcode::Nop, vec![]);
                read.implicit_uses = &[regs::X1];
            } else if mutation == 9 {
                read = MachInst::new(
                    AArch64Opcode::LdrRI,
                    vec![
                        reg(1, RegClass::Gpr64),
                        MachOperand::MemOp {
                            base: regs::X1,
                            offset: 0,
                        },
                    ],
                );
            } else if mutation == 10 {
                // Even a memory operand in a def position reads its base.
                read = MachInst::new(
                    AArch64Opcode::MovR,
                    vec![
                        MachOperand::MemOp {
                            base: regs::X1,
                            offset: 0,
                        },
                        reg(1, RegClass::Gpr64),
                    ],
                );
            }
            let read = func.push_inst(read);
            func.append_inst(successor, read);
            let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
            func.append_inst(successor, ret);
            if mutation == 0 || mutation == 4 {
                // Metadata-only edges are retained even without an explicit B.
                func.add_edge(entry, successor);
            } else if mutation == 2 || mutation == 8 {
                // No successor metadata: actual layout fallthrough still reads.
                *func.inst_mut(tail) = MachInst::new(AArch64Opcode::Nop, vec![]);
                if mutation == 8 {
                    func.inst_mut(tail).flags = InstFlags::IS_RETURN;
                }
            } else {
                *func.inst_mut(tail) =
                    MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(successor)]);
                if mutation == 7 {
                    func.block_order.retain(|block| *block != successor);
                }
            }
        }
        assert!(
            !memcpy_fill_gpr_uses_are_dead(&func, entry, 1),
            "mutation {mutation}"
        );
    }
}

/// A register-passed aggregate argument: the call lowering stores the value
/// into the argument's slot and loads it straight into the ABI register
/// (`ldr x0, [slot]`, marked as call-argument setup). Full promotion turns the
/// load into the `Copy x0 <- scalar` a scalar argument gets, keeps the setup
/// role, and retires the slot that nothing addresses any more.
fn argument_slot_fixture(load_dst: PReg) -> (MachFunction, [InstId; 3]) {
    let (mut func, [root, store, load]) = fixture(regs::X9, RegClass::Gpr64, 8);
    func.inst_mut(store).operands[0] = reg(3, RegClass::Gpr64);
    let inst = func.inst_mut(load);
    inst.operands[0] = MachOperand::PReg(load_dst);
    inst.flags.insert(InstFlags::IS_CALL_ARG_SETUP);
    (func, [root, store, load])
}

#[test]
fn physical_argument_load_becomes_a_setup_copy_and_retires_the_slot() {
    let (mut func, [root, store, load]) = argument_slot_fixture(regs::X0);
    assert!(ScalarReplacementOfAggregates.run(&mut func));
    assert_eq!(func.block(func.entry).insts, [store, load]);
    assert!(!func.block(func.entry).insts.contains(&root));
    let captured = func.inst(store).operands[0].clone();
    assert_eq!(func.inst(store).opcode, AArch64Opcode::MovR);
    assert_eq!(func.inst(store).operands[1], reg(3, RegClass::Gpr64));
    assert_eq!(func.inst(load).opcode, AArch64Opcode::Copy);
    assert_eq!(
        func.inst(load).operands,
        [MachOperand::PReg(regs::X0), captured]
    );
    assert_eq!(
        func.inst(load).flags,
        AArch64Opcode::Copy
            .default_flags()
            .union(InstFlags::IS_CALL_ARG_SETUP)
    );
    assert_eq!(func.stack_slots[0].fixed_size(), Some(0));
}

#[test]
fn physical_argument_load_refusals() {
    // Only a plain LDR into an X/W register: special registers, FP banks and
    // narrow loads keep the slot and its memory traffic.
    for dst in [regs::SP, PReg::new(160), regs::V0, regs::D0, regs::S0] {
        unchanged(argument_slot_fixture(dst).0);
    }
    let (mut func, [_, _, load]) = argument_slot_fixture(regs::W0);
    func.inst_mut(load).opcode = AArch64Opcode::LdrbRI;
    unchanged(func);
    // The setup role is the only admitted extra flag.
    let (mut func, [_, _, load]) = argument_slot_fixture(regs::X0);
    func.inst_mut(load)
        .flags
        .insert(InstFlags::HAS_SIDE_EFFECTS);
    unchanged(func);
    // The slot is still addressed by an escaping use: promoted accesses are
    // refused as before, and the slot keeps its bytes.
    let (mut func, _) = argument_slot_fixture(regs::X0);
    push(
        &mut func,
        MachInst::new(
            AArch64Opcode::Copy,
            vec![MachOperand::PReg(regs::X1), reg(10, RegClass::Gpr64)],
        ),
    );
    push(
        &mut func,
        MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol("keep".into())]),
    );
    unchanged(func);
}

/// The formal-argument live-in device: the address root of an aggregate
/// PARAMETER's slot carries implicit reads of the incoming argument registers
/// it must keep reserved. A read has no effect to erase, so the root may be
/// deleted; any other implicit read still refuses.
#[test]
fn formal_live_in_reads_on_a_root_are_admitted_and_other_reads_are_not() {
    const ARG0: &[PReg] = &[regs::X0];
    const ARGS: &[PReg] = &[regs::X0, regs::X1, regs::W7];
    const X8: &[PReg] = &[regs::X8];
    const X19: &[PReg] = &[regs::X19];
    const V0: &[PReg] = &[regs::V0];
    for (uses, admitted) in [
        (ARG0, true),
        (ARGS, true),
        (X8, false),
        (X19, false),
        (V0, false),
    ] {
        let (mut func, [root, store, _]) = fixture(regs::X0, RegClass::Gpr64, 8);
        func.inst_mut(root).implicit_uses = uses;
        func.inst_mut(store).implicit_uses = uses;
        if admitted {
            assert!(ScalarReplacementOfAggregates.run(&mut func), "{uses:?}");
            assert!(!func.block(func.entry).insts.contains(&root));
            // A rewritten access keeps its reads.
            assert_eq!(func.inst(store).implicit_uses, uses);
        } else {
            unchanged(func);
        }
    }
}

/// A slot that a source-level debug variable names as its home keeps the strict
/// shape: neither the argument-register load nor the formal live-in reads are
/// admitted, and a promoted home slot is not retired. The same plans without
/// the debug variable are promoted and retired (the controls above).
#[test]
fn debug_variable_homes_keep_the_strict_shape() {
    use trust_cg_ir::function::{DebugBaseType, DebugLocalVariable, DebugVariableStorage};
    // The two ways a local names slot 0: as its storage, and as the
    // adapter's synthetic fixed-scalar `alloca` variable (tag | slot index).
    let storages = [
        DebugVariableStorage::StackSlot(0),
        DebugVariableStorage::ProvenanceVar(trust_cg_ir::provenance::TrustIrVarId(0x8000_0000)),
    ];
    for storage in storages {
        let described = |mut func: MachFunction| {
            func.debug_meta.local_variables.push(DebugLocalVariable {
                name: "acc".into(),
                ty: DebugBaseType::I64,
                storage,
                decl_line: 1,
            });
            func
        };
        // The argument-register load into X0.
        unchanged(described(argument_slot_fixture(regs::X0).0));
        // The formal live-in reads on the root and the store.
        const ARG0: &[PReg] = &[regs::X0];
        let (mut func, [root, store, _]) = fixture(regs::X0, RegClass::Gpr64, 8);
        func.inst_mut(root).implicit_uses = ARG0;
        func.inst_mut(store).implicit_uses = ARG0;
        unchanged(described(func));
        // Control: a plain physical store with no implicit use was promoted
        // before either admission existed, and a debug home does not change
        // that; but the home slot keeps its bytes (it is not retired), since
        // the local is described by its frame slot.
        let (func, _) = fixture(regs::X0, RegClass::Gpr64, 8);
        let mut func = described(func);
        assert!(ScalarReplacementOfAggregates.run(&mut func), "{storage:?}");
        assert_eq!(func.stack_slots[0].fixed_size(), Some(8), "{storage:?}");
    }
    // A local of another slot does not make slot 0 a home.
    let (mut func, _) = argument_slot_fixture(regs::X0);
    func.debug_meta.local_variables.push(DebugLocalVariable {
        name: "other".into(),
        ty: DebugBaseType::I64,
        storage: DebugVariableStorage::StackSlot(1),
        decl_line: 1,
    });
    assert!(ScalarReplacementOfAggregates.run(&mut func));
}
