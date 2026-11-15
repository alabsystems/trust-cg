// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Allocated-endpoint grammar and concrete architectural controls only.
//! Structural refusal is not a semantic counterexample or independent proof.

use super::*;
use crate::memory_proofs::{encode_store_le, memory_sort, zeroed_memory};
use crate::smt::{EvalEnv, EvalResult};
use std::convert::Infallible;
use trust_cg_ir::regs::{W0, W1, WZR, X0, X1, X2, X3, X18, X30, XZR};
use trust_cg_ir::{BlockId, InstFlags, PReg, RegClass, Signature, StackSlot, VReg};

fn p(reg: PReg) -> O {
    O::PReg(reg)
}

fn ret() -> MachInst {
    let mut inst = MachInst::new(M::Ret, vec![p(X30)]);
    inst.implicit_uses = &[X0];
    inst
}

fn machine(params: usize, body: Vec<MachInst>) -> MachFunction {
    let mut machine = MachFunction::new(
        "read_only_machine_control".into(),
        Signature {
            params: vec![Type::I64; params],
            returns: vec![Type::I64],
        },
    );
    for inst in body.into_iter().chain([ret()]) {
        let id = machine.push_inst(inst);
        machine.append_inst(machine.entry, id);
    }
    machine
}

fn rejected(machine: &MachFunction, reason: &'static str) {
    assert_eq!(
        adapt(machine).err(),
        Some(ReadOnlyTargetError::Machine(reason))
    );
}

fn bound(expr: &E, memory: &E, env: &EvalEnv) -> EvalResult {
    let bound = expr
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok(matches!(node, E::UF { name, args, ret_sort }
            if name == "entry_memory" && args.is_empty() && *ret_sort == memory_sort())
            .then(|| memory.clone()))
        })
        .unwrap()
        .unwrap_or_else(|| expr.clone());
    bound.try_eval(env).unwrap()
}

#[test]
fn nonsetting_logical_immediate_zero_destination_is_sp_not_discard() {
    for op in [M::AndRI, M::OrrRI, M::EorRI] {
        for (src, zeroes) in [
            (X0, [p(XZR), O::Special(SpecialReg::XZR)]),
            (W0, [p(WZR), O::Special(SpecialReg::WZR)]),
        ] {
            for zero in zeroes {
                rejected(
                    &machine(1, vec![MachInst::new(op, vec![zero, p(src), O::Imm(7)])]),
                    "logical immediate would write SP",
                );
            }
        }
        // Rn=31 is still an architectural ZERO source. The refusal is
        // specifically the destination's different SP role, not every ZR.
        for (dst, zr) in [(X1, XZR), (W1, WZR)] {
            let steps = adapt(&machine(
                1,
                vec![MachInst::new(op, vec![p(dst), p(zr), O::Imm(7)])],
            ))
            .unwrap();
            let Step::Scalar {
                destination: Some(1),
                value,
                flags: None,
            } = &steps[0]
            else {
                panic!("ordinary logical destination")
            };
            assert_eq!(
                value.try_eval(&EvalEnv::default()).unwrap().as_u64(),
                if op == M::AndRI { 0 } else { 7 }
            );
        }
    }
    // The initial profile conservatively refuses even flag-setting imm
    // forms with a discarded result; it must not silently treat them as SP.
    for op in [M::AddsRI, M::SubsRI] {
        rejected(
            &machine(1, vec![MachInst::new(op, vec![p(XZR), p(X0), O::Imm(1)])]),
            "immediate ADD/SUB cannot access SP/ZR",
        );
    }
}

#[test]
fn aliased_loads_read_before_write_and_xzr_keeps_the_read_demand() {
    let machine = machine(
        2,
        vec![
            MachInst::new(M::LdrRI, vec![p(X0), p(X0), O::Imm(0)]),
            MachInst::new(M::LdrRI, vec![p(XZR), p(X1), O::Imm(0)]),
        ],
    );
    let steps = adapt(&machine).unwrap();
    assert!(matches!(
        &steps[0],
        Step::Load {
            destination: 0,
            alignment: 1,
            ..
        }
    ));
    assert!(matches!(
        &steps[1],
        Step::Load {
            destination: 31,
            alignment: 1,
            ..
        }
    ));
    let observations =
        super::super::observe(&steps, &[("abi_x0".into(), 64), ("abi_x1".into(), 64)]).unwrap();
    assert_eq!(observations.reads.len(), 2);
    let datum = 0xfedc_ba98_7654_3210;
    let memory = encode_store_le(
        &zeroed_memory(),
        &E::bv_const(0x1000, 64),
        &E::bv_const(datum, 64),
        8,
    );
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), 0x1000);
    env.insert("abi_x1".into(), 0x1000);
    for read in &observations.reads {
        assert_eq!(bound(&read.address.expr, &memory, &env).as_u64(), 0x1000);
        assert!(bound(&read.guard.expr, &memory, &env).as_bool());
        assert_eq!(read.alignment, 1);
    }
    assert_eq!(observations.returns.len(), 1);
    assert_eq!(
        bound(&observations.returns[0].1.expr, &memory, &env).as_u64(),
        datum
    );
}

#[test]
fn plain_eight_byte_load_requires_exact_address_width_offset_and_arity() {
    for offset in [-256, -1, 0, 1, 255, 256, 32760] {
        assert!(
            adapt(&machine(
                1,
                vec![MachInst::new(M::LdrRI, vec![p(X0), p(X0), O::Imm(offset)])]
            ))
            .is_ok()
        );
    }
    for offset in [-257, 32761, i64::MAX, i64::MIN] {
        rejected(
            &machine(
                1,
                vec![MachInst::new(M::LdrRI, vec![p(X0), p(X0), O::Imm(offset)])],
            ),
            "load displacement not emittable",
        );
    }
    rejected(
        &machine(
            1,
            vec![MachInst::new(M::LdrRI, vec![p(X0), p(X0), O::Imm(257)])],
        ),
        "load immediate scale",
    );
    rejected(
        &machine(
            1,
            vec![MachInst::new(M::LdrRI, vec![p(W0), p(X0), O::Imm(0)])],
        ),
        "requires 64-bit X load destination",
    );
    rejected(
        &machine(
            1,
            vec![MachInst::new(M::LdrRI, vec![p(X0), p(XZR), O::Imm(0)])],
        ),
        "load base must be ordinary X, not SP/ZR",
    );
    rejected(
        &machine(1, vec![MachInst::new(M::LdrRI, vec![p(X0), p(X0)])]),
        "unsupported allocated scalar operation/arity",
    );
}

#[test]
fn formal_nop_suffix_metadata_is_inert_only_in_entry_or_retired_arena() {
    let mut marker = MachInst::with_flags(M::Nop, vec![], InstFlags::IS_PSEUDO);
    marker.implicit_uses = &[X3];
    assert!(adapt(&machine(4, vec![marker.clone()])).is_ok());
    let mut retired = machine(4, vec![]);
    retired.push_inst(marker.clone());
    assert!(adapt(&retired).is_ok());
    let mut bad_suffix = marker.clone();
    bad_suffix.implicit_uses = &[X2];
    rejected(
        &machine(4, vec![bad_suffix]),
        "malformed/nonentry inert copy marker",
    );
    let mut duplicated = marker.clone();
    duplicated.implicit_uses = &[X3, X3];
    rejected(
        &machine(4, vec![duplicated]),
        "malformed/nonentry inert copy marker",
    );
    rejected(
        &machine(
            4,
            vec![MachInst::new(M::Movz, vec![p(X0), O::Imm(0)]), marker],
        ),
        "malformed/nonentry inert copy marker",
    );
    for mut nop in [
        MachInst::new(M::Nop, vec![p(X0), p(X1)]),
        MachInst::new(M::Nop, vec![p(X18), p(X18)]),
        MachInst::with_flags(M::Nop, vec![], InstFlags::HAS_SIDE_EFFECTS),
    ] {
        rejected(
            &machine(1, vec![nop.clone()]),
            "malformed/nonentry inert copy marker",
        );
        nop.implicit_defs = &[X0];
        rejected(
            &machine(1, vec![nop]),
            "malformed/nonentry inert copy marker",
        );
    }
}

#[test]
fn inert_markers_retain_step_indexes_and_exact_word_relative_targets() {
    for (nop_flags, expected_target) in [(InstFlags::IS_PSEUDO, 3), (InstFlags::EMPTY, 2)] {
        let machine = machine(
            1,
            vec![
                MachInst::new(M::BCond, vec![O::Imm(0), O::Imm(2)]),
                MachInst::with_flags(M::Nop, vec![], nop_flags),
                MachInst::new(M::Movz, vec![p(X0), O::Imm(1)]),
            ],
        );
        let steps = adapt(&machine).unwrap();
        assert!(matches!(&steps[1], Step::Inert));
        let Step::Branch { taken, .. } = &steps[0] else {
            panic!("actual conditional branch")
        };
        assert_eq!(*taken, expected_target, "{nop_flags:?}");
        assert_eq!(steps.len(), 4);
    }
    for offset in [-(1i64 << 25) - 1, 1i64 << 25] {
        rejected(
            &machine(1, vec![MachInst::new(M::B, vec![O::Imm(offset)])]),
            "direct displacement outside architectural field",
        );
    }
    for offset in [-1, 2] {
        rejected(
            &machine(1, vec![MachInst::new(M::B, vec![O::Imm(offset)])]),
            "direct target outside word stream",
        );
    }
    rejected(
        &machine(
            1,
            vec![MachInst::new(M::BCond, vec![O::Imm(14), O::Imm(1)])],
        ),
        "condition outside 0..13",
    );
    rejected(
        &machine(1, vec![MachInst::new(M::B, vec![O::Imm(1), O::Imm(0)])]),
        "fully allocated caller integer carrier required",
    );
}

#[test]
fn retired_direct_branches_are_harmless_only_without_any_live_owner() {
    for target in [O::Imm(0), O::Block(BlockId(0))] {
        let mut machine = machine(1, vec![]);
        let id = machine.push_inst(MachInst::new(M::B, vec![target.clone()]));
        assert_eq!(adapt(&machine).unwrap().len(), 1);
        machine.blocks[0].insts.insert(0, id);
        if matches!(target, O::Block(_)) {
            rejected(&machine, "fully allocated caller integer carrier required");
        } else {
            let steps = adapt(&machine).unwrap();
            assert!(matches!(&steps[0], Step::Jump(0)));
            assert!(matches!(
                super::super::observe(&steps, &[("abi_x0".into(), 64)]),
                Err(ReadOnlyTargetError::Control(_))
            ));
        }
    }
    let mut bad = machine(1, vec![]);
    let id = bad.push_inst(MachInst::new(M::B, vec![O::Block(BlockId(1))]));
    rejected(&bad, "unowned non-inert instruction");
    bad.insts[id.0 as usize] = MachInst::new(M::B, vec![O::Imm(0)]);
    bad.insts[id.0 as usize].implicit_uses = &[X0];
    rejected(&bad, "unowned non-inert instruction");
    bad.insts[id.0 as usize].implicit_uses = &[];
    bad.insts[id.0 as usize].flags |= InstFlags::HAS_SIDE_EFFECTS;
    rejected(&bad, "unowned non-inert instruction");
    let mut hidden_load = machine(1, vec![]);
    hidden_load.push_inst(MachInst::new(M::LdrRI, vec![p(X0), p(X0), O::Imm(0)]));
    rejected(&hidden_load, "unowned non-inert instruction");
}

#[test]
fn allocation_ownership_and_cfg_metadata_cannot_hide_instructions() {
    let mut duplicate = machine(1, vec![]);
    duplicate.blocks[0].insts.push(InstId(0));
    rejected(&duplicate, "instruction has duplicate live ownership");
    let mut outside = machine(1, vec![]);
    outside.blocks[0].insts[0] = InstId(1);
    rejected(&outside, "instruction outside arena");
    let mut block = machine(1, vec![]);
    block.create_block();
    block.block_order = vec![BlockId(0), BlockId(0)];
    rejected(&block, "duplicate/empty/loop-marked layout block");
    block.block_order = vec![BlockId(0)];
    block.blocks[1].insts.push(InstId(0));
    rejected(&block, "nonempty block outside layout");
    let mut edge = machine(1, vec![]);
    edge.blocks[0].succs.push(BlockId(1));
    rejected(&edge, "CFG metadata points outside layout");
}

#[test]
fn ret_requires_x30_and_only_exact_optional_full_x0_result_metadata() {
    let mut machine = machine(1, vec![]);
    assert!(adapt(&machine).is_ok());
    machine.insts[0].implicit_uses = &[];
    assert!(adapt(&machine).is_ok());
    for args in [vec![], vec![p(X0)], vec![p(X30), p(X0)]] {
        machine.insts[0] = ret();
        machine.insts[0].operands = args;
        rejected(
            &machine,
            "requires exact RET X30 and optional X0 result carrier",
        );
    }
    for uses in [&[X1][..], &[W0][..], &[X0, X0][..]] {
        machine.insts[0] = ret();
        machine.insts[0].implicit_uses = uses;
        rejected(
            &machine,
            "requires exact RET X30 and optional X0 result carrier",
        );
    }
    machine.insts[0] = ret();
    machine.insts[0].implicit_defs = &[X0];
    rejected(
        &machine,
        "requires exact RET X30 and optional X0 result carrier",
    );
    machine.insts[0] = ret();
    machine.insts[0].flags |= InstFlags::IS_PSEUDO;
    rejected(&machine, "unsupported pseudo in allocated stream");
}

#[test]
fn scalar_width_arity_immediates_and_typed_copies_preserve_full_x_carriers() {
    let steps = adapt(&machine(
        1,
        vec![MachInst::new(M::MOVWrr, vec![p(X1), p(X0)])],
    ))
    .unwrap();
    let Step::Scalar {
        value,
        destination: Some(1),
        ..
    } = &steps[0]
    else {
        panic!("typed W carrier")
    };
    let mut env = EvalEnv::default();
    env.insert("x0".into(), 0xffff_ffff_8765_4321);
    assert_eq!(value.try_eval(&env).unwrap().as_u64(), 0x8765_4321);
    rejected(
        &machine(1, vec![MachInst::new(M::AddRR, vec![p(X0), p(W0), p(X1)])]),
        "mixed register widths",
    );
    rejected(
        &machine(1, vec![MachInst::new(M::CmpRI, vec![p(X0), O::Imm(4096)])]),
        "CMP imm12 required",
    );
    rejected(
        &machine(1, vec![MachInst::new(M::Movz, vec![p(X0), O::Imm(65536)])]),
        "move-wide immediate/shift policy",
    );
    rejected(
        &machine(
            1,
            vec![MachInst::new(M::Movz, vec![p(X0), O::Imm(1), O::Imm(16)])],
        ),
        "move-wide immediate/shift policy",
    );
    rejected(
        &machine(
            1,
            vec![MachInst::new(M::Movk, vec![p(W0), O::Imm(1), O::Imm(32)])],
        ),
        "move-wide immediate/shift policy",
    );
    rejected(
        &machine(
            1,
            vec![MachInst::new(M::AsrRI, vec![p(X0), p(X0), O::Imm(64)])],
        ),
        "unsupported allocated scalar operation/arity",
    );
    rejected(
        &machine(1, vec![MachInst::new(M::AddRR, vec![p(X0), p(X1)])]),
        "unsupported allocated scalar operation/arity",
    );
    let mut virtual_copy = machine(
        1,
        vec![MachInst::new(
            M::Nop,
            vec![O::VReg(VReg::new(0, RegClass::Gpr64)), p(X0)],
        )],
    );
    virtual_copy.next_vreg = 1;
    assert!(adapt(&virtual_copy).is_ok());
    virtual_copy.next_vreg = 0;
    rejected(&virtual_copy, "malformed/nonentry inert copy marker");
    let mut virtual_live = machine(
        1,
        vec![MachInst::new(
            M::MovR,
            vec![p(X0), O::VReg(VReg::new(0, RegClass::Gpr64))],
        )],
    );
    virtual_live.next_vreg = 1;
    rejected(
        &virtual_live,
        "fully allocated caller integer carrier required",
    );
}

#[test]
fn unsupported_abi_frames_effects_and_implicit_nzcv_fail_closed() {
    for params in [0, 9] {
        rejected(
            &machine(params, vec![]),
            "requires 1..8 I64 ABI parameters and I64 result",
        );
    }
    let mut bad = machine(1, vec![]);
    bad.signature.params[0] = Type::I32;
    rejected(&bad, "requires 1..8 I64 ABI parameters and I64 result");
    bad.signature.params[0] = Type::I64;
    bad.stack_slots.push(StackSlot::new(8, 8));
    rejected(
        &bad,
        "frameless ordinary integer ABI/effect profile required",
    );
    let mut implicit = machine(1, vec![MachInst::new(M::Movz, vec![p(X0), O::Imm(0)])]);
    implicit.insts[0].implicit_defs = &[X0];
    rejected(&implicit, "noncanonical effects/implicit operands/proof");
    implicit.insts[0].implicit_defs = &[];
    implicit.insts[0].implicit_uses = &[trust_cg_ir::regs::NZCV];
    rejected(&implicit, "noncanonical effects/implicit operands/proof");
    rejected(
        &machine(
            1,
            vec![MachInst::new(M::StrRI, vec![p(X0), p(X1), O::Imm(0)])],
        ),
        "unsupported allocated scalar operation/arity",
    );
}

#[test]
fn machine_resource_bounds_are_structural_budget_refusals_before_expansion() {
    let mut arena = machine(1, vec![]);
    arena
        .insts
        .resize_with(MAX_ARENA + 1, || MachInst::new(M::Nop, vec![]));
    assert_eq!(
        adapt(&arena).err(),
        Some(ReadOnlyTargetError::Budget("machine arena"))
    );
    let mut vregs = machine(1, vec![]);
    vregs.next_vreg = MAX_VREGS + 1;
    assert_eq!(
        adapt(&vregs).err(),
        Some(ReadOnlyTargetError::Budget("machine arena"))
    );
    let mut blocks = machine(1, vec![]);
    for _ in 0..MAX_BLOCKS {
        blocks.create_block();
    }
    assert_eq!(
        adapt(&blocks).err(),
        Some(ReadOnlyTargetError::Budget("machine arena"))
    );
    let linked = machine(
        1,
        (0..MAX_STEPS)
            .map(|_| MachInst::with_flags(M::Nop, vec![], InstFlags::IS_PSEUDO))
            .collect(),
    );
    assert_eq!(
        adapt(&linked).err(),
        Some(ReadOnlyTargetError::Budget("machine linked steps"))
    );
    let mut metadata = machine(1, vec![]);
    metadata.blocks[0].preds = vec![BlockId(0); MAX_BLOCKS + 1];
    assert_eq!(
        adapt(&metadata).err(),
        Some(ReadOnlyTargetError::Budget("machine CFG metadata"))
    );
}
