// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_ir::function::{MachBlock, Signature, Type};
use trust_cg_ir::regs::{X0, X1, X2, X19};
use trust_cg_ir::{AArch64Opcode as M, BlockId};
use trust_cg_lower::function::BasicBlock;
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode as L, Value};

fn fixture() -> (Function, MachFunction) {
    let mut source = Function::new(
        "diamond",
        trust_cg_lower::function::Signature {
            params: vec![trust_cg_lower::Type::I64; 2],
            returns: vec![trust_cg_lower::Type::I64],
        },
    );
    let inst = |opcode, args, results| Instruction {
        opcode,
        args,
        results,
    };
    source.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![
                (Value(0), trust_cg_lower::Type::I64),
                (Value(1), trust_cg_lower::Type::I64),
            ],
            instructions: vec![
                inst(
                    L::Icmp {
                        cond: IntCC::UnsignedLessThan,
                    },
                    vec![Value(0), Value(1)],
                    vec![Value(2)],
                ),
                inst(
                    L::Brif {
                        cond: Value(2),
                        then_dest: Block(1),
                        else_dest: Block(2),
                    },
                    vec![Value(2)],
                    vec![],
                ),
            ],
            ..Default::default()
        },
    );
    for (id, value) in [(1, 0), (2, 1)] {
        source.blocks.insert(
            Block(id),
            BasicBlock {
                instructions: vec![
                    inst(L::Copy, vec![Value(value)], vec![Value(3)]),
                    inst(L::Jump { dest: Block(3) }, vec![], vec![]),
                ],
                ..Default::default()
            },
        );
    }
    source.blocks.insert(
        Block(3),
        BasicBlock {
            params: vec![(Value(3), trust_cg_lower::Type::I64)],
            instructions: vec![inst(L::Return, vec![Value(3)], vec![])],
            ..Default::default()
        },
    );
    source.block_order = (0..4).map(Block).collect();
    let p = MachOperand::PReg;
    let i = MachOperand::Imm;
    let frame = |offset| {
        vec![
            p(X29),
            p(X30),
            MachOperand::Special(SpecialReg::SP),
            i(offset),
        ]
    };
    let mut machine = MachFunction::new(
        "diamond".into(),
        Signature {
            params: vec![Type::I64; 2],
            returns: vec![Type::I64],
        },
    );
    machine.insts = vec![
        MachInst::new(M::StpPreIndex, frame(-16)),
        MachInst::new(
            M::AddRI,
            vec![p(X29), MachOperand::Special(SpecialReg::SP), i(0)],
        ),
        MachInst::new(M::CmpRR, vec![p(X0), p(X1)]),
        MachInst::new(M::BCond, vec![i(3), i(2)]),
        MachInst::new(M::B, vec![i(2)]),
        MachInst::new(M::B, vec![i(3)]),
        MachInst::new(M::MOVXrr, vec![p(X0), p(X1)]),
        MachInst::new(M::B, vec![i(1)]),
        MachInst::new(M::LdpPostIndex, frame(16)),
        MachInst::new(M::Ret, vec![p(X30)]),
    ];
    let block = |insts: Vec<u32>, preds: Vec<u32>, succs: Vec<u32>| MachBlock {
        insts: insts.into_iter().map(InstId).collect(),
        preds: preds.into_iter().map(BlockId).collect(),
        succs: succs.into_iter().map(BlockId).collect(),
        loop_depth: 0,
    };
    machine.blocks = vec![
        block(vec![0, 1, 2, 3, 4], vec![], vec![1, 2]),
        block(vec![5], vec![0], vec![3]),
        block(vec![6, 7], vec![0], vec![3]),
        block(vec![8, 9], vec![1, 2], vec![]),
    ];
    machine.block_order = (0..4).map(BlockId).collect();
    (source, machine)
}

fn comparison_fixture(bits: u32, condition: IntCC, cc: i64) -> (Function, MachFunction, InstId) {
    let (mut source, mut machine) = fixture();
    source.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode = L::Icmp { cond: condition };
    for (id, target) in [(3, 1), (4, 2), (5, 3), (7, 3)] {
        let operand = if id == 3 { 1 } else { 0 };
        machine.insts[id].operands[operand] = MachOperand::Block(BlockId(target));
    }
    if bits == 32 {
        use trust_cg_ir::regs::{W0, W1};
        source.signature.params = vec![trust_cg_lower::Type::I32; 2];
        source.signature.returns = vec![trust_cg_lower::Type::I32];
        for block in source.blocks.values_mut() {
            for (_, ty) in &mut block.params {
                *ty = trust_cg_lower::Type::I32;
            }
        }
        machine.signature.params = vec![Type::I32; 2];
        machine.signature.returns = vec![Type::I32];
        machine.insts[2] =
            MachInst::new(M::CmpRR, vec![MachOperand::PReg(W0), MachOperand::PReg(W1)]);
        machine.insts[6] = MachInst::new(
            M::MOVWrr,
            vec![MachOperand::PReg(W0), MachOperand::PReg(W1)],
        );
    }
    let cset = InstId(machine.insts.len() as u32);
    machine.insts.push(MachInst::new(
        M::CSet,
        vec![MachOperand::PReg(X2), MachOperand::Imm(cc)],
    ));
    machine.blocks[0].insts.insert(3, cset);
    machine.insts[3] = MachInst::new(
        M::Cbnz,
        vec![MachOperand::PReg(X2), MachOperand::Block(BlockId(1))],
    );
    // TV-1: the CSET materialises the `Icmp` at lir0.0, as ISel stamps it.
    stamp_from_source(&source, &mut machine, cset, 0, 0);
    (source, machine, cset)
}

/// Stamp machine instruction `id` as emitted while lowering LIR instruction
/// `(block, index)` of `source` — the TV-1 provenance ISel records, digest
/// included.
fn stamp_from_source(
    source: &Function,
    machine: &mut MachFunction,
    id: InstId,
    block: u32,
    index: u32,
) {
    let lowered = &source.blocks[&Block(block)].instructions[index as usize];
    machine.set_inst_lowering_provenance(
        id,
        trust_cg_ir::LoweringProvenance::SourceInst {
            id: trust_cg_ir::provenance::SourceInstId { block, index },
            digest: lowered.lowering_digest(),
            trust_ir_inst: None,
        },
    );
}

/// `fn(a, b) -> b1 { icmp cond a, b }` as a LINEAR framed body: `CMP a, b ;
/// CSET x0, cc` between the frame save/restore. The `CSET` is the returned
/// value, so the whole-body check OBSERVES it.
fn linear_icmp_fixture(bits: u32, condition: IntCC, cc: i64) -> (Function, MachFunction, InstId) {
    use trust_cg_ir::regs::{W0, W1};
    let (ty, mty, a, b) = if bits == 32 {
        (trust_cg_lower::Type::I32, Type::I32, W0, W1)
    } else {
        (trust_cg_lower::Type::I64, Type::I64, X0, X1)
    };
    let mut source = Function::new(
        "linear_icmp",
        trust_cg_lower::function::Signature {
            params: vec![ty.clone(); 2],
            returns: vec![trust_cg_lower::Type::B1],
        },
    );
    source.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![(Value(0), ty.clone()), (Value(1), ty)],
            instructions: vec![
                Instruction {
                    opcode: L::Icmp { cond: condition },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: L::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            ..Default::default()
        },
    );
    source.block_order = vec![Block(0)];
    let p = MachOperand::PReg;
    let i = MachOperand::Imm;
    let frame = |offset| {
        vec![
            p(X29),
            p(X30),
            MachOperand::Special(SpecialReg::SP),
            i(offset),
        ]
    };
    let mut machine = MachFunction::new(
        "linear_icmp".into(),
        Signature {
            params: vec![mty; 2],
            returns: vec![Type::B1],
        },
    );
    for inst in [
        MachInst::new(M::StpPreIndex, frame(-16)),
        MachInst::new(
            M::AddRI,
            vec![p(X29), MachOperand::Special(SpecialReg::SP), i(0)],
        ),
        MachInst::new(M::CmpRR, vec![p(a), p(b)]),
        MachInst::new(M::CSet, vec![p(X0), i(cc)]),
        MachInst::new(M::LdpPostIndex, frame(16)),
        MachInst::new(M::Ret, vec![p(X30)]),
    ] {
        let id = machine.push_inst(inst);
        machine.append_inst(machine.entry, id);
    }
    stamp_from_source(&source, &mut machine, InstId(3), 0, 0);
    (source, machine, InstId(3))
}

/// Every integer condition with the `CSET` immediate `from_intcc` gives it and
/// the registry spelling of its `Icmp_*` family member.
const SOURCE_BOUND_CONDITIONS: [(IntCC, i64, &str); 10] = [
    (IntCC::Equal, 0, "eq"),
    (IntCC::NotEqual, 1, "ne"),
    (IntCC::UnsignedGreaterThanOrEqual, 2, "uge"),
    (IntCC::UnsignedLessThan, 3, "ult"),
    (IntCC::UnsignedGreaterThan, 8, "ugt"),
    (IntCC::UnsignedLessThanOrEqual, 9, "ule"),
    (IntCC::SignedGreaterThanOrEqual, 10, "sge"),
    (IntCC::SignedLessThan, 11, "slt"),
    (IntCC::SignedGreaterThan, 12, "sgt"),
    (IntCC::SignedLessThanOrEqual, 13, "sle"),
];

/// HOLE 1 of `2e194289f`, the half that HOLDS — executed, not argued.
///
/// `source_bound_cset_query` reads its citation off the emitted `cc`, exactly
/// the defect `cset_reaching_cmp_query` had; the argument for exempting it was
/// that the owner's whole-body check already binds the condition to the source.
/// For a `CSET` whose value the body OBSERVES — returned in the linear shape,
/// branched on in the diamond — that is TRUE, and this pins it: mutating ONLY
/// the condition immediate, LIR untouched, to any of the other fifteen 4-bit
/// condition fields refuses to build the owner at all, so the lane never runs.
/// 2 shapes x 2 widths x 10 source conditions x 15 foreign immediates.
#[test]
fn hole1_the_body_check_refuses_every_foreign_condition_on_an_observed_cset() {
    use crate::function_verifier::FunctionVerifier;
    let mut refused = 0;
    for bits in [32, 64] {
        for (condition, genuine, name) in SOURCE_BOUND_CONDITIONS {
            for shape in ["linear", "diamond"] {
                let (source, machine, cset) = if shape == "linear" {
                    linear_icmp_fixture(bits, condition, genuine)
                } else {
                    comparison_fixture(bits, condition, genuine)
                };
                // LIVE control: the genuine body builds and the lane cites.
                let owner = source_bound_frame(&source, &machine).unwrap_or_else(|refusal| {
                    panic!("{shape} {condition:?}/{bits}: genuine body refused: {refusal:?}")
                });
                assert_eq!(
                    FunctionVerifier::source_bound_cset_query(&owner, cset).map(|(query, _)| query),
                    Some(format!("icmp_{name}_i{bits}").as_str()),
                    "{shape} {condition:?}/{bits}: the genuine CSET lost its citation"
                );
                for cc in 0..16 {
                    if cc == genuine {
                        continue;
                    }
                    let mut mutated = machine.clone();
                    mutated.insts[cset.0 as usize].operands[1] = MachOperand::Imm(cc);
                    assert!(
                        source_bound_frame(&source, &mutated).is_err(),
                        "{shape} {condition:?}/{bits}: cc {cc} on an OBSERVED CSET built the owner"
                    );
                    refused += 1;
                }
            }
        }
    }
    assert_eq!(refused, 2 * 10 * 2 * 15);
}

/// HOLE 1 of `2e194289f`, the half that DID NOT HOLD — the witness.
///
/// The whole-body check binds a `CSET` only through the value it observes. A
/// `CSET` whose destination the body never reads is not constrained at all:
/// with a second, DEAD `CSET x2, cc` stamped with the same `Icmp`, the owner
/// builds for every `cc` that has a modelled predicate, and — before the
/// source binding — `source_bound_cset_query` cited `Icmp_<cc>` for it, a
/// theorem about a comparison the source does not contain (`icmp_sgt` for an
/// `icmp slt` source), chosen by the instruction under test. MEASURED on the
/// base (`572c4ce34`): ten of the sixteen immediates built the owner and were
/// cited (`eq ne uge ult ugt ule sge slt sgt sle`).
///
/// Bound to the source, a scalar `Icmp` owns exactly ONE `CSET` carrying
/// `from_intcc(cond)`; a second one under the same stamp is not a lowering of a
/// scalar comparison and nothing under that stamp is cited.
#[test]
fn hole1_witness_a_dead_cset_condition_is_bound_to_the_source() {
    use crate::function_verifier::FunctionVerifier;
    let (source, machine, live) = linear_icmp_fixture(64, IntCC::SignedLessThan, 11);
    let mut built = 0;
    for cc in 0..16 {
        let mut mutated = machine.clone();
        let dead = mutated.push_inst(MachInst::new(
            M::CSet,
            vec![MachOperand::PReg(X2), MachOperand::Imm(cc)],
        ));
        mutated.blocks[0].insts.insert(4, dead);
        stamp_from_source(&source, &mut mutated, dead, 0, 0);
        let Ok(owner) = source_bound_frame(&source, &mutated) else {
            continue;
        };
        // The body check did NOT constrain this condition: it built.
        built += 1;
        assert_eq!(
            FunctionVerifier::source_bound_cset_query(&owner, dead),
            None,
            "dead CSET cc {cc} was cited under an `icmp slt` source"
        );
        // Two CSETs under one scalar stamp is not a scalar lowering: the
        // live one is refused with it, rather than guessing which is genuine.
        assert_eq!(
            FunctionVerifier::source_bound_cset_query(&owner, live),
            None
        );
    }
    assert_eq!(
        built, 10,
        "the dead CSET no longer builds the owner for the ten modelled conditions — \
         this witness stopped exercising the unconstrained case"
    );

    // An UNSTAMPED dead CSET does not disturb the live one, and earns nothing.
    let mut mutated = machine.clone();
    let dead = mutated.push_inst(MachInst::new(
        M::CSet,
        vec![MachOperand::PReg(X2), MachOperand::Imm(12)],
    ));
    mutated.blocks[0].insts.insert(4, dead);
    let owner = source_bound_frame(&source, &mutated).expect("dead CSET body builds");
    assert_eq!(
        FunctionVerifier::source_bound_cset_query(&owner, dead),
        None
    );
    assert_eq!(
        FunctionVerifier::source_bound_cset_query(&owner, live).map(|(query, _)| query),
        Some("icmp_slt_i64")
    );

    // And a CSET stamped with a DIFFERENT source instruction (the `Return`)
    // is not a comparison's CSET.
    let mut restamped = machine.clone();
    stamp_from_source(&source, &mut restamped, live, 0, 1);
    let owner = source_bound_frame(&source, &restamped).expect("stamps are not body semantics");
    assert_eq!(
        FunctionVerifier::source_bound_cset_query(&owner, live),
        None
    );
}

#[test]
fn source_bound_cset_selects_its_actual_condition_and_comparison_width() {
    use crate::function_verifier::FunctionVerifier;
    use IntCC::*;
    for bits in [32, 64] {
        for (condition, cc, name) in [
            (Equal, 0, "eq"),
            (NotEqual, 1, "ne"),
            (UnsignedGreaterThanOrEqual, 2, "uge"),
            (UnsignedLessThan, 3, "ult"),
            (UnsignedGreaterThan, 8, "ugt"),
            (UnsignedLessThanOrEqual, 9, "ule"),
            (SignedGreaterThanOrEqual, 10, "sge"),
            (SignedLessThan, 11, "slt"),
            (SignedGreaterThan, 12, "sgt"),
            (SignedLessThanOrEqual, 13, "sle"),
        ] {
            let (source, machine, cset) = comparison_fixture(bits, condition, cc);
            let owner = source_bound_frame(&source, &machine).unwrap();
            let (query, category) =
                FunctionVerifier::source_bound_cset_query(&owner, cset).unwrap();
            assert_eq!(query, format!("icmp_{name}_i{bits}"));
            assert_eq!(category, crate::proof_database::ProofCategory::Comparison);
            assert!(FunctionVerifier::source_bound_cset_query(&owner, InstId(0)).is_none());
            assert!(FunctionVerifier::opcode_to_proof_query(M::CSet).is_none());
            // The source binding: the same body with the CSET UNSTAMPED
            // builds the owner (stamps are not body semantics) and earns
            // nothing, because nothing attests which source it lowers.
            let mut unstamped = machine.clone();
            unstamped
                .set_inst_lowering_provenance(cset, trust_cg_ir::LoweringProvenance::UNATTRIBUTED);
            let unowned = source_bound_frame(&source, &unstamped).unwrap();
            assert!(FunctionVerifier::source_bound_cset_query(&unowned, cset).is_none());
            let mut wrong = machine.clone();
            wrong.insts[cset.0 as usize].operands[1] = MachOperand::Imm(cc ^ 1);
            assert!(source_bound_frame(&source, &wrong).is_err());
            wrong = machine.clone();
            wrong.insts[2].opcode = M::Fcmp;
            assert!(source_bound_frame(&source, &wrong).is_err());
            wrong = machine.clone();
            wrong.insts[2].operands[0] = MachOperand::PReg(X2);
            assert!(source_bound_frame(&source, &wrong).is_err());
        }
    }
}

#[test]
fn diamond_binds_actual_branch_predicate_and_both_arms() {
    let (source, machine) = fixture();
    let checked = source_bound_frame(&source, &machine).unwrap();
    assert!(std::ptr::eq(checked.source(), &source));
    assert!(std::ptr::eq(checked.machine(), &machine));
    for mutation in 0..16 {
        let mut changed = machine.clone();
        match mutation {
            0 => changed.insts[3].operands[0] = MachOperand::Imm(2),
            1 => changed.insts[2].operands.swap(0, 1),
            2 => changed.insts[6].operands[1] = MachOperand::PReg(X0),
            3 => changed.insts[2] = MachInst::new(M::Nop, vec![]),
            4 => changed.insts[3].operands[1] = MachOperand::Imm(1),
            5 => changed.insts[3].operands[1] = MachOperand::Imm(1 << 18),
            6 => changed.insts[3].operands[1] = MachOperand::Imm(-3),
            7 => changed.insts[3].operands[0] = MachOperand::Imm(14),
            8 => changed.insts[3].implicit_defs = &[X0],
            9 => changed.insts[3].flags = InstFlags::EMPTY,
            10 => {
                changed.insts[6] =
                    MachInst::new(M::Copy, vec![MachOperand::PReg(X0), MachOperand::PReg(X1)])
            }
            11 => changed.insts[6].operands[0] = MachOperand::PReg(X19),
            12 => changed.insts[3].operands = vec![MachOperand::Imm(3)],
            13 => changed.insts[6].implicit_defs = &[X2],
            14 => {
                // Both CFG successor sets are unchanged: only execution sense changes.
                changed.insts[3].operands[1] = MachOperand::Imm(3);
                changed.insts[4].operands[0] = MachOperand::Imm(1);
            }
            15 => changed.insts[5] = MachInst::new(M::B, vec![MachOperand::Imm(-5)]),
            _ => unreachable!(),
        }
        assert!(
            source_bound_frame(&source, &changed).is_err(),
            "machine mutation {mutation}"
        );
    }
}

#[test]
fn diamond_checks_source_join_types_definitions_and_branch_edges() {
    let (source, machine) = fixture();
    for mutation in 0..18 {
        let mut changed = source.clone();
        match mutation {
            0 => {
                changed.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode = L::Icmp {
                    cond: IntCC::UnsignedGreaterThanOrEqual,
                }
            }
            1 => changed.blocks.get_mut(&Block(1)).unwrap().instructions[0].args = vec![Value(1)],
            2 => changed.blocks.get_mut(&Block(2)).unwrap().instructions[0].args = vec![Value(0)],
            3 => changed.blocks.get_mut(&Block(1)).unwrap().instructions[0].args = vec![Value(3)],
            4 => {
                changed.blocks.get_mut(&Block(1)).unwrap().instructions[0].results = vec![Value(0)]
            }
            5 => {
                changed.blocks.get_mut(&Block(1)).unwrap().instructions[1].opcode =
                    L::Jump { dest: Block(0) }
            }
            6 => changed.blocks.get_mut(&Block(3)).unwrap().params[0].1 = trust_cg_lower::Type::I32,
            7 => changed.blocks.get_mut(&Block(3)).unwrap().instructions[0].args = vec![Value(0)],
            8 => {
                changed
                    .value_types
                    .insert(Value(3), trust_cg_lower::Type::B1);
            }
            9 => {
                changed
                    .value_types
                    .insert(Value(77), trust_cg_lower::Type::I64);
            }
            10 => changed.blocks.get_mut(&Block(0)).unwrap().instructions[1]
                .args
                .clear(),
            11 => {
                changed.blocks.get_mut(&Block(0)).unwrap().instructions[1].opcode = L::Brif {
                    cond: Value(2),
                    then_dest: Block(2),
                    else_dest: Block(1),
                }
            }
            12 => changed.block_order[1] = Block(0),
            13 => changed
                .blocks
                .get_mut(&Block(1))
                .unwrap()
                .params
                .push((Value(5), trust_cg_lower::Type::I64)),
            14 => changed.blocks.get_mut(&Block(1)).unwrap().instructions[0].opcode = L::Trap,
            15 => {
                changed.blocks.insert(Block(9), BasicBlock::default());
            }
            16 => changed.blocks.get_mut(&Block(2)).unwrap().instructions[0]
                .args
                .push(Value(0)),
            17 => {
                changed.blocks.get_mut(&Block(0)).unwrap().instructions[0].results = vec![Value(0)]
            }
            _ => unreachable!(),
        }
        assert!(
            source_bound_frame(&changed, &machine).is_err(),
            "source mutation {mutation}"
        );
    }
}

#[test]
fn diamond_checks_complete_machine_ownership_and_cfg() {
    let (source, machine) = fixture();
    for mutation in 0..12 {
        let mut changed = machine.clone();
        match mutation {
            0 => changed.blocks[0].succs.reverse(), // Order alone is not execution authority.
            1 => changed.blocks[0].succs = vec![BlockId(1), BlockId(1)],
            2 => changed.blocks[3].preds.pop().map(|_| ()).unwrap(),
            3 => changed.blocks[1].loop_depth = 1,
            4 => changed.block_order.swap(1, 2),
            5 => changed.blocks[2].insts.insert(0, InstId(2)),
            6 => changed.blocks[2].insts.insert(0, InstId(999)),
            7 => changed.insts.push(MachInst::new(
                M::MOVXrr,
                vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
            )),
            8 => changed.insts[8].operands[3] = MachOperand::Imm(32),
            9 => changed.insts[9].operands[0] = MachOperand::PReg(X0),
            10 => changed.blocks[0].preds.push(BlockId(1)),
            11 => changed.block_order.push(BlockId(1)),
            _ => unreachable!(),
        }
        assert_eq!(
            source_bound_frame(&source, &changed).is_ok(),
            mutation == 0,
            "ownership mutation {mutation}"
        );
    }
}

#[test]
fn diamond_checks_compare_branches_and_symbolic_targets() {
    let (source, mut machine) = fixture();
    machine.insts[3].operands[1] = MachOperand::Block(BlockId(1));
    machine.insts[4].operands[0] = MachOperand::Block(BlockId(2));
    machine.insts[5].operands[0] = MachOperand::Block(BlockId(3));
    machine.insts[7].operands[0] = MachOperand::Block(BlockId(3));
    assert!(source_bound_frame(&source, &machine).is_ok());
    let set = InstId(machine.insts.len() as u32);
    machine.insts.push(MachInst::new(
        M::CSet,
        vec![MachOperand::PReg(X2), MachOperand::Imm(3)],
    ));
    machine.blocks[0].insts.insert(3, set);
    machine.insts[3] = MachInst::new(
        M::Cbnz,
        vec![MachOperand::PReg(X2), MachOperand::Block(BlockId(1))],
    );
    assert!(source_bound_frame(&source, &machine).is_ok());
    machine.insts[3].opcode = M::Cbz;
    assert!(source_bound_frame(&source, &machine).is_err());
    machine.insts[3].operands[1] = MachOperand::Block(BlockId(2));
    machine.insts[4].operands[0] = MachOperand::Block(BlockId(1));
    assert!(source_bound_frame(&source, &machine).is_ok());
    machine.insts[3].operands[0] = MachOperand::PReg(X19);
    assert!(source_bound_frame(&source, &machine).is_err());
}

#[test]
fn diamond_eliminated_arm_remnant_is_never_executable() {
    let (source, mut machine) = fixture();
    machine.insts[3].operands[1] = MachOperand::Block(BlockId(3));
    machine.insts[4].operands[0] = MachOperand::Block(BlockId(2));
    machine.insts[5].operands[0] = MachOperand::Block(BlockId(3));
    machine.insts[7].operands[0] = MachOperand::Block(BlockId(3));
    machine.blocks[1] = MachBlock::default();
    machine.block_order = vec![BlockId(0), BlockId(2), BlockId(3)];
    machine.blocks[0].succs = vec![BlockId(3), BlockId(2)];
    machine.blocks[3].preds = vec![BlockId(0), BlockId(2)];
    assert!(source_bound_frame(&source, &machine).is_ok());
    for mutation in 0..4 {
        let mut changed = machine.clone();
        match mutation {
            0 => changed.insts[5].implicit_defs = &[X0],
            1 => {
                changed.insts[5] = MachInst::new(
                    M::MOVXrr,
                    vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
                )
            }
            2 => changed.blocks[1].insts.push(InstId(5)),
            3 => changed.insts[5].operands[0] = MachOperand::Block(BlockId(77)),
            _ => unreachable!(),
        }
        assert!(
            source_bound_frame(&source, &changed).is_err(),
            "remnant mutation {mutation}"
        );
    }
}

#[test]
fn supported_diamond_corruptions_are_typed_mismatches() {
    let (source, machine) = fixture();
    assert!(source_bound_frame(&source, &machine).is_ok());
    let classify = |changed: &MachFunction| match source_bound_frame(&source, changed) {
        Err(SourceBoundFrameRefusal::Mismatch(mismatch)) => mismatch,
        Err(other) => panic!("expected a mismatch, got {other}"),
        Ok(_) => panic!("expected a mismatch, got a binding"),
    };
    let body_mismatch = FrameBindingMismatch::Body(AffineLoweringError::ReturnMismatch);
    // Wrong condition code and exchanged arms: both successor sets are intact.
    let mut changed = machine.clone();
    changed.insts[3].operands[0] = MachOperand::Imm(2);
    assert_eq!(classify(&changed), body_mismatch);
    let mut changed = machine.clone();
    changed.insts[3].operands[1] = MachOperand::Imm(3);
    changed.insts[4].operands[0] = MachOperand::Imm(1);
    assert_eq!(classify(&changed), body_mismatch);
    // Wrong register in an arm.
    let mut changed = machine.clone();
    changed.insts[6].operands[1] = MachOperand::PReg(X0);
    assert_eq!(classify(&changed), body_mismatch);
    // Wrong branch targets, derived from the final word layout.
    for (inst, operand, defect) in [
        (
            3,
            MachOperand::Imm(1),
            BranchTargetDefect::NoBlockStart { displacement: 1 },
        ),
        (
            3,
            MachOperand::Imm(1 << 18),
            BranchTargetDefect::DisplacementOutOfRange {
                displacement: 1 << 18,
                bits: 19,
            },
        ),
        (
            5,
            MachOperand::Imm(2),
            BranchTargetDefect::NoBlockStart { displacement: 2 },
        ),
    ] {
        let mut changed = machine.clone();
        let index = if inst == 3 { 1 } else { 0 };
        changed.insts[inst].operands[index] = operand;
        let block = BlockId(u32::from(inst == 5));
        assert_eq!(
            classify(&changed),
            FrameBindingMismatch::BranchTarget {
                block,
                instruction: Some(InstId(inst as u32)),
                defect,
            },
            "branch {inst}"
        );
    }
    // Displacements that land on another block's start contradict the CFG.
    for (inst, index, offset, block) in [(3, 1, -3, 0), (5, 0, -5, 1)] {
        let mut changed = machine.clone();
        changed.insts[inst].operands[index] = MachOperand::Imm(offset);
        assert_eq!(
            classify(&changed),
            FrameBindingMismatch::BranchTarget {
                block: BlockId(block),
                instruction: Some(InstId(inst as u32)),
                defect: BranchTargetDefect::DisagreesWithCfg,
            },
            "branch {inst} to {offset}"
        );
    }
    // Altered frame restore and return register.
    let mut changed = machine.clone();
    changed.insts[8].operands[3] = MachOperand::Imm(32);
    assert_eq!(
        classify(&changed),
        FrameBindingMismatch::FrameEnvelope {
            role: FrameEnvelopeRole::Restore,
            instruction: InstId(8),
        }
    );
    let mut changed = machine.clone();
    changed.insts[9].operands[0] = MachOperand::PReg(X0);
    assert!(matches!(
        classify(&changed),
        FrameBindingMismatch::Body(AffineLoweringError::InvalidMachine(_))
    ));
    // A wrong CSET predicate is a mismatch for the compare-branch form too.
    let (source, machine, cset) = comparison_fixture(64, IntCC::UnsignedLessThan, 3);
    assert!(source_bound_frame(&source, &machine).is_ok());
    let mut changed = machine.clone();
    changed.insts[cset.0 as usize].operands[1] = MachOperand::Imm(2);
    assert!(matches!(
        source_bound_frame(&source, &changed),
        Err(SourceBoundFrameRefusal::Mismatch(
            FrameBindingMismatch::Body(AffineLoweringError::ReturnMismatch)
        ))
    ));
}

#[test]
fn unmodeled_diamond_control_stays_unsupported() {
    let (source, machine) = fixture();
    // A loop, or an indirect branch whose CFG edges are not all modeled, is
    // another shape even when its recorded edges differ from direct targets.
    let mut looping = machine.clone();
    looping.blocks[1].loop_depth = 1;
    let mut indirect = machine.clone();
    indirect.insts[7] = MachInst::new(M::Br, vec![MachOperand::PReg(X2)]);
    indirect.blocks[2].succs = vec![BlockId(3), BlockId(1)];
    indirect.blocks[1].preds.push(BlockId(2));
    for changed in [looping, indirect] {
        assert!(matches!(
            source_bound_frame(&source, &changed),
            Err(SourceBoundFrameRefusal::Unsupported(
                FrameShapeUnsupported::MachineControl
            ))
        ));
    }
    // Divergent epilogues after tail duplication are unsupported, not wrong.
    let mut duplicated = machine.clone();
    duplicated.insts[7] = MachInst::new(M::Nop, vec![]);
    duplicated.insts[5].operands[0] = MachOperand::Imm(4);
    let restore = duplicated.push_inst(machine.insts[8].clone());
    let ret = duplicated.push_inst(machine.insts[9].clone());
    duplicated.blocks[2].insts = vec![InstId(6), restore, ret];
    duplicated.blocks[2].succs.clear();
    duplicated.blocks[3].preds = vec![BlockId(1)];
    assert!(matches!(
        source_bound_frame(&source, &duplicated),
        Err(SourceBoundFrameRefusal::Unsupported(
            FrameShapeUnsupported::Envelope(EnvelopeShape::DivergentRestores)
        ))
    ));
}
