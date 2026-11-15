// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Structural resource/domain controls only. Exact theorem and row-inventory
//! equality does not independently check a proof or establish native credit.

use super::super::{SourceBoundA64Body, source_bound_a64_body};
use super::*;
use trust_cg_ir::function::{MachBlock, Signature as MachineSignature};
use trust_cg_ir::regs::PReg;
use trust_cg_lower::function::{BasicBlock, Signature};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode as L, Value};
use trust_cg_lower::{Function, Type};

fn lir_instruction(opcode: L, args: &[u32], results: &[u32]) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(Value).collect(),
        results: results.iter().copied().map(Value).collect(),
    }
}

fn source(instructions: Vec<Instruction>) -> Function {
    let mut source = Function::new(
        "scratch_resource",
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    source.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![(Value(0), Type::I64), (Value(1), Type::I64)],
            instructions,
            ..Default::default()
        },
    );
    source.block_order = vec![Block(0)];
    source
}

fn add_source() -> Function {
    source(vec![
        lir_instruction(L::Iadd, &[0, 1], &[2]),
        lir_instruction(L::Return, &[2], &[]),
    ])
}

fn select_source() -> Function {
    source(vec![
        lir_instruction(L::Icmp { cond: IntCC::Equal }, &[0, 1], &[2]),
        lir_instruction(
            L::Iconst {
                imm: 11,
                ty: Type::I64,
            },
            &[],
            &[3],
        ),
        lir_instruction(
            L::Iconst {
                imm: 29,
                ty: Type::I64,
            },
            &[],
            &[4],
        ),
        lir_instruction(
            L::Select {
                cond: IntCC::NotEqual,
            },
            &[2, 3, 4],
            &[5],
        ),
        lir_instruction(L::Return, &[5], &[]),
    ])
}

fn x(number: u16) -> O {
    O::PReg(PReg::new(number))
}

fn instruction(opcode: M, operands: Vec<O>) -> MachInst {
    MachInst::new(opcode, operands)
}

fn machine(blocks: Vec<(Vec<MachInst>, Vec<u32>)>) -> MachFunction {
    let mut machine = MachFunction::new(
        "scratch_resource".into(),
        MachineSignature {
            params: vec![MType::I64, MType::I64],
            returns: vec![MType::I64],
        },
    );
    machine.blocks.clear();
    machine.insts.clear();
    let mut predecessors = vec![vec![]; blocks.len()];
    for (index, (_, successors)) in blocks.iter().enumerate() {
        for successor in successors {
            predecessors[*successor as usize].push(BlockId(index as u32));
        }
    }
    for (index, (instructions, successors)) in blocks.into_iter().enumerate() {
        let mut rows = Vec::new();
        for instruction in instructions {
            rows.push(InstId(machine.insts.len() as u32));
            machine.insts.push(instruction);
        }
        machine.blocks.push(MachBlock {
            insts: rows,
            preds: predecessors[index].clone(),
            succs: successors.into_iter().map(BlockId).collect(),
            loop_depth: 0,
        });
    }
    machine.block_order = (0..machine.blocks.len() as u32).map(BlockId).collect();
    machine
}

fn chain(displacements: bool) -> MachFunction {
    let target = |block: u32| {
        if displacements {
            O::Imm(1)
        } else {
            O::Block(BlockId(block))
        }
    };
    machine(vec![
        (
            vec![
                instruction(M::AddRR, vec![x(0), x(0), x(1)]),
                instruction(M::B, vec![target(1)]),
            ],
            vec![1],
        ),
        (vec![instruction(M::B, vec![target(2)])], vec![2]),
        (vec![instruction(M::Ret, vec![x(30)])], vec![]),
    ])
}

fn diamond(displacements: bool) -> MachFunction {
    let target = |block: u32, displacement: i64| {
        if displacements {
            O::Imm(displacement)
        } else {
            O::Block(BlockId(block))
        }
    };
    machine(vec![
        (
            vec![
                instruction(M::CmpRR, vec![x(0), x(1)]),
                instruction(M::BCond, vec![O::Imm(0), target(2, 4)]),
                instruction(M::B, vec![target(1, 1)]),
            ],
            vec![2, 1],
        ),
        (
            vec![
                instruction(M::Movz, vec![x(0), O::Imm(29)]),
                instruction(M::B, vec![target(3, 3)]),
            ],
            vec![3],
        ),
        (
            vec![
                instruction(M::Movz, vec![x(0), O::Imm(11)]),
                instruction(M::B, vec![target(3, 1)]),
            ],
            vec![3],
        ),
        (vec![instruction(M::Ret, vec![x(30)])], vec![]),
    ])
}

/// Change only original arena coordinates/edge operands. Instruction IDs,
/// layout order, signatures, operands other than block targets and source
/// equations remain exact. No target is reconstructed from source semantics.
fn remap(original: &MachFunction, ids: &[u32], arena_len: usize) -> MachFunction {
    assert_eq!(original.blocks.len(), ids.len());
    assert_eq!(ids[0], 0, "preserve the existing entry-zero domain");
    assert!(ids.iter().all(|id| (*id as usize) < arena_len));
    assert_eq!(ids.iter().collect::<HashSet<_>>().len(), ids.len());
    let mut result = original.clone();
    result.blocks = (0..arena_len).map(|_| MachBlock::new()).collect();
    for (old_id, block) in original.blocks.iter().enumerate() {
        let mut block = block.clone();
        for edge in block.preds.iter_mut().chain(&mut block.succs) {
            *edge = BlockId(ids[edge.0 as usize]);
        }
        result.blocks[ids[old_id] as usize] = block;
    }
    for instruction in &mut result.insts {
        for operand in &mut instruction.operands {
            if let O::Block(block) = operand {
                *block = BlockId(ids[block.0 as usize]);
            }
        }
    }
    result.block_order = original
        .block_order
        .iter()
        .map(|id| BlockId(ids[id.0 as usize]))
        .collect();
    result
}

fn bind<'a>(source: &'a Function, machine: &'a MachFunction) -> SourceBoundA64Body<'a> {
    source_bound_a64_body(source, machine).unwrap_or_else(|error| panic!("expected body: {error}"))
}

fn refusal(source: &Function, machine: &MachFunction) -> A64BodyRefusal {
    match source_bound_a64_body(source, machine) {
        Ok(_) => panic!("invalid target must refuse"),
        Err(error) => error,
    }
}

fn same_theorem(left: &SourceBoundA64Body<'_>, right: &SourceBoundA64Body<'_>) {
    assert_eq!(left.obligation(), right.obligation());
    assert_eq!(left.covered(), right.covered());
    assert_eq!(left.copies_and_constants(), right.copies_and_constants());
    assert!(!right.covered().is_empty());
}

#[test]
fn many_empty_retired_slots_preserve_complete_theorem_and_credits() {
    let source = add_source();
    let original = chain(false);
    let owner = bind(&source, &original);
    let mut retired = original.clone();
    retired.blocks.resize_with(65_536, MachBlock::new);
    let actual = bind(&source, &retired);
    same_theorem(&owner, &actual);
    assert!(std::ptr::eq(actual.source(), &source));
    assert!(std::ptr::eq(actual.machine(), &retired));
    assert_eq!(actual.covered(), [InstId(0), InstId(1), InstId(2)]);
    assert!(actual.copies_and_constants().is_empty());
}

#[test]
fn high_sparse_live_ids_preserve_both_block_and_word_target_theorems() {
    let source = add_source();
    for displacements in [false, true] {
        let original = chain(displacements);
        let sparse = remap(&original, &[0, 61_337, 4_096], 65_536);
        same_theorem(&bind(&source, &original), &bind(&source, &sparse));
        let admitted = super::super::source::admit(&source).unwrap();
        let entry = [E::var("e0", 64), E::var("e1", 64)];
        let original_rows = encode(&original, &admitted, &mut Defs::default(), &entry).unwrap();
        let sparse_rows = encode(&sparse, &admitted, &mut Defs::default(), &entry).unwrap();
        assert_eq!(original_rows.rows, sparse_rows.rows);
        assert_eq!(original_rows.result, sparse_rows.result);
        assert_eq!(
            sparse.block_order,
            [BlockId(0), BlockId(61_337), BlockId(4_096)]
        );
    }
}

#[test]
fn sparse_conditional_join_keeps_original_flags_returns_and_row_custody() {
    let source = select_source();
    for displacements in [false, true] {
        let original = diamond(displacements);
        let sparse = remap(&original, &[0, 33_000, 900, 60_000], 65_536);
        let before_source = format!("{source:?}");
        let before_instructions = format!("{:?}", sparse.insts);
        let before_layout = sparse.block_order.clone();
        let actual = bind(&source, &sparse);
        same_theorem(&bind(&source, &original), &actual);
        assert_eq!(actual.copies_and_constants(), [InstId(3), InstId(5)]);
        assert!(!actual.covers(InstId(7)), "RET stays uncredited");
        assert_eq!(format!("{source:?}"), before_source);
        assert_eq!(format!("{:?}", sparse.insts), before_instructions);
        assert_eq!(sparse.block_order, before_layout);
    }
}

#[test]
fn duplicate_missing_and_out_of_range_layout_ids_stay_hard_refusals() {
    let source = add_source();
    let original = remap(&chain(false), &[0, 61_337, 4_096], 65_536);
    for order in [
        vec![],
        vec![BlockId(0), BlockId(61_337), BlockId(61_337)],
        vec![BlockId(0), BlockId(61_337), BlockId(u32::MAX)],
        vec![BlockId(0), BlockId(61_337)],
        vec![BlockId(61_337), BlockId(0), BlockId(4_096)],
    ] {
        let mut mutant = original.clone();
        mutant.block_order = order;
        assert!(matches!(
            refusal(&source, &mutant),
            A64BodyRefusal::Unsupported(A64BodyUnsupported::MachineControl(_))
        ));
    }
    let mut too_many = original.clone();
    too_many.block_order = (0..=MAX_MACHINE_BLOCKS as u32).map(BlockId).collect();
    assert!(matches!(
        refusal(&source, &too_many),
        A64BodyRefusal::Unsupported(A64BodyUnsupported::MachineControl(_))
    ));
}

#[test]
fn complete_retired_arena_scan_never_hides_rows_predecessors_or_successors() {
    let source = add_source();
    let original = remap(&chain(false), &[0, 61_337, 4_096], 65_536);
    for kind in 0..3 {
        let mut hidden = original.clone();
        match kind {
            0 => hidden.blocks[50_000].insts.push(InstId(0)),
            1 => hidden.blocks[50_000].preds.push(BlockId(0)),
            _ => hidden.blocks[50_000].succs.push(BlockId(4_096)),
        }
        assert_eq!(
            refusal(&source, &hidden),
            control("block 50000 holds rows or edges but is not laid out")
        );
    }
    let mut inconsistent = original;
    inconsistent.blocks[61_337].succs = vec![BlockId(50_000)];
    assert!(matches!(
        refusal(&source, &inconsistent),
        A64BodyRefusal::Mismatch(A64BodyMismatch::BranchTarget {
            block: BlockId(61_337),
            defect: BranchTargetDefect::DisagreesWithCfg,
            ..
        })
    ));
}

#[test]
fn target_refusals_keep_original_high_ids_and_do_not_alias_dense_slots() {
    let source = add_source();
    let original = remap(&chain(false), &[0, 61_337, 4_096], 65_536);
    for target in [BlockId(1), BlockId(50_000), BlockId(u32::MAX)] {
        let mut mutant = original.clone();
        mutant.insts[2].operands = vec![O::Block(target)];
        assert_eq!(
            refusal(&source, &mutant),
            mismatch(A64BodyMismatch::BranchTarget {
                block: BlockId(61_337),
                instruction: Some(InstId(2)),
                defect: BranchTargetDefect::TargetNotLaidOut { target },
            })
        );
    }
    let mut wrong_word = original.clone();
    wrong_word.insts[2].operands = vec![O::Imm(99)];
    assert_eq!(
        refusal(&source, &wrong_word),
        mismatch(A64BodyMismatch::BranchTarget {
            block: BlockId(61_337),
            instruction: Some(InstId(2)),
            defect: BranchTargetDefect::NoBlockStart { displacement: 99 },
        })
    );
    let mut looped = original;
    looped.blocks[61_337].loop_depth = 1;
    assert_eq!(
        refusal(&source, &looped),
        control("block 61337 is recorded inside a loop; loops stay outside the body owner")
    );
}

#[test]
fn ambiguous_zero_word_starts_and_invalid_linked_rows_still_refuse() {
    let source = add_source();
    let mut pseudo = instruction(M::Nop, vec![]);
    pseudo.flags = InstFlags::IS_PSEUDO;
    let zero_word = machine(vec![
        (
            vec![
                instruction(M::AddRR, vec![x(0), x(0), x(1)]),
                instruction(M::B, vec![O::Imm(1)]),
            ],
            vec![1],
        ),
        (vec![pseudo], vec![2]),
        (vec![instruction(M::Ret, vec![x(30)])], vec![]),
    ]);
    assert_eq!(
        refusal(&source, &zero_word),
        control("a branch lands on a word several laid-out blocks start at")
    );
    let sparse = remap(&zero_word, &[0, 61_337, 4_096], 65_536);
    assert_eq!(refusal(&source, &sparse), refusal(&source, &zero_word));
    let original = chain(false);
    for row in [InstId(0), InstId(u32::MAX)] {
        let mut mutant = original.clone();
        mutant.blocks[1].insts.insert(0, row);
        assert_eq!(
            refusal(&source, &mutant),
            control("a row is laid out twice or out of range")
        );
    }
}

#[test]
fn bounded_orphan_instructions_remain_unexecuted_and_uncredited() {
    let source = add_source();
    let original = chain(false);
    let mut with_orphans = original.clone();
    let orphan = instruction(M::AddRI, vec![x(19), x(18), O::Imm(1)]);
    with_orphans
        .insts
        .resize(4 * MAX_MACHINE_INSTRUCTIONS, orphan.clone());
    let owner = bind(&source, &with_orphans);
    same_theorem(&bind(&source, &original), &owner);
    assert!(!owner.covers(InstId(4)) && !owner.copies_and_constants().contains(&InstId(4)));
    // The very same row becomes a preserved-register mismatch when linked.
    let mut live = with_orphans.clone();
    live.blocks[0].insts.insert(0, InstId(4));
    assert!(matches!(
        refusal(&source, &live),
        A64BodyRefusal::Mismatch(A64BodyMismatch::PreservedWrite {
            inst: InstId(4),
            ..
        })
    ));
    with_orphans.insts.push(orphan);
    assert!(matches!(
        refusal(&source, &with_orphans),
        A64BodyRefusal::Unsupported(A64BodyUnsupported::MachineControl(_))
    ));
}
