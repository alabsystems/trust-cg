use super::*;
use trust_cg_ir::{AArch64Opcode as A, BlockId, MachInst, MachOperand as M, PReg};
use trust_cg_lower::Type;
use trust_cg_lower::function::{BasicBlock, Signature};
use trust_cg_lower::instructions::{
    DirectCallBinding, Instruction, IntCC, Opcode as L, Value as LirValue,
};

fn node(effects: Vec<Effect>, next: &[usize]) -> Node {
    Node {
        effects,
        next: next.to_vec(),
    }
}

fn counter_fixture() -> Graph {
    Graph {
        variables: 3,
        nodes: vec![
            node(
                vec![
                    Effect::Constant { dst: 0, value: 0 },
                    Effect::Constant {
                        dst: 1,
                        value: 4_000_000,
                    },
                ],
                &[1],
            ),
            node(vec![], &[2, 5]), // header
            node(vec![Effect::Copy { dst: 2, src: 0 }], &[3]),
            node(vec![], &[3, 4]), // unchanged through the inner cycle
            node(
                vec![Effect::Add {
                    dst: 0,
                    lhs: Operand::Variable(2),
                    rhs: Operand::Immediate(1),
                }],
                &[1],
            ),
            node(vec![], &[]),
        ],
    }
}

#[test]
fn counts_completed_outer_loops_through_an_inner_cycle() {
    let result = counter_fixture().recurrence(0, 1, 2, [0, 1]);
    assert_eq!(
        result,
        Some(Recurrence {
            initial: 0,
            limit: 4_000_000,
            increment: 1,
        })
    );
}

#[test]
fn refuses_paths_with_different_counter_updates() {
    let mut graph = counter_fixture();
    // Re-enter the header without going through the checked increment.
    graph.nodes[3].next.push(1);
    assert_eq!(graph.recurrence(0, 1, 2, [0, 1]), None);
}

#[test]
fn refuses_unknown_aliases_and_values_that_drift_in_the_inner_cycle() {
    let mut graph = counter_fixture();
    graph.nodes[3].effects.push(Effect::Unknown(1));
    assert_eq!(graph.recurrence(0, 1, 2, [0, 1]), None);

    let mut graph = counter_fixture();
    graph.nodes[3].effects.push(Effect::Add {
        dst: 2,
        lhs: Operand::Variable(2),
        rhs: Operand::Immediate(1),
    });
    assert_eq!(graph.recurrence(0, 1, 2, [0, 1]), None);
}

#[test]
fn starts_from_actual_initialization_and_tracks_wrapping_addition() {
    let mut graph = counter_fixture();
    graph.nodes[0].effects.push(Effect::Add {
        dst: 0,
        lhs: Operand::Immediate(u64::MAX),
        rhs: Operand::Immediate(1),
    });
    assert_eq!(
        graph.recurrence(0, 1, 2, [0, 1]).map(|r| r.initial),
        Some(0)
    );
    graph.nodes[0].next.push(5);
    assert_eq!(graph.recurrence(0, 1, 2, [0, 1]), None);
}

fn lir_inst(opcode: L, args: &[u32], results: &[u32]) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(LirValue).collect(),
        results: results.iter().copied().map(LirValue).collect(),
    }
}

const TERMINAL: SourceInstId = SourceInstId { block: 3, index: 1 };
const TRAP_WORD: InstId = InstId(7);
const EUCLIDEAN_PROGRESS: &str = "finite Euclidean remainder progress";

fn stamp(source: &Function, machine: &mut MachFunction, row: InstId, block: u32, index: u32) {
    machine.set_inst_lowering_provenance(
        row,
        LoweringProvenance::SourceInst {
            id: SourceInstId { block, index },
            digest: source.blocks[&Block(block)].instructions[index as usize].lowering_digest(),
            trust_ir_inst: None,
        },
    );
}

fn terminal_fixture() -> (Function, MachFunction) {
    let mut source = Function::new("terminal_loop", Signature::default());
    let int = |imm, result| lir_inst(L::Iconst { ty: Type::I64, imm }, &[], &[result]);
    let jump = |dest| lir_inst(L::Jump { dest: Block(dest) }, &[], &[]);
    for (block, instructions) in [
        vec![
            int(0, 0),
            int(8, 1),
            lir_inst(L::Copy, &[0], &[2]),
            lir_inst(L::Copy, &[1], &[3]),
            jump(1),
        ],
        vec![
            lir_inst(
                L::Icmp {
                    cond: IntCC::UnsignedLessThan,
                },
                &[2, 3],
                &[4],
            ),
            lir_inst(
                L::Brif {
                    cond: LirValue(4),
                    then_dest: Block(2),
                    else_dest: Block(3),
                },
                &[4],
                &[],
            ),
        ],
        vec![
            int(1, 5),
            lir_inst(L::Iadd, &[2, 5], &[6]),
            lir_inst(L::Copy, &[6], &[2]),
            jump(1),
        ],
        vec![
            lir_inst(
                L::Call {
                    name: "fixture_output".into(),
                    binding: DirectCallBinding::Interposable,
                },
                &[],
                &[],
            ),
            lir_inst(L::Trap, &[], &[]),
        ],
    ]
    .into_iter()
    .enumerate()
    {
        source.blocks.insert(
            Block(block as u32),
            BasicBlock {
                instructions,
                ..Default::default()
            },
        );
    }
    source.blocks.get_mut(&Block(1)).unwrap().params =
        vec![(LirValue(2), Type::I64), (LirValue(3), Type::I64)];
    source.block_order = [0, 1, 2, 3].map(Block).to_vec();
    source
        .value_types
        .extend((0..=6).map(|id| (LirValue(id), if id == 4 { Type::B1 } else { Type::I64 })));

    let mut machine = MachFunction::new(
        source.name.clone(),
        trust_cg_ir::Signature::new(vec![], vec![]),
    );
    for _ in 1..4 {
        machine.create_block();
    }
    let x = |index| M::PReg(PReg::new(index));
    for (block, opcode, operands, origin) in [
        (0, A::Movz, vec![x(6), M::Imm(0)], None),
        (0, A::Movz, vec![x(10), M::Imm(8)], None),
        (1, A::CmpRR, vec![x(6), x(10)], Some((1, 0))),
        (1, A::BCond, vec![M::Imm(2), M::Imm(3)], Some((1, 1))),
        (2, A::AddRI, vec![x(6), x(6), M::Imm(1)], None),
        (2, A::B, vec![M::Imm(-3)], None),
        (
            3,
            A::Bl,
            vec![M::Symbol("fixture_output".into())],
            Some((3, 0)),
        ),
        (3, A::Brk, vec![], Some((3, 1))),
    ] {
        let row = machine.push_inst(MachInst::new(opcode, operands));
        machine.append_inst(BlockId(block), row);
        if let Some((block, index)) = origin {
            stamp(&source, &mut machine, row, block, index);
        }
    }
    (source, machine)
}

#[test]
fn binds_typed_source_to_the_allocated_loop_and_normal_continuation() {
    let (source, machine) = terminal_fixture();
    let evidence = describe(&source, &machine, TRAP_WORD, TERMINAL).unwrap();
    assert!(evidence.contains("initial 0, limit 8, step 1"));
    assert!(!evidence.contains(EUCLIDEAN_PROGRESS));
}

#[test]
fn refuses_wrong_bound_inverted_edge_clobbered_counter_and_wrong_call() {
    let (source, correct) = terminal_fixture();
    for (row, operand, value) in [
        (1, 1, M::Imm(9)),
        (3, 0, M::Imm(3)),
        (3, 1, M::Imm(4)),
        (6, 0, M::Symbol("different_callee".into())),
    ] {
        let mut mutated = correct.clone();
        mutated.inst_mut(InstId(row)).operands[operand] = value;
        assert!(
            describe(&source, &mutated, TRAP_WORD, TERMINAL).is_none(),
            "mutation at word {row} operand {operand}",
        );
    }
    let mut narrow = correct;
    narrow.inst_mut(InstId(4)).operands[..2].fill(M::PReg(PReg::new(38)));
    assert!(describe(&source, &narrow, TRAP_WORD, TERMINAL).is_none());
}

struct EuclideanFixture {
    source: Function,
    machine: MachFunction,
    work_padding: InstId,
    latch_guard: InstId,
}

fn euclidean_fixture() -> EuclideanFixture {
    let (mut source, mut machine) = terminal_fixture();
    let int = |imm, result| lir_inst(L::Iconst { ty: Type::I64, imm }, &[], &[result]);
    let copy = |from, to| lir_inst(L::Copy, &[from], &[to]);
    let jump = |dest| lir_inst(L::Jump { dest: Block(dest) }, &[], &[]);
    let work = source.blocks.get_mut(&Block(2)).unwrap();
    let outer_latch = std::mem::replace(
        &mut work.instructions,
        vec![
            int(21, 65),
            int(15, 66),
            copy(65, 67),
            copy(66, 69),
            jump(10),
        ],
    );

    for (id, instructions) in [
        (
            10,
            vec![
                copy(69, 70),
                lir_inst(
                    L::Switch {
                        cases: vec![(0, Block(12))],
                        default: Block(11),
                    },
                    &[70],
                    &[],
                ),
            ],
        ),
        (
            11,
            vec![
                copy(69, 76),
                int(0, 77),
                lir_inst(L::Icmp { cond: IntCC::Equal }, &[76, 77], &[78]),
                lir_inst(
                    L::Iconst {
                        ty: Type::B1,
                        imm: 0,
                    },
                    &[],
                    &[79],
                ),
                lir_inst(L::Icmp { cond: IntCC::Equal }, &[78, 79], &[80]),
                lir_inst(
                    L::Brif {
                        cond: LirValue(80),
                        then_dest: Block(14),
                        else_dest: Block(15),
                    },
                    &[80],
                    &[],
                ),
            ],
        ),
        (12, outer_latch),
        (
            14,
            vec![
                lir_inst(L::Urem, &[67, 76], &[83]),
                copy(69, 84),
                copy(83, 85),
                copy(84, 67),
                copy(85, 69),
                jump(10),
            ],
        ),
        (15, vec![lir_inst(L::Trap, &[], &[])]),
    ] {
        source.blocks.insert(
            Block(id),
            BasicBlock {
                instructions,
                ..Default::default()
            },
        );
    }
    source.blocks.get_mut(&Block(10)).unwrap().params =
        vec![(LirValue(67), Type::I64), (LirValue(69), Type::I64)];
    source.block_order = [0, 1, 2, 10, 11, 14, 15, 12, 3].map(Block).to_vec();

    let work = BlockId(2);
    let latch = machine.create_block();
    let remainder = machine.create_block();
    let switch = machine.create_block();
    machine.block_order = vec![
        BlockId(0),
        BlockId(1),
        work,
        switch,
        latch,
        remainder,
        BlockId(3),
    ];
    machine.block_mut(latch).insts = std::mem::take(&mut machine.block_mut(work).insts);
    machine.inst_mut(InstId(3)).operands[1] = M::Imm(13); // word 3 -> 16
    machine.inst_mut(InstId(5)).operands[0] = M::Imm(-7); // word 9 -> 2

    let x = |reg| M::PReg(PReg::new(reg));
    let mut emit = |block, opcode, operands| {
        let row = machine.push_inst(MachInst::new(opcode, operands));
        machine.append_inst(block, row);
        row
    };
    emit(work, A::Movz, vec![x(3), M::Imm(21)]); // word 4
    emit(work, A::Movz, vec![x(2), M::Imm(15)]);
    let work_padding = emit(work, A::AlignNop, vec![]);
    let switch_guard = emit(switch, A::Cbnz, vec![x(2), M::Imm(3)]); // word 7 -> 10 or 8
    let divide = emit(remainder, A::UDiv, vec![x(0), x(3), x(2)]); // word 10
    let msub = emit(remainder, A::Msub, vec![x(1), x(0), x(2), x(3)]);
    emit(remainder, A::MOVXrr, vec![x(3), x(2)]);
    emit(remainder, A::MOVXrr, vec![x(2), x(1)]);
    let latch_guard = emit(remainder, A::Cbz, vec![x(2), M::Imm(-6)]); // word 14 -> 8
    emit(remainder, A::B, vec![M::Imm(-5)]); // word 15 -> 10
    stamp(&source, &mut machine, switch_guard, 10, 1);
    stamp(&source, &mut machine, divide, 14, 0);
    stamp(&source, &mut machine, msub, 14, 0);

    EuclideanFixture {
        source,
        machine,
        work_padding,
        latch_guard,
    }
}

fn assert_without_euclidean_progress(source: &Function, machine: &MachFunction) {
    let evidence = describe(source, machine, TRAP_WORD, TERMINAL)
        .expect("the mutation preserves the outer counter projection");
    assert!(
        evidence.contains("initial 0, limit 8, step 1"),
        "{evidence}"
    );
    assert!(!evidence.contains(EUCLIDEAN_PROGRESS), "{evidence}");
}

#[test]
fn matches_the_source_remainder_step_to_the_rotated_allocated_loop() {
    let fixture = euclidean_fixture();
    let evidence = describe(&fixture.source, &fixture.machine, TRAP_WORD, TERMINAL).unwrap();
    assert!(evidence.contains(EUCLIDEAN_PROGRESS), "{evidence}");
}

#[test]
fn a_wrong_loop_carried_source_alias_removes_only_the_progress_evidence() {
    let mut fixture = euclidean_fixture();
    // Assign the old dividend to the next dividend instead of the old divisor.
    // The Urem and switch stamps still match, and the counter still progresses.
    fixture
        .source
        .blocks
        .get_mut(&Block(14))
        .unwrap()
        .instructions[1]
        .args[0] = LirValue(67);
    assert_without_euclidean_progress(&fixture.source, &fixture.machine);
}

#[test]
fn wrong_machine_latch_target_width_and_an_alternate_cycle_lose_progress() {
    let fixture = euclidean_fixture();
    let mut wrong_latch = fixture.machine.clone();
    wrong_latch.inst_mut(fixture.latch_guard).operands[1] = M::Imm(-7);
    assert_without_euclidean_progress(&fixture.source, &wrong_latch);

    let mut narrow_latch = fixture.machine.clone();
    narrow_latch.inst_mut(fixture.latch_guard).operands[0] = M::PReg(PReg::new(34)); // W2
    assert_without_euclidean_progress(&fixture.source, &narrow_latch);

    let mut extra_cycle = fixture.machine.clone();
    // A new independent cycle can repeat the work prefix without entering the
    // guarded remainder at all. Neither the remainder rows nor their stamps move.
    *extra_cycle.inst_mut(fixture.work_padding) = MachInst::new(
        A::Cbz,
        vec![M::PReg(PReg::new(17)), M::Imm(-2)], // word 6 -> 4 or 7
    );
    assert_without_euclidean_progress(&fixture.source, &extra_cycle);
}

#[test]
fn an_unchecked_source_remainder_in_work_loses_progress() {
    let mut fixture = euclidean_fixture();
    let work = &mut fixture
        .source
        .blocks
        .get_mut(&Block(2))
        .unwrap()
        .instructions;
    work.insert(0, lir_inst(L::Urem, &[0, 0], &[86]));
    assert_without_euclidean_progress(&fixture.source, &fixture.machine);
}
