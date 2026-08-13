// switch_bst_block_collision.rs — regression lock for the A64-4/JIT-2/TV-6
// scale-emergent miscompile class (aarch64 BST switch nodes aliasing real
// LIR blocks).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ROOT CAUSE (pre-fix): `select_switch_binary_search` bumped `next_block_id`
// above only the ids it could see at switch-lowering time (this switch's case
// targets / default / current block, plus blocks already selected). Block
// selection is streamed in layout order, so LIR blocks appearing LATER with
// higher ids were invisible — `switch.rs::alloc_block` handed their ids to
// BST intermediate nodes. The BST compare/branch instructions were emitted
// into the future block's (empty-so-far) map entry, the real block's code was
// appended AFTER them, and every branch to the real block landed on the stale
// BST compares and mis-dispatched (typically to the switch default). That is
// exactly the pinned aarch64-JIT miscompile pair: `Constant__shape_matches_ty`
// returning false for Int-vs-Ptr / Float-vs-F64, and `fold_binop`'s Shl arm
// returning None for every input (checked_shl never reached).
//
// FIX: synthetic ids are allocated from a disjoint high range
// (`SYNTHETIC_BLOCK_ID_BASE` = 1<<31) and compacted at `finalize()`;
// `select_block_*` fail-closes on (a) a real block id in the synthetic range
// and (b) a block that already contains instructions at first selection (the
// backstop gate that catches this class).
//
// This test builds the MINIMAL collision shape and verifies (1) structural
// single-terminator-group integrity, (2) the real blocks' code is not fused
// behind foreign compares, (3) BEHAVIORAL dispatch correctness by walking the
// lowered compare/branch chain for every case value, and (4) the fail-closed
// gates fire.

use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::isel::{
    AArch64Opcode, ISelError, ISelFunction, ISelOperand, InstructionSelector,
};
use trust_cg_lower::types::Type;

fn iconst(v: u32, imm: i64) -> Instruction {
    Instruction {
        opcode: Opcode::Iconst { ty: Type::I64, imm },
        args: vec![],
        results: vec![Value(v)],
    }
}

fn ret(v: u32) -> Instruction {
    Instruction {
        opcode: Opcode::Return,
        args: vec![Value(v)],
        results: vec![],
    }
}

fn jump(dest: Block) -> Instruction {
    Instruction {
        opcode: Opcode::Jump { dest },
        args: vec![],
        results: vec![],
    }
}

/// The minimal collision shape:
///
/// b0:  switch v0 [0 -> b1, 10 -> b2, 20 -> b3, 30 -> b4] default b5
///      (4 cases, density 4/31 < 0.4 => BinarySearch => 2 intermediate nodes)
/// b1:  jump b6            ; b6/b7 have ids ABOVE every id the pre-fix bump
/// b2:  jump b7            ; loop saw at switch time => pre-fix, the BST
/// b3:  return 3           ; nodes were allocated AS Block(6)/Block(7).
/// b4:  return 4
/// b5:  return 99          ; default
/// b6:  return 1
/// b7:  return 2
fn build_collision_isel() -> ISelFunction {
    let sig = Signature {
        params: vec![Type::I64],
        returns: vec![Type::I64],
    };
    let blocks: Vec<(Block, Vec<Instruction>)> = vec![
        (
            Block(0),
            vec![Instruction {
                opcode: Opcode::Switch {
                    cases: vec![
                        (0, Block(1)),
                        (10, Block(2)),
                        (20, Block(3)),
                        (30, Block(4)),
                    ],
                    default: Block(5),
                },
                args: vec![Value(0)],
                results: vec![],
            }],
        ),
        (Block(1), vec![jump(Block(6))]),
        (Block(2), vec![jump(Block(7))]),
        (Block(3), vec![iconst(13, 3), ret(13)]),
        (Block(4), vec![iconst(14, 4), ret(14)]),
        (Block(5), vec![iconst(15, 99), ret(15)]),
        (Block(6), vec![iconst(16, 1), ret(16)]),
        (Block(7), vec![iconst(17, 2), ret(17)]),
    ];

    let mut isel = InstructionSelector::new("bst_collision".to_string(), sig.clone());
    isel.lower_formal_arguments(&sig, Block(0)).unwrap();
    for (block, insts) in &blocks {
        isel.select_block_with_source_locs(*block, insts, &[])
            .unwrap_or_else(|e| panic!("select b{}: {e}", block.0));
    }
    isel.finalize()
}

fn is_unconditional_terminator(op: AArch64Opcode) -> bool {
    matches!(
        op,
        AArch64Opcode::B | AArch64Opcode::Ret | AArch64Opcode::Br
    )
}

/// Walk the lowered compare/branch chain for a concrete selector value and
/// return the constant the reached leaf materializes. Bounded so a pre-fix
/// dispatch LOOP (case 0: b1 -> b6 -> BST node -> b1 ...) fails loudly
/// instead of hanging.
fn dispatch(func: &ISelFunction, selector: i64) -> i64 {
    let mut block = func.block_order[0];
    let mut cmp: Option<i64> = None;
    for _step in 0..64 {
        let blk = &func.blocks[&block];
        let mut next: Option<Block> = None;
        let mut leaf: Option<i64> = None;
        for inst in &blk.insts {
            match inst.opcode {
                AArch64Opcode::CmpRI => {
                    if let ISelOperand::Imm(imm) = inst.operands[1] {
                        cmp = Some(imm);
                    }
                }
                AArch64Opcode::BCond => {
                    let (cc, target) = match (&inst.operands[0], &inst.operands[1]) {
                        (ISelOperand::CondCode(cc), ISelOperand::Block(b)) => (*cc, *b),
                        other => panic!("unexpected BCond operands {other:?}"),
                    };
                    let pivot = cmp.expect("BCond without a prior CmpRI");
                    use trust_cg_lower::isel::AArch64CC;
                    let taken = match cc {
                        AArch64CC::EQ => selector == pivot,
                        AArch64CC::NE => selector != pivot,
                        AArch64CC::LT => selector < pivot,
                        AArch64CC::GE => selector >= pivot,
                        AArch64CC::GT => selector > pivot,
                        AArch64CC::LE => selector <= pivot,
                        other => panic!("unexpected cc {other:?} in switch dispatch"),
                    };
                    if taken {
                        next = Some(target);
                        break;
                    }
                }
                AArch64Opcode::B => {
                    if let ISelOperand::Block(b) = inst.operands[0] {
                        next = Some(b);
                        break;
                    }
                }
                AArch64Opcode::Movz => {
                    if let ISelOperand::Imm(imm) = inst.operands[1] {
                        leaf = Some(imm);
                    }
                }
                AArch64Opcode::Ret => {
                    return leaf.expect("reached Ret without a materialized constant");
                }
                _ => {}
            }
        }
        match next {
            Some(b) => block = b,
            None => panic!("block b{} had no successor and no Ret", block.0),
        }
    }
    panic!(
        "dispatch({selector}) did not terminate in 64 steps — control-flow loop (the pre-fix collision symptom)"
    );
}

/// The behavioral lock: every case value must reach ITS OWN leaf constant.
/// Pre-fix, selector 0 and 10 looped forever through the aliased BST nodes
/// (caught by the step bound) — the fold_binop-Shl class.
#[test]
fn bst_switch_dispatch_reaches_every_case_leaf() {
    let func = build_collision_isel();
    assert_eq!(dispatch(&func, 0), 1, "case 0 must reach b6's constant");
    assert_eq!(dispatch(&func, 10), 2, "case 10 must reach b7's constant");
    assert_eq!(dispatch(&func, 20), 3, "case 20 must reach b3's constant");
    assert_eq!(dispatch(&func, 30), 4, "case 30 must reach b4's constant");
    assert_eq!(dispatch(&func, 5), 99, "non-case must reach the default");
    assert_eq!(dispatch(&func, 31), 99, "past-max must reach the default");
    assert_eq!(dispatch(&func, -1), 99, "below-min must reach the default");
}

/// Structural locks: no block may contain a second code segment fused behind
/// an unconditional terminator (the collision's signature shape), the real
/// blocks must start with their own code (not foreign compares), and all
/// synthetic ids must be compacted below the 2^31 base by finalize().
#[test]
fn bst_switch_blocks_are_not_aliased_or_fused() {
    let func = build_collision_isel();

    // (1) Single-terminator-group invariant: an unconditional B/Ret/Br only
    // as the last instruction of its block. The pre-fix collided blocks
    // violated this (BST node's `B default` followed by the real block's
    // code).
    for (block, blk) in &func.blocks {
        for (idx, inst) in blk.insts.iter().enumerate() {
            if is_unconditional_terminator(inst.opcode) {
                assert_eq!(
                    idx,
                    blk.insts.len() - 1,
                    "b{}: unconditional {:?} at position {idx} of {} — a second \
                     code segment is fused behind a terminator (block-id collision)",
                    block.0,
                    inst.opcode,
                    blk.insts.len(),
                );
            }
        }
    }

    // (2) The late real blocks (pre-fix collision victims) hold exactly their
    // own lowered code: constant + return plumbing, no compares.
    for (block, imm) in [(Block(6), 1i64), (Block(7), 2i64)] {
        let blk = &func.blocks[&block];
        assert!(
            !blk.insts
                .iter()
                .any(|i| matches!(i.opcode, AArch64Opcode::CmpRI | AArch64Opcode::CmpRR)),
            "b{}: contains foreign switch compares — aliased by a BST node",
            block.0
        );
        assert!(
            blk.insts.iter().any(|i| i.opcode == AArch64Opcode::Movz
                && i.operands.get(1) == Some(&ISelOperand::Imm(imm))),
            "b{}: missing its own constant {imm}",
            block.0
        );
    }

    // (3) finalize() compacted the synthetic BST node ids: 8 real blocks +
    // 2 BST nodes == exactly ids 0..=9.
    let mut ids: Vec<u32> = func.blocks.keys().map(|b| b.0).collect();
    ids.sort_unstable();
    assert_eq!(
        ids,
        (0u32..=9).collect::<Vec<_>>(),
        "synthetic block ids must be compacted contiguously above the real ids"
    );
    for b in &func.block_order {
        assert!(b.0 < (1 << 31), "block_order leaked a non-compacted id");
    }
}

/// Fail-closed gate: selecting a block that already contains instructions
/// (other than the formal-arguments entry block) must be rejected — this is
/// the backstop that catches any future synthetic/real id aliasing.
#[test]
fn selecting_an_already_populated_block_fails_closed() {
    let sig = Signature {
        params: vec![Type::I64],
        returns: vec![Type::I64],
    };
    let mut isel = InstructionSelector::new("double_select".to_string(), sig.clone());
    isel.lower_formal_arguments(&sig, Block(0)).unwrap();
    let body = vec![iconst(10, 7), ret(10)];
    isel.select_block_with_source_locs(Block(1), &body, &[])
        .expect("first selection must succeed");
    let err = isel
        .select_block_with_source_locs(Block(1), &body, &[])
        .expect_err("re-selecting a populated block must fail closed");
    assert!(
        matches!(err, ISelError::BlockAlreadyPopulated { block: 1 }),
        "unexpected error: {err}"
    );
}

/// Fail-closed gate: a real LIR block id inside the selector-synthesized
/// range (>= 2^31) is refused outright.
#[test]
fn lir_block_id_in_synthetic_range_fails_closed() {
    let sig = Signature {
        params: vec![Type::I64],
        returns: vec![Type::I64],
    };
    let mut isel = InstructionSelector::new("synthetic_range".to_string(), sig.clone());
    isel.lower_formal_arguments(&sig, Block(0)).unwrap();
    let err = isel
        .select_block_with_source_locs(Block(1 << 31), &[], &[])
        .expect_err("a block id in the synthetic range must fail closed");
    assert!(
        matches!(err, ISelError::BlockIdInSyntheticRange { .. }),
        "unexpected error: {err}"
    );
}
