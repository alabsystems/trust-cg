// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Layout is target-neutral: retain the old exact order, not merely any RPO.

use super::*;

fn body(opcode: Opcode) -> BasicBlock {
    BasicBlock {
        instructions: vec![Instruction {
            opcode,
            args: vec![],
            results: vec![],
        }],
        ..Default::default()
    }
}

// Independent, bounded oracle is the former recursive production algorithm,
// including its deterministic handling of unreachable/duplicate/missing IDs.
fn legacy_order(function: &Function) -> Vec<Block> {
    fn visit(f: &Function, block: Block, seen: &mut HashSet<Block>, out: &mut Vec<Block>) {
        if !f.blocks.contains_key(&block) || !seen.insert(block) {
            return;
        }
        for next in f.blocks[&block].layout_successors() {
            visit(f, next, seen, out);
        }
        out.push(block);
    }
    let mut seen = HashSet::new();
    let mut order = Vec::new();
    visit(function, function.entry_block, &mut seen, &mut order);
    order.reverse();
    let mut remaining: Vec<_> = function
        .block_order
        .iter()
        .copied()
        .filter(|b| function.blocks.contains_key(b) && !seen.contains(b))
        .collect();
    let mut fallback: Vec<_> = function
        .blocks
        .keys()
        .copied()
        .filter(|b| !seen.contains(b) && !remaining.contains(b))
        .collect();
    fallback.sort_by_key(|b| b.0);
    remaining.extend(fallback);
    order.extend(remaining.into_iter().filter(|b| seen.insert(*b)));
    order
}

#[test]
fn layout_exactly_matches_recursive_oracle_on_seeded_cfgs() {
    let mut seed = 20_261_009_u32;
    let mut next = || {
        seed = seed.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        seed
    };
    for sample in 0..256 {
        let mut function = Function::new("layout_oracle", Signature::default());
        function.entry_block = Block(next() % 11);
        function.block_order = vec![Block(7), Block(3), Block(7), Block(99), Block(0)];
        for index in (0..9).rev() {
            let first = Block(next() % 11);
            let second = Block(next() % 11);
            let opcode = match next() % 5 {
                0 => Opcode::Return,
                1 => Opcode::Jump { dest: first },
                2 => Opcode::Brif {
                    cond: Value(0),
                    then_dest: first,
                    else_dest: second,
                },
                3 => Opcode::Invoke {
                    binding: crate::instructions::DirectCallBinding::Interposable,
                    name: "external".into(),
                    normal_dest: first,
                    unwind_dest: second,
                },
                _ => Opcode::Switch {
                    cases: vec![(0, first), (1, second), (2, first)],
                    default: Block(next() % 11),
                },
            };
            function.blocks.insert(Block(index), body(opcode));
        }
        assert_eq!(
            function.layout_order(),
            legacy_order(&function),
            "sample {sample}"
        );
    }
}

#[test]
fn deep_layout_walk_runs_on_an_unchanged_256_kib_caller() {
    const BLOCKS: u32 = 16_384;
    let mut function = Function::new("deep_layout", Signature::default());
    function.entry_block = Block(0);
    for index in 0..BLOCKS {
        let opcode = if index + 1 == BLOCKS {
            Opcode::Jump { dest: Block(0) }
        } else {
            Opcode::Jump {
                dest: Block(index + 1),
            }
        };
        function.blocks.insert(Block(index), body(opcode));
    }
    let thread = std::thread::Builder::new()
        .name("cg-rpo-256-kib".into())
        .stack_size(256 << 10)
        .spawn(move || {
            assert_eq!(
                function.layout_order(),
                (0..BLOCKS).map(Block).collect::<Vec<_>>()
            );
        })
        .unwrap();
    thread.join().unwrap();
}

#[test]
fn unreachable_layout_uses_linear_membership_and_retains_explicit_order() {
    const BLOCKS: u32 = 16_384;
    let mut function = Function::new("wide_unreachable_layout", Signature::default());
    function.entry_block = Block(0);
    for index in 0..BLOCKS {
        function.blocks.insert(Block(index), body(Opcode::Return));
    }
    function.block_order = (1..BLOCKS)
        .rev()
        .filter(|i| i % 2 == 1)
        .map(Block)
        .collect();
    function
        .block_order
        .extend([Block(99), Block(BLOCKS), Block(0)]);
    let expected = std::iter::once(Block(0))
        .chain((1..BLOCKS).rev().filter(|i| i % 2 == 1).map(Block))
        .chain((2..BLOCKS).filter(|i| i % 2 == 0).map(Block))
        .collect::<Vec<_>>();
    assert_eq!(function.layout_order(), expected);
}
