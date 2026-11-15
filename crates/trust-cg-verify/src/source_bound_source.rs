// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! ISA-neutral LIR views shared by the source-bound owners.
//!
//! These functions read only the LIR function. They decide whether a source
//! lies in a bounded unconditional block chain and, if so, flatten it into one
//! block. They never inspect machine code, so applicability stays a property
//! of the source alone. A view grants no proof authority and never replaces
//! the original input: every owner still borrows the exact source it judged.
//!
//! The AArch64 frame owner and the x86-64 body owner both consume
//! [`linear_chain_view`]; the exact affine normal form [`Affine`] is re-exported
//! here so the x86-64 owner's solver-independent refusal check does not name
//! an AArch64 module.

use std::collections::HashSet;
use trust_cg_lower::Function;
use trust_cg_lower::instructions::Opcode as L;

pub(crate) use crate::aarch64_affine_lowering::Affine;

/// A bounded unconditional LIR chain, flattened.
pub(crate) struct LinearChain {
    /// One-block copy of the source: every non-terminator instruction of the
    /// chain in execution order, then the final `Return`.
    pub(crate) view: Function,
}

/// Follow the source's entry block through unconditional `Jump`s to a
/// `Return`.
///
/// Accepts at most sixteen blocks and 256 flattened instructions. Every block
/// must lie on the chain exactly once; a non-entry block may not declare
/// parameters (cross-block values keep their SSA identities, and block
/// arguments would need a separate simultaneous substitution rule). The
/// flattened view keeps the entry block's parameters and clears source
/// locations and TrustIR origins.
pub(crate) fn linear_chain(source: &Function) -> Option<LinearChain> {
    chain_to(source, false)
}

/// [`linear_chain`], except that the chain may also end in a `Trap` (the
/// terminator the trust-ir adapter emits after a call that never returns).
/// Only the x86-64 ABI envelope owner, whose domain admits a diverging direct
/// call, reads this view; the AArch64 owners keep [`linear_chain`]. (The
/// x86-64 body owner walks every path of an acyclic CFG itself, slice 6.)
pub(crate) fn linear_chain_to_end(source: &Function) -> Option<LinearChain> {
    chain_to(source, true)
}

fn chain_to(source: &Function, accept_trap: bool) -> Option<LinearChain> {
    if source.blocks.is_empty() || source.blocks.len() > 16 {
        return None;
    }
    if source.blocks.len() == 1 {
        source.blocks.get(&source.entry_block)?;
        return Some(LinearChain {
            view: source.clone(),
        });
    }
    if !source.block_order.is_empty()
        && (source.block_order.len() != source.blocks.len()
            || source.block_order.iter().collect::<HashSet<_>>().len() != source.blocks.len()
            || source
                .block_order
                .iter()
                .any(|id| !source.blocks.contains_key(id)))
    {
        return None;
    }
    let mut visited = HashSet::new();
    let mut current = source.entry_block;
    let mut instructions = Vec::new();
    loop {
        if !visited.insert(current) {
            return None;
        }
        let block = source.blocks.get(&current)?;
        // Cross-block values retain their SSA identities. Block arguments
        // would require a separate simultaneous substitution rule.
        if current != source.entry_block && !block.params.is_empty() {
            return None;
        }
        let (last, prefix) = block.instructions.split_last()?;
        instructions.extend_from_slice(prefix);
        if instructions.len() > 256 {
            return None;
        }
        match last.opcode {
            L::Jump { dest } if last.args.is_empty() && last.results.is_empty() => current = dest,
            L::Return => {
                instructions.push(last.clone());
                break;
            }
            L::Trap if accept_trap && last.args.is_empty() && last.results.is_empty() => {
                instructions.push(last.clone());
                break;
            }
            _ => return None,
        }
    }
    if visited.len() != source.blocks.len() {
        return None;
    }
    let mut view = source.clone();
    let mut entry = source.blocks.get(&source.entry_block)?.clone();
    entry.instructions = instructions;
    entry.source_locs.clear();
    view.blocks.clear();
    view.blocks.insert(source.entry_block, entry);
    view.block_order = vec![source.entry_block];
    view.trust_ir_origins.clear();
    Some(LinearChain { view })
}

/// The flattened view of [`linear_chain`].
pub(crate) fn linear_chain_view(source: &Function) -> Option<Function> {
    linear_chain(source).map(|chain| chain.view)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::Type;
    use trust_cg_lower::function::{BasicBlock, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Value};

    fn instruction(opcode: L, args: Vec<Value>, results: Vec<Value>) -> Instruction {
        Instruction {
            opcode,
            args,
            results,
        }
    }

    fn chain() -> Function {
        let mut source = Function::new(
            "chain",
            Signature {
                params: vec![Type::I64],
                returns: vec![Type::I64],
            },
        );
        source.entry_block = Block(0);
        source.blocks.insert(
            Block(0),
            BasicBlock {
                params: vec![(Value(0), Type::I64)],
                instructions: vec![
                    instruction(L::Copy, vec![Value(0)], vec![Value(1)]),
                    instruction(L::Jump { dest: Block(1) }, vec![], vec![]),
                ],
                source_locs: vec![],
            },
        );
        source.blocks.insert(
            Block(1),
            BasicBlock {
                params: vec![],
                instructions: vec![instruction(L::Return, vec![Value(1)], vec![])],
                source_locs: vec![],
            },
        );
        source.block_order = vec![Block(0), Block(1)];
        source
    }

    #[test]
    fn chain_view_flattens_the_chain_in_execution_order() {
        let source = chain();
        let chain = linear_chain(&source).expect("two-block chain");
        let block = &chain.view.blocks[&Block(0)];
        let opcodes: Vec<&L> = block.instructions.iter().map(|inst| &inst.opcode).collect();
        assert_eq!(opcodes, [&L::Copy, &L::Return]);
        assert_eq!(chain.view.block_order, vec![Block(0)]);
        assert_eq!(linear_chain_view(&source).unwrap().blocks.len(), 1);
    }

    #[test]
    fn non_chain_sources_have_no_view() {
        let mut cyclic = chain();
        cyclic.blocks.get_mut(&Block(1)).unwrap().instructions =
            vec![instruction(L::Jump { dest: Block(0) }, vec![], vec![])];
        assert!(linear_chain(&cyclic).is_none());
        let mut orphan = chain();
        orphan.blocks.insert(
            Block(2),
            BasicBlock {
                params: vec![],
                instructions: vec![instruction(L::Return, vec![Value(0)], vec![])],
                source_locs: vec![],
            },
        );
        orphan.block_order.push(Block(2));
        assert!(linear_chain(&orphan).is_none());
    }
}
