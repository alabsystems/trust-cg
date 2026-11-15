// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded lexical SSA lifetime for the already validated source graph.
//!
//! Every operand participates, including dead instructions, both Select arms,
//! both constant-branch edges and ALL parallel edge arguments. Only evaluation
//! environments are pruned: the driver still evaluates/checks each instruction
//! and retains independent guards, geometry and load demands. No expressions,
//! semantic queries, proof rules or source instructions are rewritten.

use super::super::{Block, Boundary, Graph, MAX_VALUES, Operation, ReadOnlySourceError, Value};
use std::collections::HashMap;

const WORDS: usize = MAX_VALUES.div_ceil(64);

/// Dense bounded slots, independent of producer-controlled sparse SSA IDs.
#[derive(Clone, Copy, Default)]
struct Set([u64; WORDS]);

impl Set {
    fn insert(&mut self, index: usize) {
        self.0[index / 64] |= 1 << (index % 64);
    }

    fn remove(&mut self, index: usize) {
        self.0[index / 64] &= !(1 << (index % 64));
    }

    fn contains(&self, index: usize) -> bool {
        self.0[index / 64] & (1 << (index % 64)) != 0
    }

    fn union(&mut self, other: Self) {
        for (word, other) in self.0.iter_mut().zip(other.0) {
            *word |= other;
        }
    }
}

pub(super) struct Liveness {
    indices: HashMap<u32, usize>,
    ids: Vec<u32>,
    before: HashMap<u32, Vec<Set>>,
}

impl Liveness {
    pub(super) fn needed(&self, block: u32, instruction: usize, id: u32) -> bool {
        self.indices
            .get(&id)
            .is_some_and(|&index| self.before[&block][instruction].contains(index))
    }

    pub(super) fn retain_before(
        &self,
        block: u32,
        instruction: usize,
        values: &mut HashMap<u32, Value>,
    ) {
        values.retain(|&id, _| self.needed(block, instruction, id));
    }

    pub(super) fn release_after(
        &self,
        block: u32,
        instruction: usize,
        result: Option<u32>,
        values: &mut HashMap<u32, Value>,
    ) {
        let mut current = self.before[&block][instruction];
        if let Some(result) = result {
            current.insert(self.indices[&result]);
        }
        let next = self.before[&block][instruction + 1];
        // Remove only actual last-use slots, not a scan of the whole growing
        // environment after every instruction. The six dense words are fixed.
        for (word_index, (&current, &next)) in current.0.iter().zip(&next.0).enumerate() {
            let mut retired = current & !next;
            while retired != 0 {
                let index = word_index * 64 + retired.trailing_zeros() as usize;
                values.remove(&self.ids[index]);
                retired &= retired - 1;
            }
        }
    }
}

fn operands(operation: &Operation, mut visit: impl FnMut(u32)) {
    match operation {
        Operation::NativeTarget(op) => op.operands(visit),
        Operation::NativeTargetFrontier => {}
        Operation::Constant(_) | Operation::VoidReturn | Operation::NullPointer => {}
        Operation::ExactModuleCall { args, .. } => args.iter().copied().for_each(visit),
        Operation::NativeAggregateCall { args, .. } => args.iter().copied().for_each(visit),
        Operation::AggregateField { record, .. } => visit(*record),
        Operation::VectorReturn(values) => values.iter().map(|(id, _)| *id).for_each(visit),
        Operation::Copy(value) | Operation::Return(value) | Operation::ZeroExtend(value) => {
            visit(*value)
        }
        Operation::Binary { left, right, .. } | Operation::Compare { left, right, .. } => {
            visit(*left);
            visit(*right);
        }
        Operation::Select {
            condition,
            then_value,
            else_value,
            ..
        } => {
            visit(*condition);
            visit(*then_value);
            visit(*else_value);
        }
        Operation::Offset { base, index, .. } | Operation::ScaledOffset { base, index, .. } => {
            visit(*base);
            visit(*index);
        }
        Operation::Load { address, .. } | Operation::MemoryLoad { address, .. } => visit(*address),
        Operation::Store { address, value, .. } => {
            visit(*address);
            visit(*value);
        }
        Operation::Jump { args, .. } => args.iter().copied().for_each(visit),
        Operation::Branch {
            condition,
            then_args,
            else_args,
            ..
        } => {
            visit(*condition);
            then_args.iter().copied().for_each(&mut visit);
            else_args.iter().copied().for_each(visit);
        }
    }
}

/// The caller supplies the full shape/SSA uniqueness/reachability/acyclic
/// validation and its actual topological order, not physical block layout.
/// At most MAX_VALUES slots and MAX_INSTRUCTIONS fixed-size sets are retained.
pub(super) fn compute(
    graph: &Graph,
    blocks: &HashMap<u32, &Block>,
    order: &[u32],
    boundary: Boundary,
) -> Result<Liveness, ReadOnlySourceError> {
    let mut indices = HashMap::new();
    let mut ids = Vec::new();
    for block in &graph.blocks {
        for id in block
            .parameters
            .iter()
            .map(|&(id, _)| id)
            .chain(block.nodes.iter().flat_map(|node| node.definition_ids()))
        {
            let index = indices.len();
            if index >= MAX_VALUES {
                return Err(ReadOnlySourceError::Budget("SSA values"));
            }
            indices.insert(id, index);
            ids.push(id);
        }
    }
    let mut before: HashMap<u32, Vec<Set>> = HashMap::with_capacity(blocks.len());
    for &id in order.iter().rev() {
        let block = blocks[&id];
        let mut live = Set::default();
        for successor in super::destinations(&block.nodes.last().unwrap().operation) {
            let mut incoming = before[&successor][0];
            // Destination parameters are locally defined by parallel edge
            // copies, not dominating definitions imported from this block.
            for &(parameter, _) in &blocks[&successor].parameters {
                incoming.remove(indices[&parameter]);
            }
            live.union(incoming);
        }
        let mut node_sets = vec![Set::default(); block.nodes.len()];
        for (instruction, node) in block.nodes.iter().enumerate().rev() {
            for result in node.definition_ids() {
                live.remove(indices[&result]);
            }
            let mut missing = false;
            operands(&node.operation, |operand| {
                if let Some(&index) = indices.get(&operand) {
                    live.insert(index);
                } else {
                    missing = true;
                }
            });
            if missing {
                return Err(boundary.error("undefined or nondominating SSA operand"));
            }
            node_sets[instruction] = live;
        }
        before.insert(id, node_sets);
    }
    Ok(Liveness {
        indices,
        ids,
        before,
    })
}
