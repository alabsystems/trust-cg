// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A bounded pure-Jump CFG has a non-vacuous control observable: its next PC.
//! The source alone admits this domain, before any target is consulted. Every
//! source block contains exactly one argument-free Jump and every block is
//! reachable. The final machine body must preserve the block identifiers,
//! entry and complete edges, with exactly one resolved B per block and no
//! other row. Thus neither a missing computation nor a dropped effect can hide
//! inside this owner. This includes cycles, but no conditional/value loop.
//!
//! The theorem compares each source destination's image offset with the
//! architectural next PC of that block's independently decoded B word, for an
//! arbitrary 64-bit image base. The displacement is kept as the decoded 26-bit
//! field concatenated with two zero bits, sign-extended to 64 bits; it is not
//! replaced with the source target. Construction and the early target check
//! are trusted Rust binding/refutation, never proof. Only the existing sealed
//! source-bound replay, checking a hole-free certificate against this exact
//! original query, can give the rows Formal credit. ENC-5 and the final-layout
//! check still bind these re-derived words and graph to emitted bytes.
//!
//! This is a per-step control theorem, not a return-value equality, a general
//! loop proof, an EH proof or a proof of the Rust binder. A B writes no general
//! register, SP, NZCV or memory in the Arm model. Every admitted source and
//! machine step has one successor, so repeated corresponding steps preserve
//! the same pure control graph, including its eventual cycle. Code residency,
//! instruction-fetch permissions and faithfulness of Arm's transcription are
//! the same external premises as the existing source-bound body model.

use super::{
    A64BodyMismatch, A64BodyRefusal, A64BodyUnsupported, SourceBoundA64Body, mismatch, unsupported,
};
use crate::aarch64_instruction_word_proofs::{DecodedWord, decode_word, instruction_word};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use std::collections::HashSet;
use trust_cg_ir::function::StackProtectorMode;
use trust_cg_ir::{AArch64Opcode as M, BlockId, MachFunction, MachOperand as O};
use trust_cg_lower::Function;
use trust_cg_lower::instructions::{Block, Opcode as L};

pub(super) const OBLIGATION_NAME: &str = "Source-bound AArch64 pure-jump transition theorem (Rust CFG binding; independently replayed decoded-word next-PC equality)";

/// An admission result contains actual source destinations, never machine
/// successors or provenance sidecars. Its bound is the body owner's existing
/// sixteen-block bound.
pub(super) fn source_edges(source: &Function) -> Option<Vec<u32>> {
    let count = source.blocks.len();
    if count == 0
        || count > super::source::MAX_SOURCE_BLOCKS
        || !source.signature.params.is_empty()
        || !source.signature.returns.is_empty()
        || !source.stack_slots.is_empty()
        || !source.eh_info.is_empty()
        || source.stack_protector != StackProtectorMode::None
        || source.stack_limit.is_some()
        || !source.param_pointee_types.is_empty()
        || source.abi_sret_param.is_some()
        || !source.sret_arg_callees.is_empty()
        || !source.sret_arg_indirect_callees.is_empty()
        || !source.value_types.is_empty()
        || source.entry_block.0 as usize >= count
    {
        return None;
    }
    if !source.block_order.is_empty()
        && (source.block_order.len() != count
            || source
                .block_order
                .iter()
                .copied()
                .collect::<HashSet<_>>()
                .len()
                != count
            || source
                .block_order
                .iter()
                .any(|block| !source.blocks.contains_key(block)))
    {
        return None;
    }
    let mut edges = Vec::with_capacity(count);
    for index in 0..count {
        let block = source.blocks.get(&Block(index as u32))?;
        let [jump] = block.instructions.as_slice() else {
            return None;
        };
        let L::Jump { dest } = jump.opcode else {
            return None;
        };
        if !block.params.is_empty()
            || !jump.args.is_empty()
            || !jump.results.is_empty()
            || dest.0 as usize >= count
        {
            return None;
        }
        edges.push(dest.0);
    }
    let mut seen = vec![false; count];
    let mut block = source.entry_block.0 as usize;
    while !seen[block] {
        seen[block] = true;
        block = edges[block] as usize;
    }
    seen.into_iter().all(|reachable| reachable).then_some(edges)
}

fn machine_shape(reason: &str) -> A64BodyRefusal {
    // The source has already admitted this complete control domain. Falling
    // back to per-row coverage here could turn a dropped B into a skipped
    // pseudo row and a promotable empty inventory. Reject the function before
    // any row can inherit unrelated evidence.
    mismatch(A64BodyMismatch::PureJumpBody {
        detail: reason.into(),
    })
}

pub(super) fn build<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
    edges: &[u32],
    refute: bool,
) -> Result<SourceBoundA64Body<'a>, A64BodyRefusal> {
    let count = edges.len();
    if source.name != machine.name {
        return Err(unsupported(A64BodyUnsupported::MachineFunction(
            "the machine function is not the source's".into(),
        )));
    }
    if !machine.signature.params.is_empty() || !machine.signature.returns.is_empty() {
        return Err(mismatch(A64BodyMismatch::Signature));
    }
    if !machine.stack_slots.is_empty()
        || machine.eh_metadata.has_eh_info()
        || machine.stack_protector != StackProtectorMode::None
        || machine.stack_protector_slot.is_some()
        || machine.stack_limit.is_some()
        || machine.stack_limit_overflow_block.is_some()
        || !machine.jump_tables.is_empty()
    {
        return Err(unsupported(A64BodyUnsupported::MachineFunction(
            "pure-jump body has stack, EH, protection, stack-limit or jump-table metadata".into(),
        )));
    }
    if machine.blocks.len() != count
        || machine.insts.len() != count
        || machine.entry.0 != source.entry_block.0
        || machine.block_order.len() != count
        || machine.block_order.first() != Some(&machine.entry)
        || machine
            .block_order
            .iter()
            .copied()
            .collect::<HashSet<_>>()
            .len()
            != count
        || machine
            .block_order
            .iter()
            .any(|block| block.0 as usize >= count)
    {
        return Err(machine_shape(
            "different block ownership, entry or complete layout",
        ));
    }
    let mut offsets = vec![0i64; count];
    for (position, block) in machine.block_order.iter().enumerate() {
        offsets[block.0 as usize] = position as i64;
    }
    let mut owned = HashSet::new();
    let mut covered = Vec::with_capacity(count);
    let base = E::var("image_base", 64);
    let mut equalities = Vec::with_capacity(count);
    for (index, block) in machine.blocks.iter().enumerate() {
        let [id] = block.insts.as_slice() else {
            return Err(machine_shape("each block must own exactly one B"));
        };
        if !owned.insert(*id) {
            return Err(machine_shape("a branch has more than one block owner"));
        }
        let inst = machine
            .insts
            .get(id.0 as usize)
            .ok_or_else(|| machine_shape("a block names an absent instruction"))?;
        if inst.opcode != M::B
            || inst.flags != M::B.default_flags()
            || !inst.implicit_defs.is_empty()
            || !inst.implicit_uses.is_empty()
        {
            return Err(machine_shape(
                "only B with exact default effects is admitted",
            ));
        }
        let [O::Imm(words)] = inst.operands.as_slice() else {
            return Err(machine_shape(
                "B needs its resolved signed word displacement",
            ));
        };
        let expected = offsets[edges[index] as usize] - offsets[index];
        let word = instruction_word(inst)
            .filter(|word| word.hole_mask == 0)
            .ok_or_else(|| machine_shape("B has no complete legal instruction word"))?;
        let Some(DecodedWord::BranchImm { op: 0, imm26 }) = decode_word(word.word) else {
            return Err(machine_shape("the word is not independently decoded as B"));
        };
        if block.succs.as_slice() != [BlockId(edges[index])] {
            return Err(machine_shape(
                "recorded successor differs from the source Jump",
            ));
        }
        let mut actual_preds = block.preds.clone();
        actual_preds.sort_unstable();
        let expected_preds: Vec<_> = edges
            .iter()
            .enumerate()
            .filter_map(|(pred, dest)| (*dest == index as u32).then_some(BlockId(pred as u32)))
            .collect();
        if actual_preds != expected_preds {
            return Err(machine_shape(
                "recorded predecessors differ from the source graph",
            ));
        }
        if refute && *words != expected {
            return Err(mismatch(A64BodyMismatch::PureJumpTarget {
                block: BlockId(index as u32),
                instruction: *id,
                expected_words: expected,
                actual_words: *words,
            }));
        }
        let source_next = base
            .clone()
            .bvadd(E::bv_const((offsets[edges[index] as usize] * 4) as u64, 64));
        // Arm B: BranchTo(PC64 + SignExtend(imm26:'00', 64)). Keep the
        // independent decode's real field in the theorem, including its sign.
        let machine_next = crate::aarch64_instruction_word_proofs::decoded_b_next_pc(
            base.clone()
                .bvadd(E::bv_const((offsets[index] * 4) as u64, 64)),
            imm26,
        );
        equalities.push(source_next.eq_expr(machine_next));
        covered.push(*id);
    }
    let mut statements = equalities.into_iter();
    let first = statements
        .next()
        .expect("source admission requires a nonempty graph");
    let all_steps = statements.fold(first, E::and_expr);
    covered.sort_unstable();
    Ok(SourceBoundA64Body {
        source,
        machine,
        covered,
        copies_and_constants: Vec::new(),
        obligation: ProofObligation {
            name: OBLIGATION_NAME.into(),
            trust_ir_expr: E::BoolConst(true),
            aarch64_expr: all_steps,
            inputs: vec![("image_base".into(), 64)],
            preconditions: Vec::new(),
            fp_inputs: Vec::new(),
            category: Some(TransvalCheckKind::ControlFlow),
            machine_side_provenance: MachineSideProvenance::StaticDb,
        },
    })
}
