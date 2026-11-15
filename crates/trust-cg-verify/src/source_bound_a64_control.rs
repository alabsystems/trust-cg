// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source-CFG next-PC obligations bound to a checked frame or frameless body.
//! Construction grants no credit. A framed binding first requires independent
//! frame replay; a frameless binding first checks complete source/return routing
//! without memory or preserved-register effects. Only actual B rows receive
//! independently replayed control credit. Identity/copy value credit and RET
//! coverage are not granted by this theorem. ENC-5 and final-layout checks still
//! bind its words to emitted bytes; code residency remains an external premise.

use std::collections::{HashMap, HashSet};

use crate::aarch64_instruction_word_proofs::{
    DecodedWord, decode_word, decoded_b_next_pc, instruction_word,
};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use crate::source_bound_frame::{RawControl, SourceBoundFrame};
use trust_cg_ir::{AArch64Opcode as M, BlockId, InstId, MachOperand as O};
use trust_cg_lower::instructions::{Block, Opcode as L};

enum ControlBinding<'owner, 'inputs> {
    Frame(&'owner SourceBoundFrame<'inputs>),
    Frameless(&'owner CheckedFramelessLinear<'inputs>),
}

pub(crate) struct SourceBoundA64Control<'owner, 'inputs> {
    _binding: ControlBinding<'owner, 'inputs>,
    covered: HashSet<InstId>,
    obligation: ProofObligation,
}

impl<'owner, 'inputs> SourceBoundA64Control<'owner, 'inputs> {
    pub(crate) fn bind(frame: &'owner SourceBoundFrame<'inputs>) -> Option<Self> {
        if !matches!(frame.raw_control()?, RawControl::Chain(_)) {
            return None;
        }
        Self::build(ControlBinding::Frame(frame))
    }

    pub(crate) fn bind_frameless(body: &'owner CheckedFramelessLinear<'inputs>) -> Option<Self> {
        Self::build(ControlBinding::Frameless(body))
    }

    fn build(binding: ControlBinding<'owner, 'inputs>) -> Option<Self> {
        let (source, machine, name) = match &binding {
            ControlBinding::Frame(frame) => (
                frame.source(),
                frame.machine(),
                "Source-bound AArch64 framed control theorem: decoded B next-PC equals the original LIR successor",
            ),
            ControlBinding::Frameless(body) => (
                body.source,
                body.machine,
                "Source-bound AArch64 frameless control theorem: decoded B next-PC equals the original LIR successor",
            ),
        };
        let count = source.blocks.len();
        if count == 0
            || count > 16
            || machine.blocks.len() != count
            || machine.entry.0 != source.entry_block.0
        {
            return None;
        }
        // Reuse the final-layout chain checker, including resolved branches,
        // unique instruction ownership, predecessors, fallthrough and RET.
        crate::source_bound_frame::linear::machine_chain(machine).ok()?;
        let mut offsets = HashMap::new();
        let mut positions = HashMap::new();
        let mut word = 0i64;
        for block in &machine.block_order {
            offsets.insert(*block, word);
            for id in &machine.blocks.get(block.0 as usize)?.insts {
                positions.insert(*id, word);
                word += i64::from(!machine.insts.get(id.0 as usize)?.is_pseudo());
            }
        }
        let base = E::var("image_base", 64);
        let mut covered = HashSet::new();
        let mut claims = Vec::new();
        for index in 0..count {
            let block = source.blocks.get(&Block(index as u32))?;
            let machine_block = machine.blocks.get(index)?;
            let terminator = block.instructions.last()?;
            let branches: Vec<_> = machine_block
                .insts
                .iter()
                .copied()
                .filter(|id| machine.insts[id.0 as usize].opcode == M::B)
                .collect();
            match &terminator.opcode {
                L::Jump { dest } => {
                    if !terminator.args.is_empty()
                        || !terminator.results.is_empty()
                        || machine_block.succs.as_slice() != [BlockId(dest.0)]
                        || !source.blocks.contains_key(dest)
                    {
                        return None;
                    }
                    let [id] = branches.as_slice() else {
                        return None;
                    };
                    let inst = machine.insts.get(id.0 as usize)?;
                    if inst.flags != M::B.default_flags()
                        || !inst.implicit_defs.is_empty()
                        || !inst.implicit_uses.is_empty()
                        || !matches!(inst.operands.as_slice(), [O::Imm(_)])
                    {
                        return None;
                    }
                    let encoded = instruction_word(inst)?;
                    if encoded.hole_mask != 0 {
                        return None;
                    }
                    let DecodedWord::BranchImm { op: 0, imm26 } = decode_word(encoded.word)? else {
                        return None;
                    };
                    let source_next = base.clone().bvadd(E::bv_const(
                        (*offsets.get(&BlockId(dest.0))? * 4) as u64,
                        64,
                    ));
                    let pc = base
                        .clone()
                        .bvadd(E::bv_const((*positions.get(id)? * 4) as u64, 64));
                    claims.push(source_next.eq_expr(decoded_b_next_pc(pc, imm26)));
                    covered.insert(*id);
                }
                L::Return if branches.is_empty() && machine_block.succs.is_empty() => {}
                _ => return None,
            }
        }
        let mut claims = claims.into_iter();
        let statement = claims.next()?;
        let statement = claims.fold(statement, E::and_expr);
        Some(Self {
            _binding: binding,
            covered,
            obligation: ProofObligation {
                name: name.into(),
                trust_ir_expr: E::bool_const(true),
                aarch64_expr: statement,
                inputs: vec![("image_base".into(), 64)],
                preconditions: Vec::new(),
                fp_inputs: Vec::new(),
                category: Some(TransvalCheckKind::ControlFlow),
                machine_side_provenance: MachineSideProvenance::StaticDb,
            },
        })
    }

    pub(crate) fn replay_reason(&self) -> &'static str {
        match self._binding {
            ControlBinding::Frame(_) => {
                "source-bound framed control needs independently replayed proof"
            }
            ControlBinding::Frameless(_) => {
                "source-bound frameless control needs independently replayed proof"
            }
        }
    }

    pub(crate) fn credits(&self, id: InstId) -> bool {
        self.covered.contains(&id)
    }

    pub(crate) fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
}

/// Complete, independently interpreted source/allocated return routing for a
/// storage-free linear body. This is a trusted Rust binding witness, not an
/// SMT discharge or permission to credit identity/copy instructions.
pub(crate) struct CheckedFramelessLinear<'a> {
    source: &'a trust_cg_lower::Function,
    machine: &'a trust_cg_ir::MachFunction,
}

impl<'a> CheckedFramelessLinear<'a> {
    pub(crate) fn bind(
        source: &'a trust_cg_lower::Function,
        machine: &'a trust_cg_ir::MachFunction,
    ) -> Result<Self, crate::source_bound_frame::SourceBoundFrameRefusal> {
        use crate::source_bound_frame::{
            ControlRefusal, FrameShapeUnsupported as U, SourceBoundFrameRefusal as R,
        };
        let unsupported = |reason| R::Unsupported(reason);
        let view = crate::source_bound_source::linear_chain_view(source)
            .ok_or_else(|| unsupported(U::SourceShape))?;
        crate::aarch64_affine_lowering::check_affine_source_domain(&view)
            .map_err(|error| unsupported(U::SourceDomain(error)))?;
        let chain =
            crate::source_bound_frame::linear::machine_chain(machine).map_err(
                |error| match error {
                    ControlRefusal::Shape => unsupported(U::MachineControl),
                    ControlRefusal::Branch(mismatch) => R::Mismatch(mismatch),
                },
            )?;
        crate::source_bound_frame::check_owned_instructions(machine, &chain.live, false)
            .ok_or_else(|| unsupported(U::Ownership))?;
        let scalar = crate::source_bound_frame::scalar_body(machine, &chain.instructions);
        crate::aarch64_affine_lowering::check_allocated_aarch64_affine_lowering(&view, &scalar)
            .map_err(crate::source_bound_frame::classify_body)?;
        Ok(Self { source, machine })
    }
}
