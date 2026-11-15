// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conditional byte-memory semantics for checked static GPR64 envelopes.
//!
//! Construction is NOT discharge, source binding, instruction credit, ABI or
//! allocation authority. This owner cannot enter `SourceBoundReplay`. It runs
//! only the selected, word-checked prologue/epilogues in the legacy constructor.
//! Its exits have arbitrary resume memory and explicit SP/FP and saved-lane
//! premises. The opt-in checked-body constructor derives those preservation
//! facts from actual body words and original/LIR/byte-checked affine callees.
//! It does not establish actual E1's missing stateful provider contracts.
//!
//! The conclusion restores only the saved GPR identities and entry SP. It says
//! nothing about source results, other registers, outside memory, reachability,
//! call return, faults, allocation validity/lifetime or private saved bytes.
//! Geometry retains its own body-image/fixup/installed-image limitations.

use std::collections::BTreeMap;

use trust_cg_ir::{AArch64Opcode as Op, InstId, MachInst, MachOperand as O, SpecialReg};

use crate::aarch64_pair_memory::{PairMemoryFormat, check_pair_encoding};
use crate::aarch64_static_frame::{
    CheckedStaticFrameEnvelopes, SavedFrameRegister, SavedFrameSlot,
};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
use crate::smt::SmtExpr as E;

#[path = "aarch64_frame_body.rs"]
mod body;
pub use body::{
    CheckedFrameBody, FrameBodyCall, ReadonlyFrameBodyCall, check_frame_body,
    check_readonly_frame_body,
};

/// Meaning of a premise at the same index in an exit obligation's preconditions.
/// These labels are an inventory of assumptions, not checked body evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConditionalFramePremise {
    EntrySpNonwrapping { frame_bytes: u32 },
    EntrySpAlignment { bytes: u32 },
    ResumeSp { relative_offset: i64 },
    ResumeFp { relative_offset: i64 },
    SavedLane(SavedFrameSlot),
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ConditionalFrameRefusal {
    #[error("conditional static frame currently requires nonempty GPR64 saved slots")]
    SavedRegisterDomain,
    #[error("checked frame geometry inconsistent with its borrowed inputs: {0}")]
    Geometry(String),
}

type Result<T> = std::result::Result<T, ConditionalFrameRefusal>;
fn inconsistent(why: impl Into<String>) -> ConditionalFrameRefusal {
    ConditionalFrameRefusal::Geometry(why.into())
}

/// One conditional exit claim. Its preconditions must be established across the
/// actual body independently, even after an independent proof of this query.
#[derive(Debug)]
pub struct ConditionalStaticFrameExit {
    return_instruction: InstId,
    resume_memory: E,
    premises: Vec<ConditionalFramePremise>,
    obligation: ProofObligation,
}

impl ConditionalStaticFrameExit {
    pub fn return_instruction(&self) -> InstId {
        self.return_instruction
    }
    pub fn resume_memory(&self) -> &E {
        &self.resume_memory
    }
    pub fn premises(&self) -> &[ConditionalFramePremise] {
        &self.premises
    }
    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
}

/// Exact borrowed endpoints and still-undischarged conditional exit queries.
/// No verdict attachment, source-owner, callable or publication conversion.
#[derive(Debug)]
pub struct ConditionalStaticFrame<'g, 'a> {
    geometry: &'g CheckedStaticFrameEnvelopes<'a>,
    post_save_memory: E,
    exits: Vec<ConditionalStaticFrameExit>,
}

impl<'g, 'a> ConditionalStaticFrame<'g, 'a> {
    pub fn geometry(&self) -> &'g CheckedStaticFrameEnvelopes<'a> {
        self.geometry
    }
    /// One actual store chain shared by every exit, not independent per-pair
    /// memories or a constant-default approximation.
    pub fn post_save_memory(&self) -> &E {
        &self.post_save_memory
    }
    pub fn exits(&self) -> &[ConditionalStaticFrameExit] {
        &self.exits
    }
}

struct State {
    sp: E,
    registers: BTreeMap<u8, E>,
    memory: E,
}

impl State {
    fn register(&self, field: u8) -> Result<E> {
        self.registers
            .get(&field)
            .cloned()
            .ok_or_else(|| inconsistent("unknown GPR value"))
    }
    fn base(&self, operand: &O) -> Result<E> {
        match operand {
            O::Special(SpecialReg::SP) => Ok(self.sp.clone()),
            O::PReg(reg) if reg.encoding() == 29 => self.register(29),
            _ => Err(inconsistent("unknown frame base")),
        }
    }
    fn adjust(&mut self, inst: &MachInst, word: &[u8]) -> Result<()> {
        let [dst, src, O::Imm(_)] = inst.operands.as_slice() else {
            return Err(inconsistent("frame adjustment operands"));
        };
        // Keep the frame owner's SP/FP-only profile. The shared binding owns
        // exact fields and the existing decoded semantics owns the value;
        // neither supplies a body premise, memory permission or proof credit.
        self.base(src)?;
        let word = u32::from_le_bytes(
            word.try_into()
                .map_err(|_| inconsistent("frame adjustment word length"))?,
        );
        let bound = crate::aarch64_add_sub_immediate::bind_add_sub_immediate_word(inst, word)
            .map_err(|e| inconsistent(e.to_string()))?;
        if bound.width() != 64 || !matches!(inst.opcode, Op::AddRI | Op::SubRI) {
            return Err(inconsistent("frame adjustment opcode or width"));
        }
        let effect = bound
            .effect(&self.sp, &self.registers)
            .map_err(|e| inconsistent(e.to_string()))?;
        let next = effect.value;
        match dst {
            O::Special(SpecialReg::SP) => self.sp = next,
            O::PReg(reg) if reg.encoding() == 29 => {
                self.registers.insert(29, next);
            }
            _ => return Err(inconsistent("frame adjustment destination")),
        }
        Ok(())
    }
    fn pair(&mut self, inst: &MachInst, word: &[u8]) -> Result<()> {
        // Existing binding still owns exact MachIR/word agreement; the shared
        // actual-word pair step owns simultaneous loads/stores/writeback.
        let pair = check_pair_encoding(inst, word).map_err(|e| inconsistent(e.to_string()))?;
        if pair.format() != PairMemoryFormat::X64 {
            return Err(ConditionalFrameRefusal::SavedRegisterDomain);
        }
        if !matches!(
            pair.base(),
            crate::aarch64_pair_memory::PairMemoryBase::Sp
                | crate::aarch64_pair_memory::PairMemoryBase::Register(29)
        ) {
            return Err(inconsistent("pair base"));
        }
        if matches!(
            pair.base(),
            crate::aarch64_pair_memory::PairMemoryBase::Register(29)
        ) && pair.mode() != crate::aarch64_pair_memory::PairMemoryMode::SignedOffset
            && pair.byte_offset() != 0
        {
            return Err(inconsistent("FP writeback"));
        }
        let effect = crate::aarch64_pair_memory::gpr64_pair_effect(
            pair.word(),
            &self.sp,
            &self.registers,
            &self.memory,
        )
        .map_err(|e| inconsistent(e.to_string()))?;
        for (register, value) in effect.registers {
            self.registers.insert(register, value);
        }
        if let Some(sp) = effect.sp {
            self.sp = sp;
        }
        self.memory = effect.memory;
        Ok(())
    }
}

fn relative(base: &E, offset: i64) -> E {
    base.clone().bvadd(E::bv_const(offset as u64, 64))
}

fn step(geometry: &CheckedStaticFrameEnvelopes<'_>, state: &mut State, id: InstId) -> Result<()> {
    let inst = geometry
        .machine()
        .insts
        .get(id.0 as usize)
        .ok_or_else(|| inconsistent("missing instruction"))?;
    let offset = geometry
        .byte_offset(id)
        .ok_or_else(|| inconsistent("missing emitted coordinate"))?;
    let word = geometry
        .image()
        .get(offset..offset + 4)
        .ok_or_else(|| inconsistent("missing emitted word"))?;
    match inst.opcode {
        Op::AddRI | Op::SubRI => state.adjust(inst, word),
        Op::StpPreIndex | Op::StpRI | Op::LdpRI | Op::LdpPostIndex => state.pair(inst, word),
        Op::Ret => Ok(()), // Endpoint only, no control-flow or return claim.
        _ => Err(inconsistent("non-envelope opcode")),
    }
}

/// Construct conditional semantic claims for all checked GPR64 exits. The
/// actual prologue executes once over arbitrary entry memory. Each epilogue
/// executes over a DIFFERENT arbitrary resume memory/state; no body or call
/// fact is invented and a proof of an exit cannot discharge its own premises.
pub fn conditional_static_frame_envelopes<'g, 'a>(
    geometry: &'g CheckedStaticFrameEnvelopes<'a>,
) -> Result<ConditionalStaticFrame<'g, 'a>> {
    conditional_frame(geometry, None)
}

/// Compose the checked body footprint into the existing frame semantics.
/// Stack permissions, privacy, lifetime, source results, termination and actual
/// installation remain outside this query. In particular this does not grant
/// `SourceBoundReplay` or instruction credit. The stronger nonwrapping extent
/// includes the independently checked callee's own private stack requirement.
pub fn conditional_static_frame_with_body<'b, 'g, 'c, 'a>(
    body: &'b CheckedFrameBody<'g, 'c, 'a>,
) -> Result<ComposedStaticFrame<'b, 'g, 'c, 'a>> {
    Ok(ComposedStaticFrame {
        body,
        frame: conditional_frame(body.geometry, Some(body))?,
    })
}

/// Retains the original checked body, every callee endpoint, and the immutable
/// linked image for as long as the composed query is owned.
pub struct ComposedStaticFrame<'b, 'g, 'c, 'a> {
    body: &'b CheckedFrameBody<'g, 'c, 'a>,
    frame: ConditionalStaticFrame<'g, 'a>,
}

impl<'b, 'g, 'c, 'a> ComposedStaticFrame<'b, 'g, 'c, 'a> {
    pub fn body(&self) -> &'b CheckedFrameBody<'g, 'c, 'a> {
        self.body
    }
    pub fn exits(&self) -> &[ConditionalStaticFrameExit] {
        self.frame.exits()
    }
    pub fn post_save_memory(&self) -> &E {
        self.frame.post_save_memory()
    }
}

fn conditional_frame<'g, 'a>(
    geometry: &'g CheckedStaticFrameEnvelopes<'a>,
    body: Option<&CheckedFrameBody<'g, '_, 'a>>,
) -> Result<ConditionalStaticFrame<'g, 'a>> {
    if geometry.saved_slots().is_empty()
        || geometry
            .saved_slots()
            .iter()
            .any(|slot| !matches!(slot.register, SavedFrameRegister::X(_)))
    {
        return Err(ConditionalFrameRefusal::SavedRegisterDomain);
    }
    let alignment = geometry.required_entry_sp_alignment();
    let entry_sp = E::var("frame_entry_sp", 64);
    let mut inputs = vec![("frame_entry_sp".to_owned(), 64)];
    let mut entry_registers = BTreeMap::new();
    for slot in geometry.saved_slots() {
        let SavedFrameRegister::X(field) = slot.register else {
            unreachable!()
        };
        let name = format!("frame_entry_x{field}");
        inputs.push((name.clone(), 64));
        entry_registers.insert(field, E::var(name, 64));
    }
    let mut saved = State {
        sp: entry_sp.clone(),
        registers: entry_registers.clone(),
        memory: E::uf("frame_entry_memory", Vec::new(), memory_sort()),
    };
    for &id in &geometry.candidates().prologue {
        step(geometry, &mut saved, id)?;
    }
    // Overapproximate each actual, checked leaf's private writes below the
    // unchanged call SP. Each byte is fresh; no original byte is guessed. The
    // callee checker establishes that there are no other memory effects.
    let body_memory = body.map(|body| {
        let mut memory = saved.memory.clone();
        for (call_index, call) in body.calls.iter().enumerate() {
            for byte in 0..call.callee.private_stack_bytes() {
                let name = format!("frame_body_call_{call_index}_private_{byte}");
                inputs.push((name.clone(), 8));
                let address = relative(&saved.sp, -(byte as i64) - 1);
                memory = encode_store_le(&memory, &address, &E::var(name, 8), 1);
            }
        }
        memory
    });
    let mut exits = Vec::new();
    for (index, (exit, epilogue)) in geometry
        .conditional_exits()
        .iter()
        .zip(&geometry.candidates().epilogues)
        .enumerate()
    {
        let prefix = format!("frame_exit_{index}");
        let sp_name = format!("{prefix}_resume_sp");
        let fp_name = format!("{prefix}_resume_fp");
        let resume_memory = body_memory
            .clone()
            .unwrap_or_else(|| E::uf(format!("{prefix}_resume_memory"), Vec::new(), memory_sort()));
        let mut exit_inputs = inputs.clone();
        if body.is_none() {
            exit_inputs.push((sp_name.clone(), 64));
        }
        let resume_sp = if body.is_some() {
            saved.sp.clone()
        } else {
            E::var(sp_name, 64)
        };
        let required_bytes = body.map_or(geometry.layout_claim().total_bytes, |b| {
            b.required_entry_bytes
        });
        let mut preconditions = vec![
            entry_sp
                .clone()
                .bvuge(E::bv_const(u64::from(required_bytes), 64)),
            entry_sp
                .clone()
                .bvand(E::bv_const(u64::from(alignment - 1), 64))
                .eq_expr(E::bv_const(0, 64)),
        ];
        let mut premises = vec![
            ConditionalFramePremise::EntrySpNonwrapping {
                frame_bytes: required_bytes,
            },
            ConditionalFramePremise::EntrySpAlignment { bytes: alignment },
        ];
        if body.is_none() {
            preconditions.push(
                resume_sp
                    .clone()
                    .eq_expr(relative(&entry_sp, exit.required_sp)),
            );
            premises.push(ConditionalFramePremise::ResumeSp {
                relative_offset: exit.required_sp,
            });
        }
        let mut registers = BTreeMap::new();
        if let Some(offset) = exit.required_fp {
            let fp = if body.is_some() {
                saved.register(29)?
            } else {
                exit_inputs.push((fp_name.clone(), 64));
                let fp = E::var(fp_name, 64);
                preconditions.push(fp.clone().eq_expr(relative(&entry_sp, offset)));
                premises.push(ConditionalFramePremise::ResumeFp {
                    relative_offset: offset,
                });
                fp
            };
            registers.insert(29, fp);
        }
        for &slot in geometry.saved_slots().iter().filter(|_| body.is_none()) {
            let address = relative(&entry_sp, slot.region.start);
            preconditions.push(
                encode_load_le(&resume_memory, &address, 8).eq_expr(encode_load_le(
                    &saved.memory,
                    &address,
                    8,
                )),
            );
            premises.push(ConditionalFramePremise::SavedLane(slot));
        }
        let mut state = State {
            sp: resume_sp,
            registers,
            memory: resume_memory.clone(),
        };
        for &id in epilogue {
            step(geometry, &mut state, id)?;
        }
        let mut complete = state.sp.clone().eq_expr(entry_sp.clone());
        for (&field, entry) in &entry_registers {
            complete = complete.and_expr(state.register(field)?.eq_expr(entry.clone()));
        }
        exits.push(ConditionalStaticFrameExit {
            return_instruction: exit.return_instruction,
            resume_memory,
            premises,
            obligation: ProofObligation {
                name: format!(
                    "Conditional checked static GPR64 frame exit {index} at {:?}: {}",
                    exit.return_instruction,
                    if body.is_some() {
                        "checked body footprint composed; ABI permissions pending"
                    } else {
                        "body premises pending"
                    }
                ),
                trust_ir_expr: E::bool_const(true),
                aarch64_expr: complete,
                inputs: exit_inputs,
                preconditions,
                fp_inputs: Vec::new(),
                category: Some(TransvalCheckKind::RegisterAllocation),
                machine_side_provenance: MachineSideProvenance::StaticDb,
            },
        });
    }
    Ok(ConditionalStaticFrame {
        geometry,
        post_save_memory: saved.memory,
        exits,
    })
}

#[cfg(test)]
#[path = "aarch64_conditional_frame_tests.rs"]
mod tests;
