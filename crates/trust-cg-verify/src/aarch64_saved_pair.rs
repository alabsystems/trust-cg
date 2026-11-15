// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Conditional saved-slot reasoning for one checked AArch64 GPR64 pair.
//!
//! This proof-only seam deliberately does not construct `SourceBoundFrame`,
//! register opcode coverage, or grant machine publication authority. The two
//! descriptors bind exact words to allocated operands, not to a whole function,
//! source operation, emitted extent, or relocation-free position.
//!
//! A pre-index save allocates F >= 16 bytes below SP; a post-index restore reads
//! its first two words. The intervening body is NOT interpreted. An arbitrary
//! resume memory and SP must satisfy explicit saved-word-preservation and SP
//! premises. A consumer must independently establish these through the actual
//! body, including calls and local stack adjustments. No outside-memory or
//! other-register preservation is concluded. Numeric bounds/alignment do not
//! prove allocation ownership, writable/readable memory, lifetime or absence
//! of architectural faults; this is conditional byte-memory reasoning only.
//!
//! Construction is not discharge. In particular, different restore order or
//! writeback remains a constructible, potentially false obligation, so an
//! independent solver can refute semantic errors rather than hide them as
//! unsupported shapes.

use crate::aarch64_pair_memory::{
    CheckedPairEncoding, PairMemoryBase, PairMemoryFormat, PairMemoryMode,
};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
use crate::smt::SmtExpr;
use trust_cg_ir::MachInst;

/// Outside this conditional theorem's domain, not an instruction verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub(crate) enum SavedPairRefusal {
    #[error("saved pair requires an X64 pre-index store on SP")]
    SaveShape,
    #[error("saved pair requires an X64 post-index load on SP")]
    RestoreShape,
    #[error("saved pair {0} has noncanonical flags or implicit effects")]
    HiddenEffects(&'static str),
    #[error("saved pair allocation must be a negative multiple of 16, at least 16 bytes")]
    FrameSize,
    #[error("saved pair requires the same two distinct GPR destinations other than XZR")]
    Registers,
}

/// Exact immutable descriptors and their conditional, still-undischarged query.
/// No split/rebind or external-verdict attachment mints checked standing.
#[derive(Debug)]
pub(crate) struct ConditionalSavedPair<'a> {
    save: CheckedPairEncoding<'a>,
    restore: CheckedPairEncoding<'a>,
    obligation: ProofObligation,
}

impl<'a> ConditionalSavedPair<'a> {
    pub(crate) fn save(&self) -> &CheckedPairEncoding<'a> {
        &self.save
    }

    pub(crate) fn restore(&self) -> &CheckedPairEncoding<'a> {
        &self.restore
    }

    pub(crate) fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
}

fn canonical_effects(instruction: &MachInst) -> bool {
    instruction.flags == MachInst::new(instruction.opcode, Vec::new()).flags
        && instruction.implicit_defs.is_empty()
        && instruction.implicit_uses.is_empty()
}

/// Build, but do not discharge, one conditional save/resume/restore theorem.
pub(crate) fn conditional_saved_pair<'a>(
    save: CheckedPairEncoding<'a>,
    restore: CheckedPairEncoding<'a>,
) -> Result<ConditionalSavedPair<'a>, SavedPairRefusal> {
    if save.format() != PairMemoryFormat::X64
        || save.base() != PairMemoryBase::Sp
        || save.mode() != PairMemoryMode::PreIndex
        || save.is_load()
    {
        return Err(SavedPairRefusal::SaveShape);
    }
    if restore.format() != PairMemoryFormat::X64
        || restore.base() != PairMemoryBase::Sp
        || restore.mode() != PairMemoryMode::PostIndex
        || !restore.is_load()
    {
        return Err(SavedPairRefusal::RestoreShape);
    }
    for (role, instruction) in [
        ("save", save.instruction()),
        ("restore", restore.instruction()),
    ] {
        if !canonical_effects(instruction) {
            return Err(SavedPairRefusal::HiddenEffects(role));
        }
    }
    let offset = save.byte_offset();
    if offset > -16 || offset % 16 != 0 {
        return Err(SavedPairRefusal::FrameSize);
    }
    // The descriptor already checked the signed scaled imm7; negation cannot
    // overflow and the allocation lies within its finite X64 range.
    let frame_bytes = (-offset) as u64;
    let saved = save.transfer_fields();
    let loaded = restore.transfer_fields();
    if saved[0] == saved[1]
        || saved.contains(&31)
        || loaded.contains(&31)
        || !(loaded == saved || loaded == [saved[1], saved[0]])
    {
        return Err(SavedPairRefusal::Registers);
    }

    let entry_sp = SmtExpr::var("pair_entry_sp", 64);
    let resume_sp = SmtExpr::var("pair_resume_sp", 64);
    let register_names = saved.map(|field| format!("pair_entry_x{field}"));
    let entry_values = register_names.each_ref().map(|name| SmtExpr::var(name, 64));
    let frame = entry_sp.clone().bvsub(SmtExpr::bv_const(frame_bytes, 64));
    let second = frame.clone().bvadd(SmtExpr::bv_const(8, 64));

    // Zero-argument array-sorted functions are arbitrary memories. Do not use
    // symbolic_memory(): it models a constant-default array instead.
    let entry_memory = SmtExpr::uf("pair_entry_memory", Vec::new(), memory_sort());
    let resume_memory = SmtExpr::uf("pair_resume_memory", Vec::new(), memory_sort());
    let saved_first = encode_store_le(&entry_memory, &frame, &entry_values[0], 8);
    let saved_memory = encode_store_le(&saved_first, &second, &entry_values[1], 8);
    let resume_second = resume_sp.clone().bvadd(SmtExpr::bv_const(8, 64));
    let loaded_values = [
        encode_load_le(&resume_memory, &resume_sp, 8),
        encode_load_le(&resume_memory, &resume_second, 8),
    ];
    // Preserve architectural register identity, not just transfer position.
    // Reversing a legal LDP's destinations must change the claim's truth.
    let restored = saved.map(|field| {
        if loaded[0] == field {
            loaded_values[0].clone()
        } else {
            loaded_values[1].clone()
        }
    });
    let restored_sp = resume_sp
        .clone()
        .bvadd(SmtExpr::bv_const(restore.byte_offset() as u64, 64));
    let complete = restored[0]
        .clone()
        .eq_expr(entry_values[0].clone())
        .and_expr(restored[1].clone().eq_expr(entry_values[1].clone()))
        .and_expr(restored_sp.eq_expr(entry_sp.clone()));

    let obligation = ProofObligation {
        name: format!(
            "Conditional checked GPR64 saved pair: save={:08x}, restore={:08x}; body premises pending",
            save.word(),
            restore.word(),
        ),
        trust_ir_expr: SmtExpr::bool_const(true),
        aarch64_expr: complete,
        inputs: ["pair_entry_sp".to_owned(), "pair_resume_sp".to_owned()]
            .into_iter()
            .chain(register_names)
            .map(|name| (name, 64))
            .collect(),
        preconditions: vec![
            entry_sp.clone().bvuge(SmtExpr::bv_const(frame_bytes, 64)),
            entry_sp
                .bvand(SmtExpr::bv_const(15, 64))
                .eq_expr(SmtExpr::bv_const(0, 64)),
            resume_sp.eq_expr(frame.clone()),
            encode_load_le(&resume_memory, &frame, 8).eq_expr(encode_load_le(
                &saved_memory,
                &frame,
                8,
            )),
            encode_load_le(&resume_memory, &second, 8).eq_expr(encode_load_le(
                &saved_memory,
                &second,
                8,
            )),
        ],
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::RegisterAllocation),
        // Do not enter the reconstructed-ALU credit path. The owned checked
        // descriptors record exact word/operand agreement, but no source or
        // function-envelope correspondence has been established here.
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    Ok(ConditionalSavedPair {
        save,
        restore,
        obligation,
    })
}

#[cfg(test)]
#[path = "aarch64_saved_pair_tests.rs"]
mod tests;
