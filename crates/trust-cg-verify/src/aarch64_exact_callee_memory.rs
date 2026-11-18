// Copyright 2026 Andrew Yates | Apache-2.0

//! Exact normal-return memory effects of the SAME independently checked leaf
//! callees, in actual BL order. This is a restricted consumer of the existing
//! byte observers, not another decoder or permission/source-proof issuer.
//! The inherited untagged Normal-memory/GCS-disabled BL/RET model is an
//! unsupplied condition, not a fact established by these symbolic effects.

use super::*;
use crate::aarch64_control_decode::decode_a64_control_word;
use std::collections::BTreeMap;

#[derive(Debug)]
pub(super) struct CallMemory {
    pub instruction: InstId,
    pub entry_memory: E,
    pub entry_sp: E,
    pub return_target: E,
    pub exit_memory: E,
}

pub(super) fn observe(
    body: &CheckedFrameBody<'_, '_, '_>,
    saved: &State,
    image_base: &'static str,
    inputs: &mut Vec<(String, u32)>,
) -> Result<(E, Vec<CallMemory>)> {
    let geometry = body.geometry;
    if geometry.candidates().epilogues.len() != 1 {
        return Err(inconsistent(
            "exact call memory requires one straight-line exit",
        ));
    }
    let start = geometry
        .candidates()
        .prologue
        .last()
        .and_then(|id| geometry.byte_offset(*id))
        .and_then(|offset| offset.checked_add(4))
        .ok_or_else(|| inconsistent("exact call memory needs a complete prologue"))?;
    let end = geometry.candidates().epilogues[0]
        .first()
        .and_then(|id| geometry.byte_offset(*id))
        .ok_or_else(|| inconsistent("exact call memory needs a complete epilogue"))?;
    let words = end
        .checked_sub(start)
        .filter(|bytes| bytes.is_multiple_of(4))
        .map(|bytes| bytes / 4)
        .filter(|words| *words <= 256)
        .ok_or_else(|| inconsistent("exact call memory exceeds its 256-word linear profile"))?;
    let mut ordered = BTreeMap::new();
    for interval in geometry.unresolved_body() {
        for &id in &interval.instructions {
            let offset = geometry
                .byte_offset(id)
                .ok_or_else(|| inconsistent("exact body word lacks a byte coordinate"))?;
            if offset < start || offset >= end || ordered.len() >= words {
                return Err(inconsistent(
                    "exact call memory requires a bounded contiguous body",
                ));
            }
            if ordered.insert(offset, id).is_some() {
                return Err(inconsistent("exact body reuses a byte coordinate"));
            }
        }
    }
    if ordered.len() != words
        || (start..end)
            .step_by(4)
            .any(|offset| !ordered.contains_key(&offset))
    {
        return Err(inconsistent("exact call memory requires a contiguous body"));
    }
    // Actual code placement remains an explicit symbolic input, not a fact
    // obtained from an address-free image or a name. BL writes PC+4 modulo64.
    inputs.push((image_base.into(), 64));
    let base = E::var(image_base, 64);
    let mut memory = saved.memory.clone();
    let mut calls = Vec::new();
    for (offset, id) in ordered {
        let word = u32::from_le_bytes(geometry.image()[offset..offset + 4].try_into().unwrap());
        if word & 0xfc00_0000 != 0x9400_0000 {
            if decode_a64_control_word(word).is_some() {
                return Err(inconsistent(
                    "exact call memory does not infer branch order",
                ));
            }
            // The existing CheckedFrameBody already independently bound this
            // word and refused all non-call memory/SP/FP/LR effects.
            continue;
        }
        let call = body
            .calls
            .iter()
            .find(|call| call.instruction == id)
            .ok_or_else(|| inconsistent("exact BL lacks its original checked callee"))?;
        let return_offset = body
            .caller_offset
            .checked_add(offset)
            .and_then(|offset| offset.checked_add(4))
            .and_then(|offset| u64::try_from(offset).ok())
            .ok_or_else(|| inconsistent("exact BL return coordinate overflow"))?;
        let return_target = base.clone().bvadd(E::bv_const(return_offset, 64));
        let entry_memory = memory.clone();
        match call.callee.normal_return_memory_effect() {
            crate::aarch64_affine_lowering::NormalReturnMemoryEffect::Unchanged => (),
            // The SAME complete affine byte observer admits only this actual
            // STP X29,X30,[SP,#-16]! / MOV X29,SP / LDP ... / RET envelope.
            // Its body cannot touch SP/frame memory or introduce another store.
            crate::aarch64_affine_lowering::NormalReturnMemoryEffect::StandardFpLrRecord => {
                let address = relative(&saved.sp, -16);
                memory = encode_store_le(&memory, &address, &saved.register(29)?, 8);
                memory = encode_store_le(&memory, &relative(&address, 8), &return_target, 8);
            }
        }
        calls.push(CallMemory {
            instruction: id,
            entry_memory,
            entry_sp: saved.sp.clone(),
            return_target,
            exit_memory: memory.clone(),
        });
    }
    if calls.len() != body.calls.len() {
        return Err(inconsistent(
            "exact memory omitted a checked call occurrence",
        ));
    }
    Ok((memory, calls))
}
