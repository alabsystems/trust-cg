// Copyright 2026 Andrew Yates | Apache-2.0

//! An aggregate, source-bound actual-word trace for the bounded defined call.
//! The callee is EXECUTED word by word, including BL's link write and the
//! callee's actual RET. No callee return/result/ABI-summary premise is used.
//! Construction alone grants nothing. The public replayed owner is minted
//! only after the existing request-bound independent replay accepts this exact
//! conjunction of every checked part of the retained complete statement. No
//! monolithic-query success is implied. It grants no source/Core license,
//! machine report or installation.
//! Actual executable bytes must be immutable at the modelled placement, and the
//! complete private stack window must have live writable storage. Arithmetic
//! preconditions additionally separate that window from the linked image.

use std::collections::BTreeMap;

use crate::aarch64_affine_lowering::CheckedAarch64DefinedCallBytes;
use crate::aarch64_instruction_word_proofs::{DecodedWord, LinkedWordState, decode_word};
use crate::function_request::FunctionVerificationRequest;
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::memory_sort;
use crate::smt::SmtExpr as E;

/// Pending actual-word mathematics, bound to immutable original source/LIR,
/// captured callee and linked bytes. Only its private replay view is eligible
/// for the sealed live route; construction is not a proof verdict.
#[derive(Debug)]
pub struct DefinedCallTrace<'o, 'c, 'a> {
    bytes: &'o CheckedAarch64DefinedCallBytes<'c, 'a>,
    obligation: ProofObligation,
    parts: Vec<ProofObligation>,
    executed_words: usize,
}

/// The aggregate was independently replayed under this original request.
/// This owner does not manufacture per-row Formal reports or install/storage
/// permissions. Retain it together with its byte owner and source/Core license.
#[derive(Debug)]
pub struct ReplayedDefinedCallTrace<'t, 'o, 'c, 'a> {
    trace: &'t DefinedCallTrace<'o, 'c, 'a>,
    request: &'t FunctionVerificationRequest,
    checked_parts: usize,
    part_provenance: Vec<Option<String>>,
}

impl ReplayedDefinedCallTrace<'_, '_, '_, '_> {
    pub fn trace(&self) -> &DefinedCallTrace<'_, '_, '_> {
        self.trace
    }
    pub fn matches_request(&self, request: &FunctionVerificationRequest) -> bool {
        std::ptr::eq(self.request, request)
    }
    /// Independently replayed parts, whose exact conjunction is the retained
    /// whole statement. This is not a per-row certificate count.
    pub fn checked_parts(&self) -> usize {
        self.checked_parts
    }
    /// Existing route's constructive-producer attribution, when present.
    /// An absent label does not claim a fresh AY process rather than reuse.
    pub fn part_provenance(&self) -> &[Option<String>] {
        &self.part_provenance
    }
}

/// Private replay capability. A caller cannot supply an arbitrary obligation,
/// replace the trace's endpoints or convert a byte comparison into this type.
pub(crate) struct DefinedCallTraceReplay<'t>(&'t ProofObligation);
impl DefinedCallTraceReplay<'_> {
    pub(crate) fn obligation(&self) -> &ProofObligation {
        self.0
    }
}

fn word(code: &[u8], offset: usize) -> Result<u32, String> {
    let bytes: [u8; 4] = code
        .get(offset..offset + 4)
        .ok_or("incomplete trace word")?
        .try_into()
        .map_err(|_| "incomplete trace word")?;
    Ok(u32::from_le_bytes(bytes))
}

fn trace_obligation(
    caller: &[u8],
    caller_offset: usize,
    callee: &[u8],
    callee_offset: usize,
    image_len: usize,
    stack_bytes: usize,
    source_result: u64,
) -> Result<(ProofObligation, usize), String> {
    if caller.is_empty()
        || callee.is_empty()
        || !caller.len().is_multiple_of(4)
        || !callee.len().is_multiple_of(4)
        || caller
            .len()
            .checked_add(callee.len())
            .is_none_or(|n| n > 256)
    {
        return Err("bounded trace requires at most64 complete linked words".into());
    }
    let base = E::var("trace_image_base", 64);
    let sp = E::var("trace_entry_sp", 64);
    let probe = E::var("trace_memory_probe", 64);
    let memory = E::uf("trace_entry_memory", Vec::new(), memory_sort());
    let registers: BTreeMap<_, _> = (0..31)
        .map(|n| (n, E::var(format!("trace_x{n}"), 64)))
        .collect();
    let mut state = LinkedWordState {
        registers: registers.clone(),
        sp: sp.clone(),
        pc: base.clone().bvadd(E::bv_const(caller_offset as u64, 64)),
        nzcv: E::var("trace_nzcv", 4),
        memory: memory.clone(),
    };
    let floor = sp.clone().bvsub(E::bv_const(stack_bytes as u64, 64));
    let image_end = base.clone().bvadd(E::bv_const(
        u64::try_from(image_len).map_err(|_| "image extent overflow")?,
        64,
    ));
    let image_stack_disjoint = image_end
        .bvule(floor.clone())
        .or_expr(base.clone().bvuge(sp.clone()));
    let mut goal = E::bool_const(true);
    let mut executed = 0usize;
    let mut step =
        |state: &mut LinkedWordState, offset: usize, instruction: u32| -> Result<(), String> {
            // Fetch correctness is a CONCLUSION at every step, never a premise.
            goal = goal.clone().and_expr(
                state
                    .pc
                    .clone()
                    .eq_expr(base.clone().bvadd(E::bv_const(offset as u64, 64))),
            );
            for address in state.step(instruction)? {
                goal = goal
                    .clone()
                    .and_expr(address.clone().bvuge(floor.clone()))
                    .and_expr(address.bvule(sp.clone().bvsub(E::bv_const(8, 64))));
            }
            executed += 1;
            Ok(())
        };
    let mut calls = 0;
    for offset in (0..caller.len()).step_by(4) {
        let instruction = word(caller, offset)?;
        step(
            &mut state,
            caller_offset
                .checked_add(offset)
                .ok_or("trace offset overflow")?,
            instruction,
        )?;
        if matches!(
            decode_word(instruction),
            Some(DecodedWord::BranchImm { op: 1, .. })
        ) {
            calls += 1;
            if calls != 1 {
                return Err("trace has more than one defined call".into());
            }
            for leaf_offset in (0..callee.len()).step_by(4) {
                let instruction = word(callee, leaf_offset)?;
                if matches!(
                    decode_word(instruction),
                    Some(DecodedWord::BranchImm { .. })
                ) {
                    return Err("callee call/control is outside finite leaf trace".into());
                }
                step(
                    &mut state,
                    callee_offset
                        .checked_add(leaf_offset)
                        .ok_or("trace offset overflow")?,
                    instruction,
                )?;
            }
        }
    }
    if calls != 1 {
        return Err("trace lacks defined call".into());
    }
    goal = goal
        .and_expr(
            state.registers[&0]
                .clone()
                .eq_expr(E::bv_const(source_result, 64)),
        )
        .and_expr(state.sp.eq_expr(sp.clone()))
        .and_expr(state.pc.eq_expr(registers[&30].clone()));
    for n in 18..=30 {
        goal = goal.and_expr(state.registers[&n].clone().eq_expr(registers[&n].clone()));
    }
    // Universal arbitrary byte probe outside the complete private stack range.
    // Store chains preserve all other bytes without any memory equality axiom.
    let outside = probe
        .clone()
        .bvult(floor)
        .or_expr(probe.clone().bvuge(sp.clone()));
    goal = goal.and_expr(
        outside
            .not_expr()
            .or_expr(E::select(state.memory, probe.clone()).eq_expr(E::select(memory, probe))),
    );
    let mut inputs = vec![
        ("trace_image_base".into(), 64),
        ("trace_entry_sp".into(), 64),
        ("trace_memory_probe".into(), 64),
        ("trace_nzcv".into(), 4),
    ];
    inputs.extend((0..31).map(|n| (format!("trace_x{n}"), 64)));
    Ok((
        ProofObligation {
            name: "Source-bound actual linked AArch64 defined CALL/RET finite trace".into(),
            trust_ir_expr: E::bool_const(true),
            aarch64_expr: goal,
            inputs,
            preconditions: vec![
                image_stack_disjoint,
                base.clone()
                    .bvand(E::bv_const(3, 64))
                    .eq_expr(E::bv_const(0, 64)),
                sp.clone()
                    .bvand(E::bv_const(15, 64))
                    .eq_expr(E::bv_const(0, 64)),
                sp.bvuge(E::bv_const(stack_bytes as u64, 64)),
                base.bvule(E::bv_const(
                    u64::MAX - u64::try_from(image_len).map_err(|_| "image extent overflow")?,
                    64,
                )),
            ],
            fp_inputs: Vec::new(),
            category: Some(TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::StaticDb,
        },
        executed,
    ))
}

impl<'o, 'c, 'a> DefinedCallTrace<'o, 'c, 'a> {
    /// Reconstruct actual-word mathematics; no summary is substituted at BL.
    pub fn build(bytes: &'o CheckedAarch64DefinedCallBytes<'c, 'a>) -> Result<Self, String> {
        let (obligation, executed_words) = trace_obligation(
            bytes.code(),
            bytes.caller_offset(),
            bytes.callee().checked_bytes().code(),
            bytes.callee_offset(),
            bytes.linked_image().len(),
            bytes.required_private_stack_bytes(),
            bytes.result_u64(),
        )?;
        let parts = crate::conjunctive_obligations::split_parts(&obligation, &obligation.name)?;
        crate::conjunctive_obligations::check_parts(
            &obligation,
            &parts,
            &obligation.name,
            &["trace_entry_memory"],
        )?;
        Ok(Self {
            bytes,
            obligation,
            parts,
            executed_words,
        })
    }
    pub fn bytes(&self) -> &'o CheckedAarch64DefinedCallBytes<'c, 'a> {
        self.bytes
    }
    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }
    pub fn executed_words(&self) -> usize {
        self.executed_words
    }
    /// Complete theorem in bounded conjunctive parts, with original hypotheses.
    pub fn parts(&self) -> &[ProofObligation] {
        &self.parts
    }
    pub fn check_parts(&self) -> Result<(), String> {
        crate::conjunctive_obligations::check_parts(
            &self.obligation,
            &self.parts,
            &self.obligation.name,
            &["trace_entry_memory"],
        )
    }

    /// Diagnostic original checker problem and optional producer print view.
    /// Uses the SAME raw renderer/configuration as replay, grants no verdict,
    /// and launches no solver. Neither text can manufacture this owner.
    pub fn replay_queries(
        &self,
        request: &FunctionVerificationRequest,
    ) -> Result<(String, Option<String>), String> {
        if !self.bytes.callee().matches_request_capture(request) {
            return Err("diagnostic differs from original captured request".into());
        }
        Ok(request.with_policy(|| {
            crate::ay_bridge::source_bound_query_scripts(
                &self.obligation,
                &crate::verdict_db::live_source_bound_config(),
            )
        }))
    }

    /// Only the unchanged captured request can mint a replayed aggregate owner.
    /// The ordinary AY/Clean raw source-bound route owns the actual verdict;
    /// timeout, unsupported query or an unbound result refuses this capability.
    pub fn replay<'t>(
        &'t self,
        request: &'t FunctionVerificationRequest,
    ) -> Result<ReplayedDefinedCallTrace<'t, 'o, 'c, 'a>, String> {
        if !self.bytes.callee().matches_request_capture(request) {
            return Err("aggregate differs from original captured request".into());
        }
        self.check_parts()?;
        // Same complete-goal inventory contract as the existing scalar-cell
        // caller. Every individual result must be independently accepted and
        // bound to this original request; unknown/refuted/missing parts refuse.
        let mut part_provenance = Vec::with_capacity(self.parts.len());
        for (index, part) in self.parts.iter().enumerate() {
            let owner = DefinedCallTraceReplay(part);
            let (verdict, bound, why) = request.with_policy(|| {
                crate::verdict_db::live_source_bound_replay_explained(&owner, request)
            });
            if !bound || !matches!(verdict, Some(crate::verify::VerificationResult::Valid)) {
                return Err(format!(
                    "part {}/{}: {}",
                    index + 1,
                    self.parts.len(),
                    why.unwrap_or_else(|| {
                        "independent replay did not prove the bound original part".into()
                    })
                ));
            }
            part_provenance.push(why);
        }
        Ok(ReplayedDefinedCallTrace {
            trace: self,
            request,
            checked_parts: self.parts.len(),
            part_provenance,
        })
    }
}

#[cfg(test)]
#[path = "source_bound_defined_call_tests.rs"]
mod tests;
