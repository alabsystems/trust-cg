// trust-cg-opt - Constant Folding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Constant folding pass for machine-level IR.
//!
//! Evaluates instructions whose operands are all known constants at
//! compile time and replaces them with immediate moves.
//!
//! # Supported Operations
//!
//! | Opcode  | Folding |
//! |---------|---------|
//! | AddRI   | dst = src + imm (when src is known constant) |
//! | AddRIShift12 | dst = src + (imm << 12) (when src is known constant) |
//! | SubRI   | dst = src - imm (when src is known constant) |
//! | AddRR   | dst = lhs + rhs (when both are known constants) |
//! | SubRR   | dst = lhs - rhs (when both are known constants) |
//! | MulRR   | dst = lhs * rhs (when both are known constants) |
//! | AndRR   | dst = lhs & rhs (when both are known constants) |
//! | OrrRR   | dst = lhs | rhs (when both are known constants) |
//! | EorRR   | dst = lhs ^ rhs (when both are known constants) |
//! | LslRI   | dst = src << imm (when src is known constant) |
//! | LsrRI   | dst = src >> imm (when src is known constant, logical) |
//! | AsrRI   | dst = src >> imm (when src is known constant, arithmetic) |
//! | Neg     | dst = -src (when src is known constant) |
//!
//! # Implementation
//!
//! Single forward walk over each block's `insts`, with constants tracked only
//! within the current block. For each instruction we:
//!
//! 1. **Track constant materialization** — simulate MOVZ/MOVN/MOVK bit-chunk
//!    updates so the tracker reflects the full 64-bit value of constants
//!    built by the standard AArch64 MOVZ+MOVK chain.
//! 2. **Try to fold** — if the instruction's source operands are all known
//!    constants, compute the result and replace the instruction with
//!    `MovI dst, #result`, updating the tracker with the new value.
//! 3. **Invalidate on unfolded redefinition** — any other instruction that
//!    produces a value into a vreg that was previously tracked must drop
//!    the stale entry, since later MOVK-style writes would layer on top.
//!
//! Division is NOT folded to avoid division-by-zero at compile time.
//!
//! # Why a single pass with explicit MOVK handling
//!
//! ISel materializes 64-bit constants like `0x165667919E3779F9` as:
//!
//! ```text
//! v100 = MOVZ     #0x79F9
//! v100 = MOVK v100, #0x9E37, lsl #16
//! v100 = MOVK v100, #0x6791, lsl #32
//! v100 = MOVK v100, #0x1656, lsl #48
//! ```
//!
//! MOVK reads+writes the same vreg (the standard AArch64 idiom; not
//! strict SSA). If we ignore MOVK, the tracker only sees the first MOVZ
//! and records the low 16 bits. Any subsequent fold that uses v100 will
//! silently use the wrong value (see issue #366).

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, OpcodeCategory, PassId,
    ProvenanceMap, VReg,
};

use crate::cache::StableHasher;
use crate::pass_manager::{
    CertifiedPassCheckerRecord, CertifiedPassRunRecord, CertifiedPassRunStatus, MachinePass,
};

/// Constant folding pass.
pub struct ConstantFolding;

/// Constant folding wrapper that emits neutral certified pass run records.
#[derive(Default)]
pub struct CertifiedConstantFolding {
    certified_pass_runs: Vec<CertifiedPassRunRecord>,
}

impl CertifiedConstantFolding {
    /// Create a certified constant-folding wrapper.
    pub fn new() -> Self {
        Self::default()
    }

    fn record_run(&mut self, function_name: &str, run: &ConstFoldCertifiedRun) {
        self.certified_pass_runs
            .push(const_fold_certified_pass_record(function_name, run));
    }
}

/// Contract certified for this constant-folding slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstFoldContract {
    /// Replacement preserves exact 64-bit bitvector semantics.
    ExactBv64Equivalence,
}

/// Result produced by the local certificate checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConstFoldCertificateResult {
    Verified,
    Failed,
}

/// Canonical replacement materialization recorded in a fold obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstFoldReplacement {
    pub dst_vreg: u32,
    pub value_i64: i64,
    pub bitwidth: u32,
    pub materialization: Vec<String>,
}

/// One checked constant-folding pass certificate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstFoldCertificate {
    pub format_version: u32,
    pub pass_name: String,
    pub pass_version: u32,
    pub pass_instance_id: String,
    pub source_inst_id: u32,
    pub source_opcode: String,
    pub source_operands: Vec<String>,
    pub replacement: ConstFoldReplacement,
    pub contract: ConstFoldContract,
    pub domain: String,
    pub dtype_policy: String,
    pub obligation_hash: String,
    pub checker: String,
    pub result: ConstFoldCertificateResult,
}

/// Failed/unsupported candidate observed while running in certified mode.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstFoldCertificationFailure {
    pub source_inst_id: u32,
    pub source_opcode: String,
    pub reason: String,
}

/// Result of running constant folding through the certified pass boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstFoldCertifiedRun {
    pub changed: bool,
    pub certificates: Vec<ConstFoldCertificate>,
    pub failures: Vec<ConstFoldCertificationFailure>,
}

impl ConstFoldCertifiedRun {
    /// A certified compile may only consume this pass if every emitted
    /// obligation was checked and no unsupported constant fold candidate was
    /// observed.
    pub fn is_certified(&self) -> bool {
        self.failures.is_empty()
            && self
                .certificates
                .iter()
                .all(|cert| cert.result == ConstFoldCertificateResult::Verified)
    }
}

impl ConstantFolding {
    /// Run constant folding and emit checked per-fold certificates for the
    /// supported integer/bitvector subset.
    pub fn run_certified(&mut self, func: &mut MachFunction) -> ConstFoldCertifiedRun {
        run_impl(func, true, None)
    }

    /// Run certified constant folding while preserving instruction provenance.
    pub fn run_certified_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> ConstFoldCertifiedRun {
        run_impl(func, true, Some(provenance))
    }
}

impl MachinePass for ConstantFolding {
    fn name(&self) -> &str {
        "const-fold"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        run_impl(func, false, None).changed
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_impl(func, false, Some(provenance)).changed
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        run_impl(func, false, Some(provenance)).changed
    }
}

impl MachinePass for CertifiedConstantFolding {
    fn name(&self) -> &str {
        "const-fold"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let mut pass = ConstantFolding;
        let run = pass.run_certified(func);
        self.record_run(&func.name, &run);
        run.changed
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let mut pass = ConstantFolding;
        let run = pass.run_certified_with_provenance(func, provenance);
        self.record_run(&func.name, &run);
        run.changed
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut crate::pass_manager::AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_provenance(func, provenance)
    }

    fn take_certified_pass_runs(&mut self) -> Vec<CertifiedPassRunRecord> {
        std::mem::take(&mut self.certified_pass_runs)
    }
}

fn const_fold_certified_pass_record(
    function_name: &str,
    run: &ConstFoldCertifiedRun,
) -> CertifiedPassRunRecord {
    let status = if run.is_certified() {
        CertifiedPassRunStatus::Verified
    } else {
        CertifiedPassRunStatus::Failed
    };
    CertifiedPassRunRecord {
        format_version: "trust-cg.opt.certified_pass_run.v1".to_string(),
        pass_name: "const-fold-bv64".to_string(),
        pass_version: 1,
        pass_instance_id: "const-fold:bv64:v1".to_string(),
        function_name: function_name.to_string(),
        changed: run.changed,
        status,
        certificate_count: run.certificates.len(),
        failure_count: run.failures.len(),
        obligation_hash: const_fold_run_obligation_hash(function_name, run),
        local_checker: CertifiedPassCheckerRecord {
            kind: "trust-cg-opt-local".to_string(),
            name: "analytical-bv64 const-fold checker".to_string(),
            version: "1".to_string(),
            status,
        },
        summary: serde_json::to_value(run).expect("const-fold certified run serializes"),
    }
}

fn const_fold_run_obligation_hash(function_name: &str, run: &ConstFoldCertifiedRun) -> String {
    let mut h = StableHasher::new();
    h.write_str("trust-cg.const-fold.certified-run.v1");
    h.write_str(function_name);
    h.write_u8(u8::from(run.changed));
    h.write_u32(run.certificates.len() as u32);
    for cert in &run.certificates {
        h.write_u32(cert.source_inst_id);
        h.write_str(&cert.source_opcode);
        h.write_str(&cert.obligation_hash);
        h.write_str(cert.result.as_str());
    }
    h.write_u32(run.failures.len() as u32);
    for failure in &run.failures {
        h.write_u32(failure.source_inst_id);
        h.write_str(&failure.source_opcode);
        h.write_str(&failure.reason);
    }
    format!("trust-cg-opt-certified-pass-run-v1:{:032x}", h.finish128())
}

impl ConstFoldCertificateResult {
    fn as_str(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
        }
    }
}

fn run_impl(
    func: &mut MachFunction,
    certified_mode: bool,
    mut provenance: Option<&mut ProvenanceMap>,
) -> ConstFoldCertifiedRun {
    let mut changed = false;
    let mut certificates = Vec::new();
    let mut failures = Vec::new();

    // Single forward walk per block: track MOVZ/MOVN/MOVK materialization,
    // fold foldable instructions, and invalidate stale tracker entries when a
    // vreg is redefined by something we can't simulate.
    //
    // We rebuild each block's instruction list as we go so that we
    // can splice MOVK chains after a folded wide constant without
    // disturbing the walk.
    for block_id in func.block_order.clone() {
        // The pass has no dataflow meet over predecessors, so cross-block
        // constant propagation is not sound for loop headers or joins.
        let mut constants: HashMap<VReg, i64> = HashMap::new();
        let original_insts = func.block(block_id).insts.clone();
        let mut new_insts: Vec<InstId> = Vec::with_capacity(original_insts.len());

        for inst_id in original_insts {
            let inst = func.inst(inst_id);

            // 1. Fold if possible. A folded instruction becomes a
            //    materialization of the computed constant in the
            //    destination vreg, and no later MOVK will target
            //    the dst (ISel only emits MOVK chains immediately
            //    after the seeding MOVZ on a freshly-allocated
            //    vreg).
            if let Some((dst_vreg, result)) = try_fold(inst, &constants) {
                let cert = if certified_mode {
                    Some(make_const_fold_certificate(
                        inst_id, inst, dst_vreg, result, &constants,
                    ))
                } else {
                    None
                };
                let extra = rewrite_as_constant_materialization(func, inst_id, dst_vreg, result);
                new_insts.push(inst_id);
                if let Some(provenance) = provenance.as_deref_mut() {
                    provenance.record_in_place_transform(inst_id, PassId::new("const-fold"));
                }
                for extra_id in extra {
                    if let Some(provenance) = provenance.as_deref_mut() {
                        provenance.record_creation(
                            extra_id,
                            PassId::new("const-fold"),
                            format!(
                                "const-fold materialized folded constant from inst{} as MOVK chunk",
                                inst_id.0
                            ),
                        );
                    }
                    new_insts.push(extra_id);
                }
                if let Some(cert) = cert {
                    certificates.push(cert);
                }
                constants.insert(dst_vreg, result);
                changed = true;
                continue;
            }

            if certified_mode
                && let Some(reason) = constant_fold_candidate_failure(inst, &constants)
            {
                failures.push(ConstFoldCertificationFailure {
                    source_inst_id: inst_id.0,
                    source_opcode: format!("{:?}", inst.opcode),
                    reason,
                });
            }

            // 2. Simulate MOVZ/MOVN/MOVK writes so subsequent
            //    instructions see the correct composed value.
            if update_const_tracker(inst, &mut constants) {
                new_insts.push(inst_id);
                continue;
            }

            // 3. Invalidate: if this instruction defines a vreg and
            //    we didn't fold or track it, the stale constant
            //    entry (if any) is no longer valid.
            if inst.produces_value()
                && let Some(MachOperand::VReg(dst)) = inst.operands.first()
            {
                constants.remove(dst);
            }

            new_insts.push(inst_id);
        }

        func.block_mut(block_id).insts = new_insts;
    }

    ConstFoldCertifiedRun {
        changed,
        certificates,
        failures,
    }
}

fn make_const_fold_certificate(
    inst_id: InstId,
    inst: &MachInst,
    dst_vreg: VReg,
    result: i64,
    constants: &HashMap<VReg, i64>,
) -> ConstFoldCertificate {
    let materialization = materialization_opcodes(result);
    let source_opcode = format!("{:?}", inst.opcode);
    let source_operands = inst.operands.iter().map(format_operand).collect::<Vec<_>>();
    let replacement = ConstFoldReplacement {
        dst_vreg: dst_vreg.id,
        value_i64: result,
        bitwidth: 64,
        materialization,
    };
    let obligation_hash = const_fold_obligation_hash(
        inst_id,
        &source_opcode,
        &source_operands,
        &replacement,
        constants,
    );
    let result_status = if check_const_fold_obligation(inst, result, constants) {
        ConstFoldCertificateResult::Verified
    } else {
        ConstFoldCertificateResult::Failed
    };

    ConstFoldCertificate {
        format_version: 1,
        pass_name: "const-fold".to_string(),
        pass_version: 1,
        pass_instance_id: "const-fold:bv64:v1".to_string(),
        source_inst_id: inst_id.0,
        source_opcode,
        source_operands,
        replacement,
        contract: ConstFoldContract::ExactBv64Equivalence,
        domain: "scalar-bv64;bounds=full-u64".to_string(),
        dtype_policy: "i64 storage interpreted as BV64 with wrapping arithmetic".to_string(),
        obligation_hash,
        checker: "trust-cg-opt analytical-bv64 const-fold checker v1".to_string(),
        result: result_status,
    }
}

fn materialization_opcodes(result: i64) -> Vec<String> {
    let result_u = result as u64;
    if result >= 0 && result_u <= 0xFFFF {
        return vec!["MovI".to_string()];
    }

    if single_movn_materialization(result_u).is_some() {
        return vec!["Movn".to_string()];
    }

    let mut ops = vec!["Movz".to_string()];
    for shift in [16u64, 32u64, 48u64] {
        if ((result_u >> shift) & 0xFFFF) != 0 {
            ops.push(format!("Movk@{}", shift));
        }
    }
    ops
}

fn format_operand(operand: &MachOperand) -> String {
    match operand {
        MachOperand::VReg(vreg) => format!("v{}:{:?}", vreg.id, vreg.class),
        MachOperand::Imm(value) => format!("#{}", value),
        other => format!("{:?}", other),
    }
}

fn const_fold_obligation_hash(
    inst_id: InstId,
    source_opcode: &str,
    source_operands: &[String],
    replacement: &ConstFoldReplacement,
    constants: &HashMap<VReg, i64>,
) -> String {
    let mut h = StableHasher::new();
    h.write_str("trust-cg.const-fold.cert.v1");
    h.write_u32(inst_id.0);
    h.write_str(source_opcode);
    for operand in source_operands {
        h.write_str(operand);
    }
    h.write_u32(replacement.dst_vreg);
    h.write_u64(replacement.value_i64 as u64);
    h.write_u32(replacement.bitwidth);
    for opcode in &replacement.materialization {
        h.write_str(opcode);
    }
    let mut tracked = constants.iter().collect::<Vec<_>>();
    tracked.sort_by_key(|(vreg, _)| **vreg);
    for (vreg, value) in tracked {
        h.write_u32(vreg.id);
        h.write_str(&format!("{:?}", vreg.class));
        h.write_u64(*value as u64);
    }
    format!("{:032x}", h.finish128())
}

fn check_const_fold_obligation(
    inst: &MachInst,
    replacement: i64,
    constants: &HashMap<VReg, i64>,
) -> bool {
    try_fold(inst, constants)
        .map(|(_, checked)| checked == replacement)
        .unwrap_or(false)
}

fn constant_fold_candidate_failure(
    inst: &MachInst,
    constants: &HashMap<VReg, i64>,
) -> Option<String> {
    let category = inst.opcode.categorize();
    let ops = &inst.operands;
    match category {
        OpcodeCategory::ShlRI | OpcodeCategory::ShrRI | OpcodeCategory::SarRI => {
            if ops.len() >= 3
                && ops[0].as_vreg().is_some()
                && lookup_const(&ops[1], constants).is_some()
                && let Some(shift) = ops[2].as_imm()
                && !(0..=63).contains(&shift)
            {
                return Some(format!(
                    "unsupported certified shift amount {}; expected 0..=63",
                    shift
                ));
            }
            None
        }
        OpcodeCategory::AddRR
        | OpcodeCategory::SubRR
        | OpcodeCategory::MulRR
        | OpcodeCategory::AndRR
        | OpcodeCategory::OrRR
        | OpcodeCategory::XorRR
        | OpcodeCategory::AddRI
        | OpcodeCategory::SubRI
        | OpcodeCategory::ShlRR
        | OpcodeCategory::ShrRR
        | OpcodeCategory::SarRR
        | OpcodeCategory::Neg => {
            if inst.produces_value()
                && inst
                    .operands
                    .first()
                    .and_then(MachOperand::as_vreg)
                    .is_none()
            {
                return Some(
                    "unsupported certified fold: destination is not a virtual register".to_string(),
                );
            }
            None
        }
        _ => None,
    }
}

/// Rewrite the instruction at `inst_id` as a constant materialization of
/// `result` into `dst_vreg`.
///
/// For values that fit in a single 16-bit MOVZ field (`0..=0xFFFF`), we
/// keep the slot as a single `MovI` (the encoder emits this as a plain
/// MOVZ).
///
/// For values whose bitwise-not fits in the low 16-bit lane, use a
/// shift-zero MOVN.
///
/// For wider values we rewrite the slot as a MOVZ of the low 16 bits and
/// *append* MOVK instructions to a freshly allocated fan of InstIds. The
/// caller must splice those InstIds into the block's instruction list
/// immediately after `inst_id` to preserve program order.
fn rewrite_as_constant_materialization(
    func: &mut MachFunction,
    inst_id: InstId,
    dst_vreg: VReg,
    result: i64,
) -> Vec<InstId> {
    let result_u = result as u64;

    // Preserve source_loc from the instruction being rewritten (issue #376):
    // constant folding replaces a computation with a materialization, but
    // the source-level statement is unchanged — lldb must still point at
    // the original trust_ir source line.
    let src_loc = func.inst(inst_id).source_loc;

    // Fast path: fits in a single 16-bit MOVZ field.
    if result >= 0 && result_u <= 0xFFFF {
        let mut new_inst = MachInst::new(
            AArch64Opcode::MovI,
            vec![MachOperand::VReg(dst_vreg), MachOperand::Imm(result)],
        );
        new_inst.source_loc = src_loc;
        *func.inst_mut(inst_id) = new_inst;
        return Vec::new();
    }

    if let Some((imm16, _)) = single_movn_materialization(result_u) {
        let mut new_inst = MachInst::new(
            AArch64Opcode::Movn,
            vec![MachOperand::VReg(dst_vreg), MachOperand::Imm(imm16 as i64)],
        );
        new_inst.source_loc = src_loc;
        *func.inst_mut(inst_id) = new_inst;
        return Vec::new();
    }

    // Wide: rewrite slot as MOVZ of low 16 bits, then append MOVK for
    // each non-zero remaining 16-bit chunk.
    let low16 = result_u & 0xFFFF;
    let mut new_movz = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(dst_vreg), MachOperand::Imm(low16 as i64)],
    );
    new_movz.source_loc = src_loc;
    *func.inst_mut(inst_id) = new_movz;

    let mut extra = Vec::new();
    for shift in [16u64, 32u64, 48u64] {
        let chunk = (result_u >> shift) & 0xFFFF;
        if chunk != 0 {
            let mut movk = MachInst::new(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::VReg(dst_vreg),
                    MachOperand::Imm(chunk as i64),
                    MachOperand::Imm(shift as i64),
                ],
            );
            movk.source_loc = src_loc;
            extra.push(func.push_inst(movk));
        }
    }
    extra
}

fn single_movn_materialization(value: u64) -> Option<(u16, u64)> {
    let inverted = !value;
    if inverted & !0xFFFF == 0 {
        Some((inverted as u16, 0))
    } else {
        None
    }
}

/// Simulate MOVZ/MOVN/MOVK writes against the constant tracker.
///
/// Returns `true` if the instruction was a recognized move-wide variant
/// (whether or not the value could be fully determined). Returning
/// `true` signals the caller that this instruction's effect on the
/// tracker has been handled — no further invalidation is needed.
///
/// # Operand conventions (from ISel; see `trust-cg-lower/src/isel.rs`)
///
/// * `MovI` — exactly `[VReg(dst), Imm(imm16)]`.
/// * `Movz` / `Movn` — `[VReg(dst), Imm(imm16)]` with an optional explicit
///   zero shift. Nonzero shifts are outside the v0.1 publication subset.
/// * `Movk` — `[VReg(dst), Imm(imm16)]` with an optional architectural lane
///   shift. It writes that 16-bit field while preserving the rest of `dst`.
///   If `dst` is not tracked we cannot reconstruct the full value and drop any
///   stale entry.
/// * `MovR` / `Copy` — `[VReg(dst), VReg(src)]`. Same-class virtual-register
///   copies transparently propagate a tracked source constant; unknown or
///   mixed-class copies clear the destination.
fn update_const_tracker(inst: &MachInst, constants: &mut HashMap<VReg, i64>) -> bool {
    let Some(MachOperand::VReg(dst)) = inst.operands.first() else {
        return false;
    };
    let Some(width) = tracked_gpr_width(*dst) else {
        constants.remove(dst);
        return matches!(
            inst.opcode,
            AArch64Opcode::MovI
                | AArch64Opcode::Movz
                | AArch64Opcode::MOVZWi
                | AArch64Opcode::MOVZXi
                | AArch64Opcode::Movn
                | AArch64Opcode::Movk
        );
    };
    match inst.opcode {
        AArch64Opcode::MovI => {
            if inst.operands.len() == 2
                && let Some(v) = move_wide_imm16(inst.operands.get(1))
            {
                constants.insert(*dst, *v);
                return true;
            }
            // Malformed MovI — play safe.
            constants.remove(dst);
            true
        }
        AArch64Opcode::Movz | AArch64Opcode::MOVZWi | AArch64Opcode::MOVZXi => {
            let typed_width_matches = match inst.opcode {
                AArch64Opcode::MOVZWi => width == 32,
                AArch64Opcode::MOVZXi => width == 64,
                _ => true,
            };
            let arity_matches = if inst.opcode == AArch64Opcode::Movz {
                (2..=3).contains(&inst.operands.len())
            } else {
                inst.operands.len() == 2
            };
            if typed_width_matches
                && arity_matches
                && let Some(v) = move_wide_imm16(inst.operands.get(1))
                && move_wide_shift(inst.operands.get(2), width, false) == Some(0)
            {
                constants.insert(*dst, *v);
                return true;
            }
            constants.remove(dst);
            true
        }
        AArch64Opcode::Movn => {
            if (2..=3).contains(&inst.operands.len())
                && let Some(v) = move_wide_imm16(inst.operands.get(1))
                && move_wide_shift(inst.operands.get(2), width, false) == Some(0)
            {
                let register_mask = if width == 32 {
                    u64::from(u32::MAX)
                } else {
                    u64::MAX
                };
                constants.insert(*dst, ((!*v as u64) & register_mask) as i64);
                return true;
            }
            constants.remove(dst);
            true
        }
        AArch64Opcode::Movk => {
            // MOVK: overwrite the 16-bit chunk at `shift`, preserving
            // the rest of the register's current contents.
            if !(2..=3).contains(&inst.operands.len()) {
                constants.remove(dst);
                return true;
            }
            let Some(shift) = move_wide_shift(inst.operands.get(2), width, true) else {
                constants.remove(dst);
                return true;
            };
            if let Some(v) = move_wide_imm16(inst.operands.get(1)) {
                if let Some(old) = constants.get(dst).copied() {
                    let mask: u64 = (0xFFFFu64) << shift;
                    let ins = (*v as u64) << shift;
                    let register_mask = if width == 32 {
                        u64::from(u32::MAX)
                    } else {
                        u64::MAX
                    };
                    let new_val = (((old as u64) & !mask) | ins) & register_mask;
                    constants.insert(*dst, new_val as i64);
                } else {
                    // Cannot reconstruct full value; leave unknown.
                    constants.remove(dst);
                }
            } else {
                constants.remove(dst);
            }
            true
        }
        AArch64Opcode::MovR | AArch64Opcode::Copy => {
            track_transparent_copy(*dst, inst.operands.get(1), constants);
            true
        }
        _ => false,
    }
}

fn track_transparent_copy(
    dst: VReg,
    src_operand: Option<&MachOperand>,
    constants: &mut HashMap<VReg, i64>,
) {
    let Some(MachOperand::VReg(src)) = src_operand else {
        constants.remove(&dst);
        return;
    };
    if src.class != dst.class {
        constants.remove(&dst);
        return;
    }
    if let Some(value) = constants.get(src).copied() {
        constants.insert(dst, value);
    } else {
        constants.remove(&dst);
    }
}

fn tracked_gpr_width(dst: VReg) -> Option<u32> {
    match dst.class {
        trust_cg_ir::RegClass::Gpr32 => Some(32),
        trust_cg_ir::RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

fn move_wide_imm16(operand: Option<&MachOperand>) -> Option<&i64> {
    match operand {
        Some(MachOperand::Imm(value)) if (0..=0xFFFF).contains(value) => Some(value),
        _ => None,
    }
}

fn move_wide_shift(operand: Option<&MachOperand>, width: u32, allow_nonzero: bool) -> Option<u32> {
    match operand {
        None => Some(0),
        Some(MachOperand::Imm(shift))
            if matches!(*shift, 0 | 16 | 32 | 48)
                && (width == 64 || *shift <= 16)
                && (allow_nonzero || *shift == 0) =>
        {
            Some(*shift as u32)
        }
        Some(_) => None,
    }
}

/// Try to constant-fold an instruction.
///
/// Returns `Some((dst_vreg, folded_value))` if the instruction can be folded,
/// `None` otherwise.
///
/// Dispatch uses [`OpcodeCategory`] for target-independent pattern matching:
/// the category determines *which* folding rule applies (add, sub, shift, etc.),
/// while the concrete [`AArch64Opcode`] is still available for target-specific
/// details (e.g., shift amount masking). This means constant folding will work
/// automatically for any new target once its opcodes implement `categorize()`.
fn try_fold(inst: &MachInst, constants: &HashMap<VReg, i64>) -> Option<(VReg, i64)> {
    let opcode = inst.opcode;
    let category = opcode.categorize();
    let ops = &inst.operands;

    // WIDTH-AWARE evaluation. The tracker stores Gpr32 constants
    // ZERO-EXTENDED into the i64 map (`update_const_tracker` masks with
    // `u32::MAX`), so a width-blind i64 evaluation is WRONG for every
    // sign-sensitive operation: `asr w, w=0xFFFF_FFFF, #31` evaluated as a
    // positive i64 shift folds to 1 instead of the architectural
    // 0xFFFF_FFFF. That exact mis-fold miscompiled gcc-c-torture
    // ifcvt-onecmpl-abs-1.c / pr68376-2.c (folded self-check difference
    // 0xFFFF_FFFE instead of 0) once the inliner exposed `~n`-abs bodies to
    // constant arguments. Rules restoring architectural semantics:
    //   * every 32-bit RESULT is truncated to 32 bits and re-stored
    //     zero-extended (the map's canonical form) — also stops AddRR/Shl
    //     carry-outs from leaking into bits 32..63 and later materializing
    //     impossible W-register MOVK@32/@48 chains;
    //   * SIGNED inputs (arithmetic shift) are sign-extended from bit 31
    //     before evaluation;
    //   * 32-bit shift immediates > 31 fail closed (not encodable).
    let dst_width = ops
        .first()
        .and_then(|op| op.as_vreg())
        .and_then(tracked_gpr_width)?;
    let norm_out = |v: i64| -> i64 {
        if dst_width == 32 {
            i64::from(v as u32)
        } else {
            v
        }
    };
    let sext_in = |v: i64| -> i64 {
        if dst_width == 32 {
            i64::from(v as u32 as i32)
        } else {
            v
        }
    };
    let zext_in = |v: i64| -> u64 {
        if dst_width == 32 {
            u64::from(v as u32)
        } else {
            v as u64
        }
    };

    match category {
        // Binary register-register: dst = op(lhs, rhs)
        // Operands: [dst, lhs, rhs]
        OpcodeCategory::AddRR
        | OpcodeCategory::SubRR
        | OpcodeCategory::MulRR
        | OpcodeCategory::AndRR
        | OpcodeCategory::OrRR
        | OpcodeCategory::XorRR => {
            // EXACTLY three operands. Several of these categories also cover
            // wider opcodes whose extra operand changes the meaning of the
            // first three (`target_info.rs`):
            //   XorRR <- EorRRShift / EorRRLsl / EorRRLsr   `[Rd, Rn, Rm, shift]`
            //   AddRR <- NeonAddV, SubRR <- NeonSubV,
            //   MulRR <- NeonMulV                           `[Vd, Vn, Vm, arrangement]`
            // Folding `eor Rd, Rn, Rm, LSL #k` as a plain `Rn ^ Rm` drops the
            // shift, and folding a NEON lane-wise op as a scalar is meaningless.
            // A `< 3` guard admitted all of them; require the exact scalar shape.
            if ops.len() != 3 {
                return None;
            }
            let dst = ops[0].as_vreg()?;
            let lhs = lookup_const(&ops[1], constants)?;
            let rhs = lookup_const(&ops[2], constants)?;

            let result = match category {
                OpcodeCategory::AddRR => lhs.wrapping_add(rhs),
                OpcodeCategory::SubRR => lhs.wrapping_sub(rhs),
                OpcodeCategory::MulRR => lhs.wrapping_mul(rhs),
                OpcodeCategory::AndRR => lhs & rhs,
                OpcodeCategory::OrRR => lhs | rhs,
                OpcodeCategory::XorRR => lhs ^ rhs,
                _ => unreachable!("inner match constrained by outer arm"),
            };
            Some((dst, norm_out(result)))
        }

        // Binary register-immediate: dst = op(src, imm)
        // Operands: [dst, src, imm]
        OpcodeCategory::AddRI | OpcodeCategory::SubRI => {
            if ops.len() < 3 {
                return None;
            }
            let dst = ops[0].as_vreg()?;
            let src = lookup_const(&ops[1], constants)?;
            let imm = effective_register_immediate(opcode, ops[2].as_imm()?);

            let result = match category {
                OpcodeCategory::AddRI => src.wrapping_add(imm),
                OpcodeCategory::SubRI => src.wrapping_sub(imm),
                _ => unreachable!("inner match constrained by outer arm"),
            };
            Some((dst, norm_out(result)))
        }

        // Shift register-immediate: dst = src shift imm
        // Operands: [dst, src, imm]
        OpcodeCategory::ShlRI | OpcodeCategory::ShrRI | OpcodeCategory::SarRI => {
            if ops.len() < 3 {
                return None;
            }
            let dst = ops[0].as_vreg()?;
            let src = lookup_const(&ops[1], constants)?;
            let shift = ops[2].as_imm()?;

            // Validate shift amount: 0..63 for 64-bit, 0..31 for 32-bit
            // (a W-register shift immediate above 31 is not encodable —
            // fail closed rather than guess).
            let max_shift = i64::from(dst_width) - 1;
            if !(0..=max_shift).contains(&shift) {
                return None;
            }
            let shift = shift as u32;

            let result = match category {
                OpcodeCategory::ShlRI => src.wrapping_shl(shift),
                OpcodeCategory::ShrRI => (zext_in(src).wrapping_shr(shift)) as i64,
                OpcodeCategory::SarRI => sext_in(src).wrapping_shr(shift),
                _ => unreachable!("inner match constrained by outer arm"),
            };
            Some((dst, norm_out(result)))
        }

        // Shift register-register: dst = src shift amount
        // Operands: [dst, src, amount]
        OpcodeCategory::ShlRR | OpcodeCategory::ShrRR | OpcodeCategory::SarRR => {
            if ops.len() < 3 {
                return None;
            }
            let dst = ops[0].as_vreg()?;
            let src = lookup_const(&ops[1], constants)?;
            let amount = lookup_const(&ops[2], constants)?;

            // Mask the shift amount to the register width (architectural
            // variable-shift behavior: amount mod 64 for X, mod 32 for W).
            let shift = (amount & i64::from(dst_width - 1)) as u32;

            let result = match category {
                OpcodeCategory::ShlRR => src.wrapping_shl(shift),
                OpcodeCategory::ShrRR => (zext_in(src).wrapping_shr(shift)) as i64,
                OpcodeCategory::SarRR => sext_in(src).wrapping_shr(shift),
                _ => unreachable!("inner match constrained by outer arm"),
            };
            Some((dst, norm_out(result)))
        }

        // Unary negate: dst = -src
        // Operands: [dst, src]
        OpcodeCategory::Neg => {
            if ops.len() < 2 {
                return None;
            }
            let dst = ops[0].as_vreg()?;
            let src = lookup_const(&ops[1], constants)?;
            Some((dst, norm_out(src.wrapping_neg())))
        }

        // Other categories (Load, Store, Call, Mov, Cmp, etc.) are not foldable
        // or their folding requires target-specific logic.
        _ => None,
    }
}

fn effective_register_immediate(opcode: AArch64Opcode, imm: i64) -> i64 {
    match opcode {
        AArch64Opcode::AddRIShift12 => imm.wrapping_shl(12),
        _ => imm,
    }
}

/// Look up the constant value for an operand.
///
/// Returns `Some(value)` if the operand is an immediate or a VReg with
/// a known constant value, `None` otherwise.
fn lookup_const(operand: &MachOperand, constants: &HashMap<VReg, i64>) -> Option<i64> {
    match operand {
        MachOperand::Imm(v) => Some(*v),
        MachOperand::VReg(vreg) => constants.get(vreg).copied(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pass_manager::MachinePass;
    use trust_cg_ir::{
        BlockId, MachFunction, MachInst, MachOperand, PassId, ProvenanceStatus, RegClass,
        Signature, TransformKind, TrustIrInstId, VReg,
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new("test_cf".to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    /// Reconstruct the runtime value that `vreg_id` would hold after the
    /// entry block executes, by replaying MovI/MOVZ/MOVN/MOVK semantics.
    ///
    /// After `ConstantFolding` rewrites a folded instruction, the slot
    /// may be a plain `MovI` (for values that fit in 16 bits) OR a
    /// `Movz` followed by one or more `Movk` instructions (for wider
    /// values). Tests should compare against the reconstructed value
    /// rather than inspecting a specific slot's opcode.
    fn materialized_value(func: &MachFunction, vreg_id: u32) -> Option<i64> {
        let mut constants: HashMap<VReg, i64> = HashMap::new();
        for block_id in &func.block_order {
            let block = func.block(*block_id);
            for inst_id in &block.insts {
                let inst = func.inst(*inst_id);
                update_const_tracker(inst, &mut constants);
            }
        }
        constants.get(&VReg::new(vreg_id, RegClass::Gpr64)).copied()
    }

    #[test]
    fn test_fold_add_ri() {
        // v0 = movi #10
        // v1 = add v0, #20  → v1 = movi #30
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(20)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        // add should be replaced with MovI
        let folded = func.inst(trust_cg_ir::InstId(1));
        assert_eq!(folded.opcode, AArch64Opcode::MovI);
        assert_eq!(folded.operands[1], imm(30));
    }

    /// `OpcodeCategory::XorRR` also covers the shifted-register EOR forms,
    /// whose 4th operand is a shift amount: `eor Rd, Rn, Rm, LSL #k` is
    /// `Rn ^ (Rm << k)`, NOT `Rn ^ Rm`. Folding it as a plain XOR silently
    /// produces the wrong constant. The `< 3` guard admitted these; the fold
    /// now requires the exact 3-operand scalar shape.
    #[test]
    fn test_shifted_eor_is_not_folded_as_plain_xor() {
        for opcode in [
            AArch64Opcode::EorRRLsl,
            AArch64Opcode::EorRRLsr,
            AArch64Opcode::EorRRShift,
        ] {
            let a = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0b1010)]);
            let b = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(0b0110)]);
            let shifted = MachInst::new(opcode, vec![vreg(2), vreg(0), vreg(1), imm(3)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![a, b, shifted, ret]);

            let mut cf = ConstantFolding;
            let _ = cf.run(&mut func);

            let folded = func.inst(trust_cg_ir::InstId(2));
            assert_eq!(
                folded.opcode, opcode,
                "{opcode:?} must not be const-folded as a plain XOR"
            );
            assert_eq!(folded.operands.len(), 4, "{opcode:?} must keep its shift");
        }
    }

    /// The NEON lane-wise ops share the scalar categories but carry a 4th
    /// operand (the arrangement); folding them as scalars is meaningless.
    #[test]
    fn test_neon_vector_ops_are_not_scalar_folded() {
        for opcode in [
            AArch64Opcode::NeonAddV,
            AArch64Opcode::NeonSubV,
            AArch64Opcode::NeonMulV,
        ] {
            let a = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(3)]);
            let b = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(4)]);
            let v = MachInst::new(opcode, vec![vreg(2), vreg(0), vreg(1), imm(0)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![a, b, v, ret]);

            let mut cf = ConstantFolding;
            let _ = cf.run(&mut func);

            let after = func.inst(trust_cg_ir::InstId(2));
            assert_eq!(after.opcode, opcode, "{opcode:?} must not be scalar-folded");
        }
    }

    #[test]
    fn test_fold_add_ri_shift12_uses_shifted_immediate() {
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let shifted = MachInst::new(AArch64Opcode::AddRIShift12, vec![vreg(1), vreg(0), imm(1)]);
        let plain = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi, shifted, plain, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        assert_eq!(materialized_value(&func, 1), Some(10 + (1 << 12)));
        assert_eq!(materialized_value(&func, 2), Some(11));
    }

    #[test]
    fn test_const_fold_keeps_same_numeric_id_classes_distinct() {
        let movi64 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let movi32 = MachInst::new(AArch64Opcode::MovI, vec![vreg32(0), imm(3)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(20)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi64, movi32, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        assert_eq!(materialized_value(&func, 1), Some(30));
    }

    #[test]
    fn test_const_fold_invalidation_is_class_exact() {
        let movi64 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let movi32 = MachInst::new(AArch64Opcode::MovI, vec![vreg32(0), imm(3)]);
        let redefine32 = MachInst::new(AArch64Opcode::MovR, vec![vreg32(0), vreg32(2)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(20)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi64, movi32, redefine32, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        assert_eq!(materialized_value(&func, 1), Some(30));
    }

    #[test]
    fn test_const_fold_movk_update_is_class_exact() {
        let movz64 = MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(0x1111)]);
        let movz32 = MachInst::new(AArch64Opcode::Movz, vec![vreg32(0), imm(0x2222)]);
        let movk32 = MachInst::new(AArch64Opcode::Movk, vec![vreg32(0), imm(0x3333), imm(16)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movz64, movz32, movk32, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        assert_eq!(materialized_value(&func, 1), Some(0x1112));
    }

    #[test]
    fn test_const_fold_tracks_same_class_movr_copy() {
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let movr = MachInst::new(AArch64Opcode::MovR, vec![vreg(1), vreg(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi, movr, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        assert_eq!(materialized_value(&func, 2), Some(15));
    }

    #[test]
    fn test_const_fold_tracks_same_class_copy() {
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(11)]);
        let copy = MachInst::new(AArch64Opcode::Copy, vec![vreg(1), vreg(0)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(7)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi, copy, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        assert_eq!(materialized_value(&func, 2), Some(18));
    }

    #[test]
    fn test_const_fold_does_not_track_mixed_class_copy() {
        let movi64 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let movi32 = MachInst::new(AArch64Opcode::MovI, vec![vreg32(1), imm(3)]);
        let copy = MachInst::new(AArch64Opcode::Copy, vec![vreg(2), vreg32(1)]);
        let mixed_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(5)]);
        let preserved_add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func =
            make_func_with_insts(vec![movi64, movi32, copy, mixed_add, preserved_add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        assert_eq!(
            func.inst(trust_cg_ir::InstId(3)).opcode,
            AArch64Opcode::AddRI
        );
        assert_eq!(materialized_value(&func, 4), Some(11));
    }

    #[test]
    fn test_const_fold_copy_unknown_source_clears_stale_destination() {
        let old_dst = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(10)]);
        let copy_unknown = MachInst::new(AArch64Opcode::Copy, vec![vreg(1), vreg(99)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![old_dst, copy_unknown, add, ret]);

        let mut cf = ConstantFolding;
        assert!(!cf.run(&mut func));

        assert_eq!(
            func.inst(trust_cg_ir::InstId(2)).opcode,
            AArch64Opcode::AddRI
        );
    }

    #[test]
    fn test_const_fold_does_not_propagate_constants_across_blocks() {
        let mut func = MachFunction::new(
            "test_cf_cross_block".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let next = func.create_block();

        let movi = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]));
        let branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(next)],
        ));
        func.append_inst(entry, movi);
        func.append_inst(entry, branch);

        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(5)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(next, add);
        func.append_inst(next, ret);
        assert_eq!(func.block_order, vec![BlockId(0), next]);

        let mut cf = ConstantFolding;
        assert!(!cf.run(&mut func));
        assert_eq!(func.inst(add).opcode, AArch64Opcode::AddRI);
    }

    #[test]
    fn test_fold_sub_ri() {
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(50)]);
        let sub = MachInst::new(AArch64Opcode::SubRI, vec![vreg(1), vreg(0), imm(20)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi, sub, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        let folded = func.inst(trust_cg_ir::InstId(1));
        assert_eq!(folded.opcode, AArch64Opcode::MovI);
        assert_eq!(folded.operands[1], imm(30));
    }

    #[test]
    fn test_fold_add_rr() {
        // v0 = movi #10
        // v1 = movi #20
        // v2 = add v0, v1  → v2 = movi #30
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(20)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, m1, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        let folded = func.inst(trust_cg_ir::InstId(2));
        assert_eq!(folded.opcode, AArch64Opcode::MovI);
        assert_eq!(folded.operands[1], imm(30));
    }

    #[test]
    fn test_fold_mul_rr() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(6)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(7)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, m1, mul, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        let folded = func.inst(trust_cg_ir::InstId(2));
        assert_eq!(folded.opcode, AArch64Opcode::MovI);
        assert_eq!(folded.operands[1], imm(42));
    }

    #[test]
    fn test_fold_logical() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0xFF)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(0x0F)]);
        let and = MachInst::new(AArch64Opcode::AndRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, m1, and, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        let folded = func.inst(trust_cg_ir::InstId(2));
        assert_eq!(folded.operands[1], imm(0x0F));
    }

    #[test]
    fn test_fold_shift() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(1)]);
        let lsl = MachInst::new(AArch64Opcode::LslRI, vec![vreg(1), vreg(0), imm(4)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, lsl, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        let folded = func.inst(trust_cg_ir::InstId(1));
        assert_eq!(folded.operands[1], imm(16));
    }

    #[test]
    fn test_certified_fold_supported_integer_bitvector_subset() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(42)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(10)]);
        let m2 = MachInst::new(AArch64Opcode::Movn, vec![vreg(2), imm(15)]);
        let add_rr = MachInst::new(AArch64Opcode::AddRR, vec![vreg(10), vreg(0), vreg(1)]);
        let add_ri = MachInst::new(AArch64Opcode::AddRI, vec![vreg(11), vreg(0), imm(5)]);
        let sub_rr = MachInst::new(AArch64Opcode::SubRR, vec![vreg(12), vreg(0), vreg(1)]);
        let sub_ri = MachInst::new(AArch64Opcode::SubRI, vec![vreg(13), vreg(0), imm(5)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(14), vreg(0), vreg(1)]);
        let and = MachInst::new(AArch64Opcode::AndRR, vec![vreg(15), vreg(0), vreg(1)]);
        let orr = MachInst::new(AArch64Opcode::OrrRR, vec![vreg(16), vreg(0), vreg(1)]);
        let eor = MachInst::new(AArch64Opcode::EorRR, vec![vreg(17), vreg(0), vreg(1)]);
        let lsl = MachInst::new(AArch64Opcode::LslRI, vec![vreg(18), vreg(1), imm(3)]);
        let lsr = MachInst::new(AArch64Opcode::LsrRI, vec![vreg(19), vreg(0), imm(1)]);
        let asr = MachInst::new(AArch64Opcode::AsrRI, vec![vreg(20), vreg(2), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![
            m0, m1, m2, add_rr, add_ri, sub_rr, sub_ri, mul, and, orr, eor, lsl, lsr, asr, ret,
        ]);

        let mut cf = ConstantFolding;
        let run = cf.run_certified(&mut func);

        assert!(run.changed);
        assert!(run.is_certified(), "supported folds must certify: {run:?}");
        assert_eq!(run.certificates.len(), 11);
        assert!(run.failures.is_empty());
        assert!(run.certificates.iter().all(|cert| {
            cert.contract == ConstFoldContract::ExactBv64Equivalence
                && cert.result == ConstFoldCertificateResult::Verified
                && cert.replacement.bitwidth == 64
                && !cert.obligation_hash.is_empty()
        }));
        assert_eq!(materialized_value(&func, 10), Some(52));
        assert_eq!(materialized_value(&func, 11), Some(47));
        assert_eq!(materialized_value(&func, 12), Some(32));
        assert_eq!(materialized_value(&func, 13), Some(37));
        assert_eq!(materialized_value(&func, 14), Some(420));
        assert_eq!(materialized_value(&func, 15), Some(42 & 10));
        assert_eq!(materialized_value(&func, 16), Some(42 | 10));
        assert_eq!(materialized_value(&func, 17), Some(42 ^ 10));
        assert_eq!(materialized_value(&func, 18), Some(80));
        assert_eq!(materialized_value(&func, 19), Some(21));
        assert_eq!(materialized_value(&func, 20), Some(-4));

        let json = serde_json::to_string(&run.certificates[0]).expect("certificate serializes");
        let decoded: ConstFoldCertificate =
            serde_json::from_str(&json).expect("certificate deserializes");
        assert_eq!(decoded, run.certificates[0]);
    }

    #[test]
    fn test_certified_constant_folding_wrapper_drains_neutral_run_record() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(42)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(10)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, m1, add, ret]);

        let mut pass = CertifiedConstantFolding::new();
        assert!(pass.run(&mut func));
        let records = pass.take_certified_pass_runs();

        assert_eq!(records.len(), 1);
        let record = &records[0];
        assert!(record.is_verified());
        assert_eq!(record.pass_name, "const-fold-bv64");
        assert_eq!(record.function_name, "test_cf");
        assert_eq!(record.certificate_count, 1);
        assert_eq!(record.failure_count, 0);
        assert!(
            record
                .obligation_hash
                .starts_with("trust-cg-opt-certified-pass-run-v1:")
        );
        assert_eq!(
            record.summary["certificates"][0]["source_opcode"].as_str(),
            Some("AddRR")
        );
    }

    #[test]
    fn test_certified_fold_rejects_invalid_immediate_shift() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(1)]);
        let lsl = MachInst::new(AArch64Opcode::LslRI, vec![vreg(1), vreg(0), imm(64)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, lsl, ret]);

        let mut cf = ConstantFolding;
        let run = cf.run_certified(&mut func);

        assert!(!run.changed);
        assert!(!run.is_certified());
        assert!(run.certificates.is_empty());
        assert_eq!(run.failures.len(), 1);
        assert_eq!(run.failures[0].source_opcode, "LslRI");
        assert!(run.failures[0].reason.contains("expected 0..=63"));
        assert_eq!(
            func.inst(trust_cg_ir::InstId(1)).opcode,
            AArch64Opcode::LslRI
        );
    }

    #[test]
    fn test_certified_fold_add_ri_shift12_uses_shifted_immediate() {
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(7)]);
        let shifted = MachInst::new(AArch64Opcode::AddRIShift12, vec![vreg(1), vreg(0), imm(2)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi, shifted, ret]);

        let mut cf = ConstantFolding;
        let run = cf.run_certified(&mut func);

        assert!(run.changed);
        assert!(
            run.is_certified(),
            "AddRIShift12 fold must certify: {run:?}"
        );
        assert_eq!(run.certificates.len(), 1);
        assert_eq!(run.certificates[0].source_opcode, "AddRIShift12");
        assert_eq!(run.certificates[0].replacement.value_i64, 7 + (2 << 12));
        assert_eq!(materialized_value(&func, 1), Some(7 + (2 << 12)));
    }

    #[test]
    fn test_const_fold_obligation_hash_includes_vreg_class() {
        let source_operands = vec![
            "v1:Gpr64".to_string(),
            "v0:Gpr64".to_string(),
            "#5".to_string(),
        ];
        let replacement = ConstFoldReplacement {
            dst_vreg: 1,
            value_i64: 15,
            bitwidth: 64,
            materialization: vec!["MovI".to_string()],
        };

        let mut gpr64_constants = HashMap::new();
        gpr64_constants.insert(VReg::new(0, RegClass::Gpr64), 10);
        let mut gpr32_constants = HashMap::new();
        gpr32_constants.insert(VReg::new(0, RegClass::Gpr32), 10);

        let gpr64_hash = const_fold_obligation_hash(
            InstId(7),
            "AddRI",
            &source_operands,
            &replacement,
            &gpr64_constants,
        );
        let gpr32_hash = const_fold_obligation_hash(
            InstId(7),
            "AddRI",
            &source_operands,
            &replacement,
            &gpr32_constants,
        );

        assert_ne!(gpr64_hash, gpr32_hash);
    }

    #[test]
    fn test_fold_neg() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(42)]);
        let neg = MachInst::new(AArch64Opcode::Neg, vec![vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, neg, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        // -42 is a wide negative value (0xFFFF_FFFF_FFFF_FFD6 as u64), so
        // the folder can materialize it as MOVN #41.
        let folded = func.inst(trust_cg_ir::InstId(1));
        assert_eq!(folded.opcode, AArch64Opcode::Movn);
        assert_eq!(folded.operands, vec![vreg(1), imm(41)]);
        assert_eq!(materialized_value(&func, 1), Some(-42));
    }

    #[test]
    fn test_fold_all_ones_materializes_as_movn_zero() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(1)]);
        let neg = MachInst::new(AArch64Opcode::Neg, vec![vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, neg, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        let folded = func.inst(trust_cg_ir::InstId(1));
        assert_eq!(folded.opcode, AArch64Opcode::Movn);
        assert_eq!(folded.operands, vec![vreg(1), imm(0)]);
        assert_eq!(materialized_value(&func, 1), Some(-1));
    }

    #[test]
    fn test_fold_shifted_mostly_ones_avoids_shifted_movn() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]);
        let sub = MachInst::new(
            AArch64Opcode::SubRI,
            vec![vreg(1), vreg(0), imm(0x1234_0001)],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, sub, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        let folded = func.inst(trust_cg_ir::InstId(1));
        assert_eq!(folded.opcode, AArch64Opcode::Movz);
        assert_eq!(folded.operands, vec![vreg(1), imm(0xFFFF)]);
        let emitted: Vec<_> = func
            .block(func.entry)
            .insts
            .iter()
            .map(|id| func.inst(*id))
            .filter(|inst| inst.operands.first() == Some(&vreg(1)))
            .collect();
        assert_eq!(emitted.len(), 4);
        assert_eq!(emitted[1].operands, vec![vreg(1), imm(0xEDCB), imm(16)]);
        assert_eq!(emitted[2].operands, vec![vreg(1), imm(0xFFFF), imm(32)]);
        assert_eq!(emitted[3].operands, vec![vreg(1), imm(0xFFFF), imm(48)]);
        assert_eq!(materialized_value(&func, 1), Some(!0x1234_0000u64 as i64));
    }

    #[test]
    fn test_certified_fold_movn_materialization_metadata() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(1)]);
        let neg = MachInst::new(AArch64Opcode::Neg, vec![vreg(1), vreg(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, neg, ret]);

        let mut cf = ConstantFolding;
        let run = cf.run_certified(&mut func);

        assert!(run.changed);
        assert!(run.is_certified());
        assert_eq!(run.certificates.len(), 1);
        assert_eq!(
            run.certificates[0].replacement.materialization,
            vec!["Movn".to_string()]
        );
        assert_eq!(materialized_value(&func, 1), Some(-1));
    }

    #[test]
    fn test_no_fold_unknown_operand() {
        // v1 = add v0, #5  where v0 is NOT a known constant
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut cf = ConstantFolding;
        assert!(!cf.run(&mut func));
    }

    #[test]
    fn test_chain_folding() {
        // v0 = movi #10
        // v1 = add v0, #5   → v1 = movi #15
        // v2 = add v1, #3   → v2 = movi #18 (chain: v1 now known)
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let a1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(5)]);
        let a2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, a1, a2, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        // Both adds should be folded
        let folded1 = func.inst(trust_cg_ir::InstId(1));
        assert_eq!(folded1.opcode, AArch64Opcode::MovI);
        assert_eq!(folded1.operands[1], imm(15));

        let folded2 = func.inst(trust_cg_ir::InstId(2));
        assert_eq!(folded2.opcode, AArch64Opcode::MovI);
        assert_eq!(folded2.operands[1], imm(18));
    }

    #[test]
    fn test_fold_wrapping() {
        // Test wrapping arithmetic (no overflow trap).
        //
        // Note: i64::MAX seeds v0, but the seed is already a wide value —
        // it will not be foldable at the AddRI because our MovI seed in
        // the test doesn't fit in 16 bits. Use a small seed and a wide
        // computed result instead: 0xFFFF + 1 = 0x10000 (wide).
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0xFFFF)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        // 0x10000 is > 16 bits so the folder expands the AddRI slot as a
        // MOVZ+MOVK chain. Validate the composed runtime value.
        assert_eq!(materialized_value(&func, 1), Some(0x10000));
    }

    #[test]
    fn test_run_with_provenance_records_narrow_const_fold_in_place() {
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(20)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi, add, ret]);
        let add_id = InstId(1);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(100), &[add_id], PassId::new("isel"));

        let mut cf = ConstantFolding;
        assert!(MachinePass::run_with_provenance(
            &mut cf,
            &mut func,
            &mut provenance
        ));

        let entry = provenance
            .get_entry(add_id)
            .expect("folded instruction keeps provenance entry");
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(100)]);
        assert!(entry.transforms.iter().any(|transform| {
            transform.pass == PassId::new("const-fold") && transform.kind == TransformKind::Survived
        }));
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(100)),
            Some(&[add_id][..])
        );
        assert!(provenance.compiler_generated().is_empty());
    }

    #[test]
    fn test_run_with_provenance_records_wide_materialization_creations() {
        let movi = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0xFFFF)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movi, add, ret]);
        let add_id = InstId(1);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(101), &[add_id], PassId::new("isel"));

        let mut cf = ConstantFolding;
        assert!(MachinePass::run_with_provenance(
            &mut cf,
            &mut func,
            &mut provenance
        ));

        assert_eq!(materialized_value(&func, 1), Some(0x10000));
        let entry = provenance
            .get_entry(add_id)
            .expect("original folded slot remains active");
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(101)]);
        assert!(entry.transforms.iter().any(|transform| {
            transform.pass == PassId::new("const-fold") && transform.kind == TransformKind::Survived
        }));
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(101)),
            Some(&[add_id][..])
        );

        let generated = provenance.compiler_generated();
        assert_eq!(generated.len(), 1);
        let (extra_id, extra_entry) = generated[0];
        assert_eq!(func.inst(extra_id).opcode, AArch64Opcode::Movk);
        assert!(matches!(
            &extra_entry.status,
            ProvenanceStatus::CompilerGenerated { pass, reason }
                if *pass == PassId::new("const-fold")
                    && reason.contains("const-fold materialized folded constant")
                    && reason.contains("inst1")
        ));
    }

    // --- regression tests for issue #366 --------------------------------
    //
    // ISel materializes 64-bit constants with a MOVZ + MOVK chain writing
    // to the same vreg. Before the fix, the folder seeded its tracker from
    // `is_move_imm()` (which excludes MOVK) and used the raw 16-bit MOVZ
    // immediate as the "full" constant, producing wrong folded values for
    // any vreg built this way.

    #[test]
    fn test_fold_movz_movk_chain_materializes_full_constant() {
        // v0 = MOVZ #0x79F9
        // v0 = MOVK v0, #0x9E37, lsl #16
        // v0 = MOVK v0, #0x6791, lsl #32
        // v0 = MOVK v0, #0x1656, lsl #48
        // v1 = MOVZ #0x0002
        // v2 = MulRR v0, v1
        // expect v2 folded to 0x165667919E3779F9 * 2 (wrapping)
        let k = 0x165667919E3779F9u64 as i64;

        let movz = MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(0x79F9)]);
        let movk1 = MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0x9E37), imm(16)]);
        let movk2 = MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0x6791), imm(32)]);
        let movk3 = MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0x1656), imm(48)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(2)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movz, movk1, movk2, movk3, m1, mul, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        // The MulRR is replaced by a materialization of the full 64-bit
        // product. Since the product is wide, the folder expands it as a
        // MOVZ + MOVK chain writing into v2.
        let expected = k.wrapping_mul(2);
        assert_eq!(
            materialized_value(&func, 2),
            Some(expected),
            "fold should see full 64-bit constant 0x{:016x}, not low16 only",
            k as u64
        );
    }

    #[test]
    fn test_fold_movz_movk_xor_pattern() {
        // The xxh3 avalanche uses a 64-bit EOR with a freshly built
        // constant. Regression for #366.
        let k = 0x165667919E3779F9u64 as i64;

        let movz = MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(0x79F9)]);
        let movk1 = MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0x9E37), imm(16)]);
        let movk2 = MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0x6791), imm(32)]);
        let movk3 = MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0x1656), imm(48)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(0x1234)]);
        let eor = MachInst::new(AArch64Opcode::EorRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movz, movk1, movk2, movk3, m1, eor, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        assert_eq!(materialized_value(&func, 2), Some(k ^ 0x1234));
    }

    #[test]
    fn test_fold_movn_zero_is_all_ones() {
        // MOVN #0  →  !0  =  0xFFFF_FFFF_FFFF_FFFF (as i64: -1)
        // v0 = MOVN #0
        // v1 = MOVI #1
        // v2 = AddRR v0, v1  → 0 (wrapping)
        let movn = MachInst::new(AArch64Opcode::Movn, vec![vreg(0), imm(0)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(1)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movn, m1, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        let folded = func.inst(trust_cg_ir::InstId(2));
        assert_eq!(folded.opcode, AArch64Opcode::MovI);
        assert_eq!(folded.operands[1], imm(0));
    }

    #[test]
    fn test_movk_without_seed_does_not_produce_wrong_value() {
        // If MOVK runs on a vreg whose value is unknown (e.g. an
        // argument), we MUST NOT synthesize a bogus value. Downstream
        // folds that use that vreg must fall through.
        //
        // v0 = <unknown, e.g. arg>
        // v0 = MOVK v0, #0xABCD, lsl #0   (patching low16 of an unknown)
        // v1 = MovI #2
        // v2 = MulRR v0, v1      -- must NOT fold
        let movk = MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(0xABCD), imm(0)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(2)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movk, m1, mul, ret]);

        let mut cf = ConstantFolding;
        cf.run(&mut func);

        let mul_after = func.inst(trust_cg_ir::InstId(2));
        assert_eq!(
            mul_after.opcode,
            AArch64Opcode::MulRR,
            "MulRR must not fold when one operand has an unknown base value"
        );
    }

    #[test]
    fn test_nonzero_or_malformed_movz_movn_shift_does_not_seed_fold() {
        // Even architecturally valid nonzero MOVZ/MOVN shifts are outside the
        // v0.1 publication subset. The tracker must not normalize them
        // into a constant and fold downstream uses of encoder-invalid IR.
        for opcode in [AArch64Opcode::Movz, AArch64Opcode::Movn] {
            for shift in [16, 64] {
                let move_wide = MachInst::new(opcode, vec![vreg(0), imm(1), imm(shift)]);
                let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(2)]);
                let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
                let mut func = make_func_with_insts(vec![move_wide, add, ret]);

                let mut cf = ConstantFolding;
                assert!(!cf.run(&mut func));

                let add_after = func.inst(trust_cg_ir::InstId(1));
                assert_eq!(add_after.opcode, AArch64Opcode::AddRI);
            }
        }
    }

    #[test]
    fn test_malformed_movk_shift_clears_seed_before_fold() {
        let movz = MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(1)]);
        let movk = MachInst::new(AArch64Opcode::Movk, vec![vreg(0), imm(2), imm(8)]);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movz, movk, add, ret]);

        let mut cf = ConstantFolding;
        assert!(!cf.run(&mut func));

        let add_after = func.inst(trust_cg_ir::InstId(2));
        assert_eq!(add_after.opcode, AArch64Opcode::AddRI);
    }

    #[test]
    fn test_redef_invalidates_stale_constant() {
        // v0 = MovI #10
        // v0 = AddRR v0, v_unknown   -- redef v0 with a non-foldable op
        // v2 = MulRR v0, v1
        //
        // Without invalidation, the tracker would still believe v0 = 10
        // and fold the mul using the stale value.
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        // v99 is an unknown vreg; AddRR cannot be folded.
        let redef = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(0), vreg(99)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(3)]);
        let mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, redef, m1, mul, ret]);

        let mut cf = ConstantFolding;
        cf.run(&mut func);

        let mul_after = func.inst(trust_cg_ir::InstId(3));
        assert_eq!(
            mul_after.opcode,
            AArch64Opcode::MulRR,
            "MulRR must not fold after a non-foldable redefinition of v0"
        );
    }

    /// Regression for issue #366 residual: the full xxh3 empty-input
    /// avalanche mixing sequence should fold to the correct constant.
    ///
    /// The xxHash-derived avalanche and vectors are BSD-2-Clause; see
    /// `third_party/vendor/xxhash-LICENSE`.
    ///
    /// avalanche(h) = { h ^= h >> 37; h *= 0x165667919E3779F9; h ^= h >> 32 }
    ///
    /// Input h0 = 0x7c1b74eed9f584e5 (xor of secret[56..64] and secret[64..72]).
    /// Expected final value = 0x067e2f2a6d83f618.
    #[test]
    #[allow(clippy::vec_init_then_push)]
    fn test_fold_xxh3_empty_avalanche() {
        // Materialize h0 = 0x7c1b74eed9f584e5 via MOVZ + MOVK chain.
        let h0 = 0x7c1b74eed9f584e5u64 as i64;
        let mut insts = Vec::new();
        insts.push(MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg(0), imm(0x84e5)],
        ));
        insts.push(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(0), imm(0xd9f5), imm(16)],
        ));
        insts.push(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(0), imm(0x74ee), imm(32)],
        ));
        insts.push(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(0), imm(0x7c1b), imm(48)],
        ));

        // h_shr37 = h0 >> 37
        insts.push(MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(1), vreg(0), imm(37)],
        ));
        // h1 = h0 ^ h_shr37
        insts.push(MachInst::new(
            AArch64Opcode::EorRR,
            vec![vreg(2), vreg(0), vreg(1)],
        ));

        // mul_const = 0x165667919E3779F9 via MOVZ+MOVK
        insts.push(MachInst::new(
            AArch64Opcode::Movz,
            vec![vreg(3), imm(0x79F9)],
        ));
        insts.push(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(3), imm(0x9E37), imm(16)],
        ));
        insts.push(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(3), imm(0x6791), imm(32)],
        ));
        insts.push(MachInst::new(
            AArch64Opcode::Movk,
            vec![vreg(3), imm(0x1656), imm(48)],
        ));

        // h2 = h1 * mul_const
        insts.push(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg(4), vreg(2), vreg(3)],
        ));

        // h_shr32 = h2 >> 32
        insts.push(MachInst::new(
            AArch64Opcode::LsrRI,
            vec![vreg(5), vreg(4), imm(32)],
        ));
        // h3 = h2 ^ h_shr32
        insts.push(MachInst::new(
            AArch64Opcode::EorRR,
            vec![vreg(6), vreg(4), vreg(5)],
        ));

        insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));

        let mut func = make_func_with_insts(insts);

        let mut cf = ConstantFolding;
        cf.run(&mut func);

        // Expected intermediate values.
        let h_shr37 = (h0 as u64 >> 37) as i64;
        let h1 = h0 ^ h_shr37;
        let mul_const = 0x165667919E3779F9u64 as i64;
        let h2 = h1.wrapping_mul(mul_const);
        let h_shr32 = (h2 as u64 >> 32) as i64;
        let h3 = h2 ^ h_shr32;
        assert_eq!(h3 as u64, 0x067e2f2a6d83f618u64, "sanity: expected value");

        assert_eq!(materialized_value(&func, 0), Some(h0), "h0 materialized");
        assert_eq!(materialized_value(&func, 2), Some(h1), "h1 = h0 ^ (h0>>37)");
        assert_eq!(
            materialized_value(&func, 3),
            Some(mul_const),
            "mul_const materialized"
        );
        assert_eq!(
            materialized_value(&func, 4),
            Some(h2),
            "h2 = h1 * mul_const"
        );
        assert_eq!(
            materialized_value(&func, 5),
            Some(h_shr32),
            "h_shr32 = h2 >> 32"
        );
        assert_eq!(
            materialized_value(&func, 6),
            Some(h3),
            "h3 = h2 ^ (h2>>32) = {:#018x}",
            h3 as u64
        );
    }

    // ------------------------------------------------------------------
    // source_loc preservation across constant-folding rewrites (#376).
    //
    // Constant folding rewrites the destination instruction slot as a
    // MOVZ/MOVK sequence. The original source line (e.g., the `x + y`
    // expression the user wrote) must carry through to every emitted
    // materialization instruction, otherwise lldb __debug_line has a
    // gap at the folded computation.
    // ------------------------------------------------------------------

    #[test]
    fn test_source_loc_preserved_across_const_fold_narrow() {
        use trust_cg_ir::{AArch64Opcode, InstId, SourceLoc};
        let loc = SourceLoc {
            file: 3,
            line: 77,
            col: 12,
        };

        // v0 = movi #10
        // v1 = add v0, #20  (with source_loc)
        // ret
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let mut add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(20)]);
        add.source_loc = Some(loc);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, add, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        // After folding, InstId(1) is a MovI/MOVZ-style materialization.
        let folded = func.inst(InstId(1));
        assert_eq!(
            folded.source_loc,
            Some(loc),
            "const-fold must preserve source_loc on narrow materialization (issue #376)"
        );
    }

    #[test]
    fn test_source_loc_preserved_across_const_fold_wide() {
        use trust_cg_ir::{AArch64Opcode, InstId, SourceLoc};
        let loc = SourceLoc {
            file: 4,
            line: 200,
            col: 0,
        };

        // Build a large constant via MOVZ + MOVKs, then multiply to force a
        // wide (multi-instruction) materialization when the product folds.
        let movz = MachInst::new(AArch64Opcode::Movz, vec![vreg(0), imm(0x79F9)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(2)]);
        let mut mul = MachInst::new(AArch64Opcode::MulRR, vec![vreg(2), vreg(0), vreg(1)]);
        mul.source_loc = Some(loc);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![movz, m1, mul, ret]);

        let mut cf = ConstantFolding;
        assert!(cf.run(&mut func));

        // The original mul slot becomes MOVZ (low 16 bits) with source_loc.
        let folded = func.inst(InstId(2));
        assert_eq!(
            folded.source_loc,
            Some(loc),
            "const-fold must preserve source_loc on wide MOVZ slot (issue #376)"
        );

        // Any MOVK instructions appended to materialize upper 16-bit chunks
        // must also carry source_loc. Scan remaining new insts in the block.
        let block = func.block(func.entry);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::Movk {
                assert_eq!(
                    inst.source_loc,
                    Some(loc),
                    "const-fold MOVK materialization must preserve source_loc (issue #376)"
                );
            }
        }
    }

    /// REGRESSION PIN (gcc-c-torture ifcvt-onecmpl-abs-1.c / pr68376-2.c,
    /// first bad commit f09a588c): W-register constants are stored
    /// ZERO-extended in the i64 tracker, so a width-blind arithmetic-shift
    /// fold treated `asr w, w=0xFFFF_FFFF, #31` as a positive i64 shift and
    /// produced 1 instead of the architectural 0xFFFF_FFFF (-1). Combined
    /// with inlining of `n < 0 ? ~n : n` bodies, the folded self-check
    /// difference became 0xFFFF_FFFE and the programs aborted at runtime.
    #[test]
    fn w_register_asr_of_negative_sign_extends_before_shift() {
        // w2 = 0xFFFF_FFFF (-1 as a W register, tracker's zero-extended form)
        let mut constants = HashMap::new();
        constants.insert(VReg::new(2, RegClass::Gpr32), 0xFFFF_FFFFi64);
        // w3 = ASR w2, #31  — architecturally 0xFFFF_FFFF, NOT 1.
        let asr = MachInst::new(AArch64Opcode::AsrRI, vec![vreg32(3), vreg32(2), imm(31)]);
        assert_eq!(
            try_fold(&asr, &constants),
            Some((VReg::new(3, RegClass::Gpr32), 0xFFFF_FFFFi64)),
            "asr of a negative W constant must sign-extend from bit 31"
        );
    }

    /// W-register results are truncated to 32 bits before being re-stored
    /// (the tracker's canonical zero-extended form): an AddRI carry-out must
    /// not leak into bits 32..63 (which would later materialize impossible
    /// W-register MOVK@32 chains).
    #[test]
    fn w_register_add_carry_out_is_masked() {
        // w2 = 0xFFFF_FFFF; w3 = w2 + 1 = 0 (32-bit wrap, no bit-32 leak)
        let mut constants = HashMap::new();
        constants.insert(VReg::new(2, RegClass::Gpr32), 0xFFFF_FFFFi64);
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg32(3), vreg32(2), imm(1)]);
        assert_eq!(
            try_fold(&add, &constants),
            Some((VReg::new(3, RegClass::Gpr32), 0)),
            "32-bit add must wrap at bit 32"
        );
    }

    /// A W-register logical shift right of a bit31-set constant stays a
    /// 32-bit logical shift (input zero-extended, never the 64-bit pattern).
    #[test]
    fn w_register_lsr_shifts_the_32bit_value() {
        let mut constants = HashMap::new();
        constants.insert(VReg::new(2, RegClass::Gpr32), 0xFFFF_FFFFi64);
        let lsr = MachInst::new(AArch64Opcode::LsrRI, vec![vreg32(3), vreg32(2), imm(31)]);
        assert_eq!(
            try_fold(&lsr, &constants),
            Some((VReg::new(3, RegClass::Gpr32), 1))
        );
    }

    /// A W-register shift immediate above 31 is not encodable: fail closed
    /// (no fold), never evaluate with a 64-bit shift semantics.
    #[test]
    fn w_register_shift_over_31_refuses_to_fold() {
        let mut constants = HashMap::new();
        constants.insert(VReg::new(2, RegClass::Gpr32), 0xFFFF_FFFFi64);
        let asr = MachInst::new(AArch64Opcode::AsrRI, vec![vreg32(3), vreg32(2), imm(32)]);
        assert_eq!(try_fold(&asr, &constants), None);
    }
}
