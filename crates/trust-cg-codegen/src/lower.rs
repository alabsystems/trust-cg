// trust-cg-codegen/lower.rs - Machine code lowering (Phase 8: MachIR -> bytes)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Lowers a post-regalloc IrMachFunction to encoded AArch64 machine code bytes.
// This is Phase 8 of the pipeline: the final step before Mach-O emission.
//
// *** NOT instruction selection. ***
// Despite the name "lower", this module is unrelated to `trust-cg-lower/isel.rs`.
// The two modules operate at opposite ends of the compilation pipeline:
//
//   trust-cg-lower/isel.rs   (Phase 1): trust_ir SSA IR  -> AArch64 MachIR (VRegs)
//   trust-cg-codegen/lower.rs (Phase 8): AArch64 MachIR (PRegs) -> binary bytes
//
// isel.rs performs *instruction selection* — pattern-matching trust_ir opcodes to
// AArch64 instructions with virtual registers. This module performs *machine
// code emission* — encoding already-selected, register-allocated instructions
// into their binary representation. There is no code overlap between them.
//
// Responsibilities:
//   1. Expand pseudo-instructions surviving regalloc (PSEUDO_COPY, spills)
//   2. Run branch relaxation to resolve block targets
//   3. Encode every real instruction via the aarch64 encoder
//   4. Apply branch fixups (patch branch offsets after all code is laid out)
//   5. Collect relocations for external symbols (ADRP, BL, etc.)
//
// Reference: pipeline.rs::encode_function (inline encoding logic)
// Reference: relax.rs (branch relaxation pass)
// Reference: frame.rs (prologue/epilogue insertion, frame index elimination)

use crate::aarch64::encode::{EncodeError, encode_instruction};
use crate::aarch64::encoding;
use crate::frame::{self, FrameLayout};
use crate::relax;
use thiserror::Error;
use trust_cg_ir::function::MachFunction as IrMachFunction;
use trust_cg_ir::inst::{AArch64Opcode, InstFlags, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{RegClass, SP, SpecialReg, WSP, WZR, XZR, preg_class};

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors during machine code lowering.
#[derive(Debug, Error)]
pub enum LowerError {
    #[error("unsupported instruction: {0}")]
    UnsupportedInstruction(String),
    #[error("encoding failed: {0}")]
    EncodingFailed(String),
    #[error("missing operand at index {index} for {opcode:?}")]
    MissingOperand { opcode: AArch64Opcode, index: usize },
    #[error("unresolved pseudo-instruction after expansion: {0:?}")]
    UnresolvedPseudo(AArch64Opcode),
    #[error("branch relaxation failed: {0}")]
    RelaxationFailed(#[from] relax::RelaxError),
    /// FINDING #10a: frame lowering encountered a malformed/over-large input
    /// (e.g. a constant-count runtime stack allocation whose byte size
    /// overflows `u64`). Previously this aborted via `.expect()`; it now
    /// surfaces as a recoverable error up the existing Result chain.
    #[error("frame lowering failed: {0}")]
    FrameLowering(String),
    #[error("malformed machine function: {0}")]
    MalformedFunction(String),
    #[error(
        "exception-handling sidecar unsupported at code-only lowering API `{api}` for `{function}`"
    )]
    EhSidecarUnsupported { function: String, api: &'static str },
}

fn reject_eh_sidecar_drop(func: &IrMachFunction, api: &'static str) -> Result<(), LowerError> {
    if func.eh_metadata.has_eh_info() {
        return Err(LowerError::EhSidecarUnsupported {
            function: func.name.clone(),
            api,
        });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Relocation and fixup types
// ---------------------------------------------------------------------------

/// A relocation entry — records a reference to an external symbol that the
/// linker must patch.
#[derive(Debug, Clone)]
pub struct Relocation {
    /// Byte offset within the encoded code where the relocation applies.
    pub offset: u32,
    /// Relocation kind.
    pub kind: RelocKind,
    /// Symbol name (for external references).
    pub symbol: String,
    /// Addend (signed offset added to the symbol value).
    pub addend: i64,
}

/// AArch64 relocation kinds relevant to our lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocKind {
    /// ADRP page-relative relocation (ARM64_RELOC_PAGE21).
    AdrpPage21,
    /// ADD/LDR page-offset relocation (ARM64_RELOC_PAGEOFF12).
    AddPageOff12,
    /// BL call relocation (ARM64_RELOC_BRANCH26).
    Branch26,
}

/// A branch fixup — records a branch instruction whose target offset needs
/// to be patched after all code is emitted.
#[derive(Debug, Clone)]
pub struct BranchFixup {
    /// Byte offset within the encoded code where the branch instruction lives.
    pub offset: u32,
    /// The branch opcode (determines which bits to patch).
    pub opcode: AArch64Opcode,
    /// Target byte offset from the function start.
    pub target_offset: u32,
}

// ---------------------------------------------------------------------------
// LowerResult — output of the lowering pass
// ---------------------------------------------------------------------------

/// The result of lowering a function to machine code.
#[derive(Debug, Clone)]
pub struct LowerResult {
    /// Encoded machine code bytes.
    pub code: Vec<u8>,
    /// Relocation entries for the linker.
    pub relocations: Vec<Relocation>,
    /// Frame layout used (useful for unwind info generation).
    pub frame_layout: FrameLayout,
}

// ---------------------------------------------------------------------------
// Pseudo-instruction expansion
// ---------------------------------------------------------------------------

/// Opcode values used by the register allocator for pseudo-instructions.
/// These are u16 opcode values stored in regalloc MachInst, mapped back
/// to IR opcodes during the apply-allocation phase.
///
/// The regalloc uses these sentinel opcode values:
///   PSEUDO_COPY       = 0xFFE1 (from phi_elim.rs)
///   PSEUDO_SPILL_STORE = 0xFFF0 (from spill.rs)
///   PSEUDO_SPILL_LOAD  = 0xFFF1 (from spill.rs)
///
/// By the time code reaches lower.rs, these have been converted into
/// IR-level instructions with IS_PSEUDO flag and specific opcode patterns.
/// We expand any remaining pseudo-instructions here.

/// Expand pseudo-instructions in the function into real AArch64 instructions.
///
/// After register allocation and frame lowering, some pseudo-instructions
/// may survive:
///   - Phi instructions (should have been eliminated by phi_elim)
///   - StackAlloc (should have been eliminated by frame lowering)
///   - Nop (may be intentional alignment padding or placeholder)
///   - MovR where src == dst (identity copies from coalescing)
///
/// This pass rewrites or removes them.
///
/// Fail-closed: a surviving non-identity `Copy` is only converted to the GPR
/// `MovR` when BOTH operands are provably GPRs (Gpr32/Gpr64 physical registers
/// or the XZR/WZR/SP aliases). Any other operand — an FPR register, a System
/// register, or an unresolved virtual register — is a hard error: `MovR`
/// encodes as `ORR Rd, XZR, Rm`, which only names GPRs, so a blind conversion
/// silently encodes the FPR's hw index as an unrelated GPR (the FP
/// loop-carried block-arg P0 miscompile). A compile error beats a miscompile.
pub fn expand_pseudos(func: &mut IrMachFunction) -> Result<(), LowerError> {
    /// True when the operand is guaranteed to name a GPR: a physical Gpr32 /
    /// Gpr64 register or one of the special GPR aliases (SP/XZR/WZR).
    fn is_gpr_operand(operand: &MachOperand) -> bool {
        match operand {
            MachOperand::PReg(preg) => {
                matches!(preg_class(*preg), RegClass::Gpr32 | RegClass::Gpr64)
            }
            MachOperand::Special(_) => true,
            _ => false,
        }
    }

    for inst in &mut func.insts {
        if !inst.is_pseudo() {
            // Also remove identity MOV copies (dst == src).
            if inst.opcode == AArch64Opcode::MovR
                && inst.operands.len() >= 2
                && inst.operands[0] == inst.operands[1]
            {
                // Turn into NOP (will be skipped during encoding).
                inst.opcode = AArch64Opcode::Nop;
                inst.flags = InstFlags::IS_PSEUDO;
                inst.operands.clear();
            }
            continue;
        }

        match inst.opcode {
            AArch64Opcode::Phi => {
                // Phi should have been eliminated before reaching lowering.
                // Remove it by converting to NOP.
                inst.opcode = AArch64Opcode::Nop;
                inst.operands.clear();
            }
            AArch64Opcode::StackAlloc => {
                // Frame lowering handles stack allocation. Remove.
                inst.opcode = AArch64Opcode::Nop;
                inst.operands.clear();
            }
            AArch64Opcode::Copy => {
                // Copy pseudo-instruction: expand to real MovR (ORR Rd, XZR, Rm).
                // Normally lower_copies() in pipeline.rs handles this before we
                // get here, but if a Copy survives (e.g., standalone lowering
                // path), expand it now — GPR operands ONLY (see doc comment).
                if inst.operands.len() >= 2 && inst.operands[0] == inst.operands[1] {
                    // Identity copy: src == dst, convert to NOP.
                    inst.opcode = AArch64Opcode::Nop;
                    inst.operands.clear();
                } else if inst.operands.len() >= 2
                    && is_gpr_operand(&inst.operands[0])
                    && is_gpr_operand(&inst.operands[1])
                {
                    inst.opcode = AArch64Opcode::MovR;
                    inst.flags.remove(InstFlags::IS_PSEUDO);
                } else {
                    // Non-GPR or indeterminate operand class: converting to the
                    // GPR MovR would be a silent miscompile. Fail closed.
                    return Err(LowerError::EncodingFailed(format!(
                        "unlowered Copy pseudo with non-GPR or indeterminate operands \
                         {:?} in `{}`: lower_copies() must lower FPR copies to \
                         FmovFprFpr/NeonOrrV before pseudo expansion (fail-closed)",
                        inst.operands, func.name
                    )));
                }
            }
            AArch64Opcode::Nop => {
                // Already a no-op; will be skipped during encoding.
            }
            // Trap pseudo-instructions survive into lowering intentionally.
            // TrapNullIfZero is expanded below; the others are encoded as
            // BRK #1 by the encoder. Do not convert any of them to NOP.
            AArch64Opcode::TrapOverflow
            | AArch64Opcode::TrapBoundsCheck
            | AArch64Opcode::TrapBoundsCheckExact
            | AArch64Opcode::TrapNull
            | AArch64Opcode::TrapNullIfZero
            | AArch64Opcode::TrapDivZero
            | AArch64Opcode::TrapDivZeroIfZero
            | AArch64Opcode::TrapShiftRange
            | AArch64Opcode::TrapShiftRangeIfOOB
            | AArch64Opcode::TrapOverflowExact => {
                // Leave as-is; the encoder handles these directly (and rejects any
                // un-expanded exact carrier as a typed pseudo error — fail-closed).
            }
            // Reference counting pseudo-instructions should have been lowered
            // to actual call sequences before reaching this point. Leave as-is
            // for the encoder, which emits NOP (they are effectively eliminated).
            AArch64Opcode::Retain | AArch64Opcode::Release => {
                // Leave as-is; the encoder handles these directly.
            }
            other => {
                // Unknown pseudo-instruction — this is a bug. An unrecognized
                // pseudo reaching expansion means either ISel emitted something
                // we don't handle, or an earlier pass failed to lower it.
                // Log a warning with the opcode for debugging.
                eprintln!(
                    "WARNING: unrecognized pseudo-instruction {:?} in expand_pseudos, \
                     converting to NOP. This may indicate a missing expansion rule.",
                    other
                );
                inst.opcode = AArch64Opcode::Nop;
                inst.flags = InstFlags::IS_PSEUDO;
                inst.operands.clear();
            }
        }
    }

    Ok(())
}

/// Expand `TrapNullIfZero ptr` to a safe conditional runtime check.
///
/// The sequence is exactly `CBNZ ptr, +2; BRK #1`: non-null pointers skip over
/// the breakpoint, while null pointers fall through to the trap. This runs
/// before branch resolution so later block offsets include both emitted words.
pub fn expand_trap_null_if_zero(func: &mut IrMachFunction) {
    for block_idx in 0..func.blocks.len() {
        let old_insts = std::mem::take(&mut func.blocks[block_idx].insts);
        let mut new_insts = Vec::with_capacity(old_insts.len());

        for inst_id in old_insts {
            let inst_snapshot = func.inst(inst_id).clone();
            if inst_snapshot.opcode != AArch64Opcode::TrapNullIfZero {
                new_insts.push(inst_id);
                continue;
            }

            let source_loc = inst_snapshot.source_loc;
            if let Some(ptr) = inst_snapshot.operands.first().cloned() {
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::Cbnz;
                inst.operands = vec![ptr, MachOperand::Imm(2)];
                inst.flags = InstFlags::IS_BRANCH;
                inst.proof = None;
            } else {
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::TrapNull;
                inst.operands.clear();
                inst.flags = AArch64Opcode::TrapNull.default_flags();
                inst.proof = None;
                new_insts.push(inst_id);
                continue;
            }
            new_insts.push(inst_id);

            let mut trap = MachInst::new(AArch64Opcode::Brk, vec![]);
            trap.source_loc = source_loc;
            let trap_id = func.push_inst(trap);
            new_insts.push(trap_id);
        }

        func.blocks[block_idx].insts = new_insts;
    }
}

/// Expand `TrapDivZeroIfZero divisor` to a safe conditional runtime check.
///
/// The sequence is exactly `CBNZ divisor, +2; BRK #1` — the same shape as
/// [`expand_trap_null_if_zero`], because a div-zero guard is structurally a
/// "trap if the operand is zero" check. Non-zero divisors skip the breakpoint;
/// a zero divisor falls through to the trap. Runs before branch resolution so
/// later block offsets include both emitted words. If a `TrapDivZeroIfZero`
/// somehow lacks its divisor operand, it degrades to the bare `TrapDivZero`
/// panic trap (fail-safe) rather than silently vanishing.
pub fn expand_trap_div_zero_if_zero(func: &mut IrMachFunction) {
    for block_idx in 0..func.blocks.len() {
        let old_insts = std::mem::take(&mut func.blocks[block_idx].insts);
        let mut new_insts = Vec::with_capacity(old_insts.len());

        for inst_id in old_insts {
            let inst_snapshot = func.inst(inst_id).clone();
            if inst_snapshot.opcode != AArch64Opcode::TrapDivZeroIfZero {
                new_insts.push(inst_id);
                continue;
            }

            let source_loc = inst_snapshot.source_loc;
            if let Some(divisor) = inst_snapshot.operands.first().cloned() {
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::Cbnz;
                inst.operands = vec![divisor, MachOperand::Imm(2)];
                inst.flags = InstFlags::IS_BRANCH;
                inst.proof = None;
            } else {
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::TrapDivZero;
                inst.operands.clear();
                inst.flags = AArch64Opcode::TrapDivZero.default_flags();
                inst.proof = None;
                new_insts.push(inst_id);
                continue;
            }
            new_insts.push(inst_id);

            let mut trap = MachInst::new(AArch64Opcode::Brk, vec![]);
            trap.source_loc = source_loc;
            let trap_id = func.push_inst(trap);
            new_insts.push(trap_id);
        }

        func.blocks[block_idx].insts = new_insts;
    }
}

/// Expand `TrapBoundsCheckExact base, index, bound` to a safe runtime check.
///
/// The base operand is proof identity metadata. Runtime code compares the
/// index against the exact immediate bound and skips the trap when
/// `index < bound` unsigned:
///
/// ```text
///   bound in [0, 0xfff]:        CMP  index, #bound          ; B.LO +2 ; BRK #1
///   bound in [0x1000, 0xffff]:  MOVZ X16, #bound            ; CMP index, X16
///                                                           ; B.LO +2 ; BRK #1
///   bound in [0x10000, i32MAX]: MOVZ X16, #(bound & 0xffff) ; MOVK X16,
///                               #(bound >> 16), LSL #16     ; CMP index, X16
///                                                           ; B.LO +2 ; BRK #1
/// ```
///
/// The `MOVZ/MOVK` path is the companion to raising `BRIDGE_BOUNDS_PROBE_MAX_BOUND`
/// (and the AArch64 `max_exact_bound()` carrier cap) to `i32::MAX`: a bound above
/// the 12-bit `CMP` immediate cannot be a `CMP #imm12`, so it is materialized into
/// the intra-procedure scratch `X16` (free at this late, post-regalloc expansion
/// stage — the same scratch the overflow-mul carrier uses) and compared
/// register-to-register. The 64-bit `CMP` is exact for the full `usize` index the
/// Rust bounds check compares, and `MOVZ` zero-extends so `X16`'s upper bits are
/// clean. A bound outside `[0, i32::MAX]` (never produced under the caps above)
/// falls through to the `CMP #imm` path, which fails the compile closed on an
/// unencodable immediate rather than emitting a misencoded check.
pub fn expand_trap_bounds_check_exact(func: &mut IrMachFunction) {
    for block_idx in 0..func.blocks.len() {
        let old_insts = std::mem::take(&mut func.blocks[block_idx].insts);
        let mut new_insts = Vec::with_capacity(old_insts.len());

        for inst_id in old_insts {
            let inst_snapshot = func.inst(inst_id).clone();
            if inst_snapshot.opcode != AArch64Opcode::TrapBoundsCheckExact {
                new_insts.push(inst_id);
                continue;
            }

            let source_loc = inst_snapshot.source_loc;
            let Some(index) = inst_snapshot.operands.get(1).cloned() else {
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::TrapBoundsCheck;
                inst.operands.clear();
                inst.flags = AArch64Opcode::TrapBoundsCheck.default_flags();
                inst.proof = None;
                new_insts.push(inst_id);
                continue;
            };
            let Some(bound) = inst_snapshot.operands.get(2).cloned() else {
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::TrapBoundsCheck;
                inst.operands.clear();
                inst.flags = AArch64Opcode::TrapBoundsCheck.default_flags();
                inst.proof = None;
                new_insts.push(inst_id);
                continue;
            };

            // Emit the compare producing NZCV for `index <u bound`. A bound that
            // fits the 12-bit `CMP` immediate stays a single `CMP index, #bound`
            // (the reused carrier InstId). A wider bound (in [0x1000, i32::MAX])
            // is materialized into the scratch register `X16` with MOVZ (+ MOVK
            // for bits [31:16]) and compared register-to-register — the companion
            // that keeps a KEPT carrier for a large `N` a correct runtime check.
            const IMM12_MAX: i64 = 0xfff;
            const MOVW_MAX: i64 = i32::MAX as i64;
            let large_bound = match &bound {
                MachOperand::Imm(k) => (IMM12_MAX + 1..=MOVW_MAX).contains(k).then_some(*k),
                _ => None,
            };
            if let Some(k) = large_bound {
                let x16 = MachOperand::PReg(trust_cg_ir::regs::X16);
                let lo = k & 0xffff;
                let hi = (k >> 16) & 0xffff;

                // MOVZ X16, #lo — reuse the carrier InstId; zero-extends, clearing
                // bits [63:16] (bits [63:32] stay zero since k <= i32::MAX).
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::Movz;
                inst.operands = vec![x16.clone(), MachOperand::Imm(lo)];
                inst.flags = AArch64Opcode::Movz.default_flags();
                inst.proof = None;
                inst.source_loc = source_loc;
                new_insts.push(inst_id);

                // MOVK X16, #hi, LSL #16 — only when bits [31:16] are non-zero.
                if hi != 0 {
                    let mut movk = MachInst::new(
                        AArch64Opcode::Movk,
                        vec![x16.clone(), MachOperand::Imm(hi), MachOperand::Imm(16)],
                    );
                    movk.source_loc = source_loc;
                    let movk_id = func.push_inst(movk);
                    new_insts.push(movk_id);
                }

                // CMP index, X16 — 64-bit unsigned compare (width follows index).
                let mut cmp = MachInst::new(AArch64Opcode::CmpRR, vec![index, x16]);
                cmp.source_loc = source_loc;
                let cmp_id = func.push_inst(cmp);
                new_insts.push(cmp_id);
            } else {
                // A REGISTER bound (`index <u len` for a dynamically-sized
                // slice/Vec) compares register-to-register; only an immediate
                // bound uses CmpRI. Emitting CmpRI with a VReg operand would
                // encode the register NUMBER as the compare immediate — a
                // silently wrong runtime check on a memory-safety guard, which
                // is the worst possible place for one.
                let bound_is_reg = matches!(bound, MachOperand::VReg(_) | MachOperand::PReg(_));
                let inst = func.inst_mut(inst_id);
                inst.opcode = if bound_is_reg {
                    AArch64Opcode::CmpRR
                } else {
                    AArch64Opcode::CmpRI
                };
                inst.operands = vec![index, bound];
                inst.flags = inst.opcode.default_flags();
                inst.proof = None;
                new_insts.push(inst_id);
            }

            let mut skip_trap = MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(i64::from(trust_cg_ir::CondCode::LO.encoding())),
                    MachOperand::Imm(2),
                ],
            );
            skip_trap.source_loc = source_loc;
            let skip_id = func.push_inst(skip_trap);
            new_insts.push(skip_id);

            let mut trap = MachInst::new(AArch64Opcode::Brk, vec![]);
            trap.source_loc = source_loc;
            let trap_id = func.push_inst(trap);
            new_insts.push(trap_id);
        }

        func.blocks[block_idx].insts = new_insts;
    }
}

/// Expand `TrapShiftRangeIfOOB amount, bitwidth` to a safe runtime check.
///
/// Runtime code compares the shift amount against the immediate bitwidth and
/// skips the trap when `amount < bitwidth` unsigned: `CMP amount, #bitwidth;
/// B.LO +2; BRK #1` — the same shape as [`expand_trap_bounds_check_exact`],
/// because a shift-range guard is structurally a `value < bound` check. If a
/// `TrapShiftRangeIfOOB` somehow lacks its operands, it degrades to the bare
/// `TrapShiftRange` panic trap (fail-safe) rather than silently vanishing.
pub fn expand_trap_shift_range_if_oob(func: &mut IrMachFunction) {
    for block_idx in 0..func.blocks.len() {
        let old_insts = std::mem::take(&mut func.blocks[block_idx].insts);
        let mut new_insts = Vec::with_capacity(old_insts.len());

        for inst_id in old_insts {
            let inst_snapshot = func.inst(inst_id).clone();
            if inst_snapshot.opcode != AArch64Opcode::TrapShiftRangeIfOOB {
                new_insts.push(inst_id);
                continue;
            }

            let source_loc = inst_snapshot.source_loc;
            let amount = inst_snapshot.operands.first().cloned();
            let bitwidth = inst_snapshot.operands.get(1).cloned();
            let (Some(amount), Some(bitwidth)) = (amount, bitwidth) else {
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::TrapShiftRange;
                inst.operands.clear();
                inst.flags = AArch64Opcode::TrapShiftRange.default_flags();
                inst.proof = None;
                new_insts.push(inst_id);
                continue;
            };

            let inst = func.inst_mut(inst_id);
            inst.opcode = AArch64Opcode::CmpRI;
            inst.operands = vec![amount, bitwidth];
            inst.flags = AArch64Opcode::CmpRI.default_flags();
            inst.proof = None;
            new_insts.push(inst_id);

            let mut skip_trap = MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(i64::from(trust_cg_ir::CondCode::LO.encoding())),
                    MachOperand::Imm(2),
                ],
            );
            skip_trap.source_loc = source_loc;
            let skip_id = func.push_inst(skip_trap);
            new_insts.push(skip_id);

            let mut trap = MachInst::new(AArch64Opcode::Brk, vec![]);
            trap.source_loc = source_loc;
            let trap_id = func.push_inst(trap);
            new_insts.push(trap_id);
        }

        func.blocks[block_idx].insts = new_insts;
    }
}

/// Expand `TrapOverflowExact lhs, rhs, Imm(op_tag)` to a safe runtime overflow check.
///
/// Unlike the bounds/null/div/shift carriers (which re-check a single operand), a KEPT overflow
/// carrier RE-DERIVES the overflow condition from its own `lhs`/`rhs` by RECOMPUTING the NZCV flags
/// — the original `ADDS/SUBS` that set those flags is GONE because the value op is a SEPARATE plain
/// `ADD/SUB`. The expansion is therefore a flag-only `ADDS/SUBS` to a zero register + the matching
/// inverse-condition skip + `BRK #1`:
///
/// ```text
///     ADDS/SUBS  ZR, lhs, rhs        ; recompute NZCV, discard value (ZR = XZR/WZR by width)
///     B.<skip>   +2                  ; skip the trap iff NO overflow
///     BRK #1                         ; trap on overflow
/// ```
///
/// The flag-setter (`ADDS` vs `SUBS`) and skip condition come from the op-tag:
///   * SignedAdd / SignedSub  : overflow = V set      => skip on `VC` (V clear)
///   * UnsignedAdd            : overflow = carry set   => skip on `LO` (carry clear)
///   * UnsignedSub            : overflow = borrow      => skip on `HS` (no borrow / carry set)
///
/// The zero-register width (`XZR` for 64-bit, `WZR` for 32-bit) is selected from the tag's width so
/// the recompute matches the original operation width. A `TrapOverflowExact` with a missing/malformed
/// tag, or missing operands, degrades to the bare `TrapOverflow` panic pseudo (fail-safe) rather than
/// silently vanishing — it never becomes a no-op that lets an actual overflow through.
///
/// # Multiplication carrier (task #30, width 64 only)
///
/// `MUL`/`SMULH`/`UMULH` set NO flags, so a mul carrier CANNOT use the `ADDS/SUBS` flag-recompute.
/// Instead it expands to the canonical AArch64 mul-high overflow-detection idiom (the same one
/// `select_checked_smul`/`select_checked_umul` use), with the final `CSET` replaced by a
/// skip-on-no-overflow conditional branch:
///
/// ```text
///   SignedMul@64:
///     MUL   X16, lhs, rhs        ; low  64 bits of signed product
///     SMULH X17, lhs, rhs        ; high 64 bits of signed product
///     ASR   X16, X16, #63        ; sign-extension of the low half (reuses X16)
///     CMP   X17, X16             ; Z=1 iff hi == sext(lo)  => NO overflow
///     B.EQ  +2                   ; skip the trap iff NO overflow
///     BRK   #1                   ; trap on overflow
///
///   UnsignedMul@64:
///     UMULH X16, lhs, rhs        ; high 64 bits of unsigned product (low half unneeded)
///     CMP   X16, #0              ; Z=1 iff hi == 0          => NO overflow
///     B.EQ  +2                   ; skip the trap iff NO overflow
///     BRK   #1                   ; trap on overflow
/// ```
///
/// Detection is arithmetically EXACT: `i64::MIN * -1` overflows (hi=0, sext(lo)=-1, hi != sext),
/// `u64::MAX * 2` overflows (hi != 0), and small products never trap (hi == sext(lo) / hi == 0). The
/// skip condition is `EQ` (Z set = equal = NO overflow), the INVERSE of the add/sub `VC/LO/HS`.
///
/// This expansion runs POST-regalloc, where no fresh virtual register can be allocated, so it uses
/// the reserved non-allocatable scratch GPRs `X16`/`X17` (IP0/IP1). They are excluded from the
/// allocatable set, so writing them here cannot clobber a live allocated value; and a carrier site is
/// not inside an indirect-call/veneer sequence (the only other X16/X17 user), so they are free.
pub fn expand_trap_overflow_exact(func: &mut IrMachFunction) {
    use trust_cg_ir::overflow_tag::{OverflowOp, unpack_overflow_tag};
    use trust_cg_ir::regs::{X16, X17};

    for block_idx in 0..func.blocks.len() {
        let old_insts = std::mem::take(&mut func.blocks[block_idx].insts);
        let mut new_insts = Vec::with_capacity(old_insts.len());

        for inst_id in old_insts {
            let inst_snapshot = func.inst(inst_id).clone();
            if inst_snapshot.opcode != AArch64Opcode::TrapOverflowExact {
                new_insts.push(inst_id);
                continue;
            }

            let source_loc = inst_snapshot.source_loc;
            let lhs = inst_snapshot.operands.first().cloned();
            let rhs = inst_snapshot.operands.get(1).cloned();
            let tag = match inst_snapshot.operands.get(2) {
                Some(MachOperand::Imm(t)) => Some(*t),
                _ => None,
            };
            let decoded = tag.and_then(unpack_overflow_tag);
            let (Some(lhs), Some(rhs), Some((op, width))) = (lhs, rhs, decoded) else {
                // Fail-safe: an un-decodable carrier becomes a bare trap, never a NOP.
                let inst = func.inst_mut(inst_id);
                inst.opcode = AArch64Opcode::TrapOverflow;
                inst.operands.clear();
                inst.flags = AArch64Opcode::TrapOverflow.default_flags();
                inst.proof = None;
                new_insts.push(inst_id);
                continue;
            };

            // ---- Multiplication carrier (task #30): MUL/SMULH/UMULH mul-high idiom ----
            //
            // Mul-high opcodes set NO flags, so we CANNOT reuse the ADDS/SUBS flag recompute below.
            // We must branch FIRST (before is_sub()), or a mul tag would fall into the AddsRR branch
            // and silently expand as a bogus add-overflow check (FAIL-OPEN miscompile). The KEPT
            // expansion re-derives the overflow condition exactly and traps on a genuine overflow.
            if op.is_mul() {
                // Mul carriers are produced at width 64 ONLY (SMULH/UMULH are 64-bit-result-only).
                // A malformed width-32 mul tag must NOT silently expand with a wrong width — fail
                // safe to a bare trap (the obligation still traps on a genuine overflow).
                if width != 64 {
                    let inst = func.inst_mut(inst_id);
                    inst.opcode = AArch64Opcode::TrapOverflow;
                    inst.operands.clear();
                    inst.flags = AArch64Opcode::TrapOverflow.default_flags();
                    inst.proof = None;
                    new_insts.push(inst_id);
                    continue;
                }

                let x16 = MachOperand::PReg(X16);
                let x17 = MachOperand::PReg(X17);

                // Emit a real instruction by reusing `inst_id` for the FIRST op, then pushing the
                // remainder. Helper to push a fresh instruction with the carrier's source loc.
                let push_inst = |func: &mut IrMachFunction,
                                 new_insts: &mut Vec<_>,
                                 opcode: AArch64Opcode,
                                 operands: Vec<MachOperand>| {
                    let mut mi = MachInst::new(opcode, operands);
                    mi.source_loc = source_loc;
                    let id = func.push_inst(mi);
                    new_insts.push(id);
                };

                match op {
                    OverflowOp::SignedMul => {
                        // MUL X16, lhs, rhs — low 64 bits of the signed product.
                        let first = func.inst_mut(inst_id);
                        first.opcode = AArch64Opcode::MulRR;
                        first.operands = vec![x16.clone(), lhs.clone(), rhs.clone()];
                        first.flags = AArch64Opcode::MulRR.default_flags();
                        first.proof = None;
                        new_insts.push(inst_id);
                        // SMULH X17, lhs, rhs — high 64 bits of the signed product.
                        push_inst(
                            func,
                            &mut new_insts,
                            AArch64Opcode::Smulh,
                            vec![x17.clone(), lhs, rhs],
                        );
                        // ASR X16, X16, #63 — sign-extension of the low half (reuses X16).
                        push_inst(
                            func,
                            &mut new_insts,
                            AArch64Opcode::AsrRI,
                            vec![x16.clone(), x16.clone(), MachOperand::Imm(63)],
                        );
                        // CMP X17, X16 — Z=1 iff hi == sext(lo) => NO signed overflow.
                        push_inst(func, &mut new_insts, AArch64Opcode::CmpRR, vec![x17, x16]);
                    }
                    OverflowOp::UnsignedMul => {
                        // UMULH X16, lhs, rhs — high 64 bits of the unsigned product (low unneeded).
                        let first = func.inst_mut(inst_id);
                        first.opcode = AArch64Opcode::Umulh;
                        first.operands = vec![x16.clone(), lhs, rhs];
                        first.flags = AArch64Opcode::Umulh.default_flags();
                        first.proof = None;
                        new_insts.push(inst_id);
                        // CMP X16, #0 — Z=1 iff hi == 0 => NO unsigned overflow.
                        push_inst(
                            func,
                            &mut new_insts,
                            AArch64Opcode::CmpRI,
                            vec![x16, MachOperand::Imm(0)],
                        );
                    }
                    // Unreachable: is_mul() is true here only for the two mul variants.
                    _ => unreachable!("is_mul() implies a mul OverflowOp variant"),
                }

                // B.EQ +2 — skip the trap iff Z is set (NO overflow). Distinct from the add/sub
                // VC/LO/HS: mul overflow is detected by an equality compare, so the skip-on-no-
                // overflow condition is EQ (Z == 1).
                let mut skip_trap = MachInst::new(
                    AArch64Opcode::BCond,
                    vec![
                        MachOperand::Imm(i64::from(trust_cg_ir::CondCode::EQ.encoding())),
                        MachOperand::Imm(2),
                    ],
                );
                skip_trap.source_loc = source_loc;
                let skip_id = func.push_inst(skip_trap);
                new_insts.push(skip_id);

                let mut trap = MachInst::new(AArch64Opcode::Brk, vec![]);
                trap.source_loc = source_loc;
                let trap_id = func.push_inst(trap);
                new_insts.push(trap_id);

                continue;
            }

            // Flag-setter + width-correct zero-register destination.
            let flag_opc = if op.is_sub() {
                AArch64Opcode::SubsRR
            } else {
                AArch64Opcode::AddsRR
            };
            let zero_dst = if width == 32 {
                MachOperand::Special(SpecialReg::WZR)
            } else {
                MachOperand::Special(SpecialReg::XZR)
            };
            // Skip condition = NO overflow. (Mul is handled by the is_mul() branch above, which
            // `continue`s, so only add/sub reach here.)
            let skip_cc = match op {
                OverflowOp::SignedAdd | OverflowOp::SignedSub => trust_cg_ir::CondCode::VC,
                OverflowOp::UnsignedAdd => trust_cg_ir::CondCode::LO,
                OverflowOp::UnsignedSub => trust_cg_ir::CondCode::HS,
                OverflowOp::SignedMul | OverflowOp::UnsignedMul => {
                    unreachable!("mul carriers are expanded by the is_mul() branch above")
                }
            };

            let inst = func.inst_mut(inst_id);
            inst.opcode = flag_opc;
            inst.operands = vec![zero_dst, lhs, rhs];
            inst.flags = flag_opc.default_flags();
            inst.proof = None;
            new_insts.push(inst_id);

            let mut skip_trap = MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    MachOperand::Imm(i64::from(skip_cc.encoding())),
                    MachOperand::Imm(2),
                ],
            );
            skip_trap.source_loc = source_loc;
            let skip_id = func.push_inst(skip_trap);
            new_insts.push(skip_id);

            let mut trap = MachInst::new(AArch64Opcode::Brk, vec![]);
            trap.source_loc = source_loc;
            let trap_id = func.push_inst(trap);
            new_insts.push(trap_id);
        }

        func.blocks[block_idx].insts = new_insts;
    }
}

// ---------------------------------------------------------------------------
// Single instruction encoding
// ---------------------------------------------------------------------------

/// Encode a single IR instruction to a 32-bit AArch64 instruction word.
///
/// Delegates to the unified encoder (`encode_instruction` from `aarch64::encode`)
/// for all opcodes it supports. Handles pipeline-specific opcodes locally:
///
/// - **Adrp / AddPCRel**: Emit with imm=0; relocations will patch the offset.
///   The unified encoder uses the actual immediate, which is wrong for the
///   pipeline's relocation-based patching model.
/// - **BicRR, Csinc, Csinv, Csneg**: Also implemented in the unified
///   encoder (encode.rs). Retained here for pipeline-specific operand
///   conventions and pre-validation.
/// - **LdrRO, StrRO**: Register-offset encoding. Also in the unified encoder;
///   retained here for pipeline-specific integer-only pre-validation.
/// - **LdrGot, LdrTlvp**: 64-bit GOT/TLV loads. Also in the unified encoder;
///   retained here for pipeline-specific relocation handling.
///
/// Pre-validates operands (#98, #105) before delegation to catch malformed
/// instructions early rather than silently encoding wrong values.
fn encode_inst(inst: &MachInst) -> Result<u32, LowerError> {
    // Helper: extract physical register hardware encoding from operand.
    // Returns an error for non-register operands instead of silently
    // defaulting to XZR (reg 31), which would produce wrong code (#98).
    let preg_hw = |idx: usize| -> Result<u32, LowerError> {
        if idx >= inst.operands.len() {
            return Err(LowerError::MissingOperand {
                opcode: inst.opcode,
                index: idx,
            });
        }
        match &inst.operands[idx] {
            MachOperand::PReg(p) => Ok(p.hw_enc() as u32),
            MachOperand::Special(s) => match s {
                SpecialReg::SP | SpecialReg::XZR | SpecialReg::WZR => Ok(31),
            },
            other => Err(LowerError::EncodingFailed(format!(
                "expected register operand at index {} for {:?}, got {:?}",
                idx, inst.opcode, other
            ))),
        }
    };

    let pair_transfer_hw = |idx: usize| -> Result<u32, LowerError> {
        if idx >= inst.operands.len() {
            return Err(LowerError::MissingOperand {
                opcode: inst.opcode,
                index: idx,
            });
        }
        match &inst.operands[idx] {
            MachOperand::PReg(p) if *p != SP && *p != WSP && *p != XZR && *p != WZR => {
                Ok(p.hw_enc() as u32)
            }
            other => Err(LowerError::EncodingFailed(format!(
                "expected pair transfer register operand at index {} for {:?}, got {:?}",
                idx, inst.opcode, other
            ))),
        }
    };

    let pair_base_hw = |idx: usize| -> Result<u32, LowerError> {
        if idx >= inst.operands.len() {
            return Err(LowerError::MissingOperand {
                opcode: inst.opcode,
                index: idx,
            });
        }
        match &inst.operands[idx] {
            MachOperand::PReg(p) if *p != WSP && *p != XZR && *p != WZR => Ok(p.hw_enc() as u32),
            MachOperand::Special(SpecialReg::SP) => Ok(31),
            other => Err(LowerError::EncodingFailed(format!(
                "expected pair base register operand at index {} for {:?}, got {:?}",
                idx, inst.opcode, other
            ))),
        }
    };

    let pair_offset_imm = |idx: usize| -> Result<(), LowerError> {
        match inst.operands.get(idx) {
            Some(MachOperand::Imm(_)) | None => Ok(()),
            Some(other) => Err(LowerError::EncodingFailed(format!(
                "expected pair offset immediate operand at index {} for {:?}, got {:?}",
                idx, inst.opcode, other
            ))),
        }
    };

    let single_writeback_transfer_hw = |idx: usize| -> Result<u32, LowerError> {
        if idx >= inst.operands.len() {
            return Err(LowerError::MissingOperand {
                opcode: inst.opcode,
                index: idx,
            });
        }
        match &inst.operands[idx] {
            MachOperand::PReg(p)
                if trust_cg_ir::regs::preg_class(*p) == trust_cg_ir::regs::RegClass::Gpr64
                    && *p != SP =>
            {
                Ok(p.hw_enc() as u32)
            }
            MachOperand::Special(SpecialReg::XZR) => Ok(31),
            other => Err(LowerError::EncodingFailed(format!(
                "expected 64-bit GPR or XZR transfer operand at index {} for {:?}, got {:?}",
                idx, inst.opcode, other
            ))),
        }
    };

    let single_writeback_base_hw = |idx: usize| -> Result<u32, LowerError> {
        if idx >= inst.operands.len() {
            return Err(LowerError::MissingOperand {
                opcode: inst.opcode,
                index: idx,
            });
        }
        match &inst.operands[idx] {
            MachOperand::PReg(p)
                if trust_cg_ir::regs::preg_class(*p) == trust_cg_ir::regs::RegClass::Gpr64
                    && *p != XZR =>
            {
                Ok(p.hw_enc() as u32)
            }
            MachOperand::Special(SpecialReg::SP) => Ok(31),
            other => Err(LowerError::EncodingFailed(format!(
                "expected 64-bit GPR or SP writeback base operand at index {} for {:?}, got {:?}",
                idx, inst.opcode, other
            ))),
        }
    };

    let single_writeback_imm9 = |idx: usize| -> Result<(), LowerError> {
        match inst.operands.get(idx) {
            Some(MachOperand::Imm(v)) if (-256..=255).contains(v) => Ok(()),
            Some(MachOperand::Imm(v)) => Err(LowerError::EncodingFailed(format!(
                "single-register writeback immediate at index {} for {:?} out of signed imm9 range: {}",
                idx, inst.opcode, v
            ))),
            Some(other) => Err(LowerError::EncodingFailed(format!(
                "expected signed imm9 operand at index {} for {:?}, got {:?}",
                idx, inst.opcode, other
            ))),
            None => Err(LowerError::MissingOperand {
                opcode: inst.opcode,
                index: idx,
            }),
        }
    };

    let reject_single_writeback_overlap =
        |transfer_idx: usize, base_idx: usize| -> Result<(), LowerError> {
            let transfer_hw = single_writeback_transfer_hw(transfer_idx)?;
            let base_hw = single_writeback_base_hw(base_idx)?;
            if base_hw != 31 && transfer_hw == base_hw {
                return Err(LowerError::EncodingFailed(format!(
                    "single-register writeback transfer/base overlap is unpredictable for {:?}",
                    inst.opcode
                )));
            }
            Ok(())
        };

    // Helper: extract immediate value from operand.
    let imm_val = |idx: usize| -> i64 {
        inst.operands
            .get(idx)
            .and_then(|op| {
                if let MachOperand::Imm(v) = op {
                    Some(*v)
                } else {
                    None
                }
            })
            .unwrap_or(0)
    };

    // Helper: determine if the instruction operates on 64-bit registers.
    // Uses preg_class() to correctly distinguish W-registers (Gpr32, sf=0)
    // from X-registers (Gpr64, sf=1). The previous implementation used
    // is_gpr() which only covers X-registers (encoding 0-31), causing
    // W-registers (encoding 32-63) to fall through to the default (true),
    // producing wrong sf bit for BicRR, Csinc, Csinv, Csneg, Movn (#173).
    let is_64bit = |idx: usize| -> bool {
        match inst.operands.get(idx) {
            Some(MachOperand::PReg(p)) => match trust_cg_ir::regs::preg_class(*p) {
                trust_cg_ir::regs::RegClass::Gpr32 => false,
                _ => true,
            },
            _ => true,
        }
    };

    // Helper: determine AArch64 ftype field from an FPR operand's register class.
    // Returns 0b00 for single (S-regs), 0b01 for double (D-regs).
    // Returns an error if the operand is not an FPR, instead of silently
    // defaulting to Double precision which masks encoding bugs (#105).
    let fp_size = |idx: usize| -> Result<u32, LowerError> {
        match inst.operands.get(idx) {
            Some(MachOperand::PReg(p)) => {
                let class = trust_cg_ir::regs::preg_class(*p);
                match class {
                    trust_cg_ir::regs::RegClass::Fpr32 => Ok(0b00), // single
                    trust_cg_ir::regs::RegClass::Fpr64 => Ok(0b01), // double
                    trust_cg_ir::regs::RegClass::Fpr128 => Ok(0b01), // treat as double for data-processing
                    _ => Err(LowerError::EncodingFailed(format!(
                        "expected FPR operand at index {} for {:?}, got GPR/other class {:?}",
                        idx, inst.opcode, class
                    ))),
                }
            }
            Some(other) => Err(LowerError::EncodingFailed(format!(
                "expected FPR register operand at index {} for {:?}, got {:?}",
                idx, inst.opcode, other
            ))),
            None => Err(LowerError::MissingOperand {
                opcode: inst.opcode,
                index: idx,
            }),
        }
    };

    match inst.opcode {
        // =================================================================
        // Pipeline-specific: ADRP and AddPCRel emit with imm=0 for
        // relocation patching. The unified encoder uses the actual
        // immediate, which doesn't work in the relocation model.
        // =================================================================
        AArch64Opcode::Adrp => {
            // ADRP Xd, <page>
            // Emit with imm=0; relocation will patch it.
            let rd = preg_hw(0)?;
            Ok((1u32 << 31) | (0b10000u32 << 24) | rd)
        }
        AArch64Opcode::AddPCRel => {
            // ADD Xd, Xn, #pageoff — page offset portion of ADRP+ADD pair.
            // Emit as ADD with imm=0; relocation will patch the offset.
            let sf = 1u32;
            Ok(encoding::encode_add_sub_imm(
                sf,
                0,
                0,
                0,
                0, // imm will be patched by relocation
                preg_hw(1)?,
                preg_hw(0)?,
            ))
        }

        // =================================================================
        // Opcodes also available in the unified encoder but retained
        // here for pipeline-specific operand conventions and pre-validation.
        // =================================================================
        AArch64Opcode::BicRR => {
            // BIC Rd, Rn, Rm = AND Rd, Rn, NOT(Rm)
            let sf = if is_64bit(0) { 1 } else { 0 };
            Ok(encoding::encode_logical_shifted_reg(
                sf,
                0b00,
                1,
                0,
                preg_hw(2)?,
                0,
                preg_hw(1)?,
                preg_hw(0)?,
            ))
        }
        AArch64Opcode::Csinc => {
            // CSINC Xd, Xn, Xm, cond
            let sf = if is_64bit(0) { 1u32 } else { 0u32 };
            let rd = preg_hw(0)?;
            let rn = preg_hw(1)?;
            let rm = preg_hw(2)?;
            let cond = imm_val(3) as u32 & 0xF;
            Ok((sf << 31)
                | (0b11010100 << 21)
                | (rm << 16)
                | (cond << 12)
                | (0b01 << 10)
                | (rn << 5)
                | rd)
        }
        AArch64Opcode::Csinv => {
            // CSINV Xd, Xn, Xm, cond
            let sf = if is_64bit(0) { 1u32 } else { 0u32 };
            let rd = preg_hw(0)?;
            let rn = preg_hw(1)?;
            let rm = preg_hw(2)?;
            let cond = imm_val(3) as u32 & 0xF;
            Ok(
                ((sf << 31) | (0b10 << 29) | (0b11010100 << 21) | (rm << 16) | (cond << 12))
                    | (rn << 5)
                    | rd,
            )
        }
        AArch64Opcode::Csneg => {
            // CSNEG Xd, Xn, Xm, cond
            let sf = if is_64bit(0) { 1u32 } else { 0u32 };
            let rd = preg_hw(0)?;
            let rn = preg_hw(1)?;
            let rm = preg_hw(2)?;
            let cond = imm_val(3) as u32 & 0xF;
            Ok((sf << 31)
                | (0b10 << 29)
                | (0b11010100 << 21)
                | (rm << 16)
                | (cond << 12)
                | (0b01 << 10)
                | (rn << 5)
                | rd)
        }
        // =================================================================
        // Pipeline-specific: integer-only register-offset loads/stores.
        // The unified encoder handles FPR paths differently via encoding_mem.
        // Keep local for integer pipeline consistency.
        // =================================================================
        AArch64Opcode::LdrRO => {
            let sf = if is_64bit(0) { 1u32 } else { 0u32 };
            let rt = preg_hw(0)?;
            let rn = preg_hw(1)?;
            let rm = preg_hw(2)?;
            let size = if sf == 1 { 0b11u32 } else { 0b10u32 };
            let (option, s) = if inst.operands.len() > 3 {
                let packed = imm_val(3) as u32;
                ((packed >> 1) & 0b111, packed & 1)
            } else {
                (0b011u32, 0u32)
            };
            Ok(((size << 30) | (0b111 << 27))
                | (0b01 << 22)
                | (1 << 21)
                | (rm << 16)
                | (option << 13)
                | (s << 12)
                | (0b10 << 10)
                | (rn << 5)
                | rt)
        }
        AArch64Opcode::StrRO => {
            let sf = if is_64bit(0) { 1u32 } else { 0u32 };
            let rt = preg_hw(0)?;
            let rn = preg_hw(1)?;
            let rm = preg_hw(2)?;
            let size = if sf == 1 { 0b11u32 } else { 0b10u32 };
            let (option, s) = if inst.operands.len() > 3 {
                let packed = imm_val(3) as u32;
                ((packed >> 1) & 0b111, packed & 1)
            } else {
                (0b011u32, 0u32)
            };
            Ok(((size << 30) | (0b111 << 27))
                | (1 << 21)
                | (rm << 16)
                | (option << 13)
                | (s << 12)
                | (0b10 << 10)
                | (rn << 5)
                | rt)
        }

        // =================================================================
        // Pipeline-specific: GOT/TLV loads always use 64-bit unsigned offset.
        // =================================================================
        AArch64Opcode::LdrGot => {
            let rd = preg_hw(0)?;
            let rn = preg_hw(1)?;
            let offset = if inst.operands.len() > 2 {
                imm_val(2)
            } else {
                0
            };
            let scaled = (offset / 8) as u32 & 0xFFF;
            Ok(encoding::encode_load_store_ui(
                0b11, 0, 0b01, scaled, rn, rd,
            ))
        }
        AArch64Opcode::LdrTlvp => {
            let rd = preg_hw(0)?;
            let rn = preg_hw(1)?;
            let offset = if inst.operands.len() > 2 {
                imm_val(2)
            } else {
                0
            };
            let scaled = (offset / 8) as u32 & 0xFFF;
            Ok(encoding::encode_load_store_ui(
                0b11, 0, 0b01, scaled, rn, rd,
            ))
        }

        // LdrGottprel — ELF initial-exec GOT-TPREL load: only encodable via
        // the module emitter's fixup interception (placeholder skeleton +
        // `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC`); fail closed here.
        AArch64Opcode::LdrGottprel => Err(LowerError::EncodingFailed(
            "LdrGottprel requires ELF TLSIE fixup interception (module emitter); \
             no direct encoding exists"
                .to_string(),
        )),

        // =================================================================
        // FP instructions: pre-validate operand types (#105) then delegate.
        // The unified encoder silently defaults non-FPR operands to Double
        // precision, masking bugs. We validate first to preserve stricter
        // error checking, then delegate to encode_instruction.
        // =================================================================
        AArch64Opcode::FaddRR
        | AArch64Opcode::FsubRR
        | AArch64Opcode::FmulRR
        | AArch64Opcode::FdivRR
        | AArch64Opcode::FmaddRR => {
            // Validate that operand 0 is an FPR before delegating.
            fp_size(0)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::FnegRR | AArch64Opcode::FabsRR | AArch64Opcode::FsqrtRR => {
            fp_size(0)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Fcmp => {
            fp_size(0)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::FcvtzsRR | AArch64Opcode::FcvtzuRR => {
            // Source is FPR (operand 1)
            fp_size(1)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::ScvtfRR | AArch64Opcode::UcvtfRR => {
            // Destination is FPR (operand 0)
            fp_size(0)?;
            encode_instruction(inst).map_err(map_encode_error)
        }

        // =================================================================
        // Integer instructions with register operands: pre-validate that
        // register operands are actual registers (#98), then delegate.
        // The unified encoder defaults non-register operands to XZR (31),
        // which silently produces wrong code.
        // =================================================================
        AArch64Opcode::AddRR | AArch64Opcode::SubRR => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::MulRR | AArch64Opcode::SDiv | AArch64Opcode::UDiv => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::AndRR
        | AArch64Opcode::OrrRR
        | AArch64Opcode::EorRR
        | AArch64Opcode::OrnRR => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::LslRR | AArch64Opcode::LsrRR | AArch64Opcode::AsrRR => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Neg => {
            preg_hw(0)?;
            preg_hw(1)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::CmpRR => {
            preg_hw(0)?;
            preg_hw(1)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Tst => {
            // TST has exactly two legal shapes after register allocation:
            // `TST Rn, Rm` and `TST Rn, #logical-imm`.  The old shared CmpRR
            // arm unconditionally called `preg_hw(1)`, rejecting every legal
            // immediate produced by AndCmpFuse before the unified encoder had
            // a chance to validate and encode it.
            if inst.operands.len() != 2 {
                return Err(LowerError::EncodingFailed(format!(
                    "Tst expects exactly 2 operands, got {}",
                    inst.operands.len()
                )));
            }
            preg_hw(0)?;
            if !matches!(inst.operands.get(1), Some(MachOperand::Imm(_))) {
                preg_hw(1)?;
            }
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::MovR => {
            preg_hw(0)?;
            // Operand 1 may be Special(SP) — that's fine, preg_hw handles it
            if inst.operands.len() >= 2 {
                preg_hw(1)?;
            }
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Sxtw
        | AArch64Opcode::Uxtw
        | AArch64Opcode::Sxtb
        | AArch64Opcode::Sxth
        | AArch64Opcode::Uxtb
        | AArch64Opcode::Uxth => {
            preg_hw(0)?;
            preg_hw(1)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::AddsRR | AArch64Opcode::SubsRR => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Csel => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Msub => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            if inst.operands.len() > 3 {
                preg_hw(3)?;
            }
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Smull | AArch64Opcode::Umull => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Blr | AArch64Opcode::Br => {
            preg_hw(0)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::Cbz | AArch64Opcode::Cbnz => {
            preg_hw(0)?;
            encode_instruction(inst).map_err(map_encode_error)
        }

        // LDR/STR with immediate offset — validate base register (#98)
        AArch64Opcode::LdrRI | AArch64Opcode::StrRI => {
            preg_hw(0)?;
            preg_hw(1)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::LdrPreIndex
        | AArch64Opcode::StrPreIndex
        | AArch64Opcode::LdrPostIndex
        | AArch64Opcode::StrPostIndex => {
            reject_single_writeback_overlap(0, 1)?;
            single_writeback_imm9(2)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::LdrbRI
        | AArch64Opcode::LdrhRI
        | AArch64Opcode::LdrsbRI
        | AArch64Opcode::LdrshRI
        | AArch64Opcode::StrbRI
        | AArch64Opcode::StrhRI => {
            preg_hw(0)?;
            preg_hw(1)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::StpRI | AArch64Opcode::LdpRI => {
            pair_transfer_hw(0)?;
            pair_transfer_hw(1)?;
            pair_base_hw(2)?;
            pair_offset_imm(3)?;
            encode_instruction(inst).map_err(map_encode_error)
        }
        AArch64Opcode::StpPreIndex | AArch64Opcode::LdpPostIndex => {
            preg_hw(0)?;
            preg_hw(1)?;
            preg_hw(2)?;
            // FAIL-CLOSED (mirrors `reject_single_writeback_overlap` for the
            // single-register forms, and the NEON pair path): for a WRITEBACK
            // pair the architecture makes `Rn == Rt` or `Rn == Rt2` CONSTRAINED
            // UNPREDICTABLE, and a load pair additionally forbids `Rt == Rt2`.
            // Liveness already prevents this — the base and both transfer
            // registers are simultaneously live at the instruction, and
            // `effects::fill_operand_roles` models the base as DefUse so the
            // allocator can never overlap them (audited over 6590 emitted
            // writeback instructions: zero overlaps). This check exists so a
            // future pass emitting these opcodes gets a hard compile error
            // instead of silently-unpredictable bytes.
            let base_hw = single_writeback_base_hw(2)?;
            if base_hw != 31 {
                for t in [0usize, 1] {
                    if single_writeback_transfer_hw(t)? == base_hw {
                        return Err(LowerError::EncodingFailed(format!(
                            "pair writeback transfer/base overlap is unpredictable for {:?}",
                            inst.opcode
                        )));
                    }
                }
            }
            if inst.opcode == AArch64Opcode::LdpPostIndex {
                let (t0, t1) = (
                    single_writeback_transfer_hw(0)?,
                    single_writeback_transfer_hw(1)?,
                );
                if t0 != 31 && t0 == t1 {
                    return Err(LowerError::EncodingFailed(format!(
                        "load pair with Rt == Rt2 is unpredictable for {:?}",
                        inst.opcode
                    )));
                }
            }
            encode_instruction(inst).map_err(map_encode_error)
        }

        // =================================================================
        // All remaining opcodes: delegate directly to unified encoder.
        // No pre-validation needed (either no register operands to
        // validate, or the unified encoder handles them correctly).
        // =================================================================
        _ => encode_instruction(inst).map_err(map_encode_error),
    }
}

/// Map an `EncodeError` from the unified encoder to a `LowerError`.
fn map_encode_error(e: EncodeError) -> LowerError {
    match e {
        EncodeError::UnsupportedOpcode(op) => {
            LowerError::UnsupportedInstruction(format!("{:?}", op))
        }
        EncodeError::PseudoInstruction(op) => LowerError::UnresolvedPseudo(op),
        EncodeError::MissingOperand { opcode, index, .. } => {
            LowerError::MissingOperand { opcode, index }
        }
        other => LowerError::EncodingFailed(other.to_string()),
    }
}

// ---------------------------------------------------------------------------
// Function-level encoding with branch relaxation
// ---------------------------------------------------------------------------

/// Encode all instructions in a function after branch relaxation.
///
/// This walks the relaxed instruction sequence (where block targets have
/// already been resolved to signed displacements in instruction units)
/// and encodes each instruction.
fn encode_relaxed_instructions(
    function_name: &str,
    instructions: &[MachInst],
) -> Result<Vec<u8>, LowerError> {
    crate::pipeline::verify_aarch64_final_call_argument_sequence(
        function_name,
        instructions.iter(),
    )
    .map_err(|e| LowerError::MalformedFunction(e.to_string()))?;

    let mut code = Vec::with_capacity(instructions.len() * 4);

    for inst in instructions {
        // Pseudo-instructions should not appear in the relaxed sequence,
        // but guard against it.
        if inst.is_pseudo() {
            continue;
        }
        let word = encode_inst(inst)?;
        code.extend_from_slice(&word.to_le_bytes());
    }

    Ok(code)
}

/// Encode all instructions in a function walking blocks in layout order.
///
/// This is the simpler path used when branch relaxation is not needed
/// (e.g., when branch targets have already been resolved to immediates).
pub fn encode_function(func: &IrMachFunction) -> Result<Vec<u8>, LowerError> {
    crate::pipeline::enforce_aarch64_post_regalloc_resolved(func)
        .map_err(|e| LowerError::MalformedFunction(e.to_string()))?;
    reject_eh_sidecar_drop(func, "lower::encode_function")?;
    let mut code = Vec::new();

    for &block_id in &func.block_order {
        let block = func.block(block_id);
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            if inst.is_pseudo() {
                continue;
            }
            let word = encode_inst(inst)?;
            code.extend_from_slice(&word.to_le_bytes());
        }
    }

    Ok(code)
}

// ---------------------------------------------------------------------------
// Main entry point: lower_function
// ---------------------------------------------------------------------------

/// Lower a post-regalloc MachFunction to encoded AArch64 machine code.
///
/// This is the primary entry point for Phase 8 of the pipeline. It:
///   1. Runs frame lowering (prologue/epilogue + frame index elimination)
///   2. Expands pseudo-instructions
///   3. Runs branch relaxation (resolves block targets to byte offsets)
///   4. Encodes every instruction
///   5. Collects relocations for external references
///
/// The input function should already have:
///   - Completed ISel (all instructions are AArch64 MachInsts)
///   - Completed register allocation (all VRegs replaced with PRegs)
///   - Stack slots allocated (from spilling)
///
/// # Arguments
/// * `func` — The machine function (post-regalloc, mutable for frame lowering)
///
/// # Returns
/// * `LowerResult` containing encoded bytes, relocations, and frame layout
pub fn lower_function(func: &mut IrMachFunction) -> Result<LowerResult, LowerError> {
    crate::pipeline::validate_aarch64_mach_function(func)
        .map_err(|e| LowerError::MalformedFunction(e.to_string()))?;
    reject_eh_sidecar_drop(func, "lower::lower_function")?;

    // Phase 7: Frame lowering — compute layout, eliminate frame indices,
    // insert prologue/epilogue.
    let layout = if frame::function_has_runtime_stack_slots(func) {
        frame::compute_frame_layout_dynamic(func, 0, true)
    } else {
        frame::compute_frame_layout(func, 0, true)
    };
    frame::eliminate_frame_indices(func, &layout);
    frame::insert_prologue_epilogue(func, &layout)?;

    // Expand any remaining pseudo-instructions.
    expand_pseudos(func)?;
    expand_trap_bounds_check_exact(func);
    expand_trap_null_if_zero(func);
    expand_trap_div_zero_if_zero(func);
    expand_trap_shift_range_if_oob(func);
    expand_trap_overflow_exact(func);

    // Run branch relaxation — this resolves Block operands to immediate
    // offsets and handles out-of-range branches.
    let relaxed = relax::relax_branches(func)?;
    crate::pipeline::enforce_aarch64_post_regalloc_resolved(func)
        .map_err(|e| LowerError::MalformedFunction(e.to_string()))?;

    // Collect relocations from instructions that reference external symbols.
    let relocations = collect_relocations(&relaxed.instructions);

    // Encode the relaxed instruction sequence to bytes.
    let code = encode_relaxed_instructions(&func.name, &relaxed.instructions)
        .map_err(|e| LowerError::EncodingFailed(e.to_string()))?;

    Ok(LowerResult {
        code,
        relocations,
        frame_layout: layout,
    })
}

/// Lower a function that has already had frame lowering applied.
///
/// Skips the frame lowering phase. Useful when the caller has already
/// run `frame::insert_prologue_epilogue`.
pub fn lower_function_no_frame(func: &mut IrMachFunction) -> Result<LowerResult, LowerError> {
    crate::pipeline::validate_aarch64_mach_function(func)
        .map_err(|e| LowerError::MalformedFunction(e.to_string()))?;
    reject_eh_sidecar_drop(func, "lower::lower_function_no_frame")?;

    // Use a dummy frame layout since frame lowering was already done.
    let layout = if frame::function_has_runtime_stack_slots(func) {
        frame::compute_frame_layout_dynamic(func, 0, true)
    } else {
        frame::compute_frame_layout(func, 0, true)
    };

    // Expand any remaining pseudo-instructions.
    expand_pseudos(func)?;
    expand_trap_bounds_check_exact(func);
    expand_trap_null_if_zero(func);
    expand_trap_div_zero_if_zero(func);
    expand_trap_shift_range_if_oob(func);
    expand_trap_overflow_exact(func);

    // Run branch relaxation.
    let relaxed = relax::relax_branches(func)?;
    crate::pipeline::enforce_aarch64_post_regalloc_resolved(func)
        .map_err(|e| LowerError::MalformedFunction(e.to_string()))?;

    // Collect relocations.
    let relocations = collect_relocations(&relaxed.instructions);

    // Encode.
    let code = encode_relaxed_instructions(&func.name, &relaxed.instructions)
        .map_err(|e| LowerError::EncodingFailed(e.to_string()))?;

    Ok(LowerResult {
        code,
        relocations,
        frame_layout: layout,
    })
}

// ---------------------------------------------------------------------------
// Relocation collection
// ---------------------------------------------------------------------------

/// Scan the instruction sequence for instructions that need relocations
/// (ADRP, AddPCRel, BL to external symbols).
fn collect_relocations(instructions: &[MachInst]) -> Vec<Relocation> {
    let mut relocs = Vec::new();
    let mut byte_offset = 0u32;

    for inst in instructions {
        if inst.is_pseudo() {
            continue;
        }

        match inst.opcode {
            AArch64Opcode::Adrp => {
                // ADRP with a symbol operand needs a PAGE21 relocation.
                if let Some(sym) = extract_symbol_name(inst) {
                    relocs.push(Relocation {
                        offset: byte_offset,
                        kind: RelocKind::AdrpPage21,
                        symbol: sym,
                        addend: 0,
                    });
                }
            }
            AArch64Opcode::AddPCRel => {
                // ADD Xd, Xn, #pageoff needs a PAGEOFF12 relocation.
                if let Some(sym) = extract_symbol_name(inst) {
                    relocs.push(Relocation {
                        offset: byte_offset,
                        kind: RelocKind::AddPageOff12,
                        symbol: sym,
                        addend: 0,
                    });
                }
            }
            AArch64Opcode::Bl | AArch64Opcode::BL => {
                // BL to an external function needs a BRANCH26 relocation.
                // (Only if the target is a symbol, not a resolved offset.)
                if let Some(sym) = extract_symbol_name(inst) {
                    relocs.push(Relocation {
                        offset: byte_offset,
                        kind: RelocKind::Branch26,
                        symbol: sym,
                        addend: 0,
                    });
                }
            }
            _ => {}
        }

        byte_offset += 4;
    }

    relocs
}

/// Extract a symbol name from an instruction's operands, if present.
///
/// Walks the operand list and returns the first `Symbol(name)` found.
/// Symbol operands are created by ISel for instructions that reference
/// external names (BL for calls, ADRP/ADD for globals, etc.) and are
/// preserved through the IR pipeline by `convert_isel_operand`.
fn extract_symbol_name(inst: &MachInst) -> Option<String> {
    inst.operands
        .iter()
        .find_map(|op| op.as_symbol().map(|s| s.to_string()))
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{PReg, SP, W0, W1, W2, X0, X1, X2, X19, XZR};
    use trust_cg_ir::types::BlockId;

    /// Helper: create a minimal function with instructions in the entry block.
    fn make_func(name: &str, insts: Vec<MachInst>) -> MachFunction {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new(name.to_string(), sig);
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(BlockId(0), id);
        }
        func
    }

    // -----------------------------------------------------------------------
    // Overflow carrier expansion tests
    // -----------------------------------------------------------------------

    /// A KEPT signed-add overflow carrier expands to a flag-recompute + VC-skip + BRK so an actual
    /// overflow still traps. The flag-setter recomputes NZCV from the carrier's own lhs/rhs (the
    /// value op is a SEPARATE plain ADD this expansion never touches).
    #[test]
    fn test_expand_trap_overflow_exact_signed_add_64() {
        use trust_cg_ir::regs::SpecialReg;
        use trust_cg_ir::{CondCode, OverflowOp, pack_overflow_tag};
        let tag = pack_overflow_tag(OverflowOp::SignedAdd, 64);
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(tag),
            ],
        );
        let mut func = make_func("ovf_sadd", vec![carrier]);
        expand_trap_overflow_exact(&mut func);

        let block = &func.blocks[0];
        assert_eq!(block.insts.len(), 3, "ADDS + B.cond + BRK");
        let recompute = func.inst(block.insts[0]);
        assert_eq!(recompute.opcode, AArch64Opcode::AddsRR);
        assert_eq!(
            recompute.operands,
            vec![
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
            "flag-only ADDS XZR, lhs, rhs (64-bit recompute)"
        );
        let skip = func.inst(block.insts[1]);
        assert_eq!(skip.opcode, AArch64Opcode::BCond);
        assert_eq!(
            skip.operands,
            vec![
                MachOperand::Imm(i64::from(CondCode::VC.encoding())),
                MachOperand::Imm(2)
            ],
            "skip the trap iff V clear (no signed overflow)"
        );
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::Brk);
    }

    /// A KEPT 32-bit signed-sub carrier recomputes with SUBS WZR (32-bit) and skips on VC.
    #[test]
    fn test_expand_trap_overflow_exact_signed_sub_32() {
        use trust_cg_ir::regs::SpecialReg;
        use trust_cg_ir::{CondCode, OverflowOp, pack_overflow_tag};
        let tag = pack_overflow_tag(OverflowOp::SignedSub, 32);
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(W1),
                MachOperand::PReg(W2),
                MachOperand::Imm(tag),
            ],
        );
        let mut func = make_func("ovf_ssub32", vec![carrier]);
        expand_trap_overflow_exact(&mut func);

        let block = &func.blocks[0];
        let recompute = func.inst(block.insts[0]);
        assert_eq!(recompute.opcode, AArch64Opcode::SubsRR);
        assert_eq!(recompute.operands[0], MachOperand::Special(SpecialReg::WZR));
        let skip = func.inst(block.insts[1]);
        assert_eq!(
            skip.operands[0],
            MachOperand::Imm(i64::from(CondCode::VC.encoding()))
        );
    }

    /// Unsigned add overflow = carry set; the recompute is ADDS and the skip is LO (carry clear).
    #[test]
    fn test_expand_trap_overflow_exact_unsigned_add_skips_on_lo() {
        use trust_cg_ir::{CondCode, OverflowOp, pack_overflow_tag};
        let tag = pack_overflow_tag(OverflowOp::UnsignedAdd, 64);
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(tag),
            ],
        );
        let mut func = make_func("ovf_uadd", vec![carrier]);
        expand_trap_overflow_exact(&mut func);
        let block = &func.blocks[0];
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::AddsRR);
        assert_eq!(
            func.inst(block.insts[1]).operands[0],
            MachOperand::Imm(i64::from(CondCode::LO.encoding()))
        );
    }

    /// Unsigned sub overflow = borrow; the recompute is SUBS and the skip is HS (no borrow).
    #[test]
    fn test_expand_trap_overflow_exact_unsigned_sub_skips_on_hs() {
        use trust_cg_ir::{CondCode, OverflowOp, pack_overflow_tag};
        let tag = pack_overflow_tag(OverflowOp::UnsignedSub, 64);
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(tag),
            ],
        );
        let mut func = make_func("ovf_usub", vec![carrier]);
        expand_trap_overflow_exact(&mut func);
        let block = &func.blocks[0];
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::SubsRR);
        assert_eq!(
            func.inst(block.insts[1]).operands[0],
            MachOperand::Imm(i64::from(CondCode::HS.encoding()))
        );
    }

    /// FAIL-SAFE: a carrier with a malformed op-tag degrades to the bare TrapOverflow panic pseudo,
    /// never a NOP — an actual overflow must NEVER slip through an un-decodable carrier.
    #[test]
    fn test_expand_trap_overflow_exact_malformed_tag_fails_safe() {
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(0xBAD),
            ],
        );
        let mut func = make_func("ovf_bad", vec![carrier]);
        expand_trap_overflow_exact(&mut func);
        let block = &func.blocks[0];
        assert_eq!(block.insts.len(), 1);
        assert_eq!(
            func.inst(block.insts[0]).opcode,
            AArch64Opcode::TrapOverflow,
            "a malformed overflow carrier must fail-safe to a bare trap, never a NOP"
        );
    }

    /// A KEPT 64-bit SIGNED-mul carrier expands to the EXACT AArch64 mul-high overflow idiom:
    /// `MUL X16; SMULH X17; ASR X16,X16,#63; CMP X17,X16; B.EQ +2; BRK`. The skip is EQ (Z set =
    /// hi == sext(lo) = NO overflow), NOT the add/sub VC/LO/HS. The scratch is the reserved
    /// non-allocatable X16/X17 (this runs post-regalloc, no fresh vreg available).
    #[test]
    fn test_expand_trap_overflow_exact_signed_mul_64() {
        use trust_cg_ir::regs::{X16, X17};
        use trust_cg_ir::{CondCode, OverflowOp, pack_overflow_tag};
        let tag = pack_overflow_tag(OverflowOp::SignedMul, 64);
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(tag),
            ],
        );
        let mut func = make_func("ovf_smul", vec![carrier]);
        expand_trap_overflow_exact(&mut func);

        let block = &func.blocks[0];
        assert_eq!(block.insts.len(), 6, "MUL + SMULH + ASR + CMP + B.EQ + BRK");
        // MUL X16, X1, X2
        let mul = func.inst(block.insts[0]);
        assert_eq!(mul.opcode, AArch64Opcode::MulRR);
        assert_eq!(
            mul.operands,
            vec![
                MachOperand::PReg(X16),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ]
        );
        // SMULH X17, X1, X2
        let smulh = func.inst(block.insts[1]);
        assert_eq!(smulh.opcode, AArch64Opcode::Smulh);
        assert_eq!(
            smulh.operands,
            vec![
                MachOperand::PReg(X17),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ]
        );
        // ASR X16, X16, #63
        let asr = func.inst(block.insts[2]);
        assert_eq!(asr.opcode, AArch64Opcode::AsrRI);
        assert_eq!(
            asr.operands,
            vec![
                MachOperand::PReg(X16),
                MachOperand::PReg(X16),
                MachOperand::Imm(63),
            ]
        );
        // CMP X17, X16
        let cmp = func.inst(block.insts[3]);
        assert_eq!(cmp.opcode, AArch64Opcode::CmpRR);
        assert_eq!(
            cmp.operands,
            vec![MachOperand::PReg(X17), MachOperand::PReg(X16)]
        );
        // B.EQ +2 — skip on NO overflow (Z set).
        let skip = func.inst(block.insts[4]);
        assert_eq!(skip.opcode, AArch64Opcode::BCond);
        assert_eq!(
            skip.operands,
            vec![
                MachOperand::Imm(i64::from(CondCode::EQ.encoding())),
                MachOperand::Imm(2),
            ],
            "mul skip condition is EQ (Z set = no overflow), not VC/LO/HS"
        );
        assert_eq!(func.inst(block.insts[5]).opcode, AArch64Opcode::Brk);
    }

    /// A KEPT 64-bit UNSIGNED-mul carrier expands to `UMULH X16; CMP X16,#0; B.EQ +2; BRK`
    /// (the low MUL is unneeded — UMULH alone gives the high half; overflow iff hi != 0).
    #[test]
    fn test_expand_trap_overflow_exact_unsigned_mul_64() {
        use trust_cg_ir::regs::X16;
        use trust_cg_ir::{CondCode, OverflowOp, pack_overflow_tag};
        let tag = pack_overflow_tag(OverflowOp::UnsignedMul, 64);
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(tag),
            ],
        );
        let mut func = make_func("ovf_umul", vec![carrier]);
        expand_trap_overflow_exact(&mut func);

        let block = &func.blocks[0];
        assert_eq!(block.insts.len(), 4, "UMULH + CMP + B.EQ + BRK");
        let umulh = func.inst(block.insts[0]);
        assert_eq!(umulh.opcode, AArch64Opcode::Umulh);
        assert_eq!(
            umulh.operands,
            vec![
                MachOperand::PReg(X16),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ]
        );
        let cmp = func.inst(block.insts[1]);
        assert_eq!(cmp.opcode, AArch64Opcode::CmpRI);
        assert_eq!(
            cmp.operands,
            vec![MachOperand::PReg(X16), MachOperand::Imm(0)]
        );
        let skip = func.inst(block.insts[2]);
        assert_eq!(skip.opcode, AArch64Opcode::BCond);
        assert_eq!(
            skip.operands[0],
            MachOperand::Imm(i64::from(CondCode::EQ.encoding()))
        );
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::Brk);
    }

    /// FAIL-SAFE (mul width): a width-32 mul tag has no correct SMULH/UMULH expansion, so it must
    /// degrade to the bare TrapOverflow panic pseudo — NEVER a silently-wrong width-32 mul check.
    #[test]
    fn test_expand_trap_overflow_exact_mul_width32_fails_safe() {
        use trust_cg_ir::{OverflowOp, pack_overflow_tag};
        // Hand-pack a width-32 SignedMul tag (the producer never emits this; it is the malformed
        // shape the expansion must fail-safe on).
        let tag = pack_overflow_tag(OverflowOp::SignedMul, 32);
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(tag),
            ],
        );
        let mut func = make_func("ovf_mul32", vec![carrier]);
        expand_trap_overflow_exact(&mut func);
        let block = &func.blocks[0];
        assert_eq!(block.insts.len(), 1);
        assert_eq!(
            func.inst(block.insts[0]).opcode,
            AArch64Opcode::TrapOverflow,
            "a width-32 mul carrier has no SMULH/UMULH form and must fail-safe to a bare trap"
        );
    }

    /// An un-expanded TrapOverflowExact is a FAIL-CLOSED encoder error, not a silent NOP/BRK fallback.
    #[test]
    fn test_unexpanded_overflow_carrier_is_encoder_error() {
        use trust_cg_ir::{OverflowOp, pack_overflow_tag};
        let carrier = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(pack_overflow_tag(OverflowOp::SignedAdd, 64)),
            ],
        );
        let err = crate::aarch64::encode::encode_instruction(&carrier).unwrap_err();
        assert!(
            matches!(
                err,
                EncodeError::PseudoInstruction(AArch64Opcode::TrapOverflowExact)
            ),
            "un-expanded overflow carrier must be a typed pseudo error, got {err:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Encoding tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_add_rr() {
        // ADD X0, X0, X1
        let inst = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // sf=1, op=0, S=0, shift=0, Rm=1, imm6=0, Rn=0, Rd=0
        // = 0x8B010000  (ADD X0, X0, X1)
        assert_eq!(word, 0x8B010000, "ADD X0, X0, X1 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_sub_ri() {
        // SUB X0, X0, #16
        let inst = MachInst::new(
            AArch64Opcode::SubRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::Imm(16),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // sf=1, op=1, S=0, sh=0, imm12=16, Rn=0, Rd=0
        let expected = (1u32 << 31) | (1 << 30) | (0b100010 << 23) | (16 << 10);
        assert_eq!(word, expected, "SUB X0, X0, #16 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_mov_r() {
        // MOV X0, X1 = ORR X0, XZR, X1
        let inst = MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
        );
        let word = encode_inst(&inst).unwrap();
        // sf=1, opc=01, shift=0, N=0, Rm=1, imm6=0, Rn=31(XZR), Rd=0
        let expected = (1u32 << 31) | (0b01 << 29) | (0b01010 << 24) | (1 << 16) | (31 << 5);
        assert_eq!(word, expected, "MOV X0, X1 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_ret() {
        let inst = MachInst::new(AArch64Opcode::Ret, vec![]);
        let word = encode_inst(&inst).unwrap();
        assert_eq!(word, 0xD65F03C0, "RET = 0x{word:08X}");
    }

    #[test]
    fn test_encode_b() {
        // B +3 (instruction units)
        let inst = MachInst::new(AArch64Opcode::B, vec![MachOperand::Imm(3)]);
        let word = encode_inst(&inst).unwrap();
        let expected = (0b00101u32 << 26) | 3;
        assert_eq!(word, expected, "B +3 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_bcond() {
        // B.EQ +2
        let inst = MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(0), MachOperand::Imm(2)],
        );
        let word = encode_inst(&inst).unwrap();
        let expected = (0b01010100u32 << 24) | (2 << 5);
        assert_eq!(word, expected, "B.EQ +2 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_tbz_bit3() {
        // TBZ X0, #3, +2  (bit 3, offset 2)
        let inst = MachInst::new(
            AArch64Opcode::Tbz,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(3),
                MachOperand::Imm(2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let expected = (0b011011 << 25) | (3 << 19) | (2 << 5);
        assert_eq!(word, expected, "TBZ X0, #3, +2 = 0x{word:08X}");
        assert_ne!(word, 0xD503201F, "TBZ must not emit NOP");
    }

    #[test]
    fn test_encode_tbnz_bit3() {
        let inst = MachInst::new(
            AArch64Opcode::Tbnz,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(3),
                MachOperand::Imm(2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let expected = (0b011011 << 25) | (1 << 24) | (3 << 19) | (2 << 5);
        assert_eq!(word, expected, "TBNZ X0, #3, +2 = 0x{word:08X}");
        assert_ne!(word, 0xD503201F, "TBNZ must not emit NOP");
    }

    #[test]
    fn test_encode_tbz_high_bit() {
        // TBZ X0, #32, +5  (bit 32 means b5=1, b40=0)
        let inst = MachInst::new(
            AArch64Opcode::Tbz,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(32),
                MachOperand::Imm(5),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let expected = ((1u32 << 31) | (0b011011 << 25)) | (5 << 5);
        assert_eq!(word, expected, "TBZ X0, #32, +5 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_tbnz_bit63() {
        // TBNZ X1, #63, +10  (bit 63: b5=1, b40=31)
        let inst = MachInst::new(
            AArch64Opcode::Tbnz,
            vec![
                MachOperand::PReg(X1),
                MachOperand::Imm(63),
                MachOperand::Imm(10),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let expected = (1u32 << 31) | (0b011011 << 25) | (1 << 24) | (31 << 19) | (10 << 5) | 1;
        assert_eq!(word, expected, "TBNZ X1, #63, +10 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_tbz_matches_unified_encoder() {
        let inst = MachInst::new(
            AArch64Opcode::Tbz,
            vec![
                MachOperand::PReg(X2),
                MachOperand::Imm(7),
                MachOperand::Imm(100),
            ],
        );
        let lower_word = encode_inst(&inst).unwrap();
        let unified_word = crate::aarch64::encode::encode_instruction(&inst).unwrap();
        assert_eq!(
            lower_word, unified_word,
            "lower encode_inst and unified encode_instruction must agree for TBZ: lower=0x{lower_word:08X}, unified=0x{unified_word:08X}"
        );
    }

    #[test]
    fn test_encode_tbnz_matches_unified_encoder() {
        let inst = MachInst::new(
            AArch64Opcode::Tbnz,
            vec![
                MachOperand::PReg(X2),
                MachOperand::Imm(15),
                MachOperand::Imm(50),
            ],
        );
        let lower_word = encode_inst(&inst).unwrap();
        let unified_word = crate::aarch64::encode::encode_instruction(&inst).unwrap();
        assert_eq!(
            lower_word, unified_word,
            "lower encode_inst and unified encode_instruction must agree for TBNZ: lower=0x{lower_word:08X}, unified=0x{unified_word:08X}"
        );
    }

    #[test]
    fn test_encode_movz() {
        // MOVZ X0, #42
        let inst = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::PReg(X0), MachOperand::Imm(42)],
        );
        let word = encode_inst(&inst).unwrap();
        let expected = (1u32 << 31) | (0b10 << 29) | (0b100101 << 23) | (42 << 5);
        assert_eq!(word, expected, "MOVZ X0, #42 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_ldr_ri() {
        // LDR X0, [X1, #8]  -> scaled offset = 8/8 = 1
        let inst = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(8),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let expected =
            (0b11u32 << 30) | (0b111 << 27) | (0b01 << 24) | (0b01 << 22) | (1 << 10) | (1 << 5);
        assert_eq!(word, expected, "LDR X0, [X1, #8] = 0x{word:08X}");
    }

    #[test]
    fn test_encode_str_ri() {
        // STR X0, [X1]
        let inst = MachInst::new(
            AArch64Opcode::StrRI,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
        );
        let word = encode_inst(&inst).unwrap();
        let expected = (0b11u32 << 30) | (0b111 << 27) | (0b01 << 24) | (1 << 5);
        assert_eq!(word, expected, "STR X0, [X1] = 0x{word:08X}");
    }

    // -----------------------------------------------------------------------
    // Pseudo-expansion tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_expand_pseudos_removes_phi() {
        let mut func = make_func(
            "phi_test",
            vec![
                MachInst::new(AArch64Opcode::Phi, vec![MachOperand::Imm(0)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(func.insts[0].opcode, AArch64Opcode::Nop);
        assert!(func.insts[0].operands.is_empty());
    }

    #[test]
    fn test_expand_pseudos_removes_stack_alloc() {
        let mut func = make_func(
            "stack_test",
            vec![
                MachInst::new(AArch64Opcode::StackAlloc, vec![MachOperand::Imm(16)]),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(func.insts[0].opcode, AArch64Opcode::Nop);
    }

    #[test]
    fn test_expand_pseudos_identity_mov() {
        let mut func = make_func(
            "identity_mov",
            vec![
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X0), MachOperand::PReg(X0)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        expand_pseudos(&mut func).unwrap();
        // Identity MOV X0, X0 should become NOP.
        assert_eq!(func.insts[0].opcode, AArch64Opcode::Nop);
    }

    #[test]
    fn test_expand_pseudos_keeps_real_mov() {
        let mut func = make_func(
            "real_mov",
            vec![
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
                ),
                MachInst::new(AArch64Opcode::Ret, vec![]),
            ],
        );
        expand_pseudos(&mut func).unwrap();
        // MOV X0, X1 should be kept (not identity).
        assert_eq!(func.insts[0].opcode, AArch64Opcode::MovR);
    }

    #[test]
    fn test_expand_pseudos_preserves_trap_overflow() {
        // TrapOverflow is a real pseudo that the encoder handles as BRK #1.
        // expand_pseudos must NOT convert it to NOP.
        let mut inst = MachInst::new(AArch64Opcode::TrapOverflow, vec![MachOperand::Imm(0)]);
        inst.flags = InstFlags::IS_PSEUDO;
        let mut func = make_func(
            "trap_test",
            vec![inst, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(
            func.insts[0].opcode,
            AArch64Opcode::TrapOverflow,
            "TrapOverflow must survive expand_pseudos, not become NOP"
        );
    }

    #[test]
    fn test_expand_pseudos_preserves_trap_bounds_check() {
        let mut inst = MachInst::new(AArch64Opcode::TrapBoundsCheck, vec![]);
        inst.flags = InstFlags::IS_PSEUDO;
        let mut func = make_func(
            "trap_bounds",
            vec![inst, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(
            func.insts[0].opcode,
            AArch64Opcode::TrapBoundsCheck,
            "TrapBoundsCheck must survive expand_pseudos, not become NOP"
        );
    }

    #[test]
    fn test_expand_pseudos_preserves_trap_null() {
        let mut inst = MachInst::new(AArch64Opcode::TrapNull, vec![]);
        inst.flags = InstFlags::IS_PSEUDO;
        let mut func = make_func(
            "trap_null",
            vec![inst, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(
            func.insts[0].opcode,
            AArch64Opcode::TrapNull,
            "TrapNull must survive expand_pseudos, not become NOP"
        );
    }

    #[test]
    fn test_trap_null_if_zero_expands_to_conditional_cbnz_brk() {
        let mut guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![MachOperand::PReg(X0)]);
        guard.flags = InstFlags::IS_PSEUDO;
        let mut func = make_func(
            "trap_null_if_zero",
            vec![guard, MachInst::new(AArch64Opcode::Ret, vec![])],
        );

        let result = lower_function_no_frame(&mut func).unwrap();
        assert!(result.code.len() >= 8);

        let cbnz = u32::from_le_bytes(result.code[0..4].try_into().unwrap());
        let brk = u32::from_le_bytes(result.code[4..8].try_into().unwrap());
        assert_eq!(cbnz, encoding::encode_cmp_branch(1, 1, 2, 0));
        assert_eq!(brk, 0xD4200020);
    }

    #[test]
    fn test_trap_bounds_check_exact_expands_to_conditional_cmp_brk() {
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(8),
            ],
        );
        let mut func = make_func(
            "trap_bounds_exact",
            vec![guard, MachInst::new(AArch64Opcode::Ret, vec![])],
        );

        expand_trap_bounds_check_exact(&mut func);
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::CmpRI);
        assert_eq!(func.inst(block.insts[0]).operands[0], MachOperand::PReg(X1));
        assert_eq!(func.inst(block.insts[0]).operands[1], MachOperand::Imm(8));
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::BCond);
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::Brk);
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::Ret);
    }

    /// A REGISTER bound must expand to a register-to-register compare.
    ///
    /// This is the dynamically-sized case (`index <u v.len()`), where the bound
    /// is not known at compile time. Emitting `CmpRI` here would encode the
    /// register NUMBER as the compare immediate, turning a memory-safety guard
    /// into a silently wrong runtime check — an out-of-bounds access that still
    /// looks like a bounds-checked program.
    #[test]
    fn test_trap_bounds_check_exact_register_bound_expands_to_cmprr() {
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2), // dynamic length, not an immediate
            ],
        );
        let mut func = make_func(
            "trap_bounds_reg",
            vec![guard, MachInst::new(AArch64Opcode::Ret, vec![])],
        );

        expand_trap_bounds_check_exact(&mut func);
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(
            func.inst(block.insts[0]).opcode,
            AArch64Opcode::CmpRR,
            "a register bound must compare register-to-register, never CmpRI"
        );
        assert_eq!(func.inst(block.insts[0]).operands[0], MachOperand::PReg(X1));
        assert_eq!(func.inst(block.insts[0]).operands[1], MachOperand::PReg(X2));
        // The guard shape is otherwise unchanged: skip-on-LO, else trap.
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::BCond);
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::Brk);
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_trap_bounds_check_exact_large_bound_movz_cmprr() {
        // Bound in [0x1000, 0xffff] cannot be a CMP #imm12; it is materialized
        // into X16 with a single MOVZ (bits [31:16] are zero), then CMP reg,reg.
        use trust_cg_ir::regs::X16;
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(4096), // 0x1000 > 0xfff
            ],
        );
        let mut func = make_func(
            "trap_bounds_large",
            vec![guard, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_trap_bounds_check_exact(&mut func);
        let block = func.block(func.entry);
        // MOVZ ; CMP ; B.LO ; BRK ; RET
        assert_eq!(block.insts.len(), 5);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Movz);
        assert_eq!(
            func.inst(block.insts[0]).operands[0],
            MachOperand::PReg(X16)
        );
        assert_eq!(
            func.inst(block.insts[0]).operands[1],
            MachOperand::Imm(4096)
        );
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::CmpRR);
        assert_eq!(func.inst(block.insts[1]).operands[0], MachOperand::PReg(X1));
        assert_eq!(
            func.inst(block.insts[1]).operands[1],
            MachOperand::PReg(X16)
        );
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::BCond);
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::Brk);
        assert_eq!(func.inst(block.insts[4]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_trap_bounds_check_exact_wide_bound_movz_movk_cmprr() {
        // Bound in [0x10000, i32::MAX] needs a MOVZ (low 16) + MOVK (bits [31:16],
        // LSL #16), then CMP reg,reg. 0x12345 -> MOVZ #0x2345 ; MOVK #0x1, LSL #16.
        use trust_cg_ir::regs::X16;
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(0x12345),
            ],
        );
        let mut func = make_func(
            "trap_bounds_wide",
            vec![guard, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_trap_bounds_check_exact(&mut func);
        let block = func.block(func.entry);
        // MOVZ ; MOVK ; CMP ; B.LO ; BRK ; RET
        assert_eq!(block.insts.len(), 6);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::Movz);
        assert_eq!(
            func.inst(block.insts[0]).operands[0],
            MachOperand::PReg(X16)
        );
        assert_eq!(
            func.inst(block.insts[0]).operands[1],
            MachOperand::Imm(0x2345)
        );
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Movk);
        assert_eq!(
            func.inst(block.insts[1]).operands[0],
            MachOperand::PReg(X16)
        );
        assert_eq!(func.inst(block.insts[1]).operands[1], MachOperand::Imm(0x1));
        assert_eq!(func.inst(block.insts[1]).operands[2], MachOperand::Imm(16));
        assert_eq!(func.inst(block.insts[2]).opcode, AArch64Opcode::CmpRR);
        assert_eq!(func.inst(block.insts[2]).operands[0], MachOperand::PReg(X1));
        assert_eq!(
            func.inst(block.insts[2]).operands[1],
            MachOperand::PReg(X16)
        );
        assert_eq!(func.inst(block.insts[3]).opcode, AArch64Opcode::BCond);
        assert_eq!(func.inst(block.insts[4]).opcode, AArch64Opcode::Brk);
        assert_eq!(func.inst(block.insts[5]).opcode, AArch64Opcode::Ret);
    }

    #[test]
    fn test_expand_pseudos_preserves_trap_div_zero() {
        let mut inst = MachInst::new(AArch64Opcode::TrapDivZero, vec![]);
        inst.flags = InstFlags::IS_PSEUDO;
        let mut func = make_func(
            "trap_div",
            vec![inst, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(
            func.insts[0].opcode,
            AArch64Opcode::TrapDivZero,
            "TrapDivZero must survive expand_pseudos, not become NOP"
        );
    }

    #[test]
    fn test_expand_pseudos_preserves_trap_shift_range() {
        let mut inst = MachInst::new(AArch64Opcode::TrapShiftRange, vec![]);
        inst.flags = InstFlags::IS_PSEUDO;
        let mut func = make_func(
            "trap_shift",
            vec![inst, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(
            func.insts[0].opcode,
            AArch64Opcode::TrapShiftRange,
            "TrapShiftRange must survive expand_pseudos, not become NOP"
        );
    }

    #[test]
    fn test_expand_pseudos_preserves_retain() {
        let mut inst = MachInst::new(AArch64Opcode::Retain, vec![MachOperand::PReg(X0)]);
        inst.flags = InstFlags::IS_PSEUDO;
        let mut func = make_func(
            "retain_test",
            vec![inst, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(
            func.insts[0].opcode,
            AArch64Opcode::Retain,
            "Retain must survive expand_pseudos, not become NOP"
        );
    }

    #[test]
    fn test_expand_pseudos_preserves_release() {
        let mut inst = MachInst::new(AArch64Opcode::Release, vec![MachOperand::PReg(X0)]);
        inst.flags = InstFlags::IS_PSEUDO;
        let mut func = make_func(
            "release_test",
            vec![inst, MachInst::new(AArch64Opcode::Ret, vec![])],
        );
        expand_pseudos(&mut func).unwrap();
        assert_eq!(
            func.insts[0].opcode,
            AArch64Opcode::Release,
            "Release must survive expand_pseudos, not become NOP"
        );
    }

    // -----------------------------------------------------------------------
    // Encoding round-trip: encode_function on a simple IR function
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_function_simple() {
        // Build a simple add function: ADD X0, X0, X1; RET
        let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
        let mut func = MachFunction::new("add".to_string(), sig);
        let entry = func.entry;

        let add = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        );
        let add_id = func.push_inst(add);
        func.append_inst(entry, add_id);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(entry, ret_id);

        let code = encode_function(&func).unwrap();
        // 2 instructions * 4 bytes.
        assert_eq!(code.len(), 8);
        // Verify ADD encoding (first 4 bytes, little-endian).
        let add_word = u32::from_le_bytes([code[0], code[1], code[2], code[3]]);
        assert_eq!(add_word, 0x8B010000);
        // Verify RET encoding.
        let ret_word = u32::from_le_bytes([code[4], code[5], code[6], code[7]]);
        assert_eq!(ret_word, 0xD65F03C0);
    }

    #[test]
    fn test_exact_relaxed_encode_rejects_call_argument_source_clobber() {
        static CALL_ARGS: [PReg; 2] = [X0, X1];
        let instructions = vec![
            MachInst::with_flags(
                AArch64Opcode::MOVXrr,
                vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
                InstFlags::IS_CALL_ARG_SETUP,
            ),
            MachInst::with_flags(
                AArch64Opcode::MOVXrr,
                vec![MachOperand::PReg(X1), MachOperand::PReg(X0)],
                InstFlags::IS_CALL_ARG_SETUP,
            ),
            MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X19)])
                .with_implicit_uses(&CALL_ARGS),
        ];

        let err = encode_relaxed_instructions("mutated_relaxed_call", &instructions)
            .expect_err("the exact relaxed stream must fail before byte encoding");
        assert!(err.to_string().contains("parallel-move source identity"));
    }

    // -----------------------------------------------------------------------
    // Full lowering test
    // -----------------------------------------------------------------------

    #[test]
    fn test_lower_function_simple() {
        // Build a trivial leaf function that should survive full lowering
        // without forcing a frame.
        let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
        let mut func = MachFunction::new("add_lowered".to_string(), sig);
        let entry = func.entry;

        let add = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        );
        let add_id = func.push_inst(add);
        func.append_inst(entry, add_id);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(entry, ret_id);

        let result = lower_function(&mut func).unwrap();

        // Trivial leaf functions use the documented zero-frame lowering.
        assert_eq!(result.code.len(), 8);
        assert!(!result.frame_layout.uses_frame_pointer);
        assert!(result.frame_layout.callee_saved_pairs.is_empty());
    }

    #[test]
    fn test_lower_function_with_branch() {
        // Function with two blocks and a branch.
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("branch_test".to_string(), sig);
        let bb0 = func.entry;
        let bb1 = func.create_block();

        // bb0: B bb1
        let b_inst = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb1)]);
        let b_id = func.push_inst(b_inst);
        func.append_inst(bb0, b_id);
        func.add_edge(bb0, bb1);

        // bb1: RET
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(bb1, ret_id);

        let result = lower_function(&mut func).unwrap();
        assert!(result.code.len() >= 8, "Need at least B + RET");
    }

    #[test]
    fn test_lower_function_with_callee_saves() {
        // Function that uses X19 (callee-saved).
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("callee_save_test".to_string(), sig);
        let entry = func.entry;

        // Use X19 (callee-saved register).
        let mov = MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X19), MachOperand::PReg(X0)],
        );
        let mov_id = func.push_inst(mov);
        func.append_inst(entry, mov_id);

        let mov2 = MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X19)],
        );
        let mov2_id = func.push_inst(mov2);
        func.append_inst(entry, mov2_id);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(entry, ret_id);

        let result = lower_function(&mut func).unwrap();

        // Frame layout should include X19/X20 pair.
        assert_eq!(result.frame_layout.callee_saved_pairs.len(), 2);
        // Code should be non-trivial (prologue + body + epilogue).
        assert!(
            result.code.len() >= 20,
            "Expected at least 20 bytes with callee saves, got {}",
            result.code.len()
        );
    }

    #[test]
    fn test_lower_result_has_no_relocations_for_simple_func() {
        let sig = Signature::new(vec![], vec![]);
        let mut func = MachFunction::new("simple".to_string(), sig);
        let entry = func.entry;

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(entry, ret_id);

        let result = lower_function(&mut func).unwrap();
        assert!(result.relocations.is_empty());
    }

    #[test]
    fn test_encode_mul() {
        // MUL X0, X1, X0
        let inst = MachInst::new(
            AArch64Opcode::MulRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X0),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // MADD X0, X1, X0, XZR
        // sf=1 | 00 | 11011 | 000 | Rm=0 | o0=0 | Ra=31 | Rn=1 | Rd=0
        let expected = ((1u32 << 31)
            | (0b0011011u32 << 24))   // o0=0
            | (31 << 10)  // Ra=XZR
            | (1 << 5); // Rd=X0
        assert_eq!(word, expected, "MUL X0, X1, X0 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_cmp_rr() {
        // CMP X0, X1 = SUBS XZR, X0, X1
        let inst = MachInst::new(
            AArch64Opcode::CmpRR,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
        );
        let word = encode_inst(&inst).unwrap();
        // sf=1, op=1(SUB), S=1, shift=0, Rm=1, imm6=0, Rn=0, Rd=31(XZR)
        let expected = (1u32 << 31) | (1 << 30) | (1 << 29) | (0b01011 << 24) | (1 << 16) | 31;
        assert_eq!(word, expected, "CMP X0, X1 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_blr() {
        // BLR X0
        let inst = MachInst::new(AArch64Opcode::Blr, vec![MachOperand::PReg(X0)]);
        let word = encode_inst(&inst).unwrap();
        assert_eq!(word, 0xD63F0000, "BLR X0 = 0x{word:08X}");
    }

    // -----------------------------------------------------------------------
    // Symbol extraction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_symbol_from_bl() {
        let inst = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("_printf".to_string())],
        );
        assert_eq!(extract_symbol_name(&inst), Some("_printf".to_string()));
    }

    #[test]
    fn test_extract_symbol_from_adrp() {
        let inst = MachInst::new(
            AArch64Opcode::Adrp,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Symbol("_my_global".to_string()),
            ],
        );
        assert_eq!(extract_symbol_name(&inst), Some("_my_global".to_string()));
    }

    #[test]
    fn test_extract_symbol_from_add_pcrel() {
        let inst = MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::Symbol("_my_global".to_string()),
            ],
        );
        assert_eq!(extract_symbol_name(&inst), Some("_my_global".to_string()));
    }

    #[test]
    fn test_extract_symbol_none_for_plain_add() {
        let inst = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        );
        assert_eq!(extract_symbol_name(&inst), None);
    }

    #[test]
    fn test_extract_symbol_none_for_ret() {
        let inst = MachInst::new(AArch64Opcode::Ret, vec![]);
        assert_eq!(extract_symbol_name(&inst), None);
    }

    // -----------------------------------------------------------------------
    // Relocation collection tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_collect_relocations_bl_branch26() {
        let instructions = vec![MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("_callee".to_string())],
        )];
        let relocs = collect_relocations(&instructions);
        assert_eq!(relocs.len(), 1);
        assert_eq!(relocs[0].offset, 0);
        assert_eq!(relocs[0].kind, RelocKind::Branch26);
        assert_eq!(relocs[0].symbol, "_callee");
        assert_eq!(relocs[0].addend, 0);
    }

    #[test]
    fn test_collect_relocations_bl_alias_branch26() {
        let instructions = vec![MachInst::new(
            AArch64Opcode::BL,
            vec![MachOperand::Symbol("_callee".to_string())],
        )];
        let relocs = collect_relocations(&instructions);
        assert_eq!(relocs.len(), 1);
        assert_eq!(relocs[0].offset, 0);
        assert_eq!(relocs[0].kind, RelocKind::Branch26);
        assert_eq!(relocs[0].symbol, "_callee");
        assert_eq!(relocs[0].addend, 0);
    }

    #[test]
    fn test_collect_relocations_adrp_page21() {
        let instructions = vec![MachInst::new(
            AArch64Opcode::Adrp,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Symbol("_global_var".to_string()),
            ],
        )];
        let relocs = collect_relocations(&instructions);
        assert_eq!(relocs.len(), 1);
        assert_eq!(relocs[0].offset, 0);
        assert_eq!(relocs[0].kind, RelocKind::AdrpPage21);
        assert_eq!(relocs[0].symbol, "_global_var");
    }

    #[test]
    fn test_collect_relocations_add_pcrel_pageoff12() {
        let instructions = vec![MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::Symbol("_global_var".to_string()),
            ],
        )];
        let relocs = collect_relocations(&instructions);
        assert_eq!(relocs.len(), 1);
        assert_eq!(relocs[0].offset, 0);
        assert_eq!(relocs[0].kind, RelocKind::AddPageOff12);
        assert_eq!(relocs[0].symbol, "_global_var");
    }

    #[test]
    fn test_collect_relocations_adrp_add_pair() {
        let instructions = vec![
            MachInst::new(
                AArch64Opcode::Adrp,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Symbol("_data".to_string()),
                ],
            ),
            MachInst::new(
                AArch64Opcode::AddPCRel,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::Symbol("_data".to_string()),
                ],
            ),
        ];
        let relocs = collect_relocations(&instructions);
        assert_eq!(relocs.len(), 2);
        assert_eq!(relocs[0].offset, 0);
        assert_eq!(relocs[0].kind, RelocKind::AdrpPage21);
        assert_eq!(relocs[0].symbol, "_data");
        assert_eq!(relocs[1].offset, 4);
        assert_eq!(relocs[1].kind, RelocKind::AddPageOff12);
        assert_eq!(relocs[1].symbol, "_data");
    }

    #[test]
    fn test_collect_relocations_mixed_with_no_symbol_instrs() {
        let instructions = vec![
            MachInst::new(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                ],
            ),
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("_callee".to_string())],
            ),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        ];
        let relocs = collect_relocations(&instructions);
        assert_eq!(relocs.len(), 1);
        assert_eq!(relocs[0].offset, 4);
        assert_eq!(relocs[0].kind, RelocKind::Branch26);
        assert_eq!(relocs[0].symbol, "_callee");
    }

    #[test]
    fn test_collect_relocations_no_symbol_no_relocs() {
        let instructions = vec![
            MachInst::new(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                ],
            ),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        ];
        let relocs = collect_relocations(&instructions);
        assert!(relocs.is_empty());
    }

    #[test]
    fn test_collect_relocations_bl_without_symbol_no_reloc() {
        let inst = MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(42)]);
        let relocs = collect_relocations(&[inst]);
        assert!(relocs.is_empty());
    }

    // -----------------------------------------------------------------------
    // Bug #98: preg_hw returns error for non-register operands
    // -----------------------------------------------------------------------

    #[test]
    fn test_preg_hw_rejects_imm_operand() {
        let inst = MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::Imm(42),
            ],
        );
        let result = encode_inst(&inst);
        assert!(
            result.is_err(),
            "Imm operand where register expected should error, not silently encode as XZR"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("expected register operand"),
            "Error should mention expected register, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_preg_hw_rejects_frame_index() {
        use trust_cg_ir::types::FrameIdx;
        let inst = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![MachOperand::PReg(X0), MachOperand::FrameIndex(FrameIdx(-8))],
        );
        let result = encode_inst(&inst);
        assert!(
            result.is_err(),
            "FrameIndex where register expected should error"
        );
    }

    #[test]
    fn test_preg_hw_rejects_stack_slot() {
        use trust_cg_ir::types::StackSlotId;
        let inst = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::StackSlot(StackSlotId(0)),
            ],
        );
        let result = encode_inst(&inst);
        assert!(
            result.is_err(),
            "StackSlot where register expected should error"
        );
    }

    #[test]
    fn test_pair_offset_accepts_base_at_operand_two() {
        let stp = MachInst::new(
            AArch64Opcode::StpRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(0),
            ],
        );
        assert!(
            encode_inst(&stp).is_ok(),
            "StpRI should accept explicit SP base at operand 2"
        );

        let ldp = MachInst::new(
            AArch64Opcode::LdpRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(SP),
                MachOperand::Imm(0),
            ],
        );
        assert!(
            encode_inst(&ldp).is_ok(),
            "LdpRI should accept PReg(SP) base at operand 2"
        );
    }

    #[test]
    fn test_scalar_writeback_allows_xzr_transfer() {
        for opcode in [
            AArch64Opcode::LdrPreIndex,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::StrPostIndex,
        ] {
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::Special(SpecialReg::XZR),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(8),
                ],
            );
            assert!(
                encode_inst(&inst).is_ok(),
                "{opcode:?} should accept XZR transfer"
            );

            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(XZR),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(8),
                ],
            );
            assert!(
                encode_inst(&inst).is_ok(),
                "{opcode:?} should accept PReg(XZR) transfer"
            );
        }
    }

    #[test]
    fn test_scalar_writeback_rejects_sp_transfer() {
        for opcode in [
            AArch64Opcode::LdrPreIndex,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::StrPostIndex,
        ] {
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(8),
                ],
            );
            assert!(
                encode_inst(&inst).is_err(),
                "{opcode:?} should reject SP transfer"
            );

            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(SP),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(8),
                ],
            );
            assert!(
                encode_inst(&inst).is_err(),
                "{opcode:?} should reject PReg(SP) transfer"
            );
        }
    }

    #[test]
    fn test_scalar_writeback_allows_sp_base() {
        for opcode in [
            AArch64Opcode::LdrPreIndex,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::StrPostIndex,
        ] {
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(8),
                ],
            );
            assert!(
                encode_inst(&inst).is_ok(),
                "{opcode:?} should accept SP base"
            );

            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(SP),
                    MachOperand::Imm(8),
                ],
            );
            assert!(
                encode_inst(&inst).is_ok(),
                "{opcode:?} should accept PReg(SP) base"
            );
        }
    }

    #[test]
    fn test_scalar_writeback_rejects_base_transfer_overlap() {
        for opcode in [
            AArch64Opcode::LdrPreIndex,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::StrPostIndex,
        ] {
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(8),
                ],
            );
            assert!(
                encode_inst(&inst).is_err(),
                "{opcode:?} should reject writeback base/transfer overlap"
            );
        }
    }

    #[test]
    fn test_scalar_writeback_rejects_non_imm9_offset() {
        let bad_type = MachInst::new(
            AArch64Opcode::LdrPreIndex,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        assert!(encode_inst(&bad_type).is_err());

        let out_of_range = MachInst::new(
            AArch64Opcode::StrPostIndex,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(256),
            ],
        );
        assert!(encode_inst(&out_of_range).is_err());
    }

    #[test]
    fn test_pair_offset_rejects_old_order_sp_transfer() {
        let inst = MachInst::new(
            AArch64Opcode::StpRI,
            vec![
                MachOperand::PReg(SP),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(0),
            ],
        );
        let result = encode_inst(&inst);
        assert!(
            result.is_err(),
            "old-order StpRI with SP at operand 0 should not validate"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("pair transfer register operand"),
            "Error should mention pair transfer register, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_pair_offset_rejects_special_transfer_registers() {
        let sp_transfer = MachInst::new(
            AArch64Opcode::StpRI,
            vec![
                MachOperand::Special(SpecialReg::SP),
                MachOperand::PReg(X0),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(0),
            ],
        );
        assert!(
            encode_inst(&sp_transfer).is_err(),
            "Special(SP) is only valid as the pair base operand"
        );

        let xzr_transfer = MachInst::new(
            AArch64Opcode::LdpRI,
            vec![
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::PReg(X1),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(0),
            ],
        );
        assert!(
            encode_inst(&xzr_transfer).is_err(),
            "Special(XZR) should not validate as a pair transfer operand"
        );
    }

    #[test]
    fn test_pair_offset_rejects_preg_zero_transfer_registers() {
        let xzr_transfer = MachInst::new(
            AArch64Opcode::StpRI,
            vec![
                MachOperand::PReg(XZR),
                MachOperand::PReg(X0),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(0),
            ],
        );
        assert!(
            encode_inst(&xzr_transfer).is_err(),
            "PReg(XZR) should not validate as a pair transfer operand"
        );

        let wzr_transfer = MachInst::new(
            AArch64Opcode::LdpRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(WZR),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(0),
            ],
        );
        assert!(
            encode_inst(&wzr_transfer).is_err(),
            "PReg(WZR) should not validate as a pair transfer operand"
        );
    }

    #[test]
    fn test_pair_offset_rejects_register_31_alias_bases() {
        for base in [
            MachOperand::PReg(WSP),
            MachOperand::PReg(XZR),
            MachOperand::PReg(WZR),
        ] {
            let inst = MachInst::new(
                AArch64Opcode::StpRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    base,
                    MachOperand::Imm(0),
                ],
            );
            let result = encode_inst(&inst);
            assert!(
                result.is_err(),
                "register-31 alias should not validate as a pair base"
            );
            let err_msg = result.unwrap_err().to_string();
            assert!(
                err_msg.contains("pair base register operand"),
                "Error should mention pair base register, got: {}",
                err_msg
            );
        }
    }

    #[test]
    fn test_pair_offset_rejects_non_imm_offset_operand() {
        for opcode in [AArch64Opcode::StpRI, AArch64Opcode::LdpRI] {
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::PReg(X2),
                ],
            );
            let result = encode_inst(&inst);
            assert!(
                result.is_err(),
                "{:?} should reject non-immediate operand 3",
                opcode
            );
            let err_msg = result.unwrap_err().to_string();
            assert!(
                err_msg.contains("pair offset immediate operand"),
                "Error should mention pair offset immediate, got: {}",
                err_msg
            );
        }
    }

    // -----------------------------------------------------------------------
    // Bug #105: FP size derived from register class, not hardcoded
    // -----------------------------------------------------------------------

    #[test]
    fn test_fp_add_double_precision() {
        use trust_cg_ir::regs::{D0, D1};
        let inst = MachInst::new(
            AArch64Opcode::FaddRR,
            vec![
                MachOperand::PReg(D0),
                MachOperand::PReg(D0),
                MachOperand::PReg(D1),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let ftype = (word >> 22) & 0b11;
        assert_eq!(
            ftype, 0b01,
            "FADD with D-regs should use ftype=01 (double), got {}",
            ftype
        );
    }

    #[test]
    fn test_fp_add_single_precision() {
        use trust_cg_ir::regs::{S0, S1};
        let inst = MachInst::new(
            AArch64Opcode::FaddRR,
            vec![
                MachOperand::PReg(S0),
                MachOperand::PReg(S0),
                MachOperand::PReg(S1),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let ftype = (word >> 22) & 0b11;
        assert_eq!(
            ftype, 0b00,
            "FADD with S-regs should use ftype=00 (single), got {}",
            ftype
        );
    }

    #[test]
    fn test_fp_add_rejects_gpr_operand() {
        let inst = MachInst::new(
            AArch64Opcode::FaddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        );
        let result = encode_inst(&inst);
        assert!(
            result.is_err(),
            "FADD with GPR operands should error, not silently default to double"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("expected FPR"),
            "Error should mention expected FPR, got: {}",
            err_msg
        );
    }

    #[test]
    fn test_fp_neg_single_precision() {
        use trust_cg_ir::regs::{S0, S1};
        let inst = MachInst::new(
            AArch64Opcode::FnegRR,
            vec![MachOperand::PReg(S0), MachOperand::PReg(S1)],
        );
        let word = encode_inst(&inst).unwrap();
        let ftype = (word >> 22) & 0b11;
        assert_eq!(
            ftype, 0b00,
            "FNEG with S-regs should use ftype=00 (single), got {}",
            ftype
        );
    }

    #[test]
    fn test_fcmp_single_precision() {
        use trust_cg_ir::regs::{S0, S1};
        let inst = MachInst::new(
            AArch64Opcode::Fcmp,
            vec![MachOperand::PReg(S0), MachOperand::PReg(S1)],
        );
        let word = encode_inst(&inst).unwrap();
        let ftype = (word >> 22) & 0b11;
        assert_eq!(
            ftype, 0b00,
            "FCMP with S-regs should use ftype=00 (single), got {}",
            ftype
        );
    }

    #[test]
    fn test_fcvtzs_single_precision() {
        use trust_cg_ir::regs::S0;
        let inst = MachInst::new(
            AArch64Opcode::FcvtzsRR,
            vec![
                MachOperand::PReg(trust_cg_ir::regs::PReg::new(32)),
                MachOperand::PReg(S0),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let ftype = (word >> 22) & 0b11;
        assert_eq!(
            ftype, 0b00,
            "FCVTZS from S-reg should use ftype=00 (single), got {}",
            ftype
        );
    }

    #[test]
    fn test_scvtf_single_precision() {
        use trust_cg_ir::regs::S0;
        let inst = MachInst::new(
            AArch64Opcode::ScvtfRR,
            vec![MachOperand::PReg(S0), MachOperand::PReg(X0)],
        );
        let word = encode_inst(&inst).unwrap();
        let ftype = (word >> 22) & 0b11;
        assert_eq!(
            ftype, 0b00,
            "SCVTF to S-reg should use ftype=00 (single), got {}",
            ftype
        );
    }

    // -----------------------------------------------------------------------
    // Immediate shift encoding tests (previously emitted NOP — fixed in #134)
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_lsl_ri_not_nop() {
        // LSL X0, X1, #2 must NOT emit NOP
        let inst = MachInst::new(
            AArch64Opcode::LslRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_ne!(word, 0xD503201F, "LSL X0, X1, #2 must not emit NOP");
        // Verify it matches the unified encoder
        let unified = crate::aarch64::encode::encode_instruction(&inst).unwrap();
        assert_eq!(
            word, unified,
            "lower and unified must agree for LslRI: lower=0x{word:08X}, unified=0x{unified:08X}"
        );
    }

    #[test]
    fn test_encode_lsr_ri_not_nop() {
        let inst = MachInst::new(
            AArch64Opcode::LsrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_ne!(word, 0xD503201F, "LSR X0, X1, #2 must not emit NOP");
        let unified = crate::aarch64::encode::encode_instruction(&inst).unwrap();
        assert_eq!(
            word, unified,
            "lower and unified must agree for LsrRI: lower=0x{word:08X}, unified=0x{unified:08X}"
        );
    }

    #[test]
    fn test_encode_asr_ri_not_nop() {
        let inst = MachInst::new(
            AArch64Opcode::AsrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_ne!(word, 0xD503201F, "ASR X0, X1, #2 must not emit NOP");
        let unified = crate::aarch64::encode::encode_instruction(&inst).unwrap();
        assert_eq!(
            word, unified,
            "lower and unified must agree for AsrRI: lower=0x{word:08X}, unified=0x{unified:08X}"
        );
    }

    #[test]
    fn test_encode_lsl_ri_known_value() {
        // LSL X0, X1, #2 = UBFM X0, X1, #62, #61
        // Expected: 0xD37EF420 (from ARM ARM)
        let inst = MachInst::new(
            AArch64Opcode::LslRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(word, 0xD37EF420, "LSL X0, X1, #2 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_lsr_ri_known_value() {
        // LSR X0, X1, #2 = UBFM X0, X1, #2, #63
        // Expected: 0xD342FC20
        let inst = MachInst::new(
            AArch64Opcode::LsrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(word, 0xD342FC20, "LSR X0, X1, #2 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_asr_ri_known_value() {
        // ASR X0, X1, #2 = SBFM X0, X1, #2, #63
        // Expected: 0x9342FC20
        let inst = MachInst::new(
            AArch64Opcode::AsrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(word, 0x9342FC20, "ASR X0, X1, #2 = 0x{word:08X}");
    }

    // -----------------------------------------------------------------------
    // UBFM/SBFM/BFM encoding tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_ubfm() {
        // UBFM X0, X1, #2, #5
        let inst = MachInst::new(
            AArch64Opcode::Ubfm,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(2),
                MachOperand::Imm(5),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let unified = crate::aarch64::encode::encode_instruction(&inst).unwrap();
        assert_eq!(
            word, unified,
            "lower and unified must agree for UBFM: lower=0x{word:08X}, unified=0x{unified:08X}"
        );
        // Check opc field = 10 (UBFM)
        assert_eq!((word >> 29) & 0b11, 0b10, "UBFM opc should be 10");
    }

    #[test]
    fn test_encode_sbfm() {
        // SBFM X0, X1, #0, #31 (= SXTW alias)
        let inst = MachInst::new(
            AArch64Opcode::Sbfm,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(0),
                MachOperand::Imm(31),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let unified = crate::aarch64::encode::encode_instruction(&inst).unwrap();
        assert_eq!(
            word, unified,
            "lower and unified must agree for SBFM: lower=0x{word:08X}, unified=0x{unified:08X}"
        );
        // Check opc field = 00 (SBFM)
        assert_eq!((word >> 29) & 0b11, 0b00, "SBFM opc should be 00");
    }

    #[test]
    fn test_encode_bfm() {
        // BFM X0, X1, #4, #7
        let inst = MachInst::new(
            AArch64Opcode::Bfm,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(4),
                MachOperand::Imm(7),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let unified = crate::aarch64::encode::encode_instruction(&inst).unwrap();
        assert_eq!(
            word, unified,
            "lower and unified must agree for BFM: lower=0x{word:08X}, unified=0x{unified:08X}"
        );
        // Check opc field = 01 (BFM)
        assert_eq!((word >> 29) & 0b11, 0b01, "BFM opc should be 01");
    }

    // -----------------------------------------------------------------------
    // LDR/STR register offset encoding tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_ldr_ro() {
        // LDR X0, [X1, X2]
        let inst = MachInst::new(
            AArch64Opcode::LdrRO,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_ne!(word, 0xD503201F, "LdrRO must not emit NOP");
        // Check it's a load (opc=01) and register offset (bit 21=1)
        assert_eq!((word >> 22) & 0b11, 0b01, "LdrRO should have opc=01 (load)");
        assert_eq!(
            (word >> 21) & 1,
            1,
            "LdrRO should have bit 21=1 (register offset)"
        );
    }

    #[test]
    fn test_encode_str_ro() {
        // STR X0, [X1, X2]
        let inst = MachInst::new(
            AArch64Opcode::StrRO,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_ne!(word, 0xD503201F, "StrRO must not emit NOP");
        // Check it's a store (opc=00) and register offset (bit 21=1)
        assert_eq!(
            (word >> 22) & 0b11,
            0b00,
            "StrRO should have opc=00 (store)"
        );
        assert_eq!(
            (word >> 21) & 1,
            1,
            "StrRO should have bit 21=1 (register offset)"
        );
    }

    // -----------------------------------------------------------------------
    // GOT/TLV load encoding tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_ldr_got() {
        // LDR X0, [X1, #0] (GOT load)
        let inst = MachInst::new(
            AArch64Opcode::LdrGot,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(0),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_ne!(word, 0xD503201F, "LdrGot must not emit NOP");
        // Verify it's a 64-bit load (size=11) with unsigned offset
        assert_eq!(
            (word >> 30) & 0b11,
            0b11,
            "LdrGot size should be 11 (64-bit)"
        );
        assert_eq!((word >> 22) & 0b11, 0b01, "LdrGot opc should be 01 (load)");
    }

    #[test]
    fn test_encode_ldr_tlvp() {
        // LDR X0, [X1, #0] (TLV load)
        let inst = MachInst::new(
            AArch64Opcode::LdrTlvp,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(0),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_ne!(word, 0xD503201F, "LdrTlvp must not emit NOP");
        assert_eq!(
            (word >> 30) & 0b11,
            0b11,
            "LdrTlvp size should be 11 (64-bit)"
        );
    }

    // -----------------------------------------------------------------------
    // BIC, CSINC, CSINV, CSNEG, MOVN encoding tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_bic_rr() {
        // BIC X0, X1, X2 = AND X0, X1, NOT(X2)
        // Uses same convention as ORN: N-bit encoded via shift param in
        // encode_logical_shifted_reg (see note in ORN — pre-existing convention).
        let inst = MachInst::new(
            AArch64Opcode::BicRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // BIC uses opc=00 (AND family)
        assert_eq!(
            (word >> 29) & 0b11,
            0b00,
            "BIC opc should be 00 (AND family)"
        );
        // Verify encoding matches encode_logical_shifted_reg with same convention as ORN
        let expected = encoding::encode_logical_shifted_reg(1, 0b00, 1, 0, 2, 0, 1, 0);
        assert_eq!(word, expected, "BIC X0, X1, X2 = 0x{word:08X}");
    }

    #[test]
    fn test_encode_csinc() {
        // CSINC X0, X1, X2, EQ (cond=0)
        let inst = MachInst::new(
            AArch64Opcode::Csinc,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(0), // EQ condition
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // Check op2 field = 01 (CSINC)
        assert_eq!((word >> 10) & 0b11, 0b01, "CSINC op2 should be 01");
        // Check opc field is 00 (not CSINV/CSNEG which use 10)
        assert_eq!(
            (word >> 29) & 0b11,
            0b00,
            "CSINC should have bits 30:29 = 00"
        );
    }

    #[test]
    fn test_encode_csinv() {
        // CSINV X0, X1, X2, NE (cond=1) — 64-bit form
        let inst = MachInst::new(
            AArch64Opcode::Csinv,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(1), // NE condition
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // Check op2 field = 00 (CSINV)
        assert_eq!((word >> 10) & 0b11, 0b00, "CSINV op2 should be 00");
        // Check bit 30 = 1 (CSINV uses op=1)
        assert_eq!((word >> 30) & 1, 1, "CSINV should have bit 30 = 1");
        // S-field (bit 29) must be 0 — CSINV is non-flag-setting (#165)
        assert_eq!((word >> 29) & 1, 0, "CSINV S-field (bit 29) must be 0");
        // sf (bit 31) = 1 for 64-bit
        assert_eq!((word >> 31) & 1, 1, "64-bit CSINV should have sf=1");
    }

    #[test]
    fn test_encode_csinv_32bit() {
        // CSINV W0, W1, W2, NE (cond=1) — 32-bit form (#165)
        let inst = MachInst::new(
            AArch64Opcode::Csinv,
            vec![
                MachOperand::PReg(W0),
                MachOperand::PReg(W1),
                MachOperand::PReg(W2),
                MachOperand::Imm(1), // NE condition
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // Check op2 field = 00 (CSINV)
        assert_eq!((word >> 10) & 0b11, 0b00, "32-bit CSINV op2 should be 00");
        // Check bit 30 = 1 (CSINV uses op=1)
        assert_eq!((word >> 30) & 1, 1, "32-bit CSINV should have bit 30 = 1");
        // S-field (bit 29) must be 0 — CSINV is non-flag-setting (#165)
        assert_eq!(
            (word >> 29) & 1,
            0,
            "32-bit CSINV S-field (bit 29) must be 0"
        );
        // sf (bit 31) = 0 for 32-bit
        assert_eq!((word >> 31) & 1, 0, "32-bit CSINV should have sf=0");
    }

    #[test]
    fn test_encode_csneg() {
        // CSNEG X0, X1, X2, EQ (cond=0) — 64-bit form
        let inst = MachInst::new(
            AArch64Opcode::Csneg,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(0),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // Check op2 field = 01 (CSNEG)
        assert_eq!((word >> 10) & 0b11, 0b01, "CSNEG op2 should be 01");
        // Check bit 30 = 1 (CSNEG uses op=1)
        assert_eq!((word >> 30) & 1, 1, "CSNEG should have bit 30 = 1");
        // S-field (bit 29) must be 0 — CSNEG is non-flag-setting (#165)
        assert_eq!((word >> 29) & 1, 0, "CSNEG S-field (bit 29) must be 0");
        // sf (bit 31) = 1 for 64-bit
        assert_eq!((word >> 31) & 1, 1, "64-bit CSNEG should have sf=1");
    }

    #[test]
    fn test_encode_csneg_32bit() {
        // CSNEG W0, W1, W2, EQ (cond=0) — 32-bit form (#165)
        let inst = MachInst::new(
            AArch64Opcode::Csneg,
            vec![
                MachOperand::PReg(W0),
                MachOperand::PReg(W1),
                MachOperand::PReg(W2),
                MachOperand::Imm(0),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        // Check op2 field = 01 (CSNEG)
        assert_eq!((word >> 10) & 0b11, 0b01, "32-bit CSNEG op2 should be 01");
        // Check bit 30 = 1 (CSNEG uses op=1)
        assert_eq!((word >> 30) & 1, 1, "32-bit CSNEG should have bit 30 = 1");
        // S-field (bit 29) must be 0 — CSNEG is non-flag-setting (#165)
        assert_eq!(
            (word >> 29) & 1,
            0,
            "32-bit CSNEG S-field (bit 29) must be 0"
        );
        // sf (bit 31) = 0 for 32-bit
        assert_eq!((word >> 31) & 1, 0, "32-bit CSNEG should have sf=0");
    }

    #[test]
    fn test_encode_movn() {
        // MOVN X0, #42
        let inst = MachInst::new(
            AArch64Opcode::Movn,
            vec![MachOperand::PReg(X0), MachOperand::Imm(42)],
        );
        let word = encode_inst(&inst).unwrap();
        // MOVN uses opc=00 in the move-wide encoding
        let opc = (word >> 29) & 0b11;
        assert_eq!(opc, 0b00, "MOVN opc should be 00");
        // Check the immediate is embedded
        let imm_field = (word >> 5) & 0xFFFF;
        assert_eq!(imm_field, 42, "MOVN imm16 should be 42");
    }

    #[test]
    fn test_encode_movn_shift_zero_only() {
        let explicit_zero = MachInst::new(
            AArch64Opcode::Movn,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(0x1234),
                MachOperand::Imm(0),
            ],
        );
        let word = encode_inst(&explicit_zero).unwrap();
        assert_eq!((word >> 29) & 0b11, 0b00, "MOVN opc should be 00");
        assert_eq!((word >> 21) & 0b11, 0, "MOVN hw must remain zero");
        assert_eq!((word >> 5) & 0xFFFF, 0x1234, "MOVN imm16");

        let shifted = MachInst::new(
            AArch64Opcode::Movn,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(0xFFFF),
                MachOperand::Imm(32),
            ],
        );
        assert!(
            encode_inst(&shifted).is_err(),
            "the pipeline encoder must not bypass shifted-MOVN rejection"
        );
    }

    // -----------------------------------------------------------------------
    // Bug #173: is_64bit helper must correctly classify W-registers as 32-bit
    // -----------------------------------------------------------------------

    #[test]
    fn test_is_64bit_w0_returns_false() {
        // BicRR with W-registers should produce sf=0 (bit 31=0)
        use trust_cg_ir::regs::W0;
        let inst = MachInst::new(
            AArch64Opcode::BicRR,
            vec![
                MachOperand::PReg(W0),
                MachOperand::PReg(W1),
                MachOperand::PReg(W2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(
            (word >> 31) & 1,
            0,
            "BIC W0, W1, W2 should have sf=0 (32-bit), got sf=1"
        );
    }

    #[test]
    fn test_is_64bit_x0_returns_true() {
        // BicRR with X-registers should produce sf=1 (bit 31=1)
        let inst = MachInst::new(
            AArch64Opcode::BicRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(
            (word >> 31) & 1,
            1,
            "BIC X0, X1, X2 should have sf=1 (64-bit), got sf=0"
        );
    }

    #[test]
    fn test_is_64bit_w30_returns_false() {
        // W30 (encoding=62) must be classified as 32-bit
        use trust_cg_ir::regs::W30;
        let inst = MachInst::new(
            AArch64Opcode::Movn,
            vec![MachOperand::PReg(W30), MachOperand::Imm(0)],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(
            (word >> 31) & 1,
            0,
            "MOVN W30, #0 should have sf=0 (32-bit), got sf=1"
        );
    }

    #[test]
    fn test_is_64bit_x30_returns_true() {
        // X30 (encoding=30) must be classified as 64-bit
        use trust_cg_ir::regs::X30;
        let inst = MachInst::new(
            AArch64Opcode::Movn,
            vec![MachOperand::PReg(X30), MachOperand::Imm(0)],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(
            (word >> 31) & 1,
            1,
            "MOVN X30, #0 should have sf=1 (64-bit), got sf=0"
        );
    }

    #[test]
    fn test_csinc_w_registers_sf0() {
        // CSINC W0, W1, W2, EQ — sf must be 0
        let inst = MachInst::new(
            AArch64Opcode::Csinc,
            vec![
                MachOperand::PReg(W0),
                MachOperand::PReg(W1),
                MachOperand::PReg(W2),
                MachOperand::Imm(0), // EQ
            ],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(
            (word >> 31) & 1,
            0,
            "CSINC W0, W1, W2, EQ should have sf=0 (32-bit)"
        );
        // Also verify it's still a CSINC (op2=01)
        assert_eq!((word >> 10) & 0b11, 0b01, "CSINC op2 should be 01");
    }

    #[test]
    fn test_movn_w_register_sf0() {
        // MOVN W0, #42 — sf must be 0
        let inst = MachInst::new(
            AArch64Opcode::Movn,
            vec![MachOperand::PReg(W0), MachOperand::Imm(42)],
        );
        let word = encode_inst(&inst).unwrap();
        assert_eq!(
            (word >> 31) & 1,
            0,
            "MOVN W0, #42 should have sf=0 (32-bit)"
        );
        let imm_field = (word >> 5) & 0xFFFF;
        assert_eq!(imm_field, 42, "MOVN W0 imm16 should be 42");
    }

    #[test]
    fn test_ldr_ro_w_register_32bit_size() {
        // LDR W0, [X1, X2] — size should be 10 (32-bit), not 11 (64-bit)
        let inst = MachInst::new(
            AArch64Opcode::LdrRO,
            vec![
                MachOperand::PReg(W0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let size = (word >> 30) & 0b11;
        assert_eq!(
            size, 0b10,
            "LDR W0, [X1, X2] should have size=10 (32-bit), got {:02b}",
            size
        );
    }

    #[test]
    fn test_str_ro_w_register_32bit_size() {
        // STR W0, [X1, X2] — size should be 10 (32-bit), not 11 (64-bit)
        let inst = MachInst::new(
            AArch64Opcode::StrRO,
            vec![
                MachOperand::PReg(W0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let word = encode_inst(&inst).unwrap();
        let size = (word >> 30) & 0b11;
        assert_eq!(
            size, 0b10,
            "STR W0, [X1, X2] should have size=10 (32-bit), got {:02b}",
            size
        );
    }

    #[test]
    fn test_tst_logical_immediate_survives_final_lowering() {
        for (rn, expected_sf) in [(X0, 1u32), (W0, 0u32)] {
            let inst = MachInst::new(
                AArch64Opcode::Tst,
                vec![MachOperand::PReg(rn), MachOperand::Imm(0xff)],
            );
            let lowered = encode_inst(&inst)
                .expect("final lowering must accept AndCmpFuse's TST-immediate shape");
            assert_eq!(
                lowered,
                encode_instruction(&inst).expect("unified TST encoder must agree")
            );
            assert_eq!((lowered >> 31) & 1, expected_sf);
        }
    }

    #[test]
    fn test_tst_final_lowering_rejects_malformed_arity() {
        for operands in [
            vec![MachOperand::PReg(X0)],
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(1),
            ],
        ] {
            let err = encode_inst(&MachInst::new(AArch64Opcode::Tst, operands))
                .expect_err("malformed TST must fail closed");
            assert!(matches!(err, LowerError::EncodingFailed(_)));
        }
    }
}
