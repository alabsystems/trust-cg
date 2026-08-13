// trust-cg-codegen/aarch64/encode.rs - Unified AArch64 instruction encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Unified AArch64 instruction encoder.
//!
//! Dispatches each `AArch64Opcode` to the correct low-level encoding function
//! from [`encoding`], [`encoding_mem`], or [`encoding_fp`]. This is the single
//! entry point used by the pipeline — no inline bit manipulation elsewhere.
//!
//! Design: the encoder takes an `IrMachInst` (post-regalloc, physical registers
//! only) and returns a 32-bit encoded instruction word.

use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{RegClass, SP, SpecialReg, WSP, XZR, preg_class};

use super::encoding;
use super::encoding_fp::{self, FpArithOp, FpCmpOp, FpConvOp, FpMaddOp, FpSize};
use super::encoding_mem;
use super::encoding_neon;

use thiserror::Error;

/// AArch64 NOP encoding (used as fallback for pseudos).
const NOP: u32 = 0xD503201F;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from unified instruction encoding.
#[derive(Debug, Error)]
pub enum EncodeError {
    #[error("unsupported opcode: {0:?}")]
    UnsupportedOpcode(AArch64Opcode),
    #[error("pseudo-instruction should not reach encoder: {0:?}")]
    PseudoInstruction(AArch64Opcode),
    #[error("operand {index} missing (opcode={opcode:?}, expected at least {expected})")]
    MissingOperand {
        opcode: AArch64Opcode,
        index: usize,
        expected: usize,
    },
    #[error("memory encoding error: {0}")]
    MemEncode(#[from] encoding_mem::EncodeError),
    #[error("FP encoding error: {0}")]
    FpEncode(#[from] encoding_fp::FpEncodeError),
    #[error("NEON encoding error: {0}")]
    NeonEncode(#[from] encoding_neon::NeonEncodeError),
    #[error("unsupported FP size {size:?} for opcode {opcode:?}")]
    UnsupportedFpSize { opcode: AArch64Opcode, size: FpSize },
    #[error("invalid operand at index {index} for {opcode:?}: expected register, got {desc}")]
    InvalidOperand {
        opcode: AArch64Opcode,
        index: usize,
        desc: String,
    },
    /// A move-wide instruction carries an immediate that does not fit its
    /// 16-bit field. Silently truncating it would select a different constant
    /// (exactly how issue #366 manifested at runtime), so fail closed.
    #[error(
        "move-wide immediate 0x{imm:016x} does not fit in 16 bits for {opcode:?}; \
         use a canonical hw0 seed plus MOVK repairs instead (#366)"
    )]
    MovImmTooWide { opcode: AArch64Opcode, imm: u64 },
}

// ---------------------------------------------------------------------------
// Operand extraction helpers
// ---------------------------------------------------------------------------

/// Extract the hardware register number from an operand (PReg or Special).
/// Returns an error for non-register operands instead of silently defaulting
/// to XZR (reg 31), which would produce wrong code (#174).
fn preg_hw(inst: &MachInst, idx: usize) -> Result<u32, EncodeError> {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) => Ok(p.hw_enc() as u32),
        Some(MachOperand::Special(s)) => match s {
            SpecialReg::SP | SpecialReg::XZR | SpecialReg::WZR => Ok(31),
        },
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("{:?}", other),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: idx,
            expected: idx + 1,
        }),
    }
}

/// Reject non-GPR physical registers in a GPR-only move alias.
///
/// `MovR`/`MOVWrr`/`MOVXrr` encode as `ORR Rd, XZR, Rm` (or `ADD Rd, SP, #0`),
/// which can only name general-purpose registers. An FPR (or System) operand
/// reaching one of these opcodes would silently encode the register's 5-bit hw
/// index as an unrelated GPR — the exact mechanism of the FP loop-carried
/// block-arg P0 miscompile (clobbers a live GPR AND never moves the FP value).
/// Fail closed instead.
fn require_gpr_move_operands(inst: &MachInst, count: usize) -> Result<(), EncodeError> {
    for idx in 0..count {
        if let Some(MachOperand::PReg(p)) = inst.operands.get(idx)
            && !matches!(preg_class(*p), RegClass::Gpr32 | RegClass::Gpr64)
        {
            return Err(EncodeError::InvalidOperand {
                opcode: inst.opcode,
                index: idx,
                desc: format!(
                    "GPR move alias cannot encode {:?} (class {:?}); FPR copies must \
                     use FmovFprFpr (H/S/D) or NeonOrrV (Q) — fail-closed",
                    p,
                    preg_class(*p)
                ),
            });
        }
    }
    Ok(())
}

/// Validate one register operand of `TST` and return its architectural width.
///
/// Logical-register encodings interpret register number 31 as ZR, never SP.
/// Merely calling `preg_hw` is insufficient because SP and an FPR share an
/// encodable five-bit hardware number and would silently name a different GPR.
fn tst_gpr_width(inst: &MachInst, index: usize) -> Result<u32, EncodeError> {
    match inst.operands.get(index) {
        Some(MachOperand::PReg(p))
            if *p != SP
                && *p != WSP
                && matches!(preg_class(*p), RegClass::Gpr32 | RegClass::Gpr64) =>
        {
            Ok(preg_class(*p).size_bits())
        }
        Some(MachOperand::Special(SpecialReg::XZR)) => Ok(64),
        Some(MachOperand::Special(SpecialReg::WZR)) => Ok(32),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index,
            desc: format!(
                "TST register operand must be a scalar GPR or ZR (SP is not encodable), got {other:?}"
            ),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index,
            expected: 2,
        }),
    }
}

/// Enforce the canonical operand arity of a move-wide instruction.
fn require_move_wide_arity(inst: &MachInst, min: usize, max: usize) -> Result<(), EncodeError> {
    let actual = inst.operands.len();
    if actual < min {
        return Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: actual,
            expected: min,
        });
    }
    if actual > max {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: max,
            desc: format!("move-wide form accepts {min}..={max} operands; got {actual}"),
        });
    }
    Ok(())
}

/// Validate a move-wide destination before deriving `sf` or its hardware
/// register field. Register number 31 denotes ZR in these encodings, never SP.
fn require_move_wide_destination(inst: &MachInst) -> Result<(), EncodeError> {
    match inst.operands.first() {
        Some(MachOperand::PReg(p))
            if matches!(preg_class(*p), RegClass::Gpr32 | RegClass::Gpr64)
                && *p != SP
                && *p != WSP =>
        {
            Ok(())
        }
        Some(MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR)) => Ok(()),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 0,
            desc: format!(
                "move-wide destination must be a GPR or ZR (SP is not encodable), got {other:?}"
            ),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: 0,
            expected: 2,
        }),
    }
}

fn require_move_wide_destination_width(
    inst: &MachInst,
    expected: RegClass,
) -> Result<(), EncodeError> {
    let actual = match inst.operands.first() {
        Some(MachOperand::PReg(p)) => preg_class(*p),
        Some(MachOperand::Special(SpecialReg::WZR)) => RegClass::Gpr32,
        Some(MachOperand::Special(SpecialReg::XZR)) => RegClass::Gpr64,
        _ => return require_move_wide_destination(inst),
    };
    if actual != expected {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 0,
            desc: format!(
                "typed move-wide destination must have class {expected:?}, got {actual:?}"
            ),
        });
    }
    Ok(())
}

/// Reject operands that are not scalar FPRs (H/S/D) in `FmovFprFpr`.
///
/// Scalar `FMOV` has no Q-register form: encoding a 128-bit (or GPR) operand
/// here would silently default to the D form, truncating the upper 64 bits
/// (or moving the wrong register file). Both operands must also agree on
/// width, since `FMOV Sd, Dn` is not a valid encoding.
fn require_scalar_fpr_move_operands(inst: &MachInst) -> Result<(), EncodeError> {
    let mut classes = [RegClass::Fpr64; 2];
    for (idx, class) in classes.iter_mut().enumerate() {
        match inst.operands.get(idx) {
            Some(MachOperand::PReg(p))
                if matches!(
                    preg_class(*p),
                    RegClass::Fpr16 | RegClass::Fpr32 | RegClass::Fpr64
                ) =>
            {
                *class = preg_class(*p);
            }
            Some(other) => {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: idx,
                    desc: format!(
                        "FMOV (register) requires a scalar FPR (H/S/D), got {other:?}; \
                         Q-register copies must use NeonOrrV — fail-closed"
                    ),
                });
            }
            None => {
                return Err(EncodeError::MissingOperand {
                    opcode: inst.opcode,
                    index: idx,
                    expected: 2,
                });
            }
        }
    }
    if classes[0] != classes[1] {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 1,
            desc: format!(
                "FMOV (register) operand widths differ: dst {:?} vs src {:?} — fail-closed",
                classes[0], classes[1]
            ),
        });
    }
    Ok(())
}

/// Require that `FCSEL Rd, Rn, Rm, cond`'s three register operands (0/1/2) are
/// all the SAME scalar FPR class (S=`Fpr32` or D=`Fpr64`) and return the derived
/// [`FpSize`].
///
/// This is the BANK CHECK the GPR `Csel` encoder lacks: `Csel` writes the 5-bit
/// register number straight into the GPR field with no class check, so an FPR
/// operand reaching it would silently encode as a CSEL on the collided GPRs
/// (FPR hw 0-31 alias GPR hw 0-31) — the audit-era P0 the FP-select path
/// fail-closed around. `FcselRR` instead fails closed here on any GPR, on the
/// `Fpr16` (half — the f16 FCSEL form is deliberately not modeled) / `Fpr128`
/// (no scalar FCSEL) class, and on a width mismatch between the three regs.
fn require_fcsel_operands(inst: &MachInst) -> Result<FpSize, EncodeError> {
    let mut class = None;
    for idx in 0..3 {
        match inst.operands.get(idx) {
            Some(MachOperand::PReg(p))
                if matches!(preg_class(*p), RegClass::Fpr32 | RegClass::Fpr64) =>
            {
                let c = preg_class(*p);
                match class {
                    None => class = Some(c),
                    Some(prev) if prev != c => {
                        return Err(EncodeError::InvalidOperand {
                            opcode: inst.opcode,
                            index: idx,
                            desc: format!(
                                "FCSEL operand widths differ: {prev:?} vs {c:?} — fail-closed"
                            ),
                        });
                    }
                    _ => {}
                }
            }
            Some(other) => {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: idx,
                    desc: format!(
                        "FCSEL requires a scalar FPR (S/D) in operand {idx}, got {other:?}; \
                         all three regs must be FPRs (no GPR/half/Q, the bank check the GPR \
                         Csel lacks) — fail-closed"
                    ),
                });
            }
            None => {
                return Err(EncodeError::MissingOperand {
                    opcode: inst.opcode,
                    index: idx,
                    expected: 3,
                });
            }
        }
    }
    Ok(match class {
        Some(RegClass::Fpr32) => FpSize::Single,
        Some(RegClass::Fpr64) => FpSize::Double,
        // Unreachable: the loop only accepts Fpr32/Fpr64.
        _ => FpSize::Double,
    })
}

fn reject_sp_in_shifted_reg(inst: &MachInst) -> Result<(), EncodeError> {
    for idx in 0..3 {
        if matches!(
            inst.operands.get(idx),
            Some(MachOperand::Special(SpecialReg::SP))
        ) {
            return Err(EncodeError::InvalidOperand {
                opcode: inst.opcode,
                index: idx,
                desc: "SP is not encodable in AArch64 ADD/SUB shifted-register form; use ADD/SUB immediate or move SP through a GPR".to_string(),
            });
        }
    }
    Ok(())
}

/// Extract an immediate value from an operand. Returns 0 for non-immediates.
fn imm_val(inst: &MachInst, idx: usize) -> i64 {
    match inst.operands.get(idx) {
        Some(MachOperand::Imm(v)) => *v,
        _ => 0,
    }
}

/// Extract an immediate value from an operand, rejecting symbolic targets.
fn imm_operand(inst: &MachInst, idx: usize) -> Result<i64, EncodeError> {
    match inst.operands.get(idx) {
        Some(MachOperand::Imm(v)) => Ok(*v),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("expected immediate, got {:?}", other),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: idx,
            expected: idx + 1,
        }),
    }
}

fn imm12_operand(inst: &MachInst, idx: usize) -> Result<u32, EncodeError> {
    let imm = imm_operand(inst, idx)?;
    if !(0..=0xFFF).contains(&imm) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("add/sub immediate {imm} out of range [0, 4095]"),
        });
    }
    Ok(imm as u32)
}

fn low_mask(bits: u32) -> u64 {
    if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

fn rotate_right_within(value: u64, rot: u32, width: u32) -> u64 {
    let mask = low_mask(width);
    let value = value & mask;
    if rot == 0 {
        value
    } else {
        ((value >> rot) | (value << (width - rot))) & mask
    }
}

fn replicate_logical_element(pattern: u64, element_width: u32, register_width: u32) -> u64 {
    let mut out = 0;
    let mut shift = 0;
    while shift < register_width {
        out |= pattern << shift;
        shift += element_width;
    }
    out & low_mask(register_width)
}

fn encode_logical_imm_fields(
    raw: i64,
    register_width: u32,
    opcode: AArch64Opcode,
    index: usize,
) -> Result<(u32, u32, u32), EncodeError> {
    let register_mask = low_mask(register_width);
    let raw_mask = (raw as u64) & register_mask;
    if raw_mask == 0 || raw_mask == register_mask {
        return Err(EncodeError::InvalidOperand {
            opcode,
            index,
            desc: format!("logical immediate {raw:#x} is not encodable"),
        });
    }

    let element_widths: &[u32] = if register_width == 64 {
        &[2, 4, 8, 16, 32, 64]
    } else {
        &[2, 4, 8, 16, 32]
    };

    for &element_width in element_widths {
        for ones_len in 1..element_width {
            let ones = low_mask(ones_len);
            for rotation in 0..element_width {
                let element = rotate_right_within(ones, rotation, element_width);
                let candidate = replicate_logical_element(element, element_width, register_width);
                if candidate == raw_mask {
                    let n = u32::from(element_width == 64);
                    let immr = rotation & 0x3f;
                    let imms_prefix = (!((element_width << 1) - 1)) & 0x3f;
                    let imms = imms_prefix | (ones_len - 1);
                    return Ok((n, immr, imms));
                }
            }
        }
    }

    Err(EncodeError::InvalidOperand {
        opcode,
        index,
        desc: format!("logical immediate {raw:#x} is not encodable"),
    })
}

fn logical_imm_operands(inst: &MachInst, sf: u32) -> Result<(u32, u32, u32), EncodeError> {
    if inst.operands.len() == 3 {
        let raw = imm_operand(inst, 2)?;
        let register_width = if sf == 1 { 64 } else { 32 };
        encode_logical_imm_fields(raw, register_width, inst.opcode, 2)
    } else {
        // Pre-decomposed (N, immr, imms) fallback. The 3-operand form above
        // validates encodability; this raw form must range-check each field
        // BEFORE masking — N in {0,1}, immr/imms in [0,63] — so an out-of-range
        // value cannot silently wrap to a different (wrong) logical mask.
        Ok((
            logical_imm_raw_field(inst, 2, 1, "N")?,
            logical_imm_raw_field(inst, 3, 0x3F, "immr")?,
            logical_imm_raw_field(inst, 4, 0x3F, "imms")?,
        ))
    }
}

fn encode_logical_immediate(inst: &MachInst, opc: u32) -> Result<u32, EncodeError> {
    let sf = sf_from_operand(inst, 0);
    let rd = preg_hw(inst, 0)?;
    let rn = preg_hw(inst, 1)?;
    let (n, immr, imms) = logical_imm_operands(inst, sf)?;
    Ok((sf << 31)
        | (opc << 29)
        | (0b100100 << 23)
        | (n << 22)
        | (immr << 16)
        | (imms << 10)
        | (rn << 5)
        | rd)
}

/// Extract base register hw encoding and offset from a load/store instruction.
///
/// Handles two operand layouts:
/// 1. **Register + optional immediate**: `[PReg(base), Imm(offset)]` at indices
///    `base_idx` and `offset_idx`. This is the canonical pre-regalloc form.
/// 2. **MemOp**: `MemOp { base, offset }` at index `base_idx`. This is the
///    post-frame-lowering form produced by `eliminate_frame_indices`.
///
/// Returns `(base_hw_enc, offset)` or an error if the operand is neither.
fn extract_base_offset(
    inst: &MachInst,
    base_idx: usize,
    offset_idx: usize,
) -> Result<(u32, i64), EncodeError> {
    let offset = |inst: &MachInst| match inst.operands.get(offset_idx) {
        Some(MachOperand::Imm(v)) => Ok(*v),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: offset_idx,
            desc: format!("expected immediate offset, got {:?}", other),
        }),
        None => Ok(0),
    };

    match inst.operands.get(base_idx) {
        Some(MachOperand::PReg(p)) => Ok((p.hw_enc() as u32, offset(inst)?)),
        Some(MachOperand::Special(s)) => {
            let hw = match s {
                SpecialReg::SP | SpecialReg::XZR | SpecialReg::WZR => 31u32,
            };
            Ok((hw, offset(inst)?))
        }
        Some(MachOperand::MemOp { base, offset }) => Ok((base.hw_enc() as u32, *offset)),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: base_idx,
            desc: format!("{:?}", other),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: base_idx,
            expected: base_idx + 1,
        }),
    }
}

/// Encode a load/store with unsigned offset or unscaled immediate, depending
/// on whether the offset is non-negative and aligned (unsigned imm12) or
/// negative/unaligned (signed imm9 unscaled).
///
/// * `size` — data width encoding (00=byte, 01=half, 10=word, 11=double)
/// * `v` — 1 for SIMD/FP, 0 for integer
/// * `opc` — 00=store, 01=load (or other opc values for sign-extending loads)
/// * `scale` — access size in bytes (1, 2, 4, or 8)
/// * `offset` — byte offset (signed)
/// * `rn` — base register hw encoding
/// * `rt` — transfer register hw encoding
fn encode_load_store_auto(
    size: u32,
    v: u32,
    opc: u32,
    scale: i64,
    offset: i64,
    rn: u32,
    rt: u32,
) -> Result<u32, EncodeError> {
    if offset >= 0 && offset % scale == 0 {
        let scaled = (offset / scale) as u32;
        if scaled <= 0xFFF {
            return Ok(encoding::encode_load_store_ui(size, v, opc, scaled, rn, rt));
        }
    }
    // Negative or unaligned offset: use unscaled (LDUR/STUR) encoding.
    if (-256..=255).contains(&offset) {
        Ok(encoding::encode_load_store_unscaled(
            size,
            v,
            opc,
            offset as i32,
            rn,
            rt,
        ))
    } else {
        // Out of BOTH the unsigned-scaled and unscaled ranges. This is the
        // fail-closed point the pre-encode offset legalizer
        // (`crate::frame::legalize_large_mem_offsets`) exists to prevent: it
        // rewrites exactly the accesses for which `scalar_ri_offset_encodable`
        // (below) is false, so a well-formed function never reaches here.
        debug_assert!(!scalar_ri_offset_encodable(offset, scale));
        Err(EncodeError::InvalidOperand {
            opcode: AArch64Opcode::StrRI, // generic; caller may override
            index: 1,
            desc: format!(
                "offset {} out of range for both unsigned and unscaled encoding",
                offset
            ),
        })
    }
}

/// Whether a signed byte `offset` for an access of `scale` bytes fits EITHER
/// AArch64 scalar load/store immediate form:
///   * unsigned-scaled  (LDR/STR):   `offset >= 0`, `scale`-aligned, and
///     `offset / scale` in `[0, 4095]`
///   * unscaled signed  (LDUR/STUR): `offset` in `[-256, 255]`
///
/// This is the EXACT predicate `encode_load_store_auto` uses to decide whether
/// it can emit an instruction (both `Ok` branches ⇔ this is `true`; the `Err`
/// branch ⇔ `false`). The pre-encode offset legalizer
/// (`crate::frame::legalize_large_mem_offsets`) consults it via
/// `scalar_ri_mem_scale` so it rewrites *exactly* the accesses the encoder would
/// otherwise reject — never one more (byte-identity for in-range functions).
pub fn scalar_ri_offset_encodable(offset: i64, scale: i64) -> bool {
    debug_assert!(scale > 0);
    (offset >= 0 && offset % scale == 0 && offset / scale <= 0xFFF)
        || (-256..=255).contains(&offset)
}

/// The access size in bytes for a scalar register+immediate load/store whose
/// byte offset is encoded by [`encode_load_store_auto`]. Returns `None` for any
/// opcode/operand shape that is not such a form (pairs, pre/post-index,
/// register-offset, non-memory ops, or a transfer register whose class has no
/// scalar RI encoding here).
///
/// The scale derivation MIRRORS the per-opcode dispatch in `encode_instruction`
/// (via `sf_from_operand` / `is_fpr` / `fp_mem_fields_from_preg_class`), so a
/// `scalar_ri_offset_encodable` check built on it agrees with the encoder
/// bit-for-bit.
pub fn scalar_ri_mem_scale(inst: &MachInst) -> Option<i64> {
    use trust_cg_ir::inst::AArch64Opcode as Op;
    let scale = match inst.opcode {
        // Width follows the transfer register (operand 0), identically to the
        // `sf_from_operand` (integer) / `fp_mem_fields_from_preg_class` (FP)
        // derivation in the LdrRI/StrRI encoder arms.
        Op::LdrRI | Op::StrRI => scalar_transfer_scale(inst)?,
        // Narrow forms: the access width is fixed by the opcode, never the
        // (always 32-bit) transfer class.
        Op::LdrbRI | Op::LdrsbRI | Op::StrbRI => 1,
        Op::LdrhRI | Op::LdrshRI | Op::StrhRI => 2,
        // Typed STR aliases with a hardwired width.
        Op::STRWui | Op::STRSui => 4,
        Op::STRXui | Op::STRDui => 8,
        _ => return None,
    };
    Some(scale)
}

/// Access size in bytes implied by the transfer register at operand 0 for an
/// `LdrRI`/`StrRI`. Mirrors `sf_from_operand` (Gpr32→4, Gpr64/XZR/SP→8, WZR→4)
/// and `fp_mem_fields_from_preg_class` (Fpr128→16, Fpr64→8, Fpr32→4, Fpr16→2).
fn scalar_transfer_scale(inst: &MachInst) -> Option<i64> {
    match inst.operands.first() {
        Some(MachOperand::PReg(p)) => match preg_class(*p) {
            RegClass::Gpr64 => Some(8),
            RegClass::Gpr32 => Some(4),
            RegClass::Fpr128 => Some(16),
            RegClass::Fpr64 => Some(8),
            RegClass::Fpr32 => Some(4),
            RegClass::Fpr16 => Some(2),
            _ => None,
        },
        Some(MachOperand::Special(s)) => match s {
            SpecialReg::SP | SpecialReg::XZR => Some(8),
            SpecialReg::WZR => Some(4),
        },
        _ => None,
    }
}

fn scalar_writeback_transfer_hw(inst: &MachInst, idx: usize) -> Result<u32, EncodeError> {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) if preg_class(*p) == RegClass::Gpr64 && *p != SP => {
            Ok(p.hw_enc() as u32)
        }
        Some(MachOperand::Special(SpecialReg::XZR)) => Ok(31),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("expected 64-bit GPR or XZR transfer register, got {other:?}"),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: idx,
            expected: idx + 1,
        }),
    }
}

fn scalar_writeback_base_hw(inst: &MachInst, idx: usize) -> Result<u32, EncodeError> {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) if preg_class(*p) == RegClass::Gpr64 && *p != XZR => {
            Ok(p.hw_enc() as u32)
        }
        Some(MachOperand::Special(SpecialReg::SP)) => Ok(31),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("expected 64-bit GPR or SP writeback base, got {other:?}"),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: idx,
            expected: idx + 1,
        }),
    }
}

fn encode_scalar_writeback(
    inst: &MachInst,
    pre_index: bool,
    op: encoding_mem::LoadStoreOp,
) -> Result<u32, EncodeError> {
    let rt = scalar_writeback_transfer_hw(inst, 0)?;
    let rn = scalar_writeback_base_hw(inst, 1)?;
    if rn != 31 && rt == rn {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 1,
            desc: "writeback base overlaps transfer register".to_string(),
        });
    }
    let imm9 = imm_operand(inst, 2)?;
    let imm9 = i16::try_from(imm9).map_err(|_| EncodeError::InvalidOperand {
        opcode: inst.opcode,
        index: 2,
        desc: format!("writeback offset {imm9} is outside i16 range"),
    })?;

    if pre_index {
        Ok(encoding_mem::encode_ldr_str_pre_index(
            encoding_mem::LoadStoreSize::Double,
            false,
            op,
            imm9,
            rn as u8,
            rt as u8,
        )?)
    } else {
        Ok(encoding_mem::encode_ldr_str_post_index(
            encoding_mem::LoadStoreSize::Double,
            false,
            op,
            imm9,
            rn as u8,
            rt as u8,
        )?)
    }
}

/// Determine sf (size flag): 1 for 64-bit GPR, 0 for 32-bit.
/// Uses the register's class to determine size:
///   - Gpr32 (W registers) → sf=0
///   - Gpr64 (X registers) → sf=1
/// FPRs are handled separately. Defaults to 1 (64-bit).
fn sf_from_operand(inst: &MachInst, idx: usize) -> u32 {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) => {
            match preg_class(*p) {
                RegClass::Gpr32 => 0,
                RegClass::Gpr64 => 1,
                // FPRs and system regs: sf not applicable, default to 1
                _ => 1,
            }
        }
        Some(MachOperand::Special(s)) => match s {
            // SP and XZR are 64-bit, WZR is 32-bit
            SpecialReg::SP | SpecialReg::XZR => 1,
            SpecialReg::WZR => 0,
        },
        _ => 1,
    }
}

/// Check if an operand is an FPR (V-register).
fn is_fpr(inst: &MachInst, idx: usize) -> bool {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) => p.is_fpr(),
        _ => false,
    }
}

fn encode_gpr_move_alias(sf: u32, rd: u32, rn: u32) -> u32 {
    encoding::encode_logical_shifted_reg(sf, 0b01, 0, 0, rn, 0, 31, rd)
}

fn pair_operand_class(inst: &MachInst, idx: usize) -> Result<RegClass, EncodeError> {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) => Ok(preg_class(*p)),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("expected pair register, got {:?}", other),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: idx,
            expected: idx + 1,
        }),
    }
}

/// Derive the `(PairSize, v, scale)` for the pre/post-index LDP/STP paths from
/// the register class of the pair operands. The callee-saved frame lowering
/// emits GPR X64 pairs (FP/LR and X19–X28) and FPR D64 pairs (the low 64 bits
/// of V8–V15) through the pre-index (CSA allocation) and post-index (CSA
/// deallocation) forms; both scale by 8. Fails closed on any other class so an
/// FPR pair can never be silently encoded as a GPR pair (or vice versa), which
/// would store/restore the wrong physical registers and clobber a callee-saved
/// value — the exact miscompile this replaces.
fn pair_index_size_v(inst: &MachInst) -> Result<(encoding_mem::PairSize, bool, i64), EncodeError> {
    let class0 = pair_operand_class(inst, 0)?;
    let class1 = pair_operand_class(inst, 1)?;
    match (class0, class1) {
        (RegClass::Gpr64, RegClass::Gpr64) => Ok((encoding_mem::PairSize::X64, false, 8)),
        (RegClass::Fpr64, RegClass::Fpr64) => Ok((encoding_mem::PairSize::D64, true, 8)),
        _ => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 0,
            desc: format!(
                "pre/post-index pair operands must both be Gpr64 or both Fpr64, got {class0:?} and {class1:?}"
            ),
        }),
    }
}

fn pair_encoding_fields(inst: &MachInst) -> Result<(u32, u32, i64), EncodeError> {
    let class0 = pair_operand_class(inst, 0)?;
    let class1 = pair_operand_class(inst, 1)?;
    match (class0, class1) {
        (RegClass::Gpr64, RegClass::Gpr64) => Ok((0b10, 0, 8)),
        (RegClass::Gpr32, RegClass::Gpr32) => Ok((0b00, 0, 4)),
        (RegClass::Fpr128, RegClass::Fpr128) => Ok((0b10, 1, 16)),
        (RegClass::Fpr64, RegClass::Fpr64) => Ok((0b01, 1, 8)),
        (RegClass::Fpr32, RegClass::Fpr32) => Ok((0b00, 1, 4)),
        _ => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 0,
            desc: format!(
                "pair operands must have matching pair-encodable classes, got {class0:?} and {class1:?}"
            ),
        }),
    }
}

fn scaled_pair_imm7(inst: &MachInst, offset: i64, scale: i64) -> Result<u32, EncodeError> {
    if offset % scale != 0 {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 3,
            desc: format!("pair offset {offset} is not aligned to element scale {scale}"),
        });
    }
    // The STP/LDP `imm7` field is a SIGNED 7-bit value (scaled range -64..=63).
    // Range-check the i64 quotient BEFORE any narrowing cast — a `& 0x7F` mask
    // would silently truncate an out-of-range scaled offset into a *different*
    // (wrong) stack offset, producing a silent callee-save/frame miscompile.
    // Mirrors `encoding_mem::check_imm7` (the pre/post-index path's guard).
    let scaled = offset / scale;
    if !(-64..=63).contains(&scaled) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 3,
            desc: format!(
                "pair offset {offset} scaled by {scale} = {scaled} is out of signed 7-bit range [-64, 63]"
            ),
        });
    }
    Ok((scaled as i32 as u32) & 0x7F)
}

/// FAIL-CLOSED scaled `imm7` for the pre/post-index STP/LDP forms.
///
/// The pre/post-index pair encoders (`encode_ldp_stp_pre_index` /
/// `encode_ldp_stp_post_index`) take an `i8` and then range-check it against the
/// signed 7-bit field via `check_imm7`. The danger is the *narrowing* step:
/// computing `(offset / scale) as i8` BEFORE the range check truncates a large
/// quotient into a different (in-range) `i8`, which then passes `check_imm7` and
/// silently miscompiles the offset. For example `offset = 1536, scale = 8` gives
/// quotient `192`, and `192 as i8 == -64`, which `check_imm7` happily accepts —
/// encoding the WRONG stack offset. We therefore range-check the i64 quotient
/// (and alignment) up front and only then narrow to `i8`. Mirrors
/// [`scaled_pair_imm7`] (the signed-offset pair path's guard).
fn scaled_pair_imm7_i8(inst: &MachInst, offset: i64, scale: i64) -> Result<i8, EncodeError> {
    if offset % scale != 0 {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 3,
            desc: format!("pair offset {offset} is not aligned to element scale {scale}"),
        });
    }
    let scaled = offset / scale;
    if !(-64..=63).contains(&scaled) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 3,
            desc: format!(
                "pair offset {offset} scaled by {scale} = {scaled} is out of signed 7-bit range [-64, 63]"
            ),
        });
    }
    Ok(scaled as i8)
}

/// FAIL-CLOSED extraction of an ADR/ADRP `imm21` operand.
///
/// `encoding_mem::{encode_adr, encode_adrp}` range-check the signed 21-bit
/// field via `check_imm21`, but they take an `i32`. Casting the i64 operand
/// `imm_val(..) as i32` BEFORE that check truncates a value outside the i32
/// range into a different (possibly in-range) i32 that `check_imm21` would then
/// accept — silently encoding the wrong PC-relative offset. Range-check the i64
/// against the signed 21-bit window up front (which is strictly inside i32, so
/// the subsequent narrowing is lossless) and only then narrow.
fn adr_imm21(inst: &MachInst, idx: usize) -> Result<i32, EncodeError> {
    let imm = imm_val(inst, idx);
    if !(-1_048_576..=1_048_575).contains(&imm) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!(
                "ADR/ADRP immediate {imm} out of signed 21-bit range [-1048576, 1048575]"
            ),
        });
    }
    Ok(imm as i32)
}

/// FAIL-CLOSED extraction of a 6-bit bitfield index (`immr` / `imms`) for the
/// BFM / SBFM / UBFM family.
///
/// The bitfield encodings carry `immr`,`imms` as raw 6-bit fields in [0,63] for
/// the 64-bit (sf=1) form, and in [0,31] for the 32-bit (sf=0) form (where N=0
/// and the element is a 32-bit register). The previous `imm_val(..) as u32 &
/// 0x3F` silently wrapped an out-of-range index mod 64 (e.g. bit 64 -> bit 0),
/// selecting a *different* bitfield = a miscompile. Range-check the full i64
/// value (reject negative or above the sf-dependent max) BEFORE narrowing.
fn bitfield6_operand(inst: &MachInst, idx: usize, sf: u32) -> Result<u32, EncodeError> {
    let imm = imm_val(inst, idx);
    let max: i64 = if sf == 1 { 63 } else { 31 };
    if !(0..=max).contains(&imm) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!(
                "bitfield index {imm} out of range [0, {max}] for {}-bit form",
                if sf == 1 { 64 } else { 32 }
            ),
        });
    }
    Ok(imm as u32)
}

/// FAIL-CLOSED extraction of an unsigned 16-bit move-wide immediate (`imm16`).
///
/// The field is a 16-bit value [0,65535] (zero-extended for MOVZ/MOVK, bitwise
/// inverted by the CPU for MOVN). The previous `imm_val(..) as u32 & 0xFFFF`
/// silently truncated a wide constant leaked here to a *different* 16-bit field.
/// Reject the full i64 value outside [0,0xFFFF] before narrowing, mirroring the
/// move-wide `MovImmTooWide` guard.
fn imm16_operand(inst: &MachInst, idx: usize) -> Result<u32, EncodeError> {
    let imm = imm_operand(inst, idx)?;
    if !(0..=0xFFFF).contains(&imm) {
        return Err(EncodeError::MovImmTooWide {
            opcode: inst.opcode,
            imm: imm as u64,
        });
    }
    Ok(imm as u32)
}

/// FAIL-CLOSED extraction of a move-wide `hw` shift field (MOVZ/MOVN/MOVK).
///
/// `hw = shift / 16`; `shift` must be a non-negative multiple of 16. The
/// architectural range is hw 0..=3 for X registers and 0..=1 for W registers.
/// The previous `(imm_val(..) / 16) & 0b11` silently wrapped an oversized,
/// negative, or non-16-multiple shift to a wrong hw field.
fn move_wide_hw(inst: &MachInst, idx: usize) -> Result<u32, EncodeError> {
    let raw = imm_operand(inst, idx)?;
    if raw < 0 || raw % 16 != 0 {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("move-wide shift {raw} must be a non-negative multiple of 16"),
        });
    }
    let hw = (raw as u64) / 16;
    let max_hw = if sf_from_operand(inst, 0) == 0 { 1 } else { 3 };
    if hw > max_hw {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!(
                "move-wide shift {raw} out of range for {}-bit form \
                 (shift/16 = {hw} must be 0..={max_hw})",
                if max_hw == 1 { 32 } else { 64 }
            ),
        });
    }
    Ok(hw as u32)
}

/// FAIL-CLOSED extraction of the TBZ/TBNZ test-bit index (the `b5||b40` 6-bit
/// field).
///
/// The test-bit index is in [0,63] for a 64-bit (sf=1) register and [0,31] for
/// a 32-bit (sf=0) register (where the high bit `b5` must be 0). The previous
/// raw `>> 5` / `& 0x1F` split silently wrapped bit 64 -> bit 0. Range-check the
/// full i64 value (reject negative or above the sf-dependent max) BEFORE the
/// bit split.
fn tbz_bit_position(inst: &MachInst, idx: usize, sf: u32) -> Result<u32, EncodeError> {
    let bit = imm_val(inst, idx);
    let max: i64 = if sf == 1 { 63 } else { 31 };
    if !(0..=max).contains(&bit) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!(
                "TBZ/TBNZ bit position {bit} out of range [0, {max}] for {}-bit register",
                if sf == 1 { 64 } else { 32 }
            ),
        });
    }
    Ok(bit as u32)
}

/// FAIL-CLOSED extraction of a signed PC-relative branch offset field.
///
/// The conditional/compare/test-bit/unconditional branch encodings carry the
/// PC-relative offset as a fixed-width *signed word* offset (`bits` wide). These
/// are normally rewritten by the relocation / branch-fixup layer, but as a
/// fixed-width field a statically-supplied out-of-range offset would silently
/// wrap under `& mask` to a *different* (wrong) target. Range-check the full i64
/// word offset against the signed `bits`-wide window BEFORE the mask:
///   imm19  -> [-262144, 262143]
///   imm26  -> [-33554432, 33554431]
///   imm14  -> [-8192, 8191]
fn branch_offset_signed(inst: &MachInst, idx: usize, bits: u32) -> Result<u32, EncodeError> {
    // Reject a non-immediate (e.g. an unresolved Block/Symbol target that
    // escaped the fixup layer) rather than silently treating it as offset 0.
    let off = imm_operand(inst, idx)?;
    let min: i64 = -(1i64 << (bits - 1));
    let max: i64 = (1i64 << (bits - 1)) - 1;
    if !(min..=max).contains(&off) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("branch offset {off} out of signed {bits}-bit range [{min}, {max}]"),
        });
    }
    Ok(off as u32 & ((1u32 << bits) - 1))
}

/// FAIL-CLOSED extraction of a GOT/TLV unsigned scaled `imm12` (offset / 8).
///
/// The page-offset GOT/TLV loads carry a byte offset that must be 8-byte aligned
/// and whose scaled value `offset / 8` must fit the unsigned 12-bit field
/// [0,4095]. The previous `(offset / 8) as u32 & 0xFFF` performed no range or
/// alignment check, silently masking an out-of-range or misaligned offset. This
/// field is relocation-adjacent, but as a fixed-width field reject misaligned /
/// out-of-[0,4095] offsets BEFORE the divide and mask (cf.
/// `encode_load_store_auto`).
fn got_tlv_scaled_imm12(inst: &MachInst, offset: i64) -> Result<u32, EncodeError> {
    if offset % 8 != 0 {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 2,
            desc: format!("GOT/TLV offset {offset} is not 8-byte aligned"),
        });
    }
    let scaled = offset / 8;
    if !(0..=0xFFF).contains(&scaled) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: 2,
            desc: format!(
                "GOT/TLV offset {offset} scaled by 8 = {scaled} out of unsigned 12-bit range [0, 4095]"
            ),
        });
    }
    Ok(scaled as u32 & 0xFFF)
}

/// FAIL-CLOSED extraction of the raw `N`/`immr`/`imms` triple for the
/// pre-decomposed (5-operand) logical-immediate fallback.
///
/// When the caller supplies an already-decomposed `(N, immr, imms)`, `N` must be
/// in {0,1} and `immr`,`imms` in [0,63]. The 3-operand form validates
/// encodability via `encode_logical_imm_fields`, but this raw fallback masked
/// `N` with `& 1` and `immr`/`imms` with `& 0x3F` with no range check. Reject
/// `N>1`, `immr>63`, `imms>63` (and negatives) before masking.
fn logical_imm_raw_field(
    inst: &MachInst,
    idx: usize,
    max: i64,
    name: &str,
) -> Result<u32, EncodeError> {
    let v = imm_operand(inst, idx)?;
    if !(0..=max).contains(&v) {
        return Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: idx,
            desc: format!("logical-immediate {name} {v} out of range [0, {max}]"),
        });
    }
    Ok(v as u32)
}

// ---------------------------------------------------------------------------
// Unified encoder
// ---------------------------------------------------------------------------

/// Encode a single `MachInst` into a 32-bit AArch64 instruction word.
///
/// This is the single dispatch point for all AArch64 opcodes. The instruction
/// must be post-regalloc (all operands are `PReg`, `Special`, `Imm`, etc.).
///
/// Pseudo-instructions (`Phi`, `StackAlloc`, `Nop`) emit NOP as a safe
/// fallback — the caller should skip pseudos before reaching this function.
pub fn encode_instruction(inst: &MachInst) -> Result<u32, EncodeError> {
    match inst.opcode {
        // =================================================================
        // Arithmetic (data-processing)
        // =================================================================

        // ADD Rd, Rn, Rm (shifted register)
        AArch64Opcode::AddRR => {
            reject_sp_in_shifted_reg(inst)?;
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_add_sub_shifted_reg(
                sf,
                0,
                0,
                0,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // ADD Rd, Rn, #imm12
        AArch64Opcode::AddRI => {
            let sf = sf_from_operand(inst, 0);
            let imm = imm12_operand(inst, 2)?;
            Ok(encoding::encode_add_sub_imm(
                sf,
                0,
                0,
                0,
                imm,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // ADD Rd, Rn, #imm12, LSL #12
        AArch64Opcode::AddRIShift12 => {
            let sf = sf_from_operand(inst, 0);
            let imm = imm12_operand(inst, 2)?;
            Ok(encoding::encode_add_sub_imm(
                sf,
                0,
                0,
                1,
                imm,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // SUB Rd, Rn, Rm (shifted register)
        AArch64Opcode::SubRR => {
            reject_sp_in_shifted_reg(inst)?;
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_add_sub_shifted_reg(
                sf,
                1,
                0,
                0,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // SUB Rd, Rn, #imm12
        AArch64Opcode::SubRI => {
            let sf = sf_from_operand(inst, 0);
            let imm = imm12_operand(inst, 2)?;
            Ok(encoding::encode_add_sub_imm(
                sf,
                1,
                0,
                0,
                imm,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // MUL Rd, Rn, Rm — encoded as MADD Rd, Rn, Rm, XZR
        // ARM ARM: Data-processing (3 source)
        // 31 30:29 28:24 23:21 20:16 15 14:10 9:5 4:0
        // sf 00    11011 000   Rm    0  Ra     Rn  Rd
        // MADD with Ra=XZR(31) = MUL
        AArch64Opcode::MulRR => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let ra = 31u32; // XZR — MADD Rd, Rn, Rm, XZR = MUL
            Ok((((sf << 31)
                | (0b11011 << 24))
                | (rm << 16)) // o0 = 0 for MADD
                | (ra << 10)
                | (rn << 5)
                | rd)
        }

        // MSUB Rd, Rn, Rm, Ra — multiply-subtract: Rd = Ra - Rn * Rm
        // ARM ARM: Data-processing (3 source), o0=1
        // 31 30:29 28:24 23:21 20:16 15 14:10 9:5 4:0
        // sf 00    11011 000   Rm    1  Ra     Rn  Rd
        // When Ra=XZR (31), this is MNEG Rd, Rn, Rm.
        // Operands: [Rd, Rn, Rm, Ra] — 4 operands. If only 3, Ra defaults to XZR (MNEG).
        AArch64Opcode::Msub => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let ra = if inst.operands.len() > 3 {
                preg_hw(inst, 3)?
            } else {
                31
            };
            Ok(((sf << 31)
                | (0b11011 << 24))
                | (rm << 16)
                | (1 << 15) // o0 = 1 for MSUB
                | (ra << 10)
                | (rn << 5)
                | rd)
        }

        // SMULL Xd, Wn, Wm — signed multiply long (alias for SMADDL Xd, Wn, Wm, XZR)
        // ARM ARM: Data-processing (3 source)
        // 31 30:29 28:24 23:21 20:16 15 14:10 9:5 4:0
        //  1  00    11011 001   Rm    0  Ra     Rn  Rd
        // sf=1 (always 64-bit result), U=0 (signed), o0=0 (add), Ra=XZR(31)
        AArch64Opcode::Smull => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let ra = 31u32; // XZR for SMULL alias
            Ok(((1u32 << 31)
                | (0b11011 << 24)
                | (0b001 << 21) // op54=00, op31=1 (long multiply)
                | (rm << 16)) // o0 = 0 (SMADDL)
                | (ra << 10)
                | (rn << 5)
                | rd)
        }

        // UMULL Xd, Wn, Wm — unsigned multiply long (alias for UMADDL Xd, Wn, Wm, XZR)
        // ARM ARM: Data-processing (3 source)
        // 31 30:29 28:24 23:21 20:16 15 14:10 9:5 4:0
        //  1  00    11011 101   Rm    0  Ra     Rn  Rd
        // sf=1 (always 64-bit result), U=1 (unsigned), o0=0 (add), Ra=XZR(31)
        AArch64Opcode::Umull => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let ra = 31u32; // XZR for UMULL alias
            Ok(((1u32 << 31)
                | (0b11011 << 24)
                | (0b101 << 21) // op54=00, op31=1, U=1 (unsigned long multiply)
                | (rm << 16)) // o0 = 0 (UMADDL)
                | (ra << 10)
                | (rn << 5)
                | rd)
        }

        // SDIV Rd, Rn, Rm — Data-processing (2 source)
        // 31 30 28:21      20:16 15:10  9:5  4:0
        // sf  0 0011010110  Rm   000011  Rn   Rd
        AArch64Opcode::SDiv => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((sf << 31)
                | (0b0_0011010110u32 << 21)
                | (rm << 16)
                | (0b000011 << 10)
                | (rn << 5)
                | rd)
        }

        // UDIV Rd, Rn, Rm
        // Same as SDIV but opcode field = 000010
        AArch64Opcode::UDiv => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((sf << 31)
                | (0b0_0011010110u32 << 21)
                | (rm << 16)
                | (0b000010 << 10)
                | (rn << 5)
                | rd)
        }

        // NEG Rd, Rm — alias for SUB Rd, XZR, Rm
        AArch64Opcode::Neg => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rm = preg_hw(inst, 1)?;
            Ok(encoding::encode_add_sub_shifted_reg(
                sf, 1, 0, 0, rm, 0, 31, rd,
            ))
        }

        // =================================================================
        // Logical (shifted register)
        // =================================================================
        AArch64Opcode::AndRR => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_logical_shifted_reg(
                sf,
                0b00,
                0,
                0,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        AArch64Opcode::OrrRR => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_logical_shifted_reg(
                sf,
                0b01,
                0,
                0,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        AArch64Opcode::EorRR => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_logical_shifted_reg(
                sf,
                0b10,
                0,
                0,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // EOR Rd, Rn, Rm, ROR #amount — exclusive-OR with a ROR-shifted second
        // source. Logical (shifted register): opc=EOR=0b10, shift=ROR=0b11, N=0,
        // imm6 = ROR amount. Byte-verified against clang-assembled
        // `eor w4,w4,w20,ror #25` = 0x4AD46484 / `eor x0,x1,x2,ror #40` =
        // 0xCAC2A020 (W+X, several amounts). Operands:
        // [Rd, Rn (un-shifted), Rm (rotated source), Imm(amount)].
        AArch64Opcode::EorRRShift => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let raw_amount = imm_operand(inst, 3)?;
            let regsize = if sf == 1 { 64i64 } else { 32i64 };
            // ROR amount must be a real in-register rotate. 0 would be a plain
            // EOR (never fused to this form) and >= width is unencodable in the
            // 6-bit imm6 for W. Fail-closed on anything outside [1, width).
            if raw_amount < 1 || raw_amount >= regsize {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 3,
                    desc: format!("EOR ROR amount {raw_amount} out of range [1, {regsize})"),
                });
            }
            Ok(encoding::encode_logical_shifted_reg(
                sf,
                0b10,              // opc = EOR
                0b11,              // shift = ROR
                0,                 // N = 0
                rm,                // Rm — the rotated source
                raw_amount as u32, // imm6 = ROR amount
                rn,                // Rn — the un-shifted operand
                rd,
            ))
        }

        // EOR Rd, Rn, Rm, LSL|LSR #k — exclusive-or with a shifted second source.
        // Logical (shifted register): sf | opc=0b10 (EOR) | 01010 | shift | N=0 |
        // Rm | imm6 | Rn | Rd, with shift = 0b00 (LSL) or 0b01 (LSR). Same
        // encoder helper and operand schema as the ROR form above; only the
        // 2-bit `shift` field differs, which is exactly what the reconstruction
        // obligation refutes if it is wrong.
        // Operands: [Rd, Rn (un-shifted), Rm (shifted source), Imm(k)].
        AArch64Opcode::EorRRLsl | AArch64Opcode::EorRRLsr => {
            reject_sp_in_shifted_reg(inst)?;
            let is_lsl = inst.opcode == AArch64Opcode::EorRRLsl;
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let k = imm_operand(inst, 3)?;
            let regsize = if sf == 1 { 64i64 } else { 32i64 };
            // A 0 amount would be a plain EOR (never fused to this form) and
            // >= width is unencodable in imm6 for the W form. Fail closed.
            if k < 1 || k >= regsize {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 3,
                    desc: format!(
                        "EOR {} amount {k} out of range [1, {regsize})",
                        if is_lsl { "LSL" } else { "LSR" }
                    ),
                });
            }
            Ok(encoding::encode_logical_shifted_reg(
                sf,
                0b10, // opc = EOR
                if is_lsl { 0b00 } else { 0b01 },
                0,        // N = 0
                rm,       // Rm — the shifted source
                k as u32, // imm6 = shift amount
                rn,       // Rn — the un-shifted operand
                rd,
            ))
        }

        // ADD Rd, Rn, Rm, LSL #k — add with an LSL-shifted second source.
        // Add/subtract (shifted register): op=0 (ADD), S=0, shift=LSL=0b00,
        // imm6 = shift amount k. Byte-verified against clang-assembled
        // `add x0,x1,x2,lsl #1` = 0x8B020420 / `add w0,w1,w2,lsl #3` =
        // 0x0B020C20 (W+X, several amounts). Operands:
        // [Rd, Rn (un-shifted base), Rm (shifted source), Imm(k)].
        AArch64Opcode::AddRRShift => {
            reject_sp_in_shifted_reg(inst)?;
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let k = imm_operand(inst, 3)?;
            let regsize = if sf == 1 { 64i64 } else { 32i64 };
            // k must be a real in-register shift. 0 would be a plain ADD (never
            // fused to this form); for sf=0 (W) imm6 bit 5 must be 0, so k in
            // 32..=63 is UNDEFINED — fail-closed on anything outside [1, width).
            if k < 1 || k >= regsize {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 3,
                    desc: format!("ADD LSL amount {k} out of range [1, {regsize})"),
                });
            }
            Ok(encoding::encode_add_sub_shifted_reg(
                sf, 0,        // op = 0 (ADD)
                0,        // S = 0
                0b00,     // shift = LSL
                rm,       // Rm — the shifted source
                k as u32, // imm6 = shift amount
                rn,       // Rn — the un-shifted base
                rd,
            ))
        }

        // SUB Rd, Rn, Rm, LSL #k — subtract an LSL-shifted second source.
        // Add/subtract (shifted register): op=1 (SUB), S=0, shift=LSL=0b00,
        // imm6 = shift amount k. Byte-verified against clang-assembled
        // `sub x0,x1,x2,lsl #1` = 0xCB020420 (W+X, several amounts). NON-
        // COMMUTATIVE: the shift binds to the subtrahend (Rm) only. Operands:
        // [Rd, Rn (minuend), Rm (shifted subtrahend), Imm(k)].
        AArch64Opcode::SubRRShift => {
            reject_sp_in_shifted_reg(inst)?;
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let k = imm_operand(inst, 3)?;
            let regsize = if sf == 1 { 64i64 } else { 32i64 };
            if k < 1 || k >= regsize {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 3,
                    desc: format!("SUB LSL amount {k} out of range [1, {regsize})"),
                });
            }
            Ok(encoding::encode_add_sub_shifted_reg(
                sf, 1,        // op = 1 (SUB)
                0,        // S = 0
                0b00,     // shift = LSL
                rm,       // Rm — the shifted subtrahend
                k as u32, // imm6 = shift amount
                rn,       // Rn — the un-shifted minuend
                rd,
            ))
        }

        // ADD Rd, Rn, Rm, LSR #k — add with an LSR-shifted second source.
        // Add/subtract (shifted register): op=0 (ADD), S=0, shift=LSR=0b01,
        // imm6 = shift amount k. Byte-verified against clang-assembled
        // `add x0,x1,x2,lsr #1` = 0x8B420420 / `add w0,w1,w2,lsr #3` =
        // 0x0B420C20 (W+X, several amounts). Operands:
        // [Rd, Rn (un-shifted base), Rm (shifted source), Imm(k)].
        AArch64Opcode::AddRRShiftLsr => {
            reject_sp_in_shifted_reg(inst)?;
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let k = imm_operand(inst, 3)?;
            let regsize = if sf == 1 { 64i64 } else { 32i64 };
            // k must be a real in-register shift. 0 would be a plain ADD (never
            // fused to this form); for sf=0 (W) imm6 bit 5 must be 0, so k in
            // 32..=63 is UNDEFINED — fail-closed on anything outside [1, width).
            if k < 1 || k >= regsize {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 3,
                    desc: format!("ADD LSR amount {k} out of range [1, {regsize})"),
                });
            }
            Ok(encoding::encode_add_sub_shifted_reg(
                sf, 0,        // op = 0 (ADD)
                0,        // S = 0
                0b01,     // shift = LSR
                rm,       // Rm — the shifted source
                k as u32, // imm6 = shift amount
                rn,       // Rn — the un-shifted base
                rd,
            ))
        }

        // ORN Rd, Rn, Rm — bitwise OR-NOT (MVN when Rn=XZR)
        // Logical shifted register with opc=01, N=1, shift=0
        AArch64Opcode::OrnRR => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_logical_shifted_reg(
                sf,
                0b01,
                0,
                1,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // =================================================================
        // Shifts — Data-processing (2 source)
        // Variable shifts: LSL/LSR/ASR Rd, Rn, Rm
        // sf 0 0011010110 Rm opcode2 Rn Rd
        // opcode2: LSLV=001000, LSRV=001001, ASRV=001010
        // =================================================================
        AArch64Opcode::LslRR => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((sf << 31)
                | (0b0_0011010110u32 << 21)
                | (rm << 16)
                | (0b001000 << 10) // LSLV
                | (rn << 5)
                | rd)
        }

        AArch64Opcode::LsrRR => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((sf << 31)
                | (0b0_0011010110u32 << 21)
                | (rm << 16)
                | (0b001001 << 10) // LSRV
                | (rn << 5)
                | rd)
        }

        AArch64Opcode::AsrRR => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((sf << 31)
                | (0b0_0011010110u32 << 21)
                | (rm << 16)
                | (0b001010 << 10) // ASRV
                | (rn << 5)
                | rd)
        }

        // Immediate shifts — encoded via UBFM/SBFM
        // LSL Rd, Rn, #shift  = UBFM Rd, Rn, #(-shift MOD regsize), #(regsize-1-shift)
        // LSR Rd, Rn, #shift  = UBFM Rd, Rn, #shift, #(regsize-1)
        // ASR Rd, Rn, #shift  = SBFM Rd, Rn, #shift, #(regsize-1)
        // A zero shift is a register move; use the MOV alias instead of a
        // bitfield/extract instruction on the hot path.
        // Bitfield format:
        // sf opc(2) 100110 N immr(6) imms(6) Rn Rd
        // UBFM: opc=10, SBFM: opc=00
        AArch64Opcode::LslRI => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let raw_shift = imm_val(inst, 2);
            let regsize = if sf == 1 { 64u32 } else { 32u32 };
            // Shift must be in [0, regsize). Negative or oversized shifts
            // previously caused a debug `attempt to subtract with overflow`
            // in `imms = regsize - 1 - shift` (#447).
            if raw_shift < 0 || (raw_shift as u64) >= regsize as u64 {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 2,
                    desc: format!("shift {} out of range [0, {})", raw_shift, regsize),
                });
            }
            if raw_shift == 0 {
                return Ok(encode_gpr_move_alias(sf, rd, rn));
            }
            let shift = raw_shift as u32;
            let n = sf; // N = sf for bitfield
            let immr = regsize.wrapping_sub(shift) & (regsize - 1);
            let imms = regsize - 1 - shift;
            // UBFM: sf opc=10 100110 N immr imms Rn Rd
            Ok((sf << 31)
                | (0b10 << 29)
                | (0b100110 << 23)
                | (n << 22)
                | (immr << 16)
                | (imms << 10)
                | (rn << 5)
                | rd)
        }

        AArch64Opcode::LsrRI => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let raw_shift = imm_val(inst, 2);
            let regsize = if sf == 1 { 64u32 } else { 32u32 };
            if raw_shift < 0 || (raw_shift as u64) >= regsize as u64 {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 2,
                    desc: format!("shift {} out of range [0, {})", raw_shift, regsize),
                });
            }
            if raw_shift == 0 {
                return Ok(encode_gpr_move_alias(sf, rd, rn));
            }
            let shift = raw_shift as u32;
            let n = sf;
            let immr = shift;
            let imms = regsize - 1;
            // UBFM
            Ok((sf << 31)
                | (0b10 << 29)
                | (0b100110 << 23)
                | (n << 22)
                | (immr << 16)
                | (imms << 10)
                | (rn << 5)
                | rd)
        }

        AArch64Opcode::AsrRI => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let raw_shift = imm_val(inst, 2);
            let regsize = if sf == 1 { 64u32 } else { 32u32 };
            if raw_shift < 0 || (raw_shift as u64) >= regsize as u64 {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 2,
                    desc: format!("shift {} out of range [0, {})", raw_shift, regsize),
                });
            }
            if raw_shift == 0 {
                return Ok(encode_gpr_move_alias(sf, rd, rn));
            }
            let shift = raw_shift as u32;
            let n = sf;
            let immr = shift;
            let imms = regsize - 1;
            // SBFM: opc=00
            Ok((sf << 31)
                | (0b100110 << 23)
                | (n << 22)
                | (immr << 16)
                | (imms << 10)
                | (rn << 5)
                | rd)
        }

        // ROR Rd, Rn, #shift — alias for EXTR Rd, Rn, Rn, #shift.
        AArch64Opcode::RorRI => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let raw_shift = imm_operand(inst, 2)?;
            let regsize = if sf == 1 { 64u32 } else { 32u32 };
            if raw_shift < 0 || (raw_shift as u64) >= regsize as u64 {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 2,
                    desc: format!("rotate shift {} out of range [0, {})", raw_shift, regsize),
                });
            }
            if raw_shift == 0 {
                return Ok(encode_gpr_move_alias(sf, rd, rn));
            }
            let shift = raw_shift as u32;
            Ok(encoding::encode_extract(sf, sf, rn, shift, rn, rd))
        }

        // RBIT Rd, Rn — reverse bits in a 32-bit or 64-bit GPR.
        AArch64Opcode::Rbit => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_bit_reverse(
                sf,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // =================================================================
        // Compare
        // =================================================================

        // CMP Rn, Rm = SUBS XZR, Rn, Rm
        AArch64Opcode::CmpRR => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_add_sub_shifted_reg(
                sf,
                1,
                1,
                0,
                preg_hw(inst, 1)?,
                0,
                preg_hw(inst, 0)?,
                31,
            ))
        }

        // CMP Rn, #imm = SUBS XZR, Rn, #imm
        AArch64Opcode::CmpRI => {
            let sf = sf_from_operand(inst, 0);
            let imm = imm12_operand(inst, 1)?;
            Ok(encoding::encode_add_sub_imm(
                sf,
                1,
                1,
                0,
                imm,
                preg_hw(inst, 0)?,
                31,
            ))
        }

        // TST — discard-result ANDS. Two operand shapes, dispatched on operand 1:
        //   TST Rn, #imm = ANDS XZR, Rn, #imm   (logical immediate, opc=11)
        //   TST Rn, Rm   = ANDS XZR, Rn, Rm     (shifted register, opc=11)
        //
        // Both write NZCV and discard the result, so Rd is always XZR (31). Note
        // this is NOT `encode_logical_immediate`: that helper takes Rd at operand
        // 0 and Rn at operand 1, whereas TST has no destination operand at all —
        // operand 0 IS Rn.
        AArch64Opcode::Tst => {
            if inst.operands.len() != 2 {
                return if inst.operands.len() < 2 {
                    Err(EncodeError::MissingOperand {
                        opcode: inst.opcode,
                        index: inst.operands.len(),
                        expected: 2,
                    })
                } else {
                    Err(EncodeError::InvalidOperand {
                        opcode: inst.opcode,
                        index: 2,
                        desc: format!(
                            "TST accepts exactly two operands, got {}",
                            inst.operands.len()
                        ),
                    })
                };
            }
            let rn_width = tst_gpr_width(inst, 0)?;
            let sf = u32::from(rn_width == 64);
            match inst.operands.get(1) {
                Some(MachOperand::Imm(_)) => {
                    let register_width = if sf == 1 { 64 } else { 32 };
                    let raw = imm_operand(inst, 1)?;
                    // Fails closed on masks with no logical-immediate encoding
                    // (notably 0 and all-ones), so an unencodable mask is an error
                    // rather than a silently different instruction.
                    let (n, immr, imms) =
                        encode_logical_imm_fields(raw, register_width, inst.opcode, 1)?;
                    Ok((sf << 31)
                        | (0b11 << 29)
                        | (0b100100 << 23)
                        | (n << 22)
                        | (immr << 16)
                        | (imms << 10)
                        | (preg_hw(inst, 0)? << 5)
                        | 31)
                }
                _ => {
                    let rm_width = tst_gpr_width(inst, 1)?;
                    if rm_width != rn_width {
                        return Err(EncodeError::InvalidOperand {
                            opcode: inst.opcode,
                            index: 1,
                            desc: format!(
                                "TST register widths must match, got {rn_width}-bit Rn and {rm_width}-bit Rm"
                            ),
                        });
                    }
                    Ok(encoding::encode_logical_shifted_reg(
                        sf,
                        0b11,
                        0,
                        0,
                        preg_hw(inst, 1)?,
                        0,
                        preg_hw(inst, 0)?,
                        31,
                    ))
                }
            }
        }

        // =================================================================
        // Move
        // =================================================================

        // MOV Rd, Rm
        // When the source is SP (Special::SP), we must use ADD Rd, SP, #0
        // because register 31 in logical instructions (ORR) is XZR, not SP.
        // In ADD/SUB (immediate) context, register 31 is SP.
        // For all other registers, use ORR Rd, XZR, Rm.
        AArch64Opcode::MovR => {
            require_gpr_move_operands(inst, 2)?;
            let sf = sf_from_operand(inst, 0);
            let is_sp_source = matches!(
                inst.operands.get(1),
                Some(MachOperand::Special(SpecialReg::SP))
            );
            if is_sp_source {
                // ADD Rd, SP, #0
                Ok(encoding::encode_add_sub_imm(
                    sf,
                    0,
                    0,
                    0,
                    0,
                    31,
                    preg_hw(inst, 0)?,
                ))
            } else {
                // ORR Rd, XZR, Rm
                Ok(encoding::encode_logical_shifted_reg(
                    sf,
                    0b01,
                    0,
                    0,
                    preg_hw(inst, 1)?,
                    0,
                    31,
                    preg_hw(inst, 0)?,
                ))
            }
        }

        // CSET Xd/Wd, cond — encoded as CSINC Xd, XZR, XZR, invert(cond)
        // ARM ARM C6.2.70: sf | 0 | 0 | 11010100 | Rm(=XZR) | inv_cond | 0 | 1 | Rn(=XZR) | Rd
        // Operands: [PReg(Rd), Imm(cond_encoding)]
        AArch64Opcode::CSet => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let cond = imm_val(inst, 1) as u32 & 0xF;
            // Invert condition code: flip bit 0 (ARM ARM C6.2.70)
            let inv_cond = cond ^ 1;
            let rn = 31u32; // XZR/WZR
            let rm = 31u32; // XZR/WZR
            Ok((sf << 31)
                | (0b11010100 << 21)
                | (rm << 16)
                | (inv_cond << 12)
                | (0b01 << 10)     // op2 = 01 (CSINC)
                | (rn << 5)
                | rd)
        }

        // MovI Rd, #imm16 — encoded as MOVZ at LSL #0.
        //
        // `MovI` is expected to carry a value that fits in a single MOVZ
        // field (16 bits). Wider constants must be materialized by ISel as
        // a MOVZ+MOVK chain — never as a single MovI with a > 16-bit
        // immediate. If a pass ever produces such a MovI (e.g. a buggy
        // constant folder — see issue #366), silently truncating to the
        // low 16 bits would be a miscompile. Fail loudly instead.
        AArch64Opcode::MovI => {
            require_move_wide_arity(inst, 2, 2)?;
            require_move_wide_destination(inst)?;
            let sf = sf_from_operand(inst, 0);
            let imm16 = imm16_operand(inst, 1)?;
            Ok(encoding::encode_move_wide(
                sf,
                0b10,
                0,
                imm16,
                preg_hw(inst, 0)?,
            ))
        }

        // MOVZ Rd, #imm16{, LSL #0}.
        //
        // The v0.1 publication surface retains only the shift-zero MOVZ form.
        // Constants whose low halfword is
        // zero must therefore use `MOVZ #0; MOVK #hi, LSL #16` rather than a
        // single shifted MOVZ. Accept an explicit third operand only when it is
        // exactly zero, and fail closed on every nonzero shift.
        AArch64Opcode::Movz => {
            require_move_wide_arity(inst, 2, 3)?;
            require_move_wide_destination(inst)?;
            let sf = sf_from_operand(inst, 0);
            let imm16 = imm16_operand(inst, 1)?;
            let hw = if inst.operands.len() > 2 {
                move_wide_hw(inst, 2)?
            } else {
                0
            };
            if hw != 0 {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 2,
                    desc: "nonzero-shift MOVZ is not emittable under the v0.1 shift-zero MOVZ policy; \
                           use MOVZ #0 followed by MOVK at the required halfword"
                        .to_string(),
                });
            }
            Ok(encoding::encode_move_wide(
                sf,
                0b10,
                hw,
                imm16,
                preg_hw(inst, 0)?,
            ))
        }

        // MOVK Rd, #imm16{, LSL #shift}
        //
        // The ISel emits MOVK with an optional third operand: the shift
        // amount (0, 16, 32, or 48). This maps to the hw field in the
        // move-wide encoding (hw = shift / 16).
        //
        // Validate the shift here rather than letting `encode_move_wide`
        // silently mask — an oversized shift leaked by a buggy pass would
        // otherwise miscompile MOVK to an unrelated hw-field (#447).
        AArch64Opcode::Movk => {
            require_move_wide_arity(inst, 2, 3)?;
            require_move_wide_destination(inst)?;
            let sf = sf_from_operand(inst, 0);
            // imm16: reject a wide constant leaked here BEFORE the 16-bit mask —
            // the canonical Movz arm rejects via MovImmTooWide; do the same here
            // so MOVK never silently truncates to a wrong 16-bit field.
            let imm16 = imm16_operand(inst, 1)?;
            // Shift -> hw field: non-negative multiple of 16, hw = shift/16 in
            // 0..=3 (the #447 guard).
            let hw = if inst.operands.len() > 2 {
                move_wide_hw(inst, 2)?
            } else {
                0
            };
            Ok(encoding::encode_move_wide(
                sf,
                0b11,
                hw,
                imm16,
                preg_hw(inst, 0)?,
            ))
        }

        // =================================================================
        // Load/Store
        // =================================================================

        // LDR Rt, [Rn, #offset]
        //
        // Operand layouts after pipeline phases:
        //   Pre-frame-lowering:  [Rt(PReg), Rn(PReg), #offset(Imm)]
        //   Post-frame-lowering: [Rt(PReg), MemOp{base, offset}]
        //
        // The extract_base_offset helper handles both layouts transparently.
        // For non-negative aligned offsets, emits LDR (unsigned offset).
        // For negative/unaligned offsets, emits LDUR (unscaled immediate).
        AArch64Opcode::LdrRI | AArch64Opcode::VolatileLdrRI => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            if is_fpr(inst, 0) {
                let (size, scale, opc) = fp_mem_fields_from_inst(inst, 0, 0b01)?;
                encode_load_store_auto(size, 1, opc, scale, offset, rn, rt)
            } else {
                let sf = sf_from_operand(inst, 0);
                let (size, scale) = if sf == 1 { (0b11, 8i64) } else { (0b10, 4i64) };
                encode_load_store_auto(size, 0, 0b01, scale, offset, rn, rt)
            }
        }

        // STR Rt, [Rn, #offset]
        //
        // Same dual-layout handling as LdrRI (see above).
        // For non-negative aligned offsets, emits STR (unsigned offset).
        // For negative/unaligned offsets, emits STUR (unscaled immediate).
        AArch64Opcode::StrRI | AArch64Opcode::VolatileStrRI => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            if is_fpr(inst, 0) {
                let (size, scale, opc) = fp_mem_fields_from_inst(inst, 0, 0b00)?;
                encode_load_store_auto(size, 1, opc, scale, offset, rn, rt)
            } else {
                let sf = sf_from_operand(inst, 0);
                let (size, scale) = if sf == 1 { (0b11, 8i64) } else { (0b10, 4i64) };
                encode_load_store_auto(size, 0, 0b00, scale, offset, rn, rt)
            }
        }

        // 64-bit scalar writeback forms: [Rt, Rn|SP, imm9].
        AArch64Opcode::LdrPreIndex => {
            encode_scalar_writeback(inst, true, encoding_mem::LoadStoreOp::Load)
        }
        AArch64Opcode::StrPreIndex => {
            encode_scalar_writeback(inst, true, encoding_mem::LoadStoreOp::Store)
        }
        AArch64Opcode::LdrPostIndex => {
            encode_scalar_writeback(inst, false, encoding_mem::LoadStoreOp::Load)
        }
        AArch64Opcode::StrPostIndex => {
            encode_scalar_writeback(inst, false, encoding_mem::LoadStoreOp::Store)
        }

        // LDRB Wt, [Xn, #offset] — load byte, zero-extend to 32-bit
        // size=00, V=0, opc=01. Offset scaled by 1 byte.
        AArch64Opcode::LdrbRI | AArch64Opcode::VolatileLdrbRI => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            encode_load_store_auto(0b00, 0, 0b01, 1, offset, rn, rt)
        }

        // LDRH Wt, [Xn, #offset] — load halfword, zero-extend to 32-bit
        // size=01, V=0, opc=01. Offset scaled by 2 bytes.
        AArch64Opcode::LdrhRI | AArch64Opcode::VolatileLdrhRI => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            encode_load_store_auto(0b01, 0, 0b01, 2, offset, rn, rt)
        }

        // LDRSB Wt/Xt, [Xn, #offset] — load byte, sign-extend. size=00, V=0.
        // The sign-extension WIDTH follows the transfer register class: a Gpr32
        // destination uses opc=11 (LDRSB Wt, sign-extend to 32); a Gpr64
        // destination uses opc=10 (LDRSB Xt, sign-extend to 64). Both read the
        // identical 1 byte (offset scaled by 1). This mirrors the way the
        // full-width LdrRI/StrRI arms derive their size from `sf_from_operand`
        // (the ext-addr narrow-load sext fold is the only producer and emits
        // whichever width the folded Sxtb/Sxth had).
        AArch64Opcode::LdrsbRI => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            let opc = if sf_from_operand(inst, 0) == 1 {
                0b10
            } else {
                0b11
            };
            encode_load_store_auto(0b00, 0, opc, 1, offset, rn, rt)
        }

        // LDRSH Wt/Xt, [Xn, #offset] — load halfword, sign-extend. size=01, V=0.
        // opc follows the transfer class exactly as LDRSB above (Gpr32 -> opc=11
        // sign-extend to 32; Gpr64 -> opc=10 sign-extend to 64). Offset scaled
        // by 2.
        AArch64Opcode::LdrshRI => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            let opc = if sf_from_operand(inst, 0) == 1 {
                0b10
            } else {
                0b11
            };
            encode_load_store_auto(0b01, 0, opc, 2, offset, rn, rt)
        }

        // STRB Wt, [Xn, #offset] — store byte (truncating)
        // size=00, V=0, opc=00. Offset scaled by 1.
        AArch64Opcode::StrbRI | AArch64Opcode::VolatileStrbRI => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            encode_load_store_auto(0b00, 0, 0b00, 1, offset, rn, rt)
        }

        // STRH Wt, [Xn, #offset] — store halfword (truncating)
        // size=01, V=0, opc=00. Offset scaled by 2.
        AArch64Opcode::StrhRI | AArch64Opcode::VolatileStrhRI => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            encode_load_store_auto(0b01, 0, 0b00, 2, offset, rn, rt)
        }

        // LDR literal (PC-relative) — uses the same base encoding but with the
        // literal addressing mode. For now encode as LDR unsigned offset with
        // an immediate operand interpreted as the literal pool offset.
        AArch64Opcode::LdrLiteral => {
            // LDR (literal): opc(2)=01 | 011 | V | 00 | imm19 | Rt
            // We encode 64-bit literal load: opc=01, V=0
            // imm19 is a signed 19-bit word offset; range-check the full value
            // before masking so a static out-of-range literal offset cannot
            // silently wrap to a wrong PC-relative target.
            let imm19 = branch_offset_signed(inst, 1, 19)?;
            let rt = preg_hw(inst, 0)?;
            Ok(((0b01 << 30) | (0b011 << 27)) | (imm19 << 5) | rt)
        }

        // STP Rt, Rt2, [Rn, #offset] (signed offset)
        // Operand order: [Rt, Rt2, Rn, imm]
        AArch64Opcode::StpRI => {
            let offset = if inst.operands.len() > 3 {
                imm_val(inst, 3)
            } else {
                0
            };
            let (opc, v, scale) = pair_encoding_fields(inst)?;
            let scaled_imm7 = scaled_pair_imm7(inst, offset, scale)?;
            let rt = preg_hw(inst, 0)?;
            let rt2 = preg_hw(inst, 1)?;
            let rn = preg_hw(inst, 2)?;
            Ok(encoding::encode_load_store_pair(
                opc,
                v,
                0,
                scaled_imm7,
                rt2,
                rn,
                rt,
            ))
        }

        // STP Rt, Rt2, [Rn, #offset]! (pre-index: base updated before store)
        AArch64Opcode::StpPreIndex => {
            let offset = if inst.operands.len() > 3 {
                imm_val(inst, 3)
            } else {
                0
            };
            let (pair_size, v, scale) = pair_index_size_v(inst)?;
            let scaled_imm7 = scaled_pair_imm7_i8(inst, offset, scale)?;
            Ok(encoding_mem::encode_ldp_stp_pre_index(
                pair_size,
                v,
                encoding_mem::PairOp::StorePair,
                scaled_imm7,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 0)? as u8,
            )?)
        }

        // LDP Rt, Rt2, [Rn, #offset] (signed offset)
        // Operand order: [Rt, Rt2, Rn, imm]
        AArch64Opcode::LdpRI => {
            let offset = if inst.operands.len() > 3 {
                imm_val(inst, 3)
            } else {
                0
            };
            let (opc, v, scale) = pair_encoding_fields(inst)?;
            let scaled_imm7 = scaled_pair_imm7(inst, offset, scale)?;
            let rt = preg_hw(inst, 0)?;
            let rt2 = preg_hw(inst, 1)?;
            let rn = preg_hw(inst, 2)?;
            Ok(encoding::encode_load_store_pair(
                opc,
                v,
                1,
                scaled_imm7,
                rt2,
                rn,
                rt,
            ))
        }

        // LDP Rt, Rt2, [Rn], #offset (post-index: base updated after load)
        AArch64Opcode::LdpPostIndex => {
            let offset = if inst.operands.len() > 3 {
                imm_val(inst, 3)
            } else {
                0
            };
            let (pair_size, v, scale) = pair_index_size_v(inst)?;
            let scaled_imm7 = scaled_pair_imm7_i8(inst, offset, scale)?;
            Ok(encoding_mem::encode_ldp_stp_post_index(
                pair_size,
                v,
                encoding_mem::PairOp::LoadPair,
                scaled_imm7,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 0)? as u8,
            )?)
        }

        // =================================================================
        // Branches
        // =================================================================

        // B <offset> — imm26 signed word offset, range-checked before mask.
        AArch64Opcode::B | AArch64Opcode::TailCall => {
            let offset = branch_offset_signed(inst, 0, 26)?;
            Ok(encoding::encode_uncond_branch(0, offset))
        }

        // B.cond <offset> — imm19 signed word offset, range-checked before mask.
        AArch64Opcode::BCond => {
            let cond = imm_val(inst, 0) as u32 & 0xF;
            let offset = if inst.operands.len() > 1 {
                branch_offset_signed(inst, 1, 19)?
            } else {
                0
            };
            Ok(encoding::encode_cond_branch(offset, cond))
        }

        // CBZ Rt, <offset> — imm19 signed word offset, range-checked before mask.
        AArch64Opcode::Cbz => {
            let sf = sf_from_operand(inst, 0);
            let rt = preg_hw(inst, 0)?;
            let imm19 = if inst.operands.len() > 1 {
                branch_offset_signed(inst, 1, 19)?
            } else {
                0
            };
            Ok(encoding::encode_cmp_branch(sf, 0, imm19, rt))
        }

        // CBNZ Rt, <offset> — imm19 signed word offset, range-checked before mask.
        AArch64Opcode::Cbnz => {
            let sf = sf_from_operand(inst, 0);
            let rt = preg_hw(inst, 0)?;
            let imm19 = if inst.operands.len() > 1 {
                branch_offset_signed(inst, 1, 19)?
            } else {
                0
            };
            Ok(encoding::encode_cmp_branch(sf, 1, imm19, rt))
        }

        // TBZ Rt, #bit, <offset>
        // 31 30:25  24  23:19  18:5    4:0
        // b5 011011  op  b40   imm14   Rt
        // TBZ: op=0, TBNZ: op=1
        AArch64Opcode::Tbz => {
            let sf = sf_from_operand(inst, 0);
            let rt = preg_hw(inst, 0)?;
            // Bit position is range-checked ([0,63] for X, [0,31] for W) before
            // the b5/b40 split so bit 64 cannot silently wrap to bit 0.
            let bit = tbz_bit_position(inst, 1, sf)?;
            // imm14: signed word branch offset, range-checked before mask.
            let imm14 = if inst.operands.len() > 2 {
                branch_offset_signed(inst, 2, 14)?
            } else {
                0
            };
            let b5 = (bit >> 5) & 1;
            let b40 = bit & 0x1F;
            Ok(((b5 << 31)
                | (0b011011 << 25)) // op=0 for TBZ
                | (b40 << 19)
                | (imm14 << 5)
                | rt)
        }

        // TBNZ Rt, #bit, <offset>
        AArch64Opcode::Tbnz => {
            let sf = sf_from_operand(inst, 0);
            let rt = preg_hw(inst, 0)?;
            // Bit position is range-checked ([0,63] for X, [0,31] for W) before
            // the b5/b40 split so bit 64 cannot silently wrap to bit 0.
            let bit = tbz_bit_position(inst, 1, sf)?;
            // imm14: signed word branch offset, range-checked before mask.
            let imm14 = if inst.operands.len() > 2 {
                branch_offset_signed(inst, 2, 14)?
            } else {
                0
            };
            let b5 = (bit >> 5) & 1;
            let b40 = bit & 0x1F;
            Ok((b5 << 31)
                | (0b011011 << 25)
                | (1 << 24) // op=1 for TBNZ
                | (b40 << 19)
                | (imm14 << 5)
                | rt)
        }

        // BR Rn
        AArch64Opcode::Br => Ok(encoding::encode_branch_reg(0b0000, preg_hw(inst, 0)?)),

        // BL <offset> — imm26 signed word offset, range-checked before mask.
        AArch64Opcode::Bl => {
            let offset = branch_offset_signed(inst, 0, 26)?;
            Ok(encoding::encode_uncond_branch(1, offset))
        }

        // BLR Rn
        AArch64Opcode::Blr => Ok(encoding::encode_branch_reg(0b0001, preg_hw(inst, 0)?)),

        // RET (X30)
        AArch64Opcode::Ret => Ok(encoding::encode_branch_reg(0b0010, 30)),

        // =================================================================
        // Extension instructions — encoded via SBFM/UBFM
        // =================================================================

        // SXTW Rd, Rn = SBFM Xd, Xn, #0, #31
        AArch64Opcode::Sxtw => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            // sf=1, opc=00(SBFM), N=1, immr=0, imms=31
            Ok(((1u32 << 31)
                | (0b100110 << 23)
                | (1 << 22)) // immr=0
                | (31 << 10) // imms=31
                | (rn << 5)
                | rd)
        }

        // UXTW materializes a 32-to-64 zero extension by writing Wd. Keep sf=0
        // even when operands are tracked as X registers so the high bits clear.
        AArch64Opcode::Uxtw => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            // MOV Wd, Wn = ORR Wd, WZR, Wn (sf=0)
            Ok(encoding::encode_logical_shifted_reg(
                0, 0b01, 0, 0, rn, 0, 31, rd,
            ))
        }

        // SXTB Rd, Rn = SBFM Xd, Xn, #0, #7
        AArch64Opcode::Sxtb => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            Ok(((1u32 << 31)
                | (0b100110 << 23)
                | (1 << 22))
                | (7 << 10) // imms=7
                | (rn << 5)
                | rd)
        }

        // SXTH Rd, Rn = SBFM Xd, Xn, #0, #15
        AArch64Opcode::Sxth => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            Ok(((1u32 << 31)
                | (0b100110 << 23)
                | (1 << 22))
                | (15 << 10) // imms=15
                | (rn << 5)
                | rd)
        }

        // UXTB Wd, Wn = UBFM Wd, Wn, #0, #7
        // Zero-extend byte: clear bits [31:8], keep bits [7:0].
        AArch64Opcode::Uxtb => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            // sf=0, opc=10(UBFM), N=0, immr=0, imms=7
            Ok(((0b10 << 29)
                | (0b100110 << 23)) // immr=0
                | (7 << 10) // imms=7
                | (rn << 5)
                | rd)
        }

        // UXTH Wd, Wn = UBFM Wd, Wn, #0, #15
        // Zero-extend halfword: clear bits [31:16], keep bits [15:0].
        AArch64Opcode::Uxth => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            // sf=0, opc=10(UBFM), N=0, immr=0, imms=15
            Ok(((0b10 << 29)
                | (0b100110 << 23)) // immr=0
                | (15 << 10) // imms=15
                | (rn << 5)
                | rd)
        }

        // =================================================================
        // Address generation
        // =================================================================

        // ADRP Rd, #imm21
        AArch64Opcode::Adrp => {
            let rd = preg_hw(inst, 0)?;
            let imm21 = adr_imm21(inst, 1)?;
            let enc = encoding_mem::encode_adrp(imm21, rd as u8)?;
            Ok(enc)
        }

        // ADR Rd, #imm21 — PC-relative address (used for jump table base)
        AArch64Opcode::Adr => {
            let rd = preg_hw(inst, 0)?;
            let imm21 = adr_imm21(inst, 1)?;
            let enc = encoding_mem::encode_adr(imm21, rd as u8)?;
            Ok(enc)
        }

        // LDRSW Xt, [Xn, Xm, LSL #2] — load signed word with register offset
        AArch64Opcode::LdrswRO => {
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let enc = encoding_mem::encode_ldrsw_register(rm as u8, rn as u8, rt as u8)?;
            Ok(enc)
        }

        // ADD Rd, Rn, #imm (PC-relative page offset addition)
        AArch64Opcode::AddPCRel => {
            let sf = sf_from_operand(inst, 0);
            let imm = imm12_operand(inst, 2)?;
            Ok(encoding::encode_add_sub_imm(
                sf,
                0,
                0,
                0,
                imm,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // ELF local-exec TLS TPREL adds carry a Symbol operand and are only
        // encodable through the module emitter's fixup interception (which
        // emits the imm12-placeholder skeleton + `R_AARCH64_TLSLE_ADD_TPREL_*`
        // relocation). Reaching the unified encoder means the fixup path was
        // bypassed — fail closed rather than encode a wrong immediate.
        AArch64Opcode::AddTprelHi12 | AArch64Opcode::AddTprelLo12 => {
            Err(EncodeError::UnsupportedOpcode(inst.opcode))
        }

        // =================================================================
        // Floating-point arithmetic
        // =================================================================
        AArch64Opcode::FaddRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_arith(
                fp_size,
                FpArithOp::Add,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::FsubRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_arith(
                fp_size,
                FpArithOp::Sub,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::FmulRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_arith(
                fp_size,
                FpArithOp::Mul,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::FdivRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_arith(
                fp_size,
                FpArithOp::Div,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FMADD Rd, Rn, Rm, Ra — scalar fused multiply-add (single rounding).
        // Operands: [Rd, Rn, Rm, Ra]. fp width from Rd's FP register class.
        AArch64Opcode::FmaddRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_madd(
                fp_size,
                FpMaddOp::Madd,
                preg_hw(inst, 2)? as u8, // Rm
                preg_hw(inst, 3)? as u8, // Ra
                preg_hw(inst, 1)? as u8, // Rn
                preg_hw(inst, 0)? as u8, // Rd
            )?;
            Ok(enc)
        }

        AArch64Opcode::FminnmRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_arith(
                fp_size,
                FpArithOp::Minnm,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::FmaxnmRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_arith(
                fp_size,
                FpArithOp::Maxnm,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FNEG Dd, Dn — floating-point negate (1-source FP)
        AArch64Opcode::FnegRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_unary(
                fp_size,
                encoding_fp::FpUnaryOp::Fneg,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FABS Dd, Dn — floating-point absolute value (1-source FP)
        AArch64Opcode::FabsRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_unary(
                fp_size,
                encoding_fp::FpUnaryOp::Fabs,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FSQRT Dd, Dn — floating-point square root (1-source FP)
        AArch64Opcode::FsqrtRR => {
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_unary(
                fp_size,
                encoding_fp::FpUnaryOp::Fsqrt,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FRINTM/FRINTP/FRINTZ Dd, Dn — round to integral (floor/ceil/trunc),
        // 1-source FP. The FpUnaryOp value is the 6-bit FP-1-source opcode field.
        AArch64Opcode::FrintmRR | AArch64Opcode::FrintpRR | AArch64Opcode::FrintzRR => {
            let fp_size = fp_size_from_inst(inst);
            let op = match inst.opcode {
                AArch64Opcode::FrintmRR => encoding_fp::FpUnaryOp::FrintM,
                AArch64Opcode::FrintpRR => encoding_fp::FpUnaryOp::FrintP,
                _ => encoding_fp::FpUnaryOp::FrintZ,
            };
            let enc = encoding_fp::encode_fp_unary(
                fp_size,
                op,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FMOV Dd, Dn (or Ss, Sn) — FPR-to-FPR register move (1-source FP)
        AArch64Opcode::FmovFprFpr => {
            require_scalar_fpr_move_operands(inst)?;
            let fp_size = fp_size_from_inst(inst);
            let enc = encoding_fp::encode_fp_unary(
                fp_size,
                encoding_fp::FpUnaryOp::FmovReg,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCMP Rn, Rm
        AArch64Opcode::Fcmp => {
            let fp_size = fp_size_from_cmp_inst(inst);
            let enc = encoding_fp::encode_fcmp(
                fp_size,
                FpCmpOp::Cmp,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCVTZS Rd, Rn (FP to signed integer, round toward zero)
        AArch64Opcode::FcvtzsRR => {
            // Source is FP register (operand 1), dest is GPR (operand 0)
            let sf_64 = true; // default to 64-bit integer
            let fp_size = fp_size_from_source(inst, 1);
            let enc = encoding_fp::encode_fp_int_conv(
                sf_64,
                fp_size,
                FpConvOp::FcvtzsToInt,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // SCVTF Rd, Rn (signed integer to FP)
        AArch64Opcode::ScvtfRR => {
            let sf_64 = true;
            let fp_size = fp_size_from_source(inst, 0);
            let enc = encoding_fp::encode_fp_int_conv(
                sf_64,
                fp_size,
                FpConvOp::ScvtfToFp,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCVTZU Rd, Rn (FP to unsigned integer, round toward zero)
        AArch64Opcode::FcvtzuRR => {
            let sf_64 = true;
            let fp_size = fp_size_from_source(inst, 1);
            let enc = encoding_fp::encode_fp_int_conv(
                sf_64,
                fp_size,
                FpConvOp::FcvtzuToInt,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // UCVTF Rd, Rn (unsigned integer to FP)
        AArch64Opcode::UcvtfRR => {
            let sf_64 = true;
            let fp_size = fp_size_from_source(inst, 0);
            let enc = encoding_fp::encode_fp_int_conv(
                sf_64,
                fp_size,
                FpConvOp::UcvtfToFp,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCVT Dd, Sn (float precision widen: f32 -> f64)
        AArch64Opcode::FcvtSD => {
            let enc = encoding_fp::encode_fp_precision_cvt(
                FpSize::Single,
                FpSize::Double,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCVT Ss, Dn (float precision narrow: f64 -> f32)
        AArch64Opcode::FcvtDS => {
            let enc = encoding_fp::encode_fp_precision_cvt(
                FpSize::Double,
                FpSize::Single,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCVT Sd, Hn (float precision widen: f16 -> f32)
        AArch64Opcode::FcvtHS => {
            let enc = encoding_fp::encode_fp_precision_cvt(
                FpSize::Half,
                FpSize::Single,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCVT Dd, Hn (float precision widen: f16 -> f64)
        AArch64Opcode::FcvtHD => {
            let enc = encoding_fp::encode_fp_precision_cvt(
                FpSize::Half,
                FpSize::Double,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCVT Hd, Sn (float precision narrow: f32 -> f16)
        AArch64Opcode::FcvtSH => {
            let enc = encoding_fp::encode_fp_precision_cvt(
                FpSize::Single,
                FpSize::Half,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FCVT Hd, Dn (float precision narrow: f64 -> f16)
        AArch64Opcode::FcvtDH => {
            let enc = encoding_fp::encode_fp_precision_cvt(
                FpSize::Double,
                FpSize::Half,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FMOV Sd, Wn / FMOV Dd, Xn (GPR to FPR bitcast)
        AArch64Opcode::FmovGprFpr => {
            let sf_64 = sf_from_operand(inst, 1) == 1;
            let fp_size = fp_size_from_source(inst, 0);
            let enc = encoding_fp::encode_fp_int_conv(
                sf_64,
                fp_size,
                FpConvOp::FmovToFp,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FMOV Wn, Sd / FMOV Xn, Dd (FPR to GPR bitcast)
        AArch64Opcode::FmovFprGpr => {
            let sf_64 = sf_from_operand(inst, 0) == 1;
            let fp_size = fp_size_from_source(inst, 1);
            let enc = encoding_fp::encode_fp_int_conv(
                sf_64,
                fp_size,
                FpConvOp::FmovToGp,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // =================================================================
        // Checked arithmetic (flag-setting variants)
        // =================================================================

        // ADDS Rd, Rn, Rm (shifted register, flag-setting)
        AArch64Opcode::AddsRR => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_add_sub_shifted_reg(
                sf,
                0,
                1,
                0,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // ADDS Rd, Rn, #imm12 (flag-setting)
        AArch64Opcode::AddsRI => {
            let sf = sf_from_operand(inst, 0);
            let imm = imm12_operand(inst, 2)?;
            Ok(encoding::encode_add_sub_imm(
                sf,
                0,
                1,
                0,
                imm,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // SUBS Rd, Rn, Rm (shifted register, flag-setting)
        AArch64Opcode::SubsRR => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_add_sub_shifted_reg(
                sf,
                1,
                1,
                0,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // SUBS Rd, Rn, #imm12 (flag-setting)
        AArch64Opcode::SubsRI => {
            let sf = sf_from_operand(inst, 0);
            let imm = imm12_operand(inst, 2)?;
            Ok(encoding::encode_add_sub_imm(
                sf,
                1,
                1,
                0,
                imm,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // =================================================================
        // i128 multi-register arithmetic
        // =================================================================

        // ADC Xd, Xn, Xm — add with carry
        // ARM ARM: C6.2.1  Add with Carry
        // 31 30 29 28:21    20:16 15:10  9:5  4:0
        // sf  0  0  11010000 Rm   000000 Rn   Rd
        AArch64Opcode::Adc => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((sf << 31) | (0b0_0_11010000u32 << 21) | (rm << 16) | (rn << 5) | rd)
        }

        // SBC Xd, Xn, Xm — subtract with carry (borrow)
        // ARM ARM: C6.2.229  Subtract with Carry
        // 31 30 29 28:21    20:16 15:10  9:5  4:0
        // sf  1  0  11010000 Rm   000000 Rn   Rd
        AArch64Opcode::Sbc => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((sf << 31) | (0b1_0_11010000u32 << 21) | (rm << 16) | (rn << 5) | rd)
        }

        // UMULH Xd, Xn, Xm — unsigned multiply high
        // ARM ARM: C6.2.332  Unsigned Multiply High
        // 31 30:29 28:24 23:21 20:16 15 14:10 9:5  4:0
        //  1  00   11011 110   Rm    0  11111  Rn   Rd
        // sf=1 always (64-bit only), op54=00, op31=110, o0=0, Ra=11111
        AArch64Opcode::Umulh => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((1u32 << 31)
                | (0b11011 << 24)
                | (0b110 << 21)
                | (rm << 16)
                | (0b11111 << 10)  // Ra field = 11111 (ignored for UMULH)
                | (rn << 5)
                | rd)
        }

        // SMULH Xd, Xn, Xm — signed multiply high
        // ARM ARM: C6.2.289  Signed Multiply High
        // 31 30:29 28:24 23:21 20:16 15 14:10 9:5  4:0
        //  1  00   11011 010   Rm    0  11111  Rn   Rd
        // sf=1 always (64-bit only), op54=00, op31=010, o0=0, Ra=11111
        // Distinguishing bit from UMULH: op31 = 010 (signed) vs 110 (unsigned).
        AArch64Opcode::Smulh => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            Ok((1u32 << 31)
                | (0b11011 << 24)
                | (0b010 << 21)
                | (rm << 16)
                | (0b11111 << 10)  // Ra field = 11111 (ignored for SMULH)
                | (rn << 5)
                | rd)
        }

        // MADD Xd, Xn, Xm, Xa — multiply-add: Xd = Xa + Xn * Xm
        // ARM ARM: C6.2.163  Multiply-Add
        // 31 30:29 28:24 23:21 20:16 15 14:10 9:5  4:0
        // sf  00   11011 000   Rm    0  Ra     Rn   Rd
        // Same encoding group as MUL but Ra != XZR.
        // Operands: [Rd, Rn, Rm, Ra]
        AArch64Opcode::Madd => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let ra = preg_hw(inst, 3)?;
            Ok((sf << 31) | (0b11011 << 24) | (rm << 16) | (ra << 10) | (rn << 5) | rd)
        }

        // =================================================================
        // Conditional select / set
        // =================================================================

        // CSEL Xd, Xn, Xm, cond
        // ARM ARM: C6.2.76  Conditional Select
        // 31 30 29 28:21    20:16 15:12 11 10 9:5  4:0
        // sf  0  0  11010100 Rm    cond   0  0  Rn   Rd
        // Operands: [dst, true_src, false_src, Imm(cond_code_encoding)]
        AArch64Opcode::Csel => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let cond = imm_val(inst, 3) as u32 & 0xF;
            Ok(((sf << 31) | (0b11010100 << 21) | (rm << 16) | (cond << 12)) | (rn << 5) | rd)
        }

        // FCSEL Sd/Dd, Sn/Dn, Sm/Dm, cond — scalar FP conditional select.
        // Operands: [Rd, Rn (true), Rm (false), Imm(cond)]. FAIL-CLOSED unless
        // all three regs are the same scalar FPR class (S/D) — the bank check the
        // GPR Csel lacks (see `require_fcsel_operands`). ftype derived from that
        // class (S=00 / D=01). Byte-verified vs clang-assembled fcsel forms.
        AArch64Opcode::FcselRR => {
            let fp_size = require_fcsel_operands(inst)?;
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let cond = imm_val(inst, 3) as u32 & 0xF;
            let enc = encoding_fp::encode_fcsel(fp_size, cond, rm as u8, rn as u8, rd as u8)?;
            Ok(enc)
        }

        // =================================================================
        // NEON SIMD (vector) instructions
        // =================================================================

        // Integer vector arithmetic: ADD, SUB, MUL
        AArch64Opcode::NeonAddV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                encoding_neon::IntVec3Op::Add,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonSubV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                encoding_neon::IntVec3Op::Sub,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonMulV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                encoding_neon::IntVec3Op::Mul,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Integer vector min/max (per lane): SMAX, SMIN, UMAX, UMIN
        AArch64Opcode::NeonSmaxV
        | AArch64Opcode::NeonSminV
        | AArch64Opcode::NeonUmaxV
        | AArch64Opcode::NeonUminV => {
            let arr = neon_arrangement(inst);
            let op = match inst.opcode {
                AArch64Opcode::NeonSmaxV => encoding_neon::IntVec3Op::Smax,
                AArch64Opcode::NeonSminV => encoding_neon::IntVec3Op::Smin,
                AArch64Opcode::NeonUmaxV => encoding_neon::IntVec3Op::Umax,
                _ => encoding_neon::IntVec3Op::Umin,
            };
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                op,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FP vector arithmetic: FADD, FSUB, FMUL, FDIV
        AArch64Opcode::NeonFaddV => {
            let fp_arr = neon_fp_arrangement(inst);
            let enc = encoding_neon::encode_fp_vec3_same(
                fp_arr,
                encoding_neon::FpVec3Op::Fadd,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonFsubV => {
            let fp_arr = neon_fp_arrangement(inst);
            let enc = encoding_neon::encode_fp_vec3_same(
                fp_arr,
                encoding_neon::FpVec3Op::Fsub,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonFmulV => {
            let fp_arr = neon_fp_arrangement(inst);
            let enc = encoding_neon::encode_fp_vec3_same(
                fp_arr,
                encoding_neon::FpVec3Op::Fmul,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonFdivV => {
            let fp_arr = neon_fp_arrangement(inst);
            let enc = encoding_neon::encode_fp_vec3_same(
                fp_arr,
                encoding_neon::FpVec3Op::Fdiv,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FP vector fused multiply-accumulate/subtract: FMLA / FMLS.
        // Operand 0 (Vd) is a tied def-use accumulator (see has_tied_def_use).
        AArch64Opcode::NeonFmlaV | AArch64Opcode::NeonFmlsV => {
            let fp_arr = neon_fp_arrangement(inst);
            let op = if inst.opcode == AArch64Opcode::NeonFmlaV {
                encoding_neon::FpVec3Op::Fmla
            } else {
                encoding_neon::FpVec3Op::Fmls
            };
            let enc = encoding_neon::encode_fp_vec3_same(
                fp_arr,
                op,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FP vector fused multiply-accumulate BY ELEMENT: FMLA Vd.T, Vn.T,
        // Vm.Ts[lane]. Operand 0 (Vd) is a tied def-use accumulator; operand 3
        // is the broadcast lane, operand 4 (last) the FP arrangement.
        AArch64Opcode::NeonFmlaLaneV => {
            let fp_arr = neon_fp_arrangement(inst);
            let lane = imm_val(inst, 3) as u8;
            let enc = encoding_neon::encode_fmla_lane(
                fp_arr,
                false, // FMLA (the only by-element form emitted; FMLS is a proof control)
                lane,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Vector integer->FP conversion: UCVTF / SCVTF (vector, integer form).
        AArch64Opcode::NeonUcvtfV | AArch64Opcode::NeonScvtfV => {
            let fp_arr = neon_fp_arrangement(inst);
            let signed = inst.opcode == AArch64Opcode::NeonScvtfV;
            let enc = encoding_neon::encode_fp_int_cvt_vec(
                fp_arr,
                signed,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Vector f32->f64 widening convert: FCVTL (low half) / FCVTL2 (high half).
        AArch64Opcode::NeonFcvtlV | AArch64Opcode::NeonFcvtl2V => {
            let high = inst.opcode == AArch64Opcode::NeonFcvtl2V;
            let enc = encoding_neon::encode_fcvtl_vec(
                high,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FP lane extract to a scalar D register: MOV Dd, Vn.D[lane].
        AArch64Opcode::NeonDupScalarD => {
            let lane = imm_val(inst, 2) as u8;
            let enc = encoding_neon::encode_dup_scalar_d(
                lane,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // FP vector compare greater-than (register): FCMGT
        AArch64Opcode::NeonFcmgtV => {
            let fp_arr = neon_fp_arrangement(inst);
            let enc = encoding_neon::encode_fp_vec3_same(
                fp_arr,
                encoding_neon::FpVec3Op::Fcmgt,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Vector logic: AND, ORR, EOR, BIC
        AArch64Opcode::NeonAndV => {
            let q = neon_q_bit(inst);
            let enc = encoding_neon::encode_vec_logic(
                q,
                encoding_neon::VecLogicOp::And,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonOrrV => {
            let q = neon_q_bit(inst);
            let enc = encoding_neon::encode_vec_logic(
                q,
                encoding_neon::VecLogicOp::Orr,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonEorV => {
            let q = neon_q_bit(inst);
            let enc = encoding_neon::encode_vec_logic(
                q,
                encoding_neon::VecLogicOp::Eor,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonBicV => {
            let q = neon_q_bit(inst);
            let enc = encoding_neon::encode_vec_logic(
                q,
                encoding_neon::VecLogicOp::Bic,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Vector BIT (bitwise insert if true; Vd is a TIED def-use).
        AArch64Opcode::NeonBitV => {
            let q = neon_q_bit(inst);
            let enc = encoding_neon::encode_vec_logic(
                q,
                encoding_neon::VecLogicOp::Bit,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Vector NOT
        AArch64Opcode::NeonNotV => {
            let q = neon_q_bit(inst);
            let enc =
                encoding_neon::encode_vec_not(q, preg_hw(inst, 1)? as u8, preg_hw(inst, 0)? as u8)?;
            Ok(enc)
        }

        // Vector RBIT/REV byte operations.
        // Operands: [Vd, Vn, Imm(arrangement)] where arrangement is 8B/16B.
        AArch64Opcode::NeonRbitV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_vec_byte_2reg(
                arr,
                encoding_neon::VecByte2Op::Rbit,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonRev32V => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_vec_byte_2reg(
                arr,
                encoding_neon::VecByte2Op::Rev32,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonRev64V => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_vec_byte_2reg(
                arr,
                encoding_neon::VecByte2Op::Rev64,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Population count (per byte). Operands: [Vd, Vn, Imm(arrangement)] (16B).
        AArch64Opcode::NeonCntV => {
            let arr = neon_arrangement(inst);
            let enc =
                encoding_neon::encode_cnt(arr, preg_hw(inst, 1)? as u8, preg_hw(inst, 0)? as u8)?;
            Ok(enc)
        }

        // Unsigned add long pairwise (widening). Operands: [Vd, Vn, Imm(input
        // arrangement)] where input is 16B (-> 8H) or 8H (-> 4S).
        AArch64Opcode::NeonUaddlpV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_uaddlp(
                arr,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Signed add long pairwise (widening). Operands: [Vd, Vn, Imm(input
        // arrangement)] where input is 16B (-> 8H) or 8H (-> 4S).
        AArch64Opcode::NeonSaddlpV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_saddlp(
                arr,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Per-lane signed absolute value. Operands: [Vd, Vn, Imm(arrangement)] (.4S).
        AArch64Opcode::NeonAbsV => {
            let arr = neon_arrangement(inst);
            let enc =
                encoding_neon::encode_abs(arr, preg_hw(inst, 1)? as u8, preg_hw(inst, 0)? as u8)?;
            Ok(enc)
        }

        // Unsigned dot-product ACCUMULATE (FEAT_DotProd). Operands:
        // [Vd (accumulator, tied def-use), Vn, Vm, Imm(input arrangement 16B)].
        AArch64Opcode::NeonUdotV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_udot(
                arr,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Byte-wise extract/concatenate (sliding window). Operands:
        // [Vd, Vn (LOW source), Vm (HIGH source), Imm(byte shift 4|8|12)].
        // Operand order is load-bearing (EXT is not commutative); the encoder
        // rejects every immediate without proof credit (fail-closed).
        AArch64Opcode::NeonExtV => {
            let imm = imm_operand(inst, 3)?;
            let enc = encoding_neon::encode_ext(
                imm,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Widening multiply-accumulate-long (SMLAL/SMLAL2/UMLAL/UMLAL2). Operands:
        // [Vd (accumulator, tied def-use), Vn, Vm, Imm(input arrangement .4S)].
        // Low vs high (`.4S` lanes {0,1} vs {2,3}) and signed vs unsigned are
        // static in the opcode; the encoder fail-closes on any non-.4S input.
        AArch64Opcode::NeonSmlalV
        | AArch64Opcode::NeonSmlal2V
        | AArch64Opcode::NeonUmlalV
        | AArch64Opcode::NeonUmlal2V => {
            let arr = neon_arrangement(inst);
            let high = matches!(
                inst.opcode,
                AArch64Opcode::NeonSmlal2V | AArch64Opcode::NeonUmlal2V
            );
            let signed = matches!(
                inst.opcode,
                AArch64Opcode::NeonSmlalV | AArch64Opcode::NeonSmlal2V
            );
            let enc = encoding_neon::encode_smlal(
                arr,
                high,
                signed,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Widening add-wide (UADDW/UADDW2). Operands: [Vd (pure def), Vn (i64
        // addend, a SEPARATE source — NOT tied), Vm (.4S source), Imm(input
        // arrangement .4S)]. Low vs high (`.4S` lanes {0,1} vs {2,3}) is static
        // in the opcode; the encoder fail-closes on any non-.4S input.
        AArch64Opcode::NeonUaddwV | AArch64Opcode::NeonUaddw2V => {
            let arr = neon_arrangement(inst);
            let high = matches!(inst.opcode, AArch64Opcode::NeonUaddw2V);
            let enc = encoding_neon::encode_uaddw(
                arr,
                high,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // SIGNED widening add-wide (SADDW/SADDW2) — the signed sibling: same
        // plain three-operand layout [Vd (pure def), Vn (i64 addend, NOT tied),
        // Vm (.4S source), Imm(input arrangement .4S)]; fail-closes on any
        // non-.4S input.
        AArch64Opcode::NeonSaddwV | AArch64Opcode::NeonSaddw2V => {
            let arr = neon_arrangement(inst);
            let high = matches!(inst.opcode, AArch64Opcode::NeonSaddw2V);
            let enc = encoding_neon::encode_saddw(
                arr,
                high,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Vector integer multiply-ACCUMULATE (MLA.4S). Operands: [Vd
        // (accumulator, tied def-use — the accumulate READS Vd), Vn, Vm,
        // Imm(arrangement .4S)]; the encoder fail-closes on any non-.4S
        // arrangement.
        AArch64Opcode::NeonMlaV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_mla(
                arr,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // UNSIGNED pairwise widening ACCUMULATE (UADALP .4S -> .2D). Operands:
        // [Vd (accumulator, tied def-use — the accumulate READS Vd), Vn (.4S
        // source), Imm(input arrangement .4S)]; the encoder fail-closes on any
        // non-.4S input (contrast the non-accumulating NeonUaddlpV, which
        // accepts only 16B/8H inputs).
        AArch64Opcode::NeonUadalpV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_uadalp(
                arr,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // Vector compare: CMEQ, CMGT, CMGE, CMHI, CMHS
        AArch64Opcode::NeonCmeqV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                encoding_neon::IntVec3Op::Cmeq,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonCmgtV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                encoding_neon::IntVec3Op::Cmgt,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonCmgeV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                encoding_neon::IntVec3Op::Cmge,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonCmhiV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                encoding_neon::IntVec3Op::Cmhi,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        AArch64Opcode::NeonCmhsV => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_int_vec3_same(
                arr,
                encoding_neon::IntVec3Op::Cmhs,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // UMAXV: unsigned max across vector lanes.
        // Operands: [Sd, Vn, Imm(arrangement)]. #573 uses only .4S.
        AArch64Opcode::NeonUmaxv => {
            let arr = neon_arrangement(inst);
            if arr != encoding_neon::VectorArrangement::S4 {
                return Err(EncodeError::NeonEncode(
                    encoding_neon::NeonEncodeError::InvalidSize(arr.size() as u8),
                ));
            }
            let enc =
                encoding_neon::encode_umaxv_4s(preg_hw(inst, 1)? as u8, preg_hw(inst, 0)? as u8)?;
            Ok(enc)
        }

        // ADDP: pairwise add across two i64 lanes into scalar Dd.
        // Operands: [Dd, Vn, Imm(arrangement)]. #909 uses only .2D.
        AArch64Opcode::NeonAddpScalar => {
            let arr = neon_arrangement(inst);
            if arr != encoding_neon::VectorArrangement::D2 {
                return Err(EncodeError::NeonEncode(
                    encoding_neon::NeonEncodeError::InvalidSize(arr.size() as u8),
                ));
            }

            match inst.operands.first() {
                Some(MachOperand::PReg(p)) if preg_class(*p) == RegClass::Fpr64 => {}
                Some(other) => {
                    return Err(EncodeError::InvalidOperand {
                        opcode: inst.opcode,
                        index: 0,
                        desc: format!("expected scalar D destination, got {other:?}"),
                    });
                }
                None => {
                    return Err(EncodeError::MissingOperand {
                        opcode: inst.opcode,
                        index: 0,
                        expected: 1,
                    });
                }
            }

            let enc = encoding_neon::encode_addp_scalar_2d(
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // DUP (element): duplicate one vector lane to all lanes
        // Operands: [Vd, Vn, Imm(lane), Imm(element_size)]
        AArch64Opcode::NeonDupElem => {
            let q = neon_q_bit(inst);
            let lane = imm_val(inst, 2) as u8;
            let elem = neon_element_size(inst, 3);
            let enc = encoding_neon::encode_dup_element(
                q,
                elem,
                lane,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // DUP (general): duplicate GPR to all vector lanes
        // Operands: [Vd, Rn, Imm(element_size)]
        //
        // The Q bit (128-bit `.16b`/… vs 64-bit `.8b`/… arrangement) is derived
        // from the DESTINATION register class, NOT the trailing element-size Imm:
        // a `<8 x i8>` V64 splat targets an Fpr64 (D) register (`dup.8b`, Q=0),
        // while every 128-bit pack targets an Fpr128 (Q) register (`dup.16b`/…,
        // Q=1). Reading the element-size Imm here would wrongly force Q=1 for the
        // V64 form (it is never 0), mis-encoding a D-register dup as 128-bit.
        AArch64Opcode::NeonDupGen => {
            let q = match inst.operands.first() {
                Some(MachOperand::PReg(p)) if preg_class(*p) == RegClass::Fpr128 => 1,
                Some(MachOperand::PReg(_)) => 0,
                _ => neon_q_bit(inst),
            };
            let elem = neon_element_size(inst, 2);
            let enc = encoding_neon::encode_dup_general(
                q,
                elem,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // INS (general): insert GPR into vector lane
        // Operands: [Vd, Rn, Imm(lane), Imm(element_size)]
        AArch64Opcode::NeonInsGen => {
            let lane = imm_val(inst, 2) as u8;
            let elem = neon_element_size(inst, 3);
            let enc = encoding_neon::encode_ins_general(
                elem,
                lane,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // UMOV (general): extract vector lane to GPR
        // Operands: [Wd/Xd, Vn, Imm(lane), Imm(element_size)]
        AArch64Opcode::NeonUmovGen => {
            let elem = neon_element_size(inst, 3);
            let expected_dst = match elem {
                encoding_neon::ElementSize::B
                | encoding_neon::ElementSize::H
                | encoding_neon::ElementSize::S => RegClass::Gpr32,
                encoding_neon::ElementSize::D => RegClass::Gpr64,
            };

            match inst.operands.first() {
                Some(MachOperand::PReg(p)) if preg_class(*p) == expected_dst => {}
                Some(other) => {
                    return Err(EncodeError::InvalidOperand {
                        opcode: inst.opcode,
                        index: 0,
                        desc: format!("expected {expected_dst:?} destination, got {other:?}"),
                    });
                }
                None => {
                    return Err(EncodeError::MissingOperand {
                        opcode: inst.opcode,
                        index: 0,
                        expected: 1,
                    });
                }
            }

            let lane = imm_val(inst, 2) as u8;
            let enc = encoding_neon::encode_umov_general(
                elem,
                lane,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // MOVI: move immediate to vector (byte form)
        // Operands: [Vd, Imm(imm8)]
        AArch64Opcode::NeonMovi => {
            let q = match inst.operands.first() {
                Some(MachOperand::PReg(p)) if preg_class(*p) == RegClass::Fpr128 => 1,
                Some(MachOperand::PReg(_)) => 0,
                _ => neon_q_bit(inst),
            };
            let imm8 = imm_val(inst, 1) as u8;
            let enc = encoding_neon::encode_movi_byte(q, imm8, preg_hw(inst, 0)? as u8)?;
            Ok(enc)
        }

        // SIMD shift by immediate: SHL / USHR / SSHR
        // Operands: [Vd, Vn, Imm(shift), Imm(arrangement)]
        AArch64Opcode::NeonShlVImm | AArch64Opcode::NeonUshrVImm | AArch64Opcode::NeonSshrVImm => {
            let arr = neon_arrangement(inst);
            let shift = imm_val(inst, 2);
            if shift < 0 {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 2,
                    desc: format!("negative vector shift amount {shift}"),
                });
            }
            let op = match inst.opcode {
                AArch64Opcode::NeonShlVImm => encoding_neon::VecShiftImmOp::Shl,
                AArch64Opcode::NeonUshrVImm => encoding_neon::VecShiftImmOp::Ushr,
                AArch64Opcode::NeonSshrVImm => encoding_neon::VecShiftImmOp::Sshr,
                _ => unreachable!(),
            };
            let enc = encoding_neon::encode_vec_shift_imm(
                arr,
                op,
                shift as u32,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // LD1 post-index: SIMD load 1 register
        // Operands: [Vt, Xn, Imm(arrangement)]
        AArch64Opcode::NeonLd1Post => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_ld1_post_imm(
                arr,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // LDP Q-pair post-index: SIMD&FP load pair of 128-bit registers.
        // Operands: [Vt1, Vt2, Xn, Imm(post-index byte offset)]
        // FAIL-CLOSED on operand class: both data operands MUST be Fpr128.
        // A GPR data operand is REJECTED rather than silently encoded as the
        // integer LDP form — the prior P0 in this family was a pre/post-index
        // pair encoder hardcoding the GPR form (V=0) and clobbering FPR pairs.
        AArch64Opcode::NeonLdpQPost => {
            for idx in [0usize, 1] {
                let class = pair_operand_class(inst, idx)?;
                if class != RegClass::Fpr128 {
                    return Err(EncodeError::InvalidOperand {
                        opcode: inst.opcode,
                        index: idx,
                        desc: format!(
                            "NeonLdpQPost data operand must be Fpr128 (Q register), got {class:?}"
                        ),
                    });
                }
            }
            let offset = imm_val(inst, 3);
            let enc = encoding_neon::encode_ldp_q_post_imm(
                offset,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // STP Q-pair post-index: SIMD&FP store pair of 128-bit registers.
        // Operands: [Vt1, Vt2, Xn, Imm(post-index byte offset)]
        // FAIL-CLOSED on operand class: both data operands MUST be Fpr128 — a
        // GPR data operand is REJECTED rather than silently encoded as the
        // integer STP form (the LdpQPost P0 class: a hardcoded GPR pair form
        // clobbering FPR pairs). The STORE sibling of NeonLdpQPost.
        AArch64Opcode::NeonStpQPost => {
            for idx in [0usize, 1] {
                let class = pair_operand_class(inst, idx)?;
                if class != RegClass::Fpr128 {
                    return Err(EncodeError::InvalidOperand {
                        opcode: inst.opcode,
                        index: idx,
                        desc: format!(
                            "NeonStpQPost data operand must be Fpr128 (Q register), got {class:?}"
                        ),
                    });
                }
            }
            let offset = imm_val(inst, 3);
            let enc = encoding_neon::encode_stp_q_post_imm(
                offset,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 2)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // ST1 post-index: SIMD store 1 register
        // Operands: [Vt, Xn, Imm(arrangement)]
        AArch64Opcode::NeonSt1Post => {
            let arr = neon_arrangement(inst);
            let enc = encoding_neon::encode_st1_post_imm(
                arr,
                preg_hw(inst, 1)? as u8,
                preg_hw(inst, 0)? as u8,
            )?;
            Ok(enc)
        }

        // =================================================================
        // Atomic memory operations (ARMv8 + ARMv8.1-a LSE)
        // =================================================================

        // LDAR Xt, [Xn] — load-acquire register.
        // Encoding: size(2) 001000 010 11111 1 11111 Rn(5) Rt(5)
        // size: 10 = 32-bit, 11 = 64-bit (from register class)
        AArch64Opcode::Ldar => {
            let sf = sf_from_operand(inst, 0);
            let size = if sf == 1 { 0b11 } else { 0b10 };
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            Ok(encode_load_acquire(size, rn, rt))
        }

        // LDARB Wt, [Xn] — load-acquire byte. size=00.
        AArch64Opcode::Ldarb => {
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            Ok(encode_load_acquire(0b00, rn, rt))
        }

        // LDARH Wt, [Xn] — load-acquire halfword. size=01.
        AArch64Opcode::Ldarh => {
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            Ok(encode_load_acquire(0b01, rn, rt))
        }

        // STLR Xt, [Xn] — store-release register.
        // Encoding: size(2) 001000 100 11111 1 11111 Rn(5) Rt(5)
        AArch64Opcode::Stlr => {
            let sf = sf_from_operand(inst, 0);
            let size = if sf == 1 { 0b11 } else { 0b10 };
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            Ok(encode_store_release(size, rn, rt))
        }

        // STLRB Wt, [Xn] — store-release byte. size=00.
        AArch64Opcode::Stlrb => {
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            Ok(encode_store_release(0b00, rn, rt))
        }

        // STLRH Wt, [Xn] — store-release halfword. size=01.
        AArch64Opcode::Stlrh => {
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            Ok(encode_store_release(0b01, rn, rt))
        }

        // LSE atomic RMW instructions: LDADD, LDCLR, LDEOR, LDSET,
        // LDSMAX, LDSMIN, LDUMAX, LDUMIN, SWP
        // Encoding: size(2) 111 0 00 A R 1 Rs(5) o3(1) opc(3) 00 Rn(5) Rt(5)
        //
        // LDADD:  o3=0 opc=000
        // LDCLR:  o3=0 opc=001
        // LDEOR:  o3=0 opc=010
        // LDSET:  o3=0 opc=011
        // LDSMAX: o3=0 opc=100
        // LDSMIN: o3=0 opc=101
        // LDUMAX: o3=0 opc=110
        // LDUMIN: o3=0 opc=111
        // SWP:    o3=1 opc=000
        //
        // Ordering variants: base (A=0,R=0), A (A=1,R=0), L (A=0,R=1), AL (A=1,R=1)
        // Operands: [Rs (operand), Rt (old value dest), Rn (address)]
        AArch64Opcode::Ldadd => {
            encode_lse_atomic(inst, 0, 0b000, 0, 0) // A=0, R=0
        }
        AArch64Opcode::Ldadda => {
            encode_lse_atomic(inst, 0, 0b000, 1, 0) // A=1, R=0
        }
        AArch64Opcode::Ldaddal => {
            encode_lse_atomic(inst, 0, 0b000, 1, 1) // A=1, R=1
        }
        AArch64Opcode::Ldaddl => {
            encode_lse_atomic(inst, 0, 0b000, 0, 1) // A=0, R=1 (release-only)
        }
        AArch64Opcode::Ldclr => encode_lse_atomic(inst, 0, 0b001, 0, 0),
        AArch64Opcode::Ldclra => encode_lse_atomic(inst, 0, 0b001, 1, 0),
        AArch64Opcode::Ldclral => encode_lse_atomic(inst, 0, 0b001, 1, 1),
        AArch64Opcode::Ldclrl => encode_lse_atomic(inst, 0, 0b001, 0, 1),
        AArch64Opcode::Ldeor => encode_lse_atomic(inst, 0, 0b010, 0, 0),
        AArch64Opcode::Ldeora => encode_lse_atomic(inst, 0, 0b010, 1, 0),
        AArch64Opcode::Ldeoral => encode_lse_atomic(inst, 0, 0b010, 1, 1),
        AArch64Opcode::Ldeorl => encode_lse_atomic(inst, 0, 0b010, 0, 1),
        AArch64Opcode::Ldset => encode_lse_atomic(inst, 0, 0b011, 0, 0),
        AArch64Opcode::Ldseta => encode_lse_atomic(inst, 0, 0b011, 1, 0),
        AArch64Opcode::Ldsetal => encode_lse_atomic(inst, 0, 0b011, 1, 1),
        AArch64Opcode::Ldsetl => encode_lse_atomic(inst, 0, 0b011, 0, 1),
        AArch64Opcode::Ldsmax => encode_lse_atomic(inst, 0, 0b100, 0, 0),
        AArch64Opcode::Ldsmaxa => encode_lse_atomic(inst, 0, 0b100, 1, 0),
        AArch64Opcode::Ldsmaxal => encode_lse_atomic(inst, 0, 0b100, 1, 1),
        AArch64Opcode::Ldsmaxl => encode_lse_atomic(inst, 0, 0b100, 0, 1),
        AArch64Opcode::Ldsmin => encode_lse_atomic(inst, 0, 0b101, 0, 0),
        AArch64Opcode::Ldsmina => encode_lse_atomic(inst, 0, 0b101, 1, 0),
        AArch64Opcode::Ldsminal => encode_lse_atomic(inst, 0, 0b101, 1, 1),
        AArch64Opcode::Ldsminl => encode_lse_atomic(inst, 0, 0b101, 0, 1),
        AArch64Opcode::Ldumax => encode_lse_atomic(inst, 0, 0b110, 0, 0),
        AArch64Opcode::Ldumaxa => encode_lse_atomic(inst, 0, 0b110, 1, 0),
        AArch64Opcode::Ldumaxal => encode_lse_atomic(inst, 0, 0b110, 1, 1),
        AArch64Opcode::Ldumaxl => encode_lse_atomic(inst, 0, 0b110, 0, 1),
        AArch64Opcode::Ldumin => encode_lse_atomic(inst, 0, 0b111, 0, 0),
        AArch64Opcode::Ldumina => encode_lse_atomic(inst, 0, 0b111, 1, 0),
        AArch64Opcode::Lduminal => encode_lse_atomic(inst, 0, 0b111, 1, 1),
        AArch64Opcode::Lduminl => encode_lse_atomic(inst, 0, 0b111, 0, 1),
        AArch64Opcode::Swp => encode_lse_atomic(inst, 1, 0b000, 0, 0),
        AArch64Opcode::Swpa => encode_lse_atomic(inst, 1, 0b000, 1, 0),
        AArch64Opcode::Swpal => encode_lse_atomic(inst, 1, 0b000, 1, 1),
        AArch64Opcode::Swpl => encode_lse_atomic(inst, 1, 0b000, 0, 1),

        // CAS Rs, Rt, [Xn] — compare and swap.
        // Encoding: size(2) 001000 1 A 1 Rs(5) o0(1) 11111 Rn(5) Rt(5)
        // where o0 = R (release bit).
        // CAS:   A=0, R=0
        // CASA:  A=1, R=0
        // CASAL: A=1, R=1
        // CASL:  A=0, R=1 (release-only)
        // Operands: [Rs (expected/result), Rt (desired), Rn (address)]
        AArch64Opcode::Cas => {
            encode_cas(inst, 0, 0) // A=0, R=0
        }
        AArch64Opcode::Casa => {
            encode_cas(inst, 1, 0) // A=1, R=0
        }
        AArch64Opcode::Casal => {
            encode_cas(inst, 1, 1) // A=1, R=1
        }
        AArch64Opcode::Casl => {
            encode_cas(inst, 0, 1) // A=0, R=1 (release-only; o0 = R)
        }

        // LDAXR Xt, [Xn] — load-acquire exclusive register (LL/SC).
        // Encoding: size(2) 001000 010 11111 1 11111 Rn(5) Rt(5)
        // Same encoding as LDAR but with different bit pattern:
        // size(2) 001000 0 1 0 Rs(5=11111) o0(1=1) Rt2(5=11111) Rn(5) Rt(5)
        AArch64Opcode::Ldaxr => {
            let sf = sf_from_operand(inst, 0);
            let size = if sf == 1 { 0b11 } else { 0b10 };
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            // size(2) 001000 0 1 0 11111 1 11111 Rn(5) Rt(5)
            Ok((((size << 30) | (0b001000 << 24)) | (1 << 22))
                | (0b11111 << 16)
                | (1 << 15)
                | (0b11111 << 10)
                | (rn << 5)
                | rt)
        }

        // STLXR Ws, Xt, [Xn] — store-release exclusive register (LL/SC).
        // Encoding: size(2) 001000 0 0 0 Rs(5) 1 11111 Rn(5) Rt(5)
        // Operands: [Ws (status), Rt (value), Rn (address)]
        AArch64Opcode::Stlxr => {
            let sf = sf_from_operand(inst, 1); // size from value register
            let size = if sf == 1 { 0b11 } else { 0b10 };
            let rs = preg_hw(inst, 0)?; // status
            let rt = preg_hw(inst, 1)?; // value
            let rn = preg_hw(inst, 2)?; // address
            Ok(((size << 30) | (0b001000 << 24))
                | (rs << 16)
                | (1 << 15)
                | (0b11111 << 10)
                | (rn << 5)
                | rt)
        }

        // DMB — data memory barrier.
        // Encoding: 1101 0101 0000 0011 0011 CRm(4) 1 01 11111
        // CRm = barrier option (e.g., 0xF=SY, 0xB=ISH, 0x9=ISHLD, 0xA=ISHST)
        // Operands: [Imm(CRm)]
        AArch64Opcode::Dmb => {
            let crm = (imm_val(inst, 0) as u32) & 0xF;
            Ok(0xD5033000 | (crm << 8) | 0xBF)
        }

        // DSB — data synchronization barrier.
        // Encoding: 1101 0101 0000 0011 0011 CRm(4) 1 00 11111
        AArch64Opcode::Dsb => {
            let crm = (imm_val(inst, 0) as u32) & 0xF;
            Ok(0xD5033000 | (crm << 8) | 0x9F)
        }

        // ISB — instruction synchronization barrier.
        // Encoding: 1101 0101 0000 0011 0011 CRm(4) 1 10 11111
        AArch64Opcode::Isb => {
            let crm = (imm_val(inst, 0) as u32) & 0xF;
            Ok(0xD5033000 | (crm << 8) | 0xDF)
        }

        // =================================================================
        // System register access (ARM ARM C6.2.169)
        // =================================================================
        //
        // MRS Xd, (sysreg) — move from system register to GPR.
        //
        // Encoding (32-bit A64):
        //   31          22 21 20         5 4    0
        //   1101 0101 00  L  | systemreg | Rt
        //                 ^
        //                 L=1 for MRS, L=0 for MSR
        //
        // The `systemreg` field is 16 bits packed as (per LLVM's
        // `AArch64SystemOperands.td` `class SysReg` at line 1070):
        //   bits[15:14] = op0  (2 bits)
        //   bits[13:11] = op1  (3 bits)
        //   bits[10:7]  = CRn  (4 bits)
        //   bits[6:3]   = CRm  (4 bits)
        //   bits[2:0]   = op2  (3 bits)
        //
        // For TPIDR_EL0 (op0=11, op1=011, CRn=1101, CRm=0000, op2=010):
        //   systemreg = 11_011_1101_0000_010 = 0xDE82
        //
        // Full MRS X0, TPIDR_EL0:
        //   bits[31:22]=1101010100 | bit21=1 | bits[20:5]=0xDE82 | Rt=0
        //   = 1101 0101 0011 1011 1101 0000 0100 0000 = 0xD53BD040
        //
        // Base template (L=1, systemreg=0, Rt=0):
        //   1101 0101 0010 0000 0000 0000 0000 0000 = 0xD520_0000
        //
        // Cross-checked against LLVM `AArch64InstrFormats.td` MRSI (line 2016)
        // and `AArch64SystemOperands.td` TPIDR_EL0 (line 1463).
        //
        // Operands: [PReg(Rt), Imm(sysreg_bits_16)]
        AArch64Opcode::Mrs => {
            let rt = preg_hw(inst, 0)?;
            let sysreg_bits = (imm_val(inst, 1) as u32) & 0xFFFF;
            // 0xD520_0000 base = bits[31:22]=1101010100, bit21=1 (MRS),
            // bits[20:5]=0, Rt=0.
            Ok(0xD520_0000 | (sysreg_bits << 5) | rt)
        }

        // =================================================================
        // Trap fallbacks and pseudo-instructions
        // =================================================================

        // BRK is a real trap instruction. The legacy Trap* panic pseudos below
        // have no distinct hardware encoding, so a leaked pseudo traps with
        // BRK #1 rather than silently becoming a NOP.
        AArch64Opcode::Brk
        | AArch64Opcode::TrapOverflow
        | AArch64Opcode::TrapBoundsCheck
        | AArch64Opcode::TrapNull
        | AArch64Opcode::TrapDivZero
        | AArch64Opcode::TrapShiftRange => {
            Ok(0xD4200020) // BRK #1
        }

        // Exact guard carriers must be consumed by proof opts or expanded by
        // lowering before final encoding. Reaching this boundary is a typed
        // pseudo error, not a panic or silent fallback.
        AArch64Opcode::TrapBoundsCheckExact
        | AArch64Opcode::TrapNullIfZero
        | AArch64Opcode::TrapDivZeroIfZero
        | AArch64Opcode::TrapShiftRangeIfOOB
        | AArch64Opcode::TrapOverflowExact => Err(EncodeError::PseudoInstruction(inst.opcode)),

        AArch64Opcode::Phi
        | AArch64Opcode::StackAlloc
        | AArch64Opcode::Copy
        | AArch64Opcode::Nop
        | AArch64Opcode::Retain
        | AArch64Opcode::Release => Ok(NOP),

        // Emission-time alignment padding: a REAL (non-pseudo) instruction
        // that encodes to the architectural NOP. Unlike the pseudo arm above
        // (a defensive fallback for instructions the callers skip), AlignNop
        // is deliberately encoded — it occupies one word of the final stream
        // so every offset derivation stays exact.
        AArch64Opcode::AlignNop => Ok(NOP),

        // =================================================================
        // Bitfield move instructions (ARM ARM C6.2)
        // =================================================================

        // UBFM Rd, Rn, #immr, #imms — unsigned bitfield move
        // sf | 10 | 100110 | N | immr(6) | imms(6) | Rn(5) | Rd(5)
        // Aliases: LSL/LSR (imm), UBFX, UXTB, UXTH
        // Operands: [Rd, Rn, Imm(immr), Imm(imms)]
        AArch64Opcode::Ubfm => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let immr = bitfield6_operand(inst, 2, sf)?;
            let imms = bitfield6_operand(inst, 3, sf)?;
            let n = sf; // N = sf for 64-bit, 0 for 32-bit
            Ok((sf << 31)
                | (0b10 << 29) // opc = 10 (UBFM)
                | (0b100110 << 23)
                | (n << 22)
                | (immr << 16)
                | (imms << 10)
                | (rn << 5)
                | rd)
        }

        // SBFM Rd, Rn, #immr, #imms — signed bitfield move
        // sf | 00 | 100110 | N | immr(6) | imms(6) | Rn(5) | Rd(5)
        // Aliases: ASR (imm), SBFX, SXTB, SXTH, SXTW
        // Operands: [Rd, Rn, Imm(immr), Imm(imms)]
        AArch64Opcode::Sbfm => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let immr = bitfield6_operand(inst, 2, sf)?;
            let imms = bitfield6_operand(inst, 3, sf)?;
            let n = sf;
            Ok((sf << 31) // opc = 00 (SBFM)
                | (0b100110 << 23)
                | (n << 22)
                | (immr << 16)
                | (imms << 10)
                | (rn << 5)
                | rd)
        }

        // BFM Rd, Rn, #immr, #imms — bitfield move (insert)
        // sf | 01 | 100110 | N | immr(6) | imms(6) | Rn(5) | Rd(5)
        // Aliases: BFI, BFXIL
        // Operands: [Rd, Rn, Imm(immr), Imm(imms)]
        AArch64Opcode::Bfm => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let immr = bitfield6_operand(inst, 2, sf)?;
            let imms = bitfield6_operand(inst, 3, sf)?;
            let n = sf;
            Ok((sf << 31)
                | (0b01 << 29) // opc = 01 (BFM)
                | (0b100110 << 23)
                | (n << 22)
                | (immr << 16)
                | (imms << 10)
                | (rn << 5)
                | rd)
        }

        // =================================================================
        // Load/Store register offset (ARM ARM C6.2)
        // =================================================================

        // LDR Rt, [Rn, Rm{, extend {#amount}}] — register offset load
        // size | 111 | V | 00 | opc | 1 | Rm(5) | option(3) | S(1) | 10 | Rn(5) | Rt(5)
        // Operands: [Rt, Rn, Rm] — default LSL, no shift (S=0)
        // Optional 4th operand: Imm(extend_option_and_shift) packed as (option<<1)|S
        AArch64Opcode::LdrRO => {
            let sf = sf_from_operand(inst, 0);
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            // Default: LSL extend (option=011), no shift (S=0)
            let (option, s) = if inst.operands.len() > 3 {
                let packed = imm_val(inst, 3) as u32;
                ((packed >> 1) & 0b111, packed & 1)
            } else {
                (0b011, 0)
            };
            if is_fpr(inst, 0) {
                // FP register-offset load: V=1
                let fp_sz = fp_size_from_inst(inst);
                let mem_size = match fp_sz {
                    FpSize::Half => encoding_mem::LoadStoreSize::Half, // 16-bit (H registers)
                    FpSize::Single => encoding_mem::LoadStoreSize::Word, // 32-bit (S registers)
                    FpSize::Double => encoding_mem::LoadStoreSize::Double, // 64-bit (D registers)
                };
                Ok(encoding_mem::encode_ldr_str_register(
                    mem_size,
                    true,
                    encoding_mem::LoadStoreOp::Load,
                    rm as u8,
                    match option {
                        0b010 => encoding_mem::RegExtend::Uxtw,
                        0b110 => encoding_mem::RegExtend::Sxtw,
                        0b111 => encoding_mem::RegExtend::Sxtx,
                        _ => encoding_mem::RegExtend::Lsl,
                    },
                    s != 0,
                    rn as u8,
                    rt as u8,
                )?)
            } else {
                // Integer register-offset load: V=0
                let size = if sf == 1 {
                    encoding_mem::LoadStoreSize::Double
                } else {
                    encoding_mem::LoadStoreSize::Word
                };
                Ok(encoding_mem::encode_ldr_str_register(
                    size,
                    false,
                    encoding_mem::LoadStoreOp::Load,
                    rm as u8,
                    match option {
                        0b010 => encoding_mem::RegExtend::Uxtw,
                        0b110 => encoding_mem::RegExtend::Sxtw,
                        0b111 => encoding_mem::RegExtend::Sxtx,
                        _ => encoding_mem::RegExtend::Lsl,
                    },
                    s != 0,
                    rn as u8,
                    rt as u8,
                )?)
            }
        }

        // LDRB/LDRH Wt, [Xn, Xm{, extend {#amount}}] — narrow register-offset
        // load, zero-extend into the 32-bit W transfer register. The access
        // WIDTH comes from the OPCODE (byte / halfword), NOT the transfer class
        // (which is always Gpr32 for these), so it is fixed here and never
        // derived from `sf`. V=0 (integer), opc=01 (load). The packed extend
        // 4th operand is `(option << 1) | S`, identical to `LdrRO`; for byte
        // accesses `S` is a no-op (log2(1)=0), for halfword `S=1` shifts by 1.
        AArch64Opcode::LdrbRO | AArch64Opcode::LdrhRO => {
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let (option, s) = if inst.operands.len() > 3 {
                let packed = imm_val(inst, 3) as u32;
                ((packed >> 1) & 0b111, packed & 1)
            } else {
                (0b011, 0)
            };
            let size = if inst.opcode == AArch64Opcode::LdrbRO {
                encoding_mem::LoadStoreSize::Byte
            } else {
                encoding_mem::LoadStoreSize::Half
            };
            Ok(encoding_mem::encode_ldr_str_register(
                size,
                false,
                encoding_mem::LoadStoreOp::Load,
                rm as u8,
                match option {
                    0b010 => encoding_mem::RegExtend::Uxtw,
                    0b110 => encoding_mem::RegExtend::Sxtw,
                    0b111 => encoding_mem::RegExtend::Sxtx,
                    _ => encoding_mem::RegExtend::Lsl,
                },
                s != 0,
                rn as u8,
                rt as u8,
            )?)
        }

        // STR Rt, [Rn, Rm{, extend {#amount}}] — register offset store
        // Same encoding format as LdrRO but with opc=00 (store)
        // Operands: [Rt, Rn, Rm] — default LSL, no shift (S=0)
        AArch64Opcode::StrRO => {
            let sf = sf_from_operand(inst, 0);
            let rt = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let (option, s) = if inst.operands.len() > 3 {
                let packed = imm_val(inst, 3) as u32;
                ((packed >> 1) & 0b111, packed & 1)
            } else {
                (0b011, 0)
            };
            if is_fpr(inst, 0) {
                let fp_sz = fp_size_from_inst(inst);
                let mem_size = match fp_sz {
                    FpSize::Half => encoding_mem::LoadStoreSize::Half, // 16-bit (H registers)
                    FpSize::Single => encoding_mem::LoadStoreSize::Word, // 32-bit (S registers)
                    FpSize::Double => encoding_mem::LoadStoreSize::Double, // 64-bit (D registers)
                };
                Ok(encoding_mem::encode_ldr_str_register(
                    mem_size,
                    true,
                    encoding_mem::LoadStoreOp::Store,
                    rm as u8,
                    match option {
                        0b010 => encoding_mem::RegExtend::Uxtw,
                        0b110 => encoding_mem::RegExtend::Sxtw,
                        0b111 => encoding_mem::RegExtend::Sxtx,
                        _ => encoding_mem::RegExtend::Lsl,
                    },
                    s != 0,
                    rn as u8,
                    rt as u8,
                )?)
            } else {
                let size = if sf == 1 {
                    encoding_mem::LoadStoreSize::Double
                } else {
                    encoding_mem::LoadStoreSize::Word
                };
                Ok(encoding_mem::encode_ldr_str_register(
                    size,
                    false,
                    encoding_mem::LoadStoreOp::Store,
                    rm as u8,
                    match option {
                        0b010 => encoding_mem::RegExtend::Uxtw,
                        0b110 => encoding_mem::RegExtend::Sxtw,
                        0b111 => encoding_mem::RegExtend::Sxtx,
                        _ => encoding_mem::RegExtend::Lsl,
                    },
                    s != 0,
                    rn as u8,
                    rt as u8,
                )?)
            }
        }

        // =================================================================
        // GOT and TLV loads
        // =================================================================

        // LdrGot — LDR Xd, [Xn, #offset] from GOT slot
        // Encoded as a standard 64-bit unsigned-offset load. The relocation
        // for the GOT page offset is handled by the relocation layer; the
        // encoder just emits: LDR Xd, [Xn, #imm12] (size=11, V=0, opc=01).
        // Operands: [Rd, Rn, Imm(scaled_offset)]
        AArch64Opcode::LdrGot => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let offset = if inst.operands.len() > 2 {
                imm_val(inst, 2)
            } else {
                0
            };
            // Reject misaligned / out-of-[0,4095] scaled offsets before mask.
            let scaled = got_tlv_scaled_imm12(inst, offset)?;
            // Always 64-bit load (GOT entries are pointer-sized)
            Ok(encoding::encode_load_store_ui(
                0b11, 0, 0b01, scaled, rn, rd,
            ))
        }

        // LdrTlvp — LDR Xd, [Xn, #offset] from TLV descriptor
        // Same encoding as LdrGot: standard 64-bit unsigned-offset load.
        // The TLV page offset relocation is handled separately.
        // Operands: [Rd, Rn, Imm(scaled_offset)]
        AArch64Opcode::LdrTlvp => {
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let offset = if inst.operands.len() > 2 {
                imm_val(inst, 2)
            } else {
                0
            };
            // Reject misaligned / out-of-[0,4095] scaled offsets before mask.
            let scaled = got_tlv_scaled_imm12(inst, offset)?;
            // Always 64-bit load (TLV descriptors are pointer-sized)
            Ok(encoding::encode_load_store_ui(
                0b11, 0, 0b01, scaled, rn, rd,
            ))
        }

        // LdrGottprel — ELF initial-exec GOT-TPREL load. It always carries a
        // Symbol operand and is only encodable through the module emitter's
        // fixup interception (which emits the imm12-placeholder LDR skeleton
        // + `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC`). Reaching the unified
        // encoder means the fixup path was bypassed — fail closed rather
        // than encode a wrong immediate (exactly like AddTprelHi12/Lo12).
        // The initial-exec model is also not JIT-compatible
        // (`TlsModel::InitialExec.is_jit_compatible() == false`), so no
        // resolved-immediate JIT form exists.
        AArch64Opcode::LdrGottprel => Err(EncodeError::UnsupportedOpcode(inst.opcode)),

        // =================================================================
        // Logical immediate (ARM ARM C4.1.4 — Logical (immediate))
        // sf | opc(2) | 100100 | N | immr(6) | imms(6) | Rn(5) | Rd(5)
        // AND=00, ORR=01, EOR=10
        // Operands: [Rd, Rn, Imm(mask)] or [Rd, Rn, Imm(N), Imm(immr), Imm(imms)]
        // =================================================================
        AArch64Opcode::AndRI => encode_logical_immediate(inst, 0b00),

        AArch64Opcode::OrrRI => encode_logical_immediate(inst, 0b01),

        AArch64Opcode::EorRI => encode_logical_immediate(inst, 0b10),

        // =================================================================
        // BIC — Bitwise AND-NOT (bit clear)
        // Logical shifted register: opc=00, N=1
        // =================================================================
        AArch64Opcode::BicRR => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_logical_shifted_reg(
                sf,
                0b00,
                0,
                1,
                preg_hw(inst, 2)?,
                0,
                preg_hw(inst, 1)?,
                preg_hw(inst, 0)?,
            ))
        }

        // =================================================================
        // Conditional select variants (ARM ARM C6.2)
        // =================================================================

        // CSINC Xd, Xn, Xm, cond — conditional select increment
        // ARM ARM: sf | 0 | 0 | 11010100 | Rm | cond | 0 | 1 | Rn | Rd
        // Operands: [Rd, Rn, Rm, Imm(cond)]
        AArch64Opcode::Csinc => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let cond = imm_val(inst, 3) as u32 & 0xF;
            Ok((sf << 31)
                | (0b11010100 << 21)
                | (rm << 16)
                | (cond << 12)
                | (0b01 << 10) // op2 = 01 (CSINC)
                | (rn << 5)
                | rd)
        }

        // CSINV Xd, Xn, Xm, cond — conditional select invert
        // ARM ARM: sf | 1 | 0 | 11010100 | Rm | cond | 0 | 0 | Rn | Rd
        // Operands: [Rd, Rn, Rm, Imm(cond)]
        AArch64Opcode::Csinv => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let cond = imm_val(inst, 3) as u32 & 0xF;
            Ok(((sf << 31)
                | (0b10 << 29) // op = 1, S = 0
                | (0b11010100 << 21)
                | (rm << 16)
                | (cond << 12)) // op2 = 00 (CSINV)
                | (rn << 5)
                | rd)
        }

        // CSNEG Xd, Xn, Xm, cond — conditional select negate
        // ARM ARM: sf | 1 | 0 | 11010100 | Rm | cond | 0 | 1 | Rn | Rd
        // Operands: [Rd, Rn, Rm, Imm(cond)]
        AArch64Opcode::Csneg => {
            let sf = sf_from_operand(inst, 0);
            let rd = preg_hw(inst, 0)?;
            let rn = preg_hw(inst, 1)?;
            let rm = preg_hw(inst, 2)?;
            let cond = imm_val(inst, 3) as u32 & 0xF;
            Ok((sf << 31)
                | (0b10 << 29) // op = 1, S = 0
                | (0b11010100 << 21)
                | (rm << 16)
                | (cond << 12)
                | (0b01 << 10) // op2 = 01 (CSNEG)
                | (rn << 5)
                | rd)
        }

        // =================================================================
        // MOVN — Move Wide with NOT
        // ARM ARM: sf | 00 | 100101 | hw | imm16 | Rd
        // opc = 00 for MOVN
        // Operands: [Rd, Imm(imm16)] or [Rd, Imm(imm16), Imm(hw_shift)]
        // =================================================================
        AArch64Opcode::Movn => {
            require_move_wide_arity(inst, 2, 3)?;
            require_move_wide_destination(inst)?;
            let sf = sf_from_operand(inst, 0);
            // imm16: reject a wide constant leaked here BEFORE the 16-bit mask
            // (the canonical MovI/Movz arm rejects via MovImmTooWide; mirror it).
            let imm16 = imm16_operand(inst, 1)?;
            // An explicit shift operand is accepted for canonical-form
            // compatibility only when it denotes hw0. Validate its full
            // architectural shape first, then enforce the narrower v0.1 policy.
            let hw = if inst.operands.len() > 2 {
                move_wide_hw(inst, 2)?
            } else {
                0
            };
            if hw != 0 {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 2,
                    desc: "nonzero-shift MOVN is not emittable under the v0.1 shift-zero MOVN policy; \
                           seed at hw0 and repair higher halfwords with MOVK"
                        .to_string(),
                });
            }
            Ok(encoding::encode_move_wide(
                sf,
                0b00,
                hw,
                imm16,
                preg_hw(inst, 0)?,
            ))
        }

        // =================================================================
        // FMOV immediate — move FP immediate to FPR
        // ARM ARM C7.2.132: 0 | 0 | 0 | 11110 | ftype(2) | 1 | imm8 | 100 | 00000 | Rd
        // ftype: 00=single(S), 01=double(D), 11=half(H)
        // Operands: [PReg(Rd), FImm(value)]
        // =================================================================
        AArch64Opcode::FmovImm => {
            let rd = preg_hw(inst, 0)?;
            let fp_size = fp_size_from_inst(inst);
            let ftype = match fp_size {
                FpSize::Single => 0b00u32,
                FpSize::Double => 0b01u32,
                FpSize::Half => 0b11u32,
            };
            // Extract the FImm value and encode as 8-bit immediate
            let imm8 = match inst.operands.get(1) {
                Some(MachOperand::FImm(v)) => encode_fmov_imm8(*v),
                Some(MachOperand::Imm(v)) => (*v as u32) & 0xFF,
                _ => 0,
            };
            Ok(
                ((0b00011110u32 << 24) | (ftype << 22) | (1 << 21) | (imm8 << 13) | (0b100 << 10))
                    | rd,
            )
        }

        // =================================================================
        // LLVM-style typed aliases — delegate to generic encoders
        // =================================================================

        // MOVWrr → MOV Wd, Wn (32-bit); MOVXrr → MOV Xd, Xn (64-bit)
        AArch64Opcode::MOVWrr | AArch64Opcode::MOVXrr => {
            require_gpr_move_operands(inst, 2)?;
            // The typed opcode, not the allocated register view, owns the
            // architectural width. Regalloc deliberately preserves MOVWrr
            // over Gpr64 vregs as a 32-bit truncation idiom.
            let sf = match inst.opcode {
                AArch64Opcode::MOVWrr => 0,
                AArch64Opcode::MOVXrr => 1,
                _ => unreachable!(),
            };
            let is_sp_source = matches!(
                inst.operands.get(1),
                Some(MachOperand::Special(SpecialReg::SP))
            );
            if is_sp_source {
                Ok(encoding::encode_add_sub_imm(
                    sf,
                    0,
                    0,
                    0,
                    0,
                    31,
                    preg_hw(inst, 0)?,
                ))
            } else {
                Ok(encoding::encode_logical_shifted_reg(
                    sf,
                    0b01,
                    0,
                    0,
                    preg_hw(inst, 1)?,
                    0,
                    31,
                    preg_hw(inst, 0)?,
                ))
            }
        }

        // STR typed aliases — delegate to StrRI encoding
        AArch64Opcode::STRWui => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            encode_load_store_auto(0b10, 0, 0b00, 4, offset, rn, rt)
        }

        AArch64Opcode::STRXui => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            encode_load_store_auto(0b11, 0, 0b00, 8, offset, rn, rt)
        }

        AArch64Opcode::STRSui => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            encode_load_store_auto(0b10, 1, 0b00, 4, offset, rn, rt)
        }

        AArch64Opcode::STRDui => {
            let rt = preg_hw(inst, 0)?;
            let (rn, offset) = extract_base_offset(inst, 1, 2)?;
            encode_load_store_auto(0b11, 1, 0b00, 8, offset, rn, rt)
        }

        // BL (LLVM alias) → Bl encoding — imm26 signed word offset,
        // range-checked before mask.
        AArch64Opcode::BL => {
            let offset = branch_offset_signed(inst, 0, 26)?;
            Ok(encoding::encode_uncond_branch(1, offset))
        }

        // BLR (LLVM alias) → Blr encoding
        AArch64Opcode::BLR => Ok(encoding::encode_branch_reg(0b0001, preg_hw(inst, 0)?)),

        // CMP register aliases
        AArch64Opcode::CMPWrr | AArch64Opcode::CMPXrr => {
            let sf = sf_from_operand(inst, 0);
            Ok(encoding::encode_add_sub_shifted_reg(
                sf,
                1,
                1,
                0,
                preg_hw(inst, 1)?,
                0,
                preg_hw(inst, 0)?,
                31,
            ))
        }

        // CMP immediate aliases
        AArch64Opcode::CMPWri | AArch64Opcode::CMPXri => {
            let sf = sf_from_operand(inst, 0);
            let imm = imm12_operand(inst, 1)?;
            Ok(encoding::encode_add_sub_imm(
                sf,
                1,
                1,
                0,
                imm,
                preg_hw(inst, 0)?,
                31,
            ))
        }

        // MOVZ typed aliases — imm16 rejected before mask (the canonical
        // MovI/Movz arm rejects via MovImmTooWide; these aliases bypassed it).
        AArch64Opcode::MOVZWi | AArch64Opcode::MOVZXi => {
            require_move_wide_arity(inst, 2, 2)?;
            require_move_wide_destination(inst)?;
            let expected = if inst.opcode == AArch64Opcode::MOVZWi {
                RegClass::Gpr32
            } else {
                RegClass::Gpr64
            };
            require_move_wide_destination_width(inst, expected)?;
            let sf = sf_from_operand(inst, 0);
            let imm16 = imm16_operand(inst, 1)?;
            Ok(encoding::encode_move_wide(
                sf,
                0b10,
                0,
                imm16,
                preg_hw(inst, 0)?,
            ))
        }

        // Bcc (LLVM alias) → BCond encoding — imm19 signed word offset,
        // range-checked before mask.
        AArch64Opcode::Bcc => {
            let cond = imm_val(inst, 0) as u32 & 0xF;
            let offset = if inst.operands.len() > 1 {
                branch_offset_signed(inst, 1, 19)?
            } else {
                0
            };
            Ok(encoding::encode_cond_branch(offset, cond))
        }
    }
}

// ---------------------------------------------------------------------------
// FMOV immediate encoding helper
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Atomic encoding helpers
// ---------------------------------------------------------------------------

/// Encode LDAR (load-acquire): size(2) 001000 010 11111 1 11111 Rn(5) Rt(5).
///
/// ARM ARM C6.2.117: LDAR encoding uses the load-acquire ordered access format.
fn encode_load_acquire(size: u32, rn: u32, rt: u32) -> u32 {
    // size(2) 001000 1 1 0 11111 1 11111 Rn(5) Rt(5)
    ((size << 30)
        | (0b001000 << 24)
        | (1 << 23) // o2 = 1 (ordered)
        | (1 << 22)) // o1 = 0
        | (0b11111 << 16) // Rs = 11111 (not used)
        | (1 << 15) // o0 = 1
        | (0b11111 << 10) // Rt2 = 11111 (not used)
        | (rn << 5)
        | rt
}

/// Encode STLR (store-release): size(2) 001000 100 11111 1 11111 Rn(5) Rt(5).
///
/// ARM ARM C6.2.260: STLR encoding uses the store-release ordered access format.
fn encode_store_release(size: u32, rn: u32, rt: u32) -> u32 {
    // size(2) 001000 1 0 0 11111 1 11111 Rn(5) Rt(5)
    ((size << 30)
        | (0b001000 << 24)
        | (1 << 23)) // o1 = 0
        | (0b11111 << 16) // Rs = 11111 (not used)
        | (1 << 15) // o0 = 1
        | (0b11111 << 10) // Rt2 = 11111 (not used)
        | (rn << 5)
        | rt
}

/// Encode LSE atomic RMW instruction (ARMv8.1-a).
///
/// Format: size(2) 111 0 00 A R 1 Rs(5) o3(1) opc(3) 00 Rn(5) Rt(5)
///
/// - o3=0, opc=000: LDADD
/// - o3=0, opc=001: LDCLR
/// - o3=0, opc=010: LDEOR
/// - o3=0, opc=011: LDSET
/// - o3=0, opc=100: LDSMAX
/// - o3=0, opc=101: LDSMIN
/// - o3=0, opc=110: LDUMAX
/// - o3=0, opc=111: LDUMIN
/// - o3=1, opc=000: SWP
///
/// Operands: [Rs (operand), Rt (old value dest), Rn (address)]
fn encode_lse_atomic(
    inst: &MachInst,
    o3: u32,
    opc: u32,
    a: u32,
    r: u32,
) -> Result<u32, EncodeError> {
    // A 4th operand is an explicit access-size immediate for narrow (byte/half)
    // atomics (0=byte, 1=half); i8/i16/i32 all use W registers, so the register
    // class alone cannot distinguish byte/half/word. Without it, derive the size
    // from Rt's register width (W -> word, X -> dword) as before.
    let size = if inst.operands.len() > 3 {
        match imm_val(inst, 3) {
            0 => 0b00, // byte
            1 => 0b01, // half
            other => {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 3,
                    desc: format!(
                        "LSE atomic access-size immediate must be 0 (byte) or 1 (half), got {other}"
                    ),
                });
            }
        }
    } else {
        let sf = sf_from_operand(inst, 1); // size from Rt (result)
        if sf == 1 { 0b11 } else { 0b10 }
    };
    let rs = preg_hw(inst, 0)?;
    let rt = preg_hw(inst, 1)?;
    let rn = preg_hw(inst, 2)?;

    Ok((((size << 30) | (0b111 << 27))
        | (a << 23)
        | (r << 22)
        | (1 << 21)
        | (rs << 16)
        | (o3 << 15)
        | (opc << 12))
        | (rn << 5)
        | rt)
}

/// Encode CAS (compare and swap, ARMv8.1-a LSE).
///
/// Format: size(2) 001000 1 A 1 Rs(5) o0 11111 Rn(5) Rt(5)
/// where o0 = R (release bit).
///
/// Operands: [Rs (expected/result), Rt (desired), Rn (address)]
fn encode_cas(inst: &MachInst, a: u32, r: u32) -> Result<u32, EncodeError> {
    // A 4th operand is an explicit access-size immediate for narrow (byte/half)
    // CAS (0=byte, 1=half); otherwise derive from Rs's register width.
    let size = if inst.operands.len() > 3 {
        match imm_val(inst, 3) {
            0 => 0b00, // byte
            1 => 0b01, // half
            other => {
                return Err(EncodeError::InvalidOperand {
                    opcode: inst.opcode,
                    index: 3,
                    desc: format!(
                        "CAS access-size immediate must be 0 (byte) or 1 (half), got {other}"
                    ),
                });
            }
        }
    } else {
        let sf = sf_from_operand(inst, 0); // size from Rs
        if sf == 1 { 0b11 } else { 0b10 }
    };
    let rs = preg_hw(inst, 0)?;
    let rt = preg_hw(inst, 1)?;
    let rn = preg_hw(inst, 2)?;

    Ok((size << 30)
        | (0b001000 << 24)
        | (1 << 23)  // o2 = 1
        | (a << 22)  // A
        | (1 << 21)  // o1 = 1
        | (rs << 16)
        | (r << 15)  // o0 = R
        | (0b11111 << 10) // Rt2 = 11111 (unused)
        | (rn << 5)
        | rt)
}

/// Encode an f64 value into the 8-bit FMOV immediate format.
///
/// ARM ARM C5.6.5: The 8-bit immediate `abcdefgh` encodes:
///   value = (-1)^a * 2^(NOT(b).ccc - 3) * 1.defgh
///
/// where the mantissa `1.defgh` uses 4 fraction bits.
///
/// Only a small subset of FP values are representable. If the value is not
/// exactly representable, returns 0 (which encodes +2.0).
fn encode_fmov_imm8(value: f64) -> u32 {
    let bits = value.to_bits();

    // Extract sign, exponent, mantissa from f64
    let sign = ((bits >> 63) & 1) as u32;
    let exp = ((bits >> 52) & 0x7FF) as i32;
    let frac = bits & 0x000F_FFFF_FFFF_FFFF;

    // Only the top 4 bits of the mantissa can be non-zero
    if frac & 0x0000_FFFF_FFFF_FFFF != 0 {
        return 0;
    }

    let top4 = ((frac >> 48) & 0xF) as u32;

    // Exponent must be in range: biased [1020, 1027] for f64 (bias=1023)
    // This maps to unbiased [-3, +4]
    if !(1020..=1027).contains(&exp) {
        return 0;
    }

    // The 3-bit exponent encoding: biased_3 = exp - 1020, range [0, 7]
    let biased_3 = (exp - 1020) as u32;
    // bit 6 = NOT(biased_3[2]), bits 5:4 = biased_3[1:0]
    let not_b = ((biased_3 >> 2) ^ 1) & 1;

    (sign << 7) | (not_b << 6) | ((biased_3 & 0b11) << 4) | top4
}

// ---------------------------------------------------------------------------
// FP size helpers
// ---------------------------------------------------------------------------

/// Determine FP precision from a register operand's class.
fn fp_size_from_preg_class(class: RegClass) -> FpSize {
    match class {
        RegClass::Fpr32 => FpSize::Single,
        RegClass::Fpr64 => FpSize::Double,
        RegClass::Fpr16 => FpSize::Half,
        // Fpr128, Fpr8, or GPR/System: default to Double
        _ => FpSize::Double,
    }
}

/// Determine FP precision from the destination register for FP arithmetic.
/// Uses register class: Fpr32 (S registers) → Single, Fpr64 (D registers) → Double.
/// Defaults to Double if register class is ambiguous (e.g., V/Q registers).
fn fp_size_from_inst(inst: &MachInst) -> FpSize {
    match inst.operands.first() {
        Some(MachOperand::PReg(p)) => fp_size_from_preg_class(preg_class(*p)),
        _ => FpSize::Double,
    }
}

fn fp_mem_fields_from_preg_class(class: RegClass, base_opc: u32) -> Option<(u32, i64, u32)> {
    match class {
        RegClass::Fpr128 => Some((0b00, 16, base_opc | 0b10)),
        RegClass::Fpr64 => Some((0b11, 8, base_opc)),
        RegClass::Fpr32 => Some((0b10, 4, base_opc)),
        RegClass::Fpr16 => Some((0b01, 2, base_opc)),
        _ => None,
    }
}

fn fp_mem_fields_from_inst(
    inst: &MachInst,
    operand_idx: usize,
    base_opc: u32,
) -> Result<(u32, i64, u32), EncodeError> {
    match inst.operands.get(operand_idx) {
        Some(MachOperand::PReg(p)) => fp_mem_fields_from_preg_class(preg_class(*p), base_opc)
            .ok_or_else(|| EncodeError::InvalidOperand {
                opcode: inst.opcode,
                index: operand_idx,
                desc: format!(
                    "expected FP memory register class, got {:?}",
                    preg_class(*p)
                ),
            }),
        Some(other) => Err(EncodeError::InvalidOperand {
            opcode: inst.opcode,
            index: operand_idx,
            desc: format!("expected FP memory register, got {:?}", other),
        }),
        None => Err(EncodeError::MissingOperand {
            opcode: inst.opcode,
            index: operand_idx,
            expected: operand_idx + 1,
        }),
    }
}

/// FP size for compare instructions (uses first source operand).
fn fp_size_from_cmp_inst(inst: &MachInst) -> FpSize {
    match inst.operands.first() {
        Some(MachOperand::PReg(p)) => fp_size_from_preg_class(preg_class(*p)),
        _ => FpSize::Double,
    }
}

/// FP size derived from a specific source operand index.
fn fp_size_from_source(inst: &MachInst, idx: usize) -> FpSize {
    match inst.operands.get(idx) {
        Some(MachOperand::PReg(p)) => fp_size_from_preg_class(preg_class(*p)),
        _ => FpSize::Double,
    }
}

// ---------------------------------------------------------------------------
// NEON helpers
// ---------------------------------------------------------------------------

/// Arrangement encoding convention for NEON instructions:
///
/// The last `Imm` operand of three-register NEON instructions encodes
/// the vector arrangement as a small integer:
///   0 = 8B, 1 = 16B, 2 = 4H, 3 = 8H, 4 = 2S, 5 = 4S, 6 = 2D
///
/// For instructions with only register operands (logic/NOT), the arrangement
/// is inferred from the register class (V registers = Q=1, default 128-bit).
fn neon_arrangement(inst: &MachInst) -> encoding_neon::VectorArrangement {
    // Check last operand for arrangement encoding
    let arr_idx = inst.operands.len().saturating_sub(1);
    let arr_val = imm_val(inst, arr_idx) as u32;
    match arr_val {
        0 => encoding_neon::VectorArrangement::B8,
        1 => encoding_neon::VectorArrangement::B16,
        2 => encoding_neon::VectorArrangement::H4,
        3 => encoding_neon::VectorArrangement::H8,
        4 => encoding_neon::VectorArrangement::S2,
        5 => encoding_neon::VectorArrangement::S4,
        6 => encoding_neon::VectorArrangement::D2,
        _ => encoding_neon::VectorArrangement::S4, // default: 4S
    }
}

/// FP arrangement for NEON FP instructions.
///
/// Convention: last Imm operand encodes arrangement:
///   0 = 2S, 1 = 4S, 2 = 2D
fn neon_fp_arrangement(inst: &MachInst) -> encoding_neon::FpVectorArrangement {
    let arr_idx = inst.operands.len().saturating_sub(1);
    let arr_val = imm_val(inst, arr_idx) as u32;
    match arr_val {
        0 => encoding_neon::FpVectorArrangement::S2,
        1 => encoding_neon::FpVectorArrangement::S4,
        2 => encoding_neon::FpVectorArrangement::D2,
        _ => encoding_neon::FpVectorArrangement::S4, // default: 4S
    }
}

/// Extract the Q bit for NEON logic/move instructions.
///
/// For logic instructions that don't carry arrangement in their operands,
/// infer from the register class: V registers (Fpr128) = Q=1 (128-bit).
fn neon_q_bit(inst: &MachInst) -> u32 {
    // Check if last operand is an Imm encoding Q directly
    let last_idx = inst.operands.len().saturating_sub(1);
    match inst.operands.get(last_idx) {
        Some(MachOperand::Imm(v)) => {
            // For logic: 0 = 8B(Q=0), 1 = 16B(Q=1)
            if *v == 0 { 0 } else { 1 }
        }
        _ => {
            // Infer from register class: V registers are 128-bit (Q=1)
            match inst.operands.first() {
                Some(MachOperand::PReg(p)) => {
                    if preg_class(*p) == RegClass::Fpr128 {
                        1
                    } else {
                        0
                    }
                }
                _ => 1, // default to Q=1 (128-bit)
            }
        }
    }
}

/// Extract element size from an Imm operand at `idx`.
///
/// Convention: 1=B, 2=H, 4=S, 8=D
fn neon_element_size(inst: &MachInst, idx: usize) -> encoding_neon::ElementSize {
    let val = imm_val(inst, idx) as u32;
    match val {
        1 => encoding_neon::ElementSize::B,
        2 => encoding_neon::ElementSize::H,
        4 => encoding_neon::ElementSize::S,
        8 => encoding_neon::ElementSize::D,
        _ => encoding_neon::ElementSize::S, // default: 32-bit
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{
        D0, D1, D2, D3, D4, D5, D8, D9, H0, H1, PReg, S0, S1, S2, S3, S4, S5, SP, SpecialReg, V0,
        V1, V2, V3, V4, V5, V6, V7, V9, V11, V17, V20, V29, V30, V31, W0, W1, W2, W3, W4, W5, W6,
        W8, W9, W10, W11, X0, X1, X2, X3, X4, X5, X9, X10, X11, X29, X30, XZR,
    };

    /// Helper to build a MachInst with given opcode and operands.
    fn mk(opcode: AArch64Opcode, ops: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, ops)
    }

    fn preg(r: PReg) -> MachOperand {
        MachOperand::PReg(r)
    }

    fn imm(v: i64) -> MachOperand {
        MachOperand::Imm(v)
    }

    fn sp() -> MachOperand {
        MachOperand::Special(SpecialReg::SP)
    }

    fn xzr() -> MachOperand {
        MachOperand::Special(SpecialReg::XZR)
    }

    // --- Verify unified encoder produces same output as direct encoding calls ---

    #[test]
    fn test_add_rr() {
        // ADD X0, X1, X2
        let inst = mk(AArch64Opcode::AddRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(1, 0, 0, 0, 2, 0, 1, 0);
        assert_eq!(
            enc, direct,
            "ADD X0, X1, X2: unified={enc:#010X}, direct={direct:#010X}"
        );
    }

    /// EOR with ROR-shifted second source (`EorRRShift`) — the rotate-fusion
    /// peephole's shifted-register EOR. Every expected word is ground-truthed
    /// against Apple `clang -c` + `otool -tvj` of `eor <Rd>, <Rn>, <Rm>, ror #k`.
    /// Operands: [Rd, Rn (un-shifted), Rm (rotated source), Imm(amount)].
    #[test]
    fn test_eor_ror_shifted_register_encodings() {
        // W (32-bit) forms.
        for (rd, rn, rm, k, expected) in [
            (W4, W4, W2, 25i64, 0x4AC2_6484u32), // eor w4, w4, w2, ror #25
            (W0, W1, W2, 7, 0x4AC2_1C20),        // eor w0, w1, w2, ror #7
            (W3, W5, W6, 1, 0x4AC6_04A3),        // eor w3, w5, w6, ror #1
            (W8, W0, W1, 31, 0x4AC1_7C08),       // eor w8, w0, w1, ror #31
        ] {
            let inst = mk(
                AArch64Opcode::EorRRShift,
                vec![preg(rd), preg(rn), preg(rm), imm(k)],
            );
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected, "eor W ror #{k}: got {enc:#010X}");
        }
        // X (64-bit) forms.
        for (rd, rn, rm, k, expected) in [
            (X0, X1, X2, 40i64, 0xCAC2_A020u32), // eor x0, x1, x2, ror #40
            (X9, X3, X2, 63, 0xCAC2_FC69),       // eor x9, x3, x2, ror #63
            (X0, X0, X1, 1, 0xCAC1_0400),        // eor x0, x0, x1, ror #1
            (X3, X2, X9, 17, 0xCAC9_4443),       // eor x3, x2, x9, ror #17
        ] {
            let inst = mk(
                AArch64Opcode::EorRRShift,
                vec![preg(rd), preg(rn), preg(rm), imm(k)],
            );
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected, "eor X ror #{k}: got {enc:#010X}");
        }
    }

    /// EOR with an LSL/LSR-shifted second source (`EorRRLsl` / `EorRRLsr`) — the
    /// xorshift fusion forms. Every expected word is ground-truthed against
    /// `gcc -c` + `objdump -d` of `eor <Rd>, <Rn>, <Rm>, {lsl|lsr} #k` on this
    /// host. Operands: [Rd, Rn (un-shifted), Rm (shifted source), Imm(k)].
    #[test]
    fn test_eor_lsl_lsr_shifted_register_encodings() {
        for (op, rd, rn, rm, k, expected) in [
            // eor x0, x1, x2, lsl #13
            (AArch64Opcode::EorRRLsl, X0, X1, X2, 13i64, 0xCA02_3420u32),
            // eor x9, x9, x9, lsl #13   (the p1_xorshift step-1 shape)
            (AArch64Opcode::EorRRLsl, X9, X9, X9, 13, 0xCA09_3529),
            // eor x9, x9, x9, lsr #7    (the p1_xorshift step-2 shape)
            (AArch64Opcode::EorRRLsr, X9, X9, X9, 7, 0xCA49_1D29),
            // eor w0, w1, w2, lsl #3
            (AArch64Opcode::EorRRLsl, W0, W1, W2, 3, 0x4A02_0C20),
            // eor w0, w1, w2, lsr #31
            (AArch64Opcode::EorRRLsr, W0, W1, W2, 31, 0x4A42_7C20),
        ] {
            let inst = mk(op, vec![preg(rd), preg(rn), preg(rm), imm(k)]);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected, "{op:?} #{k}: got {enc:#010X}");
        }
    }

    /// The LSL and LSR forms must NOT encode identically — the 2-bit `shift`
    /// field is the only thing distinguishing them, and getting it wrong is a
    /// silent wrong-value miscompile rather than a crash.
    #[test]
    fn test_eor_lsl_and_lsr_differ_in_shift_field() {
        let ops = [AArch64Opcode::EorRRLsl, AArch64Opcode::EorRRLsr];
        let encs: Vec<u32> = ops
            .iter()
            .map(|op| {
                let inst = mk(*op, vec![preg(X0), preg(X1), preg(X2), imm(13)]);
                encode_instruction(&inst).unwrap()
            })
            .collect();
        assert_ne!(
            encs[0], encs[1],
            "EOR LSL and LSR encoded identically ({:#010X}) — shift field lost",
            encs[0]
        );
        // shift field is bits 23:22; LSL=0b00, LSR=0b01.
        assert_eq!((encs[0] >> 22) & 0b11, 0b00, "LSL shift field");
        assert_eq!((encs[1] >> 22) & 0b11, 0b01, "LSR shift field");
    }

    /// `EorRRLsl`/`EorRRLsr` fail closed on an out-of-range amount (0 or >= width).
    #[test]
    fn test_eor_lsl_lsr_reject_out_of_range() {
        for op in [AArch64Opcode::EorRRLsl, AArch64Opcode::EorRRLsr] {
            // 0 would be a plain EOR — never emitted to this form.
            let zero = mk(op, vec![preg(X0), preg(X1), preg(X2), imm(0)]);
            assert!(encode_instruction(&zero).is_err(), "{op:?} amount 0");
            // >= width is unencodable in imm6 for the W form.
            let wide = mk(op, vec![preg(W0), preg(W1), preg(W2), imm(32)]);
            assert!(encode_instruction(&wide).is_err(), "{op:?} W amount 32");
            let too_big = mk(op, vec![preg(X0), preg(X1), preg(X2), imm(64)]);
            assert!(encode_instruction(&too_big).is_err(), "{op:?} X amount 64");
        }
    }

    /// `EorRRShift` fails closed on an out-of-range rotate amount (0 or >= width).
    #[test]
    fn test_eor_ror_shifted_register_rejects_out_of_range() {
        // amount 0 (would be a plain EOR — never emitted to this form).
        let inst = mk(
            AArch64Opcode::EorRRShift,
            vec![preg(W0), preg(W1), preg(W2), imm(0)],
        );
        assert!(
            encode_instruction(&inst).is_err(),
            "ror #0 must fail-closed"
        );
        // amount == width (32 for W) is out of range.
        let inst = mk(
            AArch64Opcode::EorRRShift,
            vec![preg(W0), preg(W1), preg(W2), imm(32)],
        );
        assert!(
            encode_instruction(&inst).is_err(),
            "W ror #32 must fail-closed"
        );
        // amount == 64 for X is out of range.
        let inst = mk(
            AArch64Opcode::EorRRShift,
            vec![preg(X0), preg(X1), preg(X2), imm(64)],
        );
        assert!(
            encode_instruction(&inst).is_err(),
            "X ror #64 must fail-closed"
        );
    }

    /// ADD/SUB with an LSL-shifted second source (`AddRRShift` / `SubRRShift`) —
    /// the shift-add/sub fusion peephole's shifted-register ADD/SUB. Every
    /// expected word is ground-truthed against Apple `clang -c` + `otool -tvj` of
    /// `add/sub <Rd>, <Rn>, <Rm>, lsl #k`. Operands: [Rd, Rn (un-shifted base/
    /// minuend), Rm (shifted source/subtrahend), Imm(k)].
    #[test]
    fn test_add_sub_lsl_shifted_register_encodings() {
        // ADD — W (32-bit) and X (64-bit) forms.
        for (rd, rn, rm, k, expected) in [
            (X0, X1, X2, 1i64, 0x8B02_0420u32), // add x0, x1, x2, lsl #1
            (X0, X1, X2, 3, 0x8B02_0C20),       // add x0, x1, x2, lsl #3
            (X9, X3, X2, 63, 0x8B02_FC69),      // add x9, x3, x2, lsl #63
            (W0, W1, W2, 3, 0x0B02_0C20),       // add w0, w1, w2, lsl #3
            (W3, W5, W6, 1, 0x0B06_04A3),       // add w3, w5, w6, lsl #1
            (W8, W0, W1, 31, 0x0B01_7C08),      // add w8, w0, w1, lsl #31
        ] {
            let inst = mk(
                AArch64Opcode::AddRRShift,
                vec![preg(rd), preg(rn), preg(rm), imm(k)],
            );
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected, "add lsl #{k}: got {enc:#010X}");
        }
        // SUB — W (32-bit) and X (64-bit) forms.
        for (rd, rn, rm, k, expected) in [
            (X0, X1, X2, 1i64, 0xCB02_0420u32), // sub x0, x1, x2, lsl #1
            (X0, X1, X2, 3, 0xCB02_0C20),       // sub x0, x1, x2, lsl #3
            (X9, X3, X2, 63, 0xCB02_FC69),      // sub x9, x3, x2, lsl #63
            (W0, W1, W2, 3, 0x4B02_0C20),       // sub w0, w1, w2, lsl #3
            (W8, W0, W1, 31, 0x4B01_7C08),      // sub w8, w0, w1, lsl #31
        ] {
            let inst = mk(
                AArch64Opcode::SubRRShift,
                vec![preg(rd), preg(rn), preg(rm), imm(k)],
            );
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected, "sub lsl #{k}: got {enc:#010X}");
        }
    }

    /// ADD with an LSR-shifted second source (`AddRRShiftLsr`) — the shift-ALU
    /// fusion peephole's LSR sibling of `AddRRShift` (the srem/sdiv magic
    /// sign-bit correction `add r, r, x, lsr #31` and the udiv magic add-back
    /// `add r, mh, sub, lsr #1`). Every expected word is ground-truthed against
    /// Apple `clang -c` + `objdump -d` of `add <Rd>, <Rn>, <Rm>, lsr #k`.
    /// Operands: [Rd, Rn (un-shifted base), Rm (shifted source), Imm(k)].
    #[test]
    fn test_add_lsr_shifted_register_encodings() {
        for (rd, rn, rm, k, expected) in [
            (X0, X1, X2, 1i64, 0x8B42_0420u32), // add x0, x1, x2, lsr #1
            (X3, X4, X5, 63, 0x8B45_FC83),      // add x3, x4, x5, lsr #63
            (X9, X10, X11, 40, 0x8B4B_A149),    // add x9, x10, x11, lsr #40
            (W0, W1, W2, 3, 0x0B42_0C20),       // add w0, w1, w2, lsr #3
            (W3, W4, W5, 31, 0x0B45_7C83),      // add w3, w4, w5, lsr #31
            (W9, W10, W11, 16, 0x0B4B_4149),    // add w9, w10, w11, lsr #16
        ] {
            let inst = mk(
                AArch64Opcode::AddRRShiftLsr,
                vec![preg(rd), preg(rn), preg(rm), imm(k)],
            );
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected, "add lsr #{k}: got {enc:#010X}");
        }
    }

    /// `AddRRShift`/`SubRRShift`/`AddRRShiftLsr` fail closed on an out-of-range
    /// shift amount (0 or >= width). Critically, for the W (32-bit) form imm6
    /// bit 5 must be 0, so `k` in `32..=63` is UNDEFINED and MUST be rejected.
    #[test]
    fn test_add_sub_lsl_shifted_register_rejects_out_of_range() {
        for op in [
            AArch64Opcode::AddRRShift,
            AArch64Opcode::SubRRShift,
            AArch64Opcode::AddRRShiftLsr,
        ] {
            // amount 0 (would be a plain ADD/SUB — never emitted to this form).
            let inst = mk(op, vec![preg(W0), preg(W1), preg(W2), imm(0)]);
            assert!(
                encode_instruction(&inst).is_err(),
                "{op:?} lsl #0 must fail-closed"
            );
            // amount == width (32 for W) is out of range (imm6 bit 5 set).
            let inst = mk(op, vec![preg(W0), preg(W1), preg(W2), imm(32)]);
            assert!(
                encode_instruction(&inst).is_err(),
                "{op:?} W lsl #32 must fail-closed"
            );
            // amount == 64 for X is out of range.
            let inst = mk(op, vec![preg(X0), preg(X1), preg(X2), imm(64)]);
            assert!(
                encode_instruction(&inst).is_err(),
                "{op:?} X lsl #64 must fail-closed"
            );
        }
    }

    /// FCSEL scalar FP conditional select (`FcselRR`) — every expected word is
    /// ground-truthed against Apple `clang -c` + `otool -tvj` of
    /// `fcsel <Sd/Dd>, <Sn>, <Sm>, <cc>`. Operands: [Rd, Rn (true), Rm (false),
    /// Imm(cond)]; the cond immediate is the ARM 4-bit condition code
    /// (`convert_isel_operand_to_ir`: EQ=0, NE=1, HS=2, LO=3, MI=4, GE=10, LT=11,
    /// GT=12, LE=13, AL=14). S forms have ftype=00 (bits 23:22), D forms ftype=01
    /// — the S/D pairs below differ ONLY in that field (0x1e2… vs 0x1e6…),
    /// grounding the width selection.
    #[test]
    fn test_fcsel_scalar_encodings() {
        // S (single, 32-bit) forms.
        for (rd, rn, rm, cond, expected) in [
            (S0, S1, S2, 0i64, 0x1E22_0C20u32), // fcsel s0, s1, s2, eq
            (S3, S4, S5, 1, 0x1E25_1C83),       // fcsel s3, s4, s5, ne
            (S5, S1, S3, 11, 0x1E23_BC25),      // fcsel s5, s1, s3, lt
            (S2, S0, S4, 12, 0x1E24_CC02),      // fcsel s2, s0, s4, gt
            (S4, S5, S0, 10, 0x1E20_ACA4),      // fcsel s4, s5, s0, ge
            (S1, S2, S3, 13, 0x1E23_DC41),      // fcsel s1, s2, s3, le
            (S0, S0, S0, 2, 0x1E20_2C00),       // fcsel s0, s0, s0, hs
            (S3, S2, S1, 3, 0x1E21_3C43),       // fcsel s3, s2, s1, lo
            (S4, S3, S2, 4, 0x1E22_4C64),       // fcsel s4, s3, s2, mi
            (S5, S4, S3, 14, 0x1E23_EC85),      // fcsel s5, s4, s3, al
        ] {
            let inst = mk(
                AArch64Opcode::FcselRR,
                vec![preg(rd), preg(rn), preg(rm), imm(cond)],
            );
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected, "fcsel S cond={cond}: got {enc:#010X}");
        }
        // D (double, 64-bit) forms — same register/cond matrix, ftype=01.
        for (rd, rn, rm, cond, expected) in [
            (D0, D1, D2, 0i64, 0x1E62_0C20u32), // fcsel d0, d1, d2, eq
            (D3, D4, D5, 1, 0x1E65_1C83),       // fcsel d3, d4, d5, ne
            (D5, D1, D3, 11, 0x1E63_BC25),      // fcsel d5, d1, d3, lt
            (D2, D0, D4, 12, 0x1E64_CC02),      // fcsel d2, d0, d4, gt
            (D4, D5, D0, 10, 0x1E60_ACA4),      // fcsel d4, d5, d0, ge
            (D1, D2, D3, 13, 0x1E63_DC41),      // fcsel d1, d2, d3, le
            (D0, D0, D0, 2, 0x1E60_2C00),       // fcsel d0, d0, d0, hs
            (D3, D2, D1, 3, 0x1E61_3C43),       // fcsel d3, d2, d1, lo
            (D4, D3, D2, 4, 0x1E62_4C64),       // fcsel d4, d3, d2, mi
            (D5, D4, D3, 14, 0x1E63_EC85),      // fcsel d5, d4, d3, al
        ] {
            let inst = mk(
                AArch64Opcode::FcselRR,
                vec![preg(rd), preg(rn), preg(rm), imm(cond)],
            );
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected, "fcsel D cond={cond}: got {enc:#010X}");
        }
    }

    /// `FcselRR` FAILS CLOSED (the bank check the GPR Csel lacks) on any operand
    /// that is not a matching scalar FPR: a GPR in any reg slot, an f16 (half)
    /// operand (that form is not modeled), a Q (128-bit) operand, and a width
    /// mismatch between the three registers.
    #[test]
    fn test_fcsel_rejects_non_fpr_and_mismatch() {
        // GPR in the destination slot — would silently collide onto GPRs on a
        // bank-blind encoder (the exact P0). Must fail closed.
        let inst = mk(
            AArch64Opcode::FcselRR,
            vec![preg(W0), preg(S1), preg(S2), imm(0)],
        );
        assert!(
            encode_instruction(&inst).is_err(),
            "GPR dest must fail-closed"
        );
        // GPR in a source slot.
        let inst = mk(
            AArch64Opcode::FcselRR,
            vec![preg(S0), preg(X1), preg(S2), imm(0)],
        );
        assert!(
            encode_instruction(&inst).is_err(),
            "GPR source must fail-closed"
        );
        // f16 (half) operands — the FEAT_FP16 form is deliberately not modeled.
        let inst = mk(
            AArch64Opcode::FcselRR,
            vec![preg(H0), preg(H1), preg(H0), imm(0)],
        );
        assert!(encode_instruction(&inst).is_err(), "f16 must fail-closed");
        // Q (128-bit) operand — no scalar FCSEL form.
        let inst = mk(
            AArch64Opcode::FcselRR,
            vec![preg(V0), preg(V1), preg(V2), imm(0)],
        );
        assert!(encode_instruction(&inst).is_err(), "Q reg must fail-closed");
        // Width mismatch: S dest, D sources.
        let inst = mk(
            AArch64Opcode::FcselRR,
            vec![preg(S0), preg(D1), preg(D2), imm(0)],
        );
        assert!(
            encode_instruction(&inst).is_err(),
            "S/D width mismatch must fail-closed"
        );
    }

    #[test]
    fn test_lse_atomic_min_max_al_encodings() {
        for (opcode, expected) in [
            (AArch64Opcode::Ldsmaxal, 0xF8E2_4020),
            (AArch64Opcode::Ldsminal, 0xF8E2_5020),
            (AArch64Opcode::Ldumaxal, 0xF8E2_6020),
            (AArch64Opcode::Lduminal, 0xF8E2_7020),
        ] {
            let inst = mk(opcode, vec![preg(X2), preg(X0), preg(X1)]);
            assert_eq!(encode_instruction(&inst).unwrap(), expected);
        }
    }

    #[test]
    fn test_lse_atomic_acquire_only_encodings() {
        // Exact load-acquire-only (`A`, A=1 R=0) forms for the full RMW op
        // set. Every expected word is ground-truthed against LLVM:
        //   `clang -arch arm64 -march=armv8.1-a` + `llvm-objdump -d` of
        //   `<op>a x2, x0, [x1]` disassembles to exactly these bytes.
        for (opcode, expected) in [
            (AArch64Opcode::Ldadda, 0xF8A2_0020u32), // ldadda x2, x0, [x1]
            (AArch64Opcode::Ldclra, 0xF8A2_1020),    // ldclra x2, x0, [x1]
            (AArch64Opcode::Ldeora, 0xF8A2_2020),    // ldeora x2, x0, [x1]
            (AArch64Opcode::Ldseta, 0xF8A2_3020),    // ldseta x2, x0, [x1]
            (AArch64Opcode::Ldsmaxa, 0xF8A2_4020),   // ldsmaxa x2, x0, [x1]
            (AArch64Opcode::Ldsmina, 0xF8A2_5020),   // ldsmina x2, x0, [x1]
            (AArch64Opcode::Ldumaxa, 0xF8A2_6020),   // ldumaxa x2, x0, [x1]
            (AArch64Opcode::Ldumina, 0xF8A2_7020),   // ldumina x2, x0, [x1]
            (AArch64Opcode::Swpa, 0xF8A2_8020),      // swpa x2, x0, [x1]
        ] {
            let inst = mk(opcode, vec![preg(X2), preg(X0), preg(X1)]);
            assert_eq!(
                encode_instruction(&inst).unwrap(),
                expected,
                "{opcode:?} X-form"
            );
        }

        // 32-bit / byte / half access sizes (llvm-objdump ground truth:
        // ldadda w2, w0, [x1] = 0xB8A20020; ldaddab = 0x38A20020;
        // ldaddah = 0x78A20020; swpa w2, w0, [x1] = 0xB8A28020).
        let w_form = mk(AArch64Opcode::Ldadda, vec![preg(W2), preg(W0), preg(X1)]);
        assert_eq!(encode_instruction(&w_form).unwrap(), 0xB8A2_0020);
        let b_form = mk(
            AArch64Opcode::Ldadda,
            vec![preg(W2), preg(W0), preg(X1), imm(0)],
        );
        assert_eq!(encode_instruction(&b_form).unwrap(), 0x38A2_0020);
        let h_form = mk(
            AArch64Opcode::Ldadda,
            vec![preg(W2), preg(W0), preg(X1), imm(1)],
        );
        assert_eq!(encode_instruction(&h_form).unwrap(), 0x78A2_0020);
        let swpa_w = mk(AArch64Opcode::Swpa, vec![preg(W2), preg(W0), preg(X1)]);
        assert_eq!(encode_instruction(&swpa_w).unwrap(), 0xB8A2_8020);
    }

    #[test]
    fn test_cas_release_only_encodings() {
        // Exact store-release-only CASL (A=0, o0/R=1), all access sizes.
        // Ground truth (clang -march=armv8.1-a + llvm-objdump):
        //   casl  x2, x0, [x1] = 0xC8A2FC20
        //   casl  w2, w0, [x1] = 0x88A2FC20
        //   caslb w2, w0, [x1] = 0x08A2FC20
        //   caslh w2, w0, [x1] = 0x48A2FC20
        let x_form = mk(AArch64Opcode::Casl, vec![preg(X2), preg(X0), preg(X1)]);
        assert_eq!(encode_instruction(&x_form).unwrap(), 0xC8A2_FC20);
        let w_form = mk(AArch64Opcode::Casl, vec![preg(W2), preg(W0), preg(X1)]);
        assert_eq!(encode_instruction(&w_form).unwrap(), 0x88A2_FC20);
        let b_form = mk(
            AArch64Opcode::Casl,
            vec![preg(W2), preg(W0), preg(X1), imm(0)],
        );
        assert_eq!(encode_instruction(&b_form).unwrap(), 0x08A2_FC20);
        let h_form = mk(
            AArch64Opcode::Casl,
            vec![preg(W2), preg(W0), preg(X1), imm(1)],
        );
        assert_eq!(encode_instruction(&h_form).unwrap(), 0x48A2_FC20);
    }

    #[test]
    fn test_add_ri() {
        // ADD X0, X1, #42
        let inst = mk(AArch64Opcode::AddRI, vec![preg(X0), preg(X1), imm(42)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_imm(1, 0, 0, 0, 42, 1, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_sub_rr() {
        let inst = mk(AArch64Opcode::SubRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(1, 1, 0, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_sub_ri() {
        let inst = mk(AArch64Opcode::SubRI, vec![preg(X0), preg(X1), imm(42)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_imm(1, 1, 0, 0, 42, 1, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_mul_rr() {
        // MUL X0, X1, X2 = MADD X0, X1, X2, XZR
        let inst = mk(AArch64Opcode::MulRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        // Expected: sf=1, 00 11011 000 Rm=2 0 Ra=31 Rn=1 Rd=0
        let expected = (1u32 << 31) | (0b11011 << 24) | (2 << 16) | (31 << 10) | (1 << 5);
        assert_eq!(enc, expected, "MUL X0, X1, X2 = {enc:#010X}");
    }

    #[test]
    fn test_neon_umaxv_4s() {
        // UMAXV S0, V1.4S
        let inst = mk(AArch64Opcode::NeonUmaxv, vec![preg(S0), preg(V1), imm(5)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_neon::encode_umaxv_4s(1, 0).unwrap();
        assert_eq!(enc, direct);
        assert_eq!(enc, 0x6EB0A820);
    }

    #[test]
    fn test_neon_umaxv_rejects_non_4s_arrangement() {
        let inst = mk(AArch64Opcode::NeonUmaxv, vec![preg(S0), preg(V1), imm(4)]);
        assert!(
            encode_instruction(&inst).is_err(),
            "UMAXV slice is intentionally limited to .4S for #573"
        );
    }

    #[test]
    fn test_neon_addp_scalar_2d() {
        // Verified with `xcrun clang -target arm64-apple-macosx -x assembler`:
        //   addp d0, v1.2d
        let inst = mk(
            AArch64Opcode::NeonAddpScalar,
            vec![preg(D0), preg(V1), imm(6)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_neon::encode_addp_scalar_2d(1, 0).unwrap();
        assert_eq!(enc, direct);
        assert_eq!(enc, 0x5EF1_B820);
    }

    #[test]
    fn test_neon_addp_scalar_rejects_non_2d_arrangement() {
        let inst = mk(
            AArch64Opcode::NeonAddpScalar,
            vec![preg(D0), preg(V1), imm(5)],
        );
        assert!(
            encode_instruction(&inst).is_err(),
            "ADDP scalar slice is intentionally limited to .2D for #909"
        );
    }

    #[test]
    fn test_neon_int_minmax_4s() {
        // Reference bytes verified against the system assembler
        // (`clang -c -target aarch64-apple-darwin`; `otool -tv`):
        //   smax.4s v0, v1, v2  = 0x4ea26420
        //   smin.4s v0, v1, v2  = 0x4ea26c20
        //   umax.4s v0, v1, v2  = 0x6ea26420
        //   umin.4s v0, v1, v2  = 0x6ea26c20
        // Operands: [Vd, Vn, Vm, Imm(arrangement=5 => .4S)].
        let cases = [
            (AArch64Opcode::NeonSmaxV, 0x4EA2_6420u32),
            (AArch64Opcode::NeonSminV, 0x4EA2_6C20u32),
            (AArch64Opcode::NeonUmaxV, 0x6EA2_6420u32),
            (AArch64Opcode::NeonUminV, 0x6EA2_6C20u32),
        ];
        for (op, want) in cases {
            let inst = mk(op, vec![preg(V0), preg(V1), preg(V2), imm(5)]);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, want, "{op:?} .4S encoding mismatch");
        }
    }

    #[test]
    fn test_neon_narrow_arithmetic_arrangement_immediates() {
        let cases = [
            (
                AArch64Opcode::NeonAddV,
                1,
                encoding_neon::VectorArrangement::B16,
                encoding_neon::IntVec3Op::Add,
            ),
            (
                AArch64Opcode::NeonSubV,
                1,
                encoding_neon::VectorArrangement::B16,
                encoding_neon::IntVec3Op::Sub,
            ),
            (
                AArch64Opcode::NeonAddV,
                3,
                encoding_neon::VectorArrangement::H8,
                encoding_neon::IntVec3Op::Add,
            ),
            (
                AArch64Opcode::NeonSubV,
                3,
                encoding_neon::VectorArrangement::H8,
                encoding_neon::IntVec3Op::Sub,
            ),
            (
                AArch64Opcode::NeonMulV,
                3,
                encoding_neon::VectorArrangement::H8,
                encoding_neon::IntVec3Op::Mul,
            ),
            (
                AArch64Opcode::NeonMulV,
                5,
                encoding_neon::VectorArrangement::S4,
                encoding_neon::IntVec3Op::Mul,
            ),
        ];

        for (opcode, arrangement_imm, arrangement, op) in cases {
            let inst = mk(
                opcode,
                vec![preg(V0), preg(V1), preg(V2), imm(arrangement_imm)],
            );
            let enc = encode_instruction(&inst).unwrap();
            let direct = encoding_neon::encode_int_vec3_same(arrangement, op, 2, 1, 0).unwrap();
            assert_eq!(enc, direct, "{opcode:?} arrangement imm {arrangement_imm}");
        }
    }

    #[test]
    fn test_neon_typed_vector_compare_arrangement_immediates() {
        let cases = [
            (
                AArch64Opcode::NeonCmeqV,
                1,
                encoding_neon::VectorArrangement::B16,
                encoding_neon::IntVec3Op::Cmeq,
            ),
            (
                AArch64Opcode::NeonCmgtV,
                3,
                encoding_neon::VectorArrangement::H8,
                encoding_neon::IntVec3Op::Cmgt,
            ),
            (
                AArch64Opcode::NeonCmgeV,
                6,
                encoding_neon::VectorArrangement::D2,
                encoding_neon::IntVec3Op::Cmge,
            ),
            (
                AArch64Opcode::NeonCmhiV,
                1,
                encoding_neon::VectorArrangement::B16,
                encoding_neon::IntVec3Op::Cmhi,
            ),
            (
                AArch64Opcode::NeonCmhsV,
                3,
                encoding_neon::VectorArrangement::H8,
                encoding_neon::IntVec3Op::Cmhs,
            ),
            (
                AArch64Opcode::NeonCmhiV,
                5,
                encoding_neon::VectorArrangement::S4,
                encoding_neon::IntVec3Op::Cmhi,
            ),
            (
                AArch64Opcode::NeonCmhsV,
                5,
                encoding_neon::VectorArrangement::S4,
                encoding_neon::IntVec3Op::Cmhs,
            ),
        ];

        for (opcode, arrangement_imm, arrangement, op) in cases {
            let inst = mk(
                opcode,
                vec![preg(V0), preg(V1), preg(V2), imm(arrangement_imm)],
            );
            let enc = encode_instruction(&inst).unwrap();
            let direct = encoding_neon::encode_int_vec3_same(arrangement, op, 2, 1, 0).unwrap();
            assert_eq!(enc, direct, "{opcode:?} arrangement imm {arrangement_imm}");
        }
    }

    #[test]
    fn test_neon_rbit_rev_byte_opcodes() {
        let rbit_8b = mk(AArch64Opcode::NeonRbitV, vec![preg(V0), preg(V1), imm(0)]);
        let rbit_16b = mk(AArch64Opcode::NeonRbitV, vec![preg(V2), preg(V3), imm(1)]);
        let rev32_8b = mk(AArch64Opcode::NeonRev32V, vec![preg(V4), preg(V5), imm(0)]);
        let rev64_16b = mk(AArch64Opcode::NeonRev64V, vec![preg(V6), preg(V7), imm(1)]);

        assert_eq!(encode_instruction(&rbit_8b).unwrap(), 0x2E60_5820);
        assert_eq!(encode_instruction(&rbit_16b).unwrap(), 0x6E60_5862);
        assert_eq!(encode_instruction(&rev32_8b).unwrap(), 0x2E20_08A4);
        assert_eq!(encode_instruction(&rev64_16b).unwrap(), 0x4E20_08E6);
    }

    #[test]
    fn test_neon_rbit_16b_ground_truth() {
        // The per-byte 8-bit-reverse form (`RBIT Vd.16B, Vn.16B` — the per-byte
        // bit reversal the neon-bitrev vectorizer emits for `a[i].reverse_bits()`
        // over a `[u8; N]`, matching LLVM -O3's `rbit.16b`). Verified against the
        // assembler (`clang -c -target arm64-apple-macos` + `otool -t`):
        //   rbit v1.16b,  v1.16b   = 0x6E605821
        //   rbit v2.16b,  v3.16b   = 0x6E605862
        //   rbit v0.16b,  v31.16b  = 0x6E605BE0
        //   rbit v31.16b, v0.16b   = 0x6E60581F
        let cases = [
            (V1, V1, 0x6E60_5821u32),
            (V2, V3, 0x6E60_5862),
            (V0, V31, 0x6E60_5BE0),
            (V31, V0, 0x6E60_581F),
        ];
        for (rd, rn, want) in cases {
            let inst = mk(AArch64Opcode::NeonRbitV, vec![preg(rd), preg(rn), imm(1)]);
            assert_eq!(
                encode_instruction(&inst).unwrap(),
                want,
                "rbit {rd:?}, {rn:?}"
            );
        }
    }

    #[test]
    fn test_neon_rev64_4s_ground_truth() {
        // The 32-bit-element form (`REV64 Vd.4S` — the complex-pair swap the
        // neon_butterfly vectorizer emits). Verified against the assembler
        // (`clang -c` + `objdump -d`):
        //   rev64 v6.4s,  v7.4s   = 0x4EA008E6
        //   rev64 v0.4s,  v31.4s  = 0x4EA00BE0
        //   rev64 v31.4s, v0.4s   = 0x4EA0081F
        let cases = [
            (V6, V7, 0x4EA0_08E6u32),
            (V0, V31, 0x4EA0_0BE0),
            (V31, V0, 0x4EA0_081F),
        ];
        for (rd, rn, want) in cases {
            let inst = mk(AArch64Opcode::NeonRev64V, vec![preg(rd), preg(rn), imm(5)]);
            assert_eq!(encode_instruction(&inst).unwrap(), want);
        }
    }

    #[test]
    fn test_neon_rev64_rejects_unsupported_arrangements() {
        // Only the byte forms and `.4S` exist for REV64 here; `.2D` does not
        // exist in the ISA and `.2S`/`.4H`/`.8H` stay fail-closed (unemitted).
        for arr in [2i64, 3, 4, 6] {
            let inst = mk(
                AArch64Opcode::NeonRev64V,
                vec![preg(V0), preg(V1), imm(arr)],
            );
            assert!(
                encode_instruction(&inst).is_err(),
                "REV64 arrangement imm {arr} must be rejected"
            );
        }
        // REV32/RBIT gain no element forms from the REV64 extension.
        let rev32_4s = mk(AArch64Opcode::NeonRev32V, vec![preg(V0), preg(V1), imm(5)]);
        assert!(encode_instruction(&rev32_4s).is_err());
        let rbit_4s = mk(AArch64Opcode::NeonRbitV, vec![preg(V0), preg(V1), imm(5)]);
        assert!(encode_instruction(&rbit_4s).is_err());
    }

    #[test]
    fn test_neon_rbit_rejects_non_byte_arrangement() {
        let inst = mk(AArch64Opcode::NeonRbitV, vec![preg(V0), preg(V1), imm(5)]);
        let err = encode_instruction(&inst).unwrap_err();
        assert!(matches!(
            err,
            EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(2))
        ));
    }

    #[test]
    fn test_neon_cnt_uaddlp_ground_truth() {
        // Verified against the assembler (`clang -c` + `otool -tvV`):
        //   cnt    v0.16b, v1.16b   = 0x4E205820
        //   cnt    v3.16b, v7.16b   = 0x4E2058E3
        //   uaddlp v0.8h,  v1.16b   = 0x6E202820   (arrangement imm 1 = input 16B)
        //   uaddlp v3.8h,  v7.16b   = 0x6E2028E3
        //   uaddlp v0.4s,  v1.8h    = 0x6E602820   (arrangement imm 3 = input 8H)
        //   uaddlp v3.4s,  v7.8h    = 0x6E6028E3
        let cnt_0_1 = mk(AArch64Opcode::NeonCntV, vec![preg(V0), preg(V1), imm(1)]);
        let cnt_3_7 = mk(AArch64Opcode::NeonCntV, vec![preg(V3), preg(V7), imm(1)]);
        let uaddlp_h_0_1 = mk(AArch64Opcode::NeonUaddlpV, vec![preg(V0), preg(V1), imm(1)]);
        let uaddlp_h_3_7 = mk(AArch64Opcode::NeonUaddlpV, vec![preg(V3), preg(V7), imm(1)]);
        let uaddlp_s_0_1 = mk(AArch64Opcode::NeonUaddlpV, vec![preg(V0), preg(V1), imm(3)]);
        let uaddlp_s_3_7 = mk(AArch64Opcode::NeonUaddlpV, vec![preg(V3), preg(V7), imm(3)]);

        assert_eq!(encode_instruction(&cnt_0_1).unwrap(), 0x4E20_5820);
        assert_eq!(encode_instruction(&cnt_3_7).unwrap(), 0x4E20_58E3);
        assert_eq!(encode_instruction(&uaddlp_h_0_1).unwrap(), 0x6E20_2820);
        assert_eq!(encode_instruction(&uaddlp_h_3_7).unwrap(), 0x6E20_28E3);
        assert_eq!(encode_instruction(&uaddlp_s_0_1).unwrap(), 0x6E60_2820);
        assert_eq!(encode_instruction(&uaddlp_s_3_7).unwrap(), 0x6E60_28E3);
    }

    #[test]
    fn test_neon_cnt_rejects_non_byte_arrangement() {
        // CNT exists only for 8B/16B; a 4S arrangement (imm 5) must be rejected.
        let inst = mk(AArch64Opcode::NeonCntV, vec![preg(V0), preg(V1), imm(5)]);
        let err = encode_instruction(&inst).unwrap_err();
        assert!(matches!(
            err,
            EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(_))
        ));
    }

    #[test]
    fn test_neon_abs_4s_ground_truth() {
        // Verified against the assembler (`clang -c` + `otool -t`):
        //   abs v0.4s, v1.4s = 0x4EA0B820   (arrangement imm 5 = .4S)
        //   abs v3.4s, v7.4s = 0x4EA0B8E3
        let abs_0_1 = mk(AArch64Opcode::NeonAbsV, vec![preg(V0), preg(V1), imm(5)]);
        let abs_3_7 = mk(AArch64Opcode::NeonAbsV, vec![preg(V3), preg(V7), imm(5)]);
        assert_eq!(encode_instruction(&abs_0_1).unwrap(), 0x4EA0_B820);
        assert_eq!(encode_instruction(&abs_3_7).unwrap(), 0x4EA0_B8E3);
    }

    #[test]
    fn test_neon_udot_4s_ground_truth() {
        // Verified against the assembler (`clang -c -march=armv8.2-a+dotprod` +
        // `objdump -d`); arrangement imm 1 = input 16B; operand order
        // [Vd (accumulator, tied def-use), Vn, Vm, Imm]:
        //   udot v0.4s,  v1.16b,  v2.16b  = 0x6E829420
        //   udot v3.4s,  v7.16b,  v9.16b  = 0x6E8994E3
        //   udot v31.4s, v30.16b, v29.16b = 0x6E9D97DF   (high reg numbers)
        //   udot v17.4s, v0.16b,  v31.16b = 0x6E9F9411
        //   udot v5.4s,  v20.16b, v11.16b = 0x6E8B9685
        let cases = [
            (V0, V1, V2, 0x6E82_9420u32),
            (V3, V7, V9, 0x6E89_94E3),
            (V31, V30, V29, 0x6E9D_97DF),
            (V17, V0, V31, 0x6E9F_9411),
            (V5, V20, V11, 0x6E8B_9685),
        ];
        for (vd, vn, vm, expect) in cases {
            let inst = mk(
                AArch64Opcode::NeonUdotV,
                vec![preg(vd), preg(vn), preg(vm), imm(1)],
            );
            assert_eq!(encode_instruction(&inst).unwrap(), expect);
        }
    }

    #[test]
    fn test_neon_udot_rejects_non_16b_arrangement() {
        // UDOT is emitted (and proven) only in the `.16B -> .4S` form; a .4S
        // input arrangement (imm 5) must be rejected.
        let inst = mk(
            AArch64Opcode::NeonUdotV,
            vec![preg(V0), preg(V1), preg(V2), imm(5)],
        );
        let err = encode_instruction(&inst).unwrap_err();
        assert!(matches!(
            err,
            EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(_))
        ));
    }

    #[test]
    fn test_neon_smlal_2d_ground_truth() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand layout [Vd (tied acc), Vn, Vm, Imm(input arr .4S = 5)]:
        //   smlal.2d  v0,v1,v2    = 0x0EA28020   smlal2.2d v0,v1,v2    = 0x4EA28020
        //   umlal.2d  v0,v1,v2    = 0x2EA28020   umlal2.2d v0,v1,v2    = 0x6EA28020
        //   smlal.2d  v31,v30,v29 = 0x0EBD83DF   smlal2.2d v7,v3,v9    = 0x4EA98067
        let cases = [
            (AArch64Opcode::NeonSmlalV, V0, V1, V2, 0x0EA2_8020u32),
            (AArch64Opcode::NeonSmlal2V, V0, V1, V2, 0x4EA2_8020),
            (AArch64Opcode::NeonUmlalV, V0, V1, V2, 0x2EA2_8020),
            (AArch64Opcode::NeonUmlal2V, V0, V1, V2, 0x6EA2_8020),
            (AArch64Opcode::NeonSmlalV, V31, V30, V29, 0x0EBD_83DF),
            (AArch64Opcode::NeonSmlal2V, V7, V3, V9, 0x4EA9_8067),
        ];
        for (op, vd, vn, vm, expect) in cases {
            let inst = mk(op, vec![preg(vd), preg(vn), preg(vm), imm(5)]);
            assert_eq!(encode_instruction(&inst).unwrap(), expect, "{op:?}");
        }
    }

    #[test]
    fn test_neon_smlal_rejects_non_4s_input() {
        // The widening dot is emitted (and proven) only in the `.4S -> .2D` form;
        // a non-.4S input arrangement must fail CLOSED.
        for op in [
            AArch64Opcode::NeonSmlalV,
            AArch64Opcode::NeonSmlal2V,
            AArch64Opcode::NeonUmlalV,
            AArch64Opcode::NeonUmlal2V,
        ] {
            let inst = mk(op, vec![preg(V0), preg(V1), preg(V2), imm(6)]); // .2D marker
            let err = encode_instruction(&inst).unwrap_err();
            assert!(
                matches!(
                    err,
                    EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(_))
                ),
                "{op:?} must reject non-.4S input"
            );
        }
    }

    #[test]
    fn test_neon_uaddw_2d_ground_truth() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand layout [Vd (pure def), Vn (i64 addend), Vm, Imm(input arr .4S = 5)]:
        //   uaddw.2d  v0,v1,v2    = 0x2EA21020   uaddw2.2d v0,v1,v2    = 0x6EA21020
        //   uaddw.2d  v31,v30,v29 = 0x2EBD13DF   uaddw2.2d v7,v3,v9    = 0x6EA91067
        let cases = [
            (AArch64Opcode::NeonUaddwV, V0, V1, V2, 0x2EA2_1020u32),
            (AArch64Opcode::NeonUaddw2V, V0, V1, V2, 0x6EA2_1020),
            (AArch64Opcode::NeonUaddwV, V31, V30, V29, 0x2EBD_13DF),
            (AArch64Opcode::NeonUaddw2V, V7, V3, V9, 0x6EA9_1067),
        ];
        for (op, vd, vn, vm, expect) in cases {
            let inst = mk(op, vec![preg(vd), preg(vn), preg(vm), imm(5)]);
            assert_eq!(encode_instruction(&inst).unwrap(), expect, "{op:?}");
        }
    }

    #[test]
    fn test_neon_uaddw_rejects_non_4s_input() {
        // The widening add-wide is emitted (and proven) only in the `.4S -> .2D`
        // form; a non-.4S input arrangement must fail CLOSED.
        for op in [AArch64Opcode::NeonUaddwV, AArch64Opcode::NeonUaddw2V] {
            let inst = mk(op, vec![preg(V0), preg(V1), preg(V2), imm(6)]); // .2D marker
            let err = encode_instruction(&inst).unwrap_err();
            assert!(
                matches!(
                    err,
                    EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(_))
                ),
                "{op:?} must reject non-.4S input"
            );
        }
    }

    #[test]
    fn test_neon_saddw_2d_ground_truth() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand layout [Vd (pure def), Vn (i64 addend), Vm, Imm(input arr .4S = 5)]:
        //   saddw.2d  v0,v1,v2    = 0x0EA21020   saddw2.2d v0,v1,v2    = 0x4EA21020
        //   saddw.2d  v31,v30,v29 = 0x0EBD13DF   saddw2.2d v7,v3,v9    = 0x4EA91067
        let cases = [
            (AArch64Opcode::NeonSaddwV, V0, V1, V2, 0x0EA2_1020u32),
            (AArch64Opcode::NeonSaddw2V, V0, V1, V2, 0x4EA2_1020),
            (AArch64Opcode::NeonSaddwV, V31, V30, V29, 0x0EBD_13DF),
            (AArch64Opcode::NeonSaddw2V, V7, V3, V9, 0x4EA9_1067),
        ];
        for (op, vd, vn, vm, expect) in cases {
            let inst = mk(op, vec![preg(vd), preg(vn), preg(vm), imm(5)]);
            assert_eq!(encode_instruction(&inst).unwrap(), expect, "{op:?}");
        }
    }

    #[test]
    fn test_neon_saddw_rejects_non_4s_input() {
        // The SIGNED widening add-wide is emitted (and proven) only in the
        // `.4S -> .2D` form; a non-.4S input arrangement must fail CLOSED.
        for op in [AArch64Opcode::NeonSaddwV, AArch64Opcode::NeonSaddw2V] {
            let inst = mk(op, vec![preg(V0), preg(V1), preg(V2), imm(6)]); // .2D marker
            let err = encode_instruction(&inst).unwrap_err();
            assert!(
                matches!(
                    err,
                    EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(_))
                ),
                "{op:?} must reject non-.4S input"
            );
        }
    }

    #[test]
    fn test_neon_mla_4s_ground_truth() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand layout [Vd (accumulator, tied def-use), Vn, Vm, Imm(arr .4S = 5)]:
        //   mla.4s v0, v1, v2   = 0x4EA29420   mla.4s v31, v30, v29 = 0x4EBD97DF
        //   mla.4s v5, v20, v11 = 0x4EAB9685   mla.4s v7, v3, v9    = 0x4EA99467
        // NOT MLS (0x6EA29420, U-bit subtract) and NOT MUL (0x4EA29C20,
        // no-accumulate) — both distinctness axes pinned at the encoding_neon
        // layer (test_mla_is_not_mls_nor_mul).
        let cases = [
            (V0, V1, V2, 0x4EA2_9420u32),
            (V31, V30, V29, 0x4EBD_97DF),
            (V5, V20, V11, 0x4EAB_9685),
            (V7, V3, V9, 0x4EA9_9467),
        ];
        for (vd, vn, vm, expect) in cases {
            let inst = mk(
                AArch64Opcode::NeonMlaV,
                vec![preg(vd), preg(vn), preg(vm), imm(5)],
            );
            assert_eq!(encode_instruction(&inst).unwrap(), expect);
        }
    }

    #[test]
    fn test_neon_mla_rejects_non_4s() {
        // MLA is emitted (and proven) only in the `.4S` arrangement; anything
        // else must fail CLOSED.
        for arr_code in [1, 3, 6] {
            // .16B / .8H / .2D markers
            let inst = mk(
                AArch64Opcode::NeonMlaV,
                vec![preg(V0), preg(V1), preg(V2), imm(arr_code)],
            );
            let err = encode_instruction(&inst).unwrap_err();
            assert!(
                matches!(
                    err,
                    EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(_))
                ),
                "MLA must reject non-.4S arrangement code {arr_code}"
            );
        }
    }

    #[test]
    fn test_neon_uadalp_2d_ground_truth() {
        // Assembler-verified (`clang -c -target arm64-apple-macos` + `otool -tvj`);
        // operand layout [Vd (accumulator, tied def-use), Vn, Imm(input arr .4S = 5)]:
        //   uadalp v0.2d, v1.4s  = 0x6EA06820   uadalp v31.2d, v30.4s = 0x6EA06BDF
        //   uadalp v5.2d, v20.4s = 0x6EA06A85   uadalp v7.2d, v3.4s   = 0x6EA06867
        // NOT UADDLP (0x6EA02820, no-accumulate) and NOT SADALP (0x4EA06820,
        // sign-extending) — both distinctness axes pinned at the encoding_neon
        // layer (test_uadalp_is_not_uaddlp_nor_sadalp).
        let cases = [
            (V0, V1, 0x6EA0_6820u32),
            (V31, V30, 0x6EA0_6BDF),
            (V5, V20, 0x6EA0_6A85),
            (V7, V3, 0x6EA0_6867),
        ];
        for (vd, vn, expect) in cases {
            let inst = mk(AArch64Opcode::NeonUadalpV, vec![preg(vd), preg(vn), imm(5)]);
            assert_eq!(encode_instruction(&inst).unwrap(), expect);
        }
    }

    #[test]
    fn test_neon_uadalp_rejects_non_4s_input() {
        // The accumulating pairwise widen is emitted (and proven) only in the
        // `.4S -> .2D` form; any other input arrangement must fail CLOSED —
        // including the `.16B`/`.8H` inputs that ARE legal for the
        // non-accumulating NeonUaddlpV.
        for arr_code in [1, 3, 6] {
            // .16B / .8H / .2D markers
            let inst = mk(
                AArch64Opcode::NeonUadalpV,
                vec![preg(V0), preg(V1), imm(arr_code)],
            );
            let err = encode_instruction(&inst).unwrap_err();
            assert!(
                matches!(
                    err,
                    EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(_))
                ),
                "UADALP must reject non-.4S input arrangement code {arr_code}"
            );
        }
    }

    #[test]
    fn test_neon_ext_16b_ground_truth() {
        // Verified against the assembler (`clang -c` + `otool -t`); operand
        // order [Vd, Vn (LOW source), Vm (HIGH source), Imm(byte shift)]:
        //   ext v0.16b,  v1.16b,  v2.16b,  #1  = 0x6E020820   (neighbor shift)
        //   ext v0.16b,  v1.16b,  v2.16b,  #4  = 0x6E022020
        //   ext v0.16b,  v1.16b,  v2.16b,  #8  = 0x6E024020
        //   ext v0.16b,  v1.16b,  v2.16b,  #12 = 0x6E026020
        //   ext v0.16b,  v1.16b,  v2.16b,  #15 = 0x6E027820   (neighbor shift)
        //   ext v31.16b, v30.16b, v29.16b, #1  = 0x6E1D0BDF   (high regs)
        //   ext v31.16b, v30.16b, v29.16b, #12 = 0x6E1D63DF   (high regs)
        //   ext v17.16b, v0.16b,  v31.16b, #4  = 0x6E1F2011   (asymmetric)
        //   ext v17.16b, v0.16b,  v31.16b, #15 = 0x6E1F7811   (asymmetric)
        //   ext v5.16b,  v20.16b, v11.16b, #8  = 0x6E0B4285
        let cases = [
            (V0, V1, V2, 1i64, 0x6E02_0820u32),
            (V0, V1, V2, 4, 0x6E02_2020),
            (V0, V1, V2, 8, 0x6E02_4020),
            (V0, V1, V2, 12, 0x6E02_6020),
            (V0, V1, V2, 15, 0x6E02_7820),
            (V31, V30, V29, 1, 0x6E1D_0BDF),
            (V31, V30, V29, 12, 0x6E1D_63DF),
            (V17, V0, V31, 4, 0x6E1F_2011),
            (V17, V0, V31, 15, 0x6E1F_7811),
            (V5, V20, V11, 8, 0x6E0B_4285),
        ];
        for (vd, vn, vm, sh, expect) in cases {
            let inst = mk(
                AArch64Opcode::NeonExtV,
                vec![preg(vd), preg(vn), preg(vm), imm(sh)],
            );
            assert_eq!(encode_instruction(&inst).unwrap(), expect);
        }
    }

    #[test]
    fn test_neon_ext_rejects_unproven_immediates() {
        // Only the byte shifts the vectorizers emit (and the SMT proofs credit)
        // encode: the whole-i32-lane #4/#8/#12 and the single-byte-neighbor
        // #1/#15. Hardware-valid but unproven immediates must fail CLOSED.
        for sh in [0i64, 2, 3, 5, 7, 11, 13, 16] {
            let inst = mk(
                AArch64Opcode::NeonExtV,
                vec![preg(V0), preg(V1), preg(V2), imm(sh)],
            );
            let err = encode_instruction(&inst).unwrap_err();
            assert!(matches!(
                err,
                EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidExtImmediate(_))
            ));
        }
    }

    #[test]
    fn test_neon_abs_rejects_non_4s_arrangement() {
        // ABS.4S is the only form the abs-sum lowering emits/proves; a .16B
        // arrangement (imm 1) must be rejected.
        let inst = mk(AArch64Opcode::NeonAbsV, vec![preg(V0), preg(V1), imm(1)]);
        let err = encode_instruction(&inst).unwrap_err();
        assert!(matches!(
            err,
            EncodeError::NeonEncode(encoding_neon::NeonEncodeError::InvalidSize(_))
        ));
    }

    #[test]
    fn test_neon_umov_gen_s_lanes_ground_truth() {
        // Verified with `xcrun as -arch arm64`:
        //   umov w0, v1.s[0]
        //   umov w2, v3.s[1]
        //   umov w4, v5.s[2]
        //   umov w6, v7.s[3]
        let cases = [
            (W0, V1, 0, 0x0E043C20),
            (W2, V3, 1, 0x0E0C3C62),
            (W4, V5, 2, 0x0E143CA4),
            (W6, V7, 3, 0x0E1C3CE6),
        ];

        for (dst, src, lane, expected) in cases {
            let inst = mk(
                AArch64Opcode::NeonUmovGen,
                vec![preg(dst), preg(src), imm(lane), imm(4)],
            );
            let enc = encode_instruction(&inst).unwrap();
            let direct = encoding_neon::encode_umov_general(
                encoding_neon::ElementSize::S,
                lane as u8,
                src.hw_enc(),
                dst.hw_enc(),
            )
            .unwrap();
            assert_eq!(enc, direct);
            assert_eq!(
                enc, expected,
                "UMOV {:?}, {:?}.S[{lane}] = {enc:#010X}",
                dst, src
            );
        }
    }

    #[test]
    fn test_neon_umov_gen_b_h_lanes_ground_truth() {
        // Verified with `xcrun clang -target arm64-apple-macosx -x assembler`:
        //   umov w0, v1.b[0]
        //   umov w2, v3.b[15]
        //   umov w4, v5.h[0]
        //   umov w6, v7.h[7]
        let cases = [
            (W0, V1, 0, 1, encoding_neon::ElementSize::B, 0x0E01_3C20),
            (W2, V3, 15, 1, encoding_neon::ElementSize::B, 0x0E1F_3C62),
            (W4, V5, 0, 2, encoding_neon::ElementSize::H, 0x0E02_3CA4),
            (W6, V7, 7, 2, encoding_neon::ElementSize::H, 0x0E1E_3CE6),
        ];

        for (dst, src, lane, elem_bytes, elem, expected) in cases {
            let inst = mk(
                AArch64Opcode::NeonUmovGen,
                vec![preg(dst), preg(src), imm(lane), imm(elem_bytes)],
            );
            let enc = encode_instruction(&inst).unwrap();
            let direct =
                encoding_neon::encode_umov_general(elem, lane as u8, src.hw_enc(), dst.hw_enc())
                    .unwrap();
            assert_eq!(enc, direct);
            assert_eq!(
                enc, expected,
                "UMOV {:?}, {:?} lane {lane} = {enc:#010X}",
                dst, src
            );
        }
    }

    #[test]
    fn test_neon_umov_gen_d_lanes_ground_truth() {
        // Verified with `xcrun clang -target arm64-apple-macosx -x assembler`:
        //   umov x0, v1.d[0]
        //   umov x2, v3.d[1]
        let cases = [(X0, V1, 0, 0x4E08_3C20), (X2, V3, 1, 0x4E18_3C62)];

        for (dst, src, lane, expected) in cases {
            let inst = mk(
                AArch64Opcode::NeonUmovGen,
                vec![preg(dst), preg(src), imm(lane), imm(8)],
            );
            let enc = encode_instruction(&inst).unwrap();
            let direct = encoding_neon::encode_umov_general(
                encoding_neon::ElementSize::D,
                lane as u8,
                src.hw_enc(),
                dst.hw_enc(),
            )
            .unwrap();
            assert_eq!(enc, direct);
            assert_eq!(
                enc, expected,
                "UMOV {:?}, {:?}.D[{lane}] = {enc:#010X}",
                dst, src
            );
        }
    }

    #[test]
    fn test_neon_umov_gen_rejects_unsupported_shapes() {
        let lane4 = mk(
            AArch64Opcode::NeonUmovGen,
            vec![preg(W0), preg(V1), imm(4), imm(4)],
        );
        assert!(encode_instruction(&lane4).is_err());

        let x_dst = mk(
            AArch64Opcode::NeonUmovGen,
            vec![preg(X0), preg(V1), imm(0), imm(4)],
        );
        assert!(encode_instruction(&x_dst).is_err());

        let bad_d_lane = mk(
            AArch64Opcode::NeonUmovGen,
            vec![preg(X0), preg(V1), imm(2), imm(8)],
        );
        assert!(encode_instruction(&bad_d_lane).is_err());

        let w_dst_for_d = mk(
            AArch64Opcode::NeonUmovGen,
            vec![preg(W0), preg(V1), imm(0), imm(8)],
        );
        assert!(encode_instruction(&w_dst_for_d).is_err());
    }

    #[test]
    fn test_neon_dup_gen_4s_ground_truth() {
        // Verified with `xcrun as -arch arm64`:
        //   dup v0.4s, w1
        //   dup v4.4s, w8
        //   dup v30.4s, w4
        let cases = [
            (V0, W1, 0x4E04_0C20),
            (V4, W8, 0x4E04_0D04),
            (V30, W4, 0x4E04_0C9E),
        ];

        for (dst, src, expected) in cases {
            let inst = mk(
                AArch64Opcode::NeonDupGen,
                vec![preg(dst), preg(src), imm(4)],
            );
            let enc = encode_instruction(&inst).unwrap();
            let direct = encoding_neon::encode_dup_general(
                1,
                encoding_neon::ElementSize::S,
                src.hw_enc(),
                dst.hw_enc(),
            )
            .unwrap();
            let ins_lane0 = encoding_neon::encode_ins_general(
                encoding_neon::ElementSize::S,
                0,
                src.hw_enc(),
                dst.hw_enc(),
            )
            .unwrap();

            assert_eq!(enc, direct);
            assert_eq!(enc, expected, "DUP {:?}.4S, {:?} = {enc:#010X}", dst, src);
            assert_ne!(enc, ins_lane0, "DUP must not encode as INS lane zero");
        }
    }

    #[test]
    fn test_neon_dup_gen_2d_and_ins_gen_d_ground_truth() {
        // Verified with `xcrun clang -target arm64-apple-macosx -x assembler`:
        //   dup v0.2d, x1
        //   ins v0.d[1], x2
        let dup = mk(AArch64Opcode::NeonDupGen, vec![preg(V0), preg(X1), imm(8)]);
        let dup_enc = encode_instruction(&dup).unwrap();
        let dup_direct =
            encoding_neon::encode_dup_general(1, encoding_neon::ElementSize::D, 1, 0).unwrap();
        assert_eq!(dup_enc, dup_direct);
        assert_eq!(dup_enc, 0x4E08_0C20);

        let ins = mk(
            AArch64Opcode::NeonInsGen,
            vec![preg(V0), preg(X2), imm(1), imm(8)],
        );
        let ins_enc = encode_instruction(&ins).unwrap();
        let ins_direct =
            encoding_neon::encode_ins_general(encoding_neon::ElementSize::D, 1, 2, 0).unwrap();
        assert_eq!(ins_enc, ins_direct);
        assert_eq!(ins_enc, 0x4E18_1C40);
    }

    #[test]
    fn test_neon_dup_gen_8b_v64_is_q0_ground_truth() {
        // A `<8 x i8>` splat targets a 64-bit (D) destination register, so the
        // Q bit is derived from the register class (Fpr64 => Q=0, `.8b`), NOT
        // the trailing element-size Imm. Verified with
        // `xcrun clang -target arm64-apple-macosx -x assembler`:
        //   dup v0.8b, w1   =>   0x0e010c20
        let dup = mk(AArch64Opcode::NeonDupGen, vec![preg(D0), preg(W1), imm(1)]);
        let dup_enc = encode_instruction(&dup).unwrap();
        let q0 = encoding_neon::encode_dup_general(0, encoding_neon::ElementSize::B, 1, 0).unwrap();
        assert_eq!(dup_enc, q0, "Fpr64 dup must encode with Q=0 (`.8b`)");
        assert_eq!(dup_enc, 0x0e01_0c20, "dup v0.8b, w1");

        // The Q=1 (`.16b`) form must be distinct — a D-register dup must NOT
        // mis-encode as the 128-bit arrangement.
        let q1 = encoding_neon::encode_dup_general(1, encoding_neon::ElementSize::B, 1, 0).unwrap();
        assert_ne!(
            dup_enc, q1,
            "V64 dup must not encode as the 128-bit `.16b` form"
        );
    }

    #[test]
    fn test_neon_ins_gen_b_h_lanes_ground_truth() {
        // Verified with `xcrun clang -target arm64-apple-macosx -x assembler`:
        //   ins v0.b[15], w1
        //   ins v2.h[7], w3
        let cases = [
            (V0, W1, 15, 1, encoding_neon::ElementSize::B, 0x4E1F_1C20),
            (V2, W3, 7, 2, encoding_neon::ElementSize::H, 0x4E1E_1C62),
        ];

        for (dst, src, lane, elem_bytes, elem, expected) in cases {
            let inst = mk(
                AArch64Opcode::NeonInsGen,
                vec![preg(dst), preg(src), imm(lane), imm(elem_bytes)],
            );
            let enc = encode_instruction(&inst).unwrap();
            let direct =
                encoding_neon::encode_ins_general(elem, lane as u8, src.hw_enc(), dst.hw_enc())
                    .unwrap();
            assert_eq!(enc, direct);
            assert_eq!(
                enc, expected,
                "INS {:?} lane {lane}, {:?} = {enc:#010X}",
                dst, src
            );
        }
    }

    #[test]
    fn test_neon_movi_zero_uses_128_bit_q_for_fpr128() {
        let inst = mk(AArch64Opcode::NeonMovi, vec![preg(V0), imm(0)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_neon::encode_movi_byte(1, 0, 0).unwrap();
        assert_eq!(enc, direct);
        assert_eq!(enc, 0x4F00_E400);
        assert_eq!((enc >> 30) & 1, 1, "MOVI V0.16B, #0 must set Q=1");
    }

    #[test]
    fn test_fmov_fpr_gpr_uses_32_bit_sf_for_w_s() {
        // FMOV W0, S1
        let inst = mk(AArch64Opcode::FmovFprGpr, vec![preg(W0), preg(S1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct =
            encoding_fp::encode_fp_int_conv(false, FpSize::Single, FpConvOp::FmovToGp, 1, 0)
                .unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_fmov_gpr_fpr_uses_32_bit_sf_for_s_w() {
        // FMOV S0, W1
        let inst = mk(AArch64Opcode::FmovGprFpr, vec![preg(S0), preg(W1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct =
            encoding_fp::encode_fp_int_conv(false, FpSize::Single, FpConvOp::FmovToFp, 1, 0)
                .unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_msub() {
        // MSUB X0, X1, X2, X9 — Rd = X9 - X1 * X2
        // ARM ARM: sf=1 00 11011 000 Rm=2 1 Ra=9 Rn=1 Rd=0
        let inst = mk(
            AArch64Opcode::Msub,
            vec![preg(X0), preg(X1), preg(X2), preg(X9)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (1u32 << 31)
            | (0b11011 << 24)
            | (2 << 16)
            | (1 << 15) // o0 = 1 for MSUB
            | (9 << 10) // Ra = X9
            | (1 << 5);
        assert_eq!(enc, expected, "MSUB X0, X1, X2, X9 = {enc:#010X}");
    }

    #[test]
    fn test_msub_mneg_alias() {
        // MNEG X0, X1, X2 = MSUB X0, X1, X2, XZR (3 operands, Ra defaults to XZR)
        let inst = mk(AArch64Opcode::Msub, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = (1u32 << 31)
            | (0b11011 << 24)
            | (2 << 16)
            | (1 << 15) // o0 = 1 for MSUB
            | (31 << 10) // Ra = XZR (31)
            | (1 << 5);
        assert_eq!(enc, expected, "MNEG X0, X1, X2 = {enc:#010X}");
    }

    #[test]
    fn test_smull() {
        // SMULL X0, W1, W2 = SMADDL X0, W1, W2, XZR
        // ARM ARM: sf=1 00 11011 001 Rm=2 0 Ra=31 Rn=1 Rd=0
        let inst = mk(AArch64Opcode::Smull, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b11011 << 24)
            | (0b001 << 21) // signed long multiply
            | (2 << 16)) // o0 = 0
            | (31 << 10) // Ra = XZR
            | (1 << 5);
        assert_eq!(enc, expected, "SMULL X0, W1, W2 = {enc:#010X}");
    }

    #[test]
    fn test_umull() {
        // UMULL X0, W1, W2 = UMADDL X0, W1, W2, XZR
        // ARM ARM: sf=1 00 11011 101 Rm=2 0 Ra=31 Rn=1 Rd=0
        let inst = mk(AArch64Opcode::Umull, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b11011 << 24)
            | (0b101 << 21) // unsigned long multiply
            | (2 << 16)) // o0 = 0
            | (31 << 10) // Ra = XZR
            | (1 << 5);
        assert_eq!(enc, expected, "UMULL X0, W1, W2 = {enc:#010X}");
    }

    #[test]
    fn test_adds_rr() {
        // ADDS X0, X1, X2
        let inst = mk(AArch64Opcode::AddsRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(1, 0, 1, 0, 2, 0, 1, 0);
        assert_eq!(
            enc, direct,
            "ADDS X0, X1, X2: unified={enc:#010X}, direct={direct:#010X}"
        );
    }

    #[test]
    fn test_subs_rr() {
        // SUBS X0, X1, X2
        let inst = mk(AArch64Opcode::SubsRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(1, 1, 1, 0, 2, 0, 1, 0);
        assert_eq!(
            enc, direct,
            "SUBS X0, X1, X2: unified={enc:#010X}, direct={direct:#010X}"
        );
    }

    #[test]
    fn test_sdiv() {
        // SDIV X0, X1, X2
        let inst = mk(AArch64Opcode::SDiv, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        // sf=1 0 0011010110 Rm=2 000011 Rn=1 Rd=0
        let expected =
            (1u32 << 31) | (0b0_0011010110 << 21) | (2 << 16) | (0b000011 << 10) | (1 << 5);
        assert_eq!(enc, expected, "SDIV X0, X1, X2 = {enc:#010X}");
    }

    #[test]
    fn test_udiv() {
        let inst = mk(AArch64Opcode::UDiv, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected =
            (1u32 << 31) | (0b0_0011010110 << 21) | (2 << 16) | (0b000010 << 10) | (1 << 5);
        assert_eq!(enc, expected, "UDIV X0, X1, X2 = {enc:#010X}");
    }

    #[test]
    fn test_neg() {
        // NEG X0, X1 = SUB X0, XZR, X1
        let inst = mk(AArch64Opcode::Neg, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(1, 1, 0, 0, 1, 0, 31, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_and_rr() {
        let inst = mk(AArch64Opcode::AndRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(1, 0b00, 0, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_orr_rr() {
        let inst = mk(AArch64Opcode::OrrRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(1, 0b01, 0, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_eor_rr() {
        let inst = mk(AArch64Opcode::EorRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(1, 0b10, 0, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_mov_r() {
        // MOV X0, X1 = ORR X0, XZR, X1
        let inst = mk(AArch64Opcode::MovR, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(1, 0b01, 0, 0, 1, 0, 31, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_movz() {
        let unshifted = mk(AArch64Opcode::Movz, vec![preg(X0), imm(0x1234)]);
        let explicit_zero = mk(AArch64Opcode::Movz, vec![preg(X0), imm(0x1234), imm(0)]);
        let direct = encoding::encode_move_wide(1, 0b10, 0, 0x1234, 0);
        assert_eq!(encode_instruction(&unshifted).unwrap(), direct);
        assert_eq!(encode_instruction(&explicit_zero).unwrap(), direct);
    }

    #[test]
    fn test_movz_rejects_invalid_shift() {
        for shift in [-16i64, 8, 16, 32, 48, 64] {
            let inst = mk(AArch64Opcode::Movz, vec![preg(X0), imm(0x1234), imm(shift)]);
            assert!(
                matches!(
                    encode_instruction(&inst),
                    Err(EncodeError::InvalidOperand { index: 2, .. })
                ),
                "MOVZ shift {shift} must fail closed"
            );
        }

        // W-form move-wide encodings expose only hw=0/1, but this release's
        // v0.1's retained MOVZ-proof subset is narrower still: only hw=0.
        let inst = mk(AArch64Opcode::Movz, vec![preg(W0), imm(0x1234), imm(32)]);
        assert!(matches!(
            encode_instruction(&inst),
            Err(EncodeError::InvalidOperand { index: 2, .. })
        ));

        let extra = mk(AArch64Opcode::Movz, vec![preg(X0), imm(1), imm(16), imm(0)]);
        assert!(matches!(
            encode_instruction(&extra),
            Err(EncodeError::InvalidOperand { index: 3, .. })
        ));

        let sp_dst = mk(AArch64Opcode::Movz, vec![sp(), imm(1)]);
        assert!(matches!(
            encode_instruction(&sp_dst),
            Err(EncodeError::InvalidOperand { index: 0, .. })
        ));

        for opcode in [
            AArch64Opcode::MovI,
            AArch64Opcode::Movz,
            AArch64Opcode::Movn,
            AArch64Opcode::Movk,
        ] {
            let extra_operands = if opcode == AArch64Opcode::MovI {
                vec![preg(X0), imm(1), imm(0)]
            } else {
                vec![preg(X0), imm(1), imm(0), imm(0)]
            };
            assert!(
                matches!(
                    encode_instruction(&mk(opcode, extra_operands)),
                    Err(EncodeError::InvalidOperand { .. })
                ),
                "{opcode:?} must reject extra operands"
            );

            for bad_dst in [sp(), preg(D0)] {
                assert!(
                    matches!(
                        encode_instruction(&mk(opcode, vec![bad_dst, imm(1)])),
                        Err(EncodeError::InvalidOperand { index: 0, .. })
                    ),
                    "{opcode:?} must reject SP and non-GPR destinations"
                );
            }
        }

        for opcode in [AArch64Opcode::MOVZWi, AArch64Opcode::MOVZXi] {
            assert!(matches!(
                encode_instruction(&mk(opcode, vec![preg(X0), imm(1), imm(0)])),
                Err(EncodeError::InvalidOperand { .. })
            ));
            assert!(matches!(
                encode_instruction(&mk(opcode, vec![sp(), imm(1)])),
                Err(EncodeError::InvalidOperand { index: 0, .. })
            ));
        }
        assert!(matches!(
            encode_instruction(&mk(AArch64Opcode::MOVZWi, vec![preg(X0), imm(1)])),
            Err(EncodeError::InvalidOperand { index: 0, .. })
        ));
        assert!(matches!(
            encode_instruction(&mk(AArch64Opcode::MOVZXi, vec![preg(W0), imm(1)])),
            Err(EncodeError::InvalidOperand { index: 0, .. })
        ));

        for opcode in [
            AArch64Opcode::MovI,
            AArch64Opcode::Movz,
            AArch64Opcode::Movn,
            AArch64Opcode::Movk,
        ] {
            let non_imm = mk(opcode, vec![preg(X0), preg(X1)]);
            assert!(
                matches!(
                    encode_instruction(&non_imm),
                    Err(EncodeError::InvalidOperand { index: 1, .. })
                ),
                "{opcode:?} must reject a non-immediate imm16"
            );

            if opcode != AArch64Opcode::MovI {
                let non_imm_shift = mk(opcode, vec![preg(X0), imm(1), preg(X1)]);
                assert!(
                    matches!(
                        encode_instruction(&non_imm_shift),
                        Err(EncodeError::InvalidOperand { index: 2, .. })
                    ),
                    "{opcode:?} must reject a non-immediate shift"
                );
            }
        }
    }

    #[test]
    fn test_movk() {
        let inst = mk(AArch64Opcode::Movk, vec![preg(X0), imm(0x5678)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_move_wide(1, 0b11, 0, 0x5678, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_ldr_ri() {
        // LDR X0, [X1, #8]
        let inst = mk(AArch64Opcode::LdrRI, vec![preg(X0), preg(X1), imm(8)]);
        let enc = encode_instruction(&inst).unwrap();
        // offset 8 / 8 = 1 (scaled)
        let direct = encoding::encode_load_store_ui(0b11, 0, 0b01, 1, 1, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_ldr_ri_q_scalar() {
        let base = mk(AArch64Opcode::LdrRI, vec![preg(V0), preg(X1)]);
        assert_eq!(encode_instruction(&base).unwrap(), 0x3DC00020);

        let offset = mk(AArch64Opcode::LdrRI, vec![preg(V0), preg(X1), imm(16)]);
        assert_eq!(encode_instruction(&offset).unwrap(), 0x3DC00420);
    }

    #[test]
    fn test_str_ri() {
        // STR X0, [X1]
        let inst = mk(AArch64Opcode::StrRI, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b11, 0, 0b00, 0, 1, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_str_ri_q_scalar() {
        let base = mk(AArch64Opcode::StrRI, vec![preg(V0), preg(X1)]);
        assert_eq!(encode_instruction(&base).unwrap(), 0x3D800020);

        let offset = mk(AArch64Opcode::StrRI, vec![preg(V0), preg(X1), imm(16)]);
        assert_eq!(encode_instruction(&offset).unwrap(), 0x3D800420);
    }

    #[test]
    fn test_scalar_writeback_imm9_boundaries() {
        for (opcode, expected_mode) in [
            (AArch64Opcode::LdrPreIndex, 0b11),
            (AArch64Opcode::StrPreIndex, 0b11),
            (AArch64Opcode::LdrPostIndex, 0b01),
            (AArch64Opcode::StrPostIndex, 0b01),
        ] {
            for imm9 in [-256, 255] {
                let inst = mk(opcode, vec![preg(X0), preg(X1), imm(imm9)]);
                let enc = encode_instruction(&inst).unwrap();
                assert_eq!((enc >> 12) & 0x1ff, (imm9 as u32) & 0x1ff);
                assert_eq!((enc >> 10) & 0b11, expected_mode);
            }

            for imm9 in [-257, 256] {
                let inst = mk(opcode, vec![preg(X0), preg(X1), imm(imm9)]);
                assert!(
                    matches!(
                        encode_instruction(&inst),
                        Err(EncodeError::MemEncode(
                            encoding_mem::EncodeError::Imm9OutOfRange { .. }
                        ))
                    ),
                    "{opcode:?} should reject imm9={imm9}"
                );
            }
        }
    }

    #[test]
    fn test_scalar_writeback_rejects_rt_rn_overlap() {
        for opcode in [
            AArch64Opcode::LdrPreIndex,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::StrPostIndex,
        ] {
            let inst = mk(opcode, vec![preg(X1), preg(X1), imm(8)]);
            assert!(
                matches!(
                    encode_instruction(&inst),
                    Err(EncodeError::InvalidOperand { index: 1, .. })
                ),
                "{opcode:?} should reject writeback base/transfer overlap"
            );
        }
    }

    #[test]
    fn test_scalar_writeback_allows_xzr_transfer() {
        for opcode in [
            AArch64Opcode::LdrPreIndex,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::StrPostIndex,
        ] {
            let inst = mk(opcode, vec![xzr(), preg(X1), imm(8)]);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!((enc & 0x1f), 31, "{opcode:?} should allow XZR transfer");

            let inst = mk(opcode, vec![preg(XZR), preg(X1), imm(8)]);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(
                (enc & 0x1f),
                31,
                "{opcode:?} should allow PReg(XZR) transfer"
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
            let inst = mk(opcode, vec![sp(), preg(X1), imm(8)]);
            assert!(
                matches!(
                    encode_instruction(&inst),
                    Err(EncodeError::InvalidOperand { index: 0, .. })
                ),
                "{opcode:?} should reject SP as transfer register"
            );

            let inst = mk(opcode, vec![preg(SP), preg(X1), imm(8)]);
            assert!(
                matches!(
                    encode_instruction(&inst),
                    Err(EncodeError::InvalidOperand { index: 0, .. })
                ),
                "{opcode:?} should reject PReg(SP) as transfer register"
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
            let inst = mk(opcode, vec![preg(X0), sp(), imm(8)]);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!((enc >> 5) & 0x1f, 31, "{opcode:?} should allow SP base");

            let inst = mk(opcode, vec![preg(X0), preg(SP), imm(8)]);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(
                (enc >> 5) & 0x1f,
                31,
                "{opcode:?} should allow PReg(SP) base"
            );
        }
    }

    #[test]
    fn test_scalar_writeback_rejects_non_immediate_offset() {
        let inst = mk(
            AArch64Opcode::LdrPreIndex,
            vec![preg(X0), preg(X1), preg(X2)],
        );
        assert!(matches!(
            encode_instruction(&inst),
            Err(EncodeError::InvalidOperand { index: 2, .. })
        ));
    }

    #[test]
    fn test_stp() {
        // STP X0, X1, [SP, #16]
        let inst = mk(
            AArch64Opcode::StpRI,
            vec![preg(X0), preg(X1), sp(), imm(16)],
        );
        let enc = encode_instruction(&inst).unwrap();
        // offset 16 / 8 = 2, scaled imm7 = 2
        let direct = encoding::encode_load_store_pair(0b10, 0, 0, 2, 1, 31, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_stp_d_pair() {
        // STP D8, D9, [SP, #16]
        let inst = mk(
            AArch64Opcode::StpRI,
            vec![preg(D8), preg(D9), sp(), imm(16)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_pair(0b01, 1, 0, 2, 9, 31, 8);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_stp_q_pair() {
        // STP Q0, Q1, [X9, #32]
        let inst = mk(
            AArch64Opcode::StpRI,
            vec![preg(V0), preg(V1), preg(X9), imm(32)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_pair(0b10, 1, 0, 2, 1, 9, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_ldp() {
        // LDP X0, X1, [SP]
        let inst = mk(AArch64Opcode::LdpRI, vec![preg(X0), preg(X1), sp()]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_pair(0b10, 0, 1, 0, 1, 31, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_ldp_d_pair() {
        // LDP D8, D9, [SP, #16]
        let inst = mk(
            AArch64Opcode::LdpRI,
            vec![preg(D8), preg(D9), sp(), imm(16)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_pair(0b01, 1, 1, 2, 9, 31, 8);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_ldp_q_pair() {
        // LDP Q0, Q1, [X9, #32]
        let inst = mk(
            AArch64Opcode::LdpRI,
            vec![preg(V0), preg(V1), preg(X9), imm(32)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_pair(0b10, 1, 1, 2, 1, 9, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_stp_pre_index_gpr() {
        // STP X29, X30, [SP, #-16]!  (the FP/LR prologue store)
        let inst = mk(
            AArch64Opcode::StpPreIndex,
            vec![preg(X29), preg(X30), sp(), imm(-16)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldp_stp_pre_index(
            encoding_mem::PairSize::X64,
            false,
            encoding_mem::PairOp::StorePair,
            -2, // -16 / 8
            30,
            31,
            29,
        )
        .unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_stp_pre_index_fpr_d_pair() {
        // STP D9, D8, [SP, #-16]!  — the callee-saved FPR CSA-allocating store.
        // Regression: this used to be mis-encoded as the GPR form (`stp x9, x8`),
        // silently clobbering the caller's callee-saved D8/D9. It must carry the
        // FP variant: opc = 0b01 (D64) and V = 1.
        let inst = mk(
            AArch64Opcode::StpPreIndex,
            vec![preg(D9), preg(D8), sp(), imm(-16)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldp_stp_pre_index(
            encoding_mem::PairSize::D64,
            true,
            encoding_mem::PairOp::StorePair,
            -2,
            8,
            31,
            9,
        )
        .unwrap();
        assert_eq!(enc, direct);
        // The V (SIMD/FP) bit is bit 26; it MUST be set for an FPR pair.
        assert_ne!(enc & (1 << 26), 0, "FPR pre-index STP must set the V bit");
    }

    #[test]
    fn test_ldp_post_index_fpr_d_pair() {
        // LDP D9, D8, [SP], #16  — the callee-saved FPR CSA-deallocating load.
        let inst = mk(
            AArch64Opcode::LdpPostIndex,
            vec![preg(D9), preg(D8), sp(), imm(16)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldp_stp_post_index(
            encoding_mem::PairSize::D64,
            true,
            encoding_mem::PairOp::LoadPair,
            2,
            8,
            31,
            9,
        )
        .unwrap();
        assert_eq!(enc, direct);
        assert_ne!(enc & (1 << 26), 0, "FPR post-index LDP must set the V bit");
    }

    #[test]
    fn test_pair_pre_index_mixed_class_fails_closed() {
        // A pair whose operands are not both Gpr64 or both Fpr64 must be rejected
        // rather than silently encoded with the wrong register file.
        let inst = mk(
            AArch64Opcode::StpPreIndex,
            vec![preg(X0), preg(D0), sp(), imm(-16)],
        );
        assert!(matches!(
            encode_instruction(&inst),
            Err(EncodeError::InvalidOperand { index: 0, .. })
        ));
    }

    #[test]
    fn test_stp_ri_known_instruction_words() {
        let cases = [
            // STP X0, X1, [SP, #16]
            (vec![preg(X0), preg(X1), sp(), imm(16)], 0xA90107E0),
            // STP X2, X3, [X9, #-16]
            (vec![preg(X2), preg(X3), preg(X9), imm(-16)], 0xA93F0D22),
        ];

        for (operands, expected) in cases {
            let inst = mk(AArch64Opcode::StpRI, operands);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected);
        }
    }

    #[test]
    fn test_ldp_ri_known_instruction_words() {
        let cases = [
            // LDP X0, X1, [SP]
            (vec![preg(X0), preg(X1), sp()], 0xA94007E0),
            // LDP X2, X3, [X9, #-16]
            (vec![preg(X2), preg(X3), preg(X9), imm(-16)], 0xA97F0D22),
        ];

        for (operands, expected) in cases {
            let inst = mk(AArch64Opcode::LdpRI, operands);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, expected);
        }
    }

    #[test]
    fn test_stp_ri_imm7_out_of_range_returns_err() {
        // FINDING #3: imm7 is a SIGNED 7-bit scaled field (range -64..=63).
        // For a Gpr64 pair (scale 8), an offset of 64*8 = 512 scales to 64,
        // which is OUT of range and was previously silently masked by `& 0x7F`
        // (64 & 0x7F = 64 -> wrong negative-or-aliased offset). It must now
        // return a typed InvalidOperand error rather than emit wrong bytes.
        let inst = mk(
            AArch64Opcode::StpRI,
            vec![preg(X0), preg(X1), sp(), imm(512)],
        );
        let err = encode_instruction(&inst);
        assert!(
            matches!(err, Err(EncodeError::InvalidOperand { index: 3, .. })),
            "expected InvalidOperand at index 3, got {err:?}"
        );

        // Negative out-of-range: -65*8 = -520 scales to -65 (< -64).
        let inst = mk(
            AArch64Opcode::StpRI,
            vec![preg(X0), preg(X1), sp(), imm(-520)],
        );
        assert!(matches!(
            encode_instruction(&inst),
            Err(EncodeError::InvalidOperand { index: 3, .. })
        ));

        // A huge offset that would alias back into range after `as i32`/`& 0x7F`
        // truncation must still be rejected — the check is on the i64 quotient.
        let inst = mk(
            AArch64Opcode::LdpRI,
            // 0x1_0000_0000 / 8 = 0x2000_0000; `as i32 as u32 & 0x7F` would
            // have yielded 0 (in range) — a silent-wrong zero offset.
            vec![preg(X0), preg(X1), sp(), imm(0x1_0000_0000)],
        );
        assert!(matches!(
            encode_instruction(&inst),
            Err(EncodeError::InvalidOperand { index: 3, .. })
        ));
    }

    #[test]
    fn test_stp_ldp_ri_imm7_boundaries_still_encode() {
        // The largest IN-RANGE signed scaled values (+63, -64) must still
        // encode to the identical instruction word as before the safety gate.
        // STP X0, X1, [SP, #504]  (504/8 = 63, max positive imm7)
        let inst = mk(
            AArch64Opcode::StpRI,
            vec![preg(X0), preg(X1), sp(), imm(504)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(
            enc,
            encoding::encode_load_store_pair(0b10, 0, 0, 63, 1, 31, 0)
        );

        // LDP X0, X1, [SP, #-512]  (-512/8 = -64, min negative imm7)
        let inst = mk(
            AArch64Opcode::LdpRI,
            vec![preg(X0), preg(X1), sp(), imm(-512)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(
            enc,
            encoding::encode_load_store_pair(0b10, 0, 1, (-64i32 as u32) & 0x7F, 1, 31, 0)
        );
    }

    #[test]
    fn test_b() {
        let inst = mk(AArch64Opcode::B, vec![imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_uncond_branch(0, 2);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_bcond() {
        // B.EQ <+8>: cond=0, offset=2
        let inst = mk(AArch64Opcode::BCond, vec![imm(0), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_cond_branch(2, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_bl() {
        let inst = mk(AArch64Opcode::Bl, vec![imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_uncond_branch(1, 2);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_bl_symbol_rejected_by_raw_encoder() {
        let inst = mk(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("_callee".to_string())],
        );
        assert!(matches!(
            encode_instruction(&inst),
            Err(EncodeError::InvalidOperand {
                opcode: AArch64Opcode::Bl,
                index: 0,
                ..
            })
        ));
    }

    #[test]
    fn test_blr() {
        let inst = mk(AArch64Opcode::Blr, vec![preg(X0)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_branch_reg(0b0001, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_ret() {
        let inst = mk(AArch64Opcode::Ret, vec![]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_branch_reg(0b0010, 30);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_cbz() {
        // CBZ X0, <+8>
        let inst = mk(AArch64Opcode::Cbz, vec![preg(X0), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_cmp_branch(1, 0, 2, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_cbnz() {
        // CBNZ X0, <+8>
        let inst = mk(AArch64Opcode::Cbnz, vec![preg(X0), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_cmp_branch(1, 1, 2, 0);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_tbz_bit3() {
        // TBZ X0, #3, +2
        let inst = mk(AArch64Opcode::Tbz, vec![preg(X0), imm(3), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b011011 << 25)       // op=0 (TBZ)
            | (3 << 19)       // b40=3
            | (2 << 5); // Rt=X0=0
        assert_eq!(enc, expected, "TBZ X0, #3, +2 = {enc:#010X}");
        assert_ne!(enc, NOP, "TBZ must not emit NOP");
    }

    #[test]
    fn test_tbnz_bit3() {
        let inst = mk(AArch64Opcode::Tbnz, vec![preg(X0), imm(3), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b011011 << 25)
            | (1 << 24)       // op=1 (TBNZ)
            | (3 << 19)
            | (2 << 5);
        assert_eq!(enc, expected, "TBNZ X0, #3, +2 = {enc:#010X}");
        assert_ne!(enc, NOP, "TBNZ must not emit NOP");
    }

    #[test]
    fn test_tbz_high_bit() {
        // TBZ X0, #32, +5  (bit 32: b5=1, b40=0)
        let inst = mk(AArch64Opcode::Tbz, vec![preg(X0), imm(32), imm(5)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b011011 << 25))       // b40 = 32 & 0x1F = 0
            | (5 << 5);
        assert_eq!(enc, expected, "TBZ X0, #32, +5 = {enc:#010X}");
    }

    #[test]
    fn test_tbnz_bit63() {
        // TBNZ X1, #63, +10  (bit 63: b5=1, b40=31)
        let inst = mk(AArch64Opcode::Tbnz, vec![preg(X1), imm(63), imm(10)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = (1u32 << 31)
            | (0b011011 << 25)
            | (1 << 24)
            | (31 << 19)      // b40 = 63 & 0x1F = 31
            | (10 << 5)
            | 1; // Rt=X1=1
        assert_eq!(enc, expected, "TBNZ X1, #63, +10 = {enc:#010X}");
    }

    #[test]
    fn test_tbz_known_encoding() {
        // TBZ W0, #0, +0 should encode as 0x36000000
        let inst = mk(AArch64Opcode::Tbz, vec![preg(X0), imm(0), imm(0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x36000000, "TBZ X0, #0, +0 = {enc:#010X}");
    }

    #[test]
    fn test_tbnz_known_encoding() {
        // TBNZ W0, #0, +0 should encode as 0x37000000
        let inst = mk(AArch64Opcode::Tbnz, vec![preg(X0), imm(0), imm(0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x37000000, "TBNZ X0, #0, +0 = {enc:#010X}");
    }

    #[test]
    fn test_cmp_rr() {
        let inst = mk(AArch64Opcode::CmpRR, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(1, 1, 1, 0, 1, 0, 0, 31);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_cmp_ri() {
        let inst = mk(AArch64Opcode::CmpRI, vec![preg(X0), imm(42)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_imm(1, 1, 1, 0, 42, 0, 31);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_tst() {
        let inst = mk(AArch64Opcode::Tst, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(1, 0b11, 0, 0, 1, 0, 0, 31);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_adrp() {
        let inst = mk(AArch64Opcode::Adrp, vec![preg(X0), imm(1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_adrp(1, 0).unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_fadd() {
        let inst = mk(AArch64Opcode::FaddRR, vec![preg(V0), preg(V1), preg(V2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_fp::encode_fp_arith(FpSize::Double, FpArithOp::Add, 2, 1, 0).unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_fsub() {
        let inst = mk(AArch64Opcode::FsubRR, vec![preg(V0), preg(V1), preg(V2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_fp::encode_fp_arith(FpSize::Double, FpArithOp::Sub, 2, 1, 0).unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_fmul() {
        let inst = mk(AArch64Opcode::FmulRR, vec![preg(V0), preg(V1), preg(V2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_fp::encode_fp_arith(FpSize::Double, FpArithOp::Mul, 2, 1, 0).unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_fdiv() {
        let inst = mk(AArch64Opcode::FdivRR, vec![preg(V0), preg(V1), preg(V2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_fp::encode_fp_arith(FpSize::Double, FpArithOp::Div, 2, 1, 0).unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_fcmp() {
        let inst = mk(AArch64Opcode::Fcmp, vec![preg(V0), preg(V1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_fp::encode_fcmp(FpSize::Double, FpCmpOp::Cmp, 1, 0).unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_fp_size_from_h_register() {
        let inst = mk(AArch64Opcode::FmovFprFpr, vec![preg(H0), preg(H0)]);
        assert_eq!(fp_size_from_inst(&inst), FpSize::Half);
        assert_eq!(
            fp_size_from_preg_class(trust_cg_ir::regs::preg_class(H0)),
            FpSize::Half
        );
    }

    #[test]
    fn test_fcmp_half_uses_half_precision() {
        let inst = mk(AArch64Opcode::Fcmp, vec![preg(H0), preg(H1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_fp::encode_fcmp(FpSize::Half, FpCmpOp::Cmp, 1, 0).unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_fcvt_half_precision_pairs() {
        let cases = [
            (
                AArch64Opcode::FcvtHS,
                H1,
                S0,
                FpSize::Half,
                FpSize::Single,
                1,
                0,
            ),
            (
                AArch64Opcode::FcvtHD,
                H1,
                D0,
                FpSize::Half,
                FpSize::Double,
                1,
                0,
            ),
            (
                AArch64Opcode::FcvtSH,
                S1,
                H0,
                FpSize::Single,
                FpSize::Half,
                1,
                0,
            ),
            (
                AArch64Opcode::FcvtDH,
                D0,
                H1,
                FpSize::Double,
                FpSize::Half,
                0,
                1,
            ),
        ];

        for (opcode, src, dst, src_size, dst_size, rn, rd) in cases {
            let inst = mk(opcode, vec![preg(dst), preg(src)]);
            let enc = encode_instruction(&inst).unwrap();
            let direct = encoding_fp::encode_fp_precision_cvt(src_size, dst_size, rn, rd).unwrap();
            assert_eq!(enc, direct);
        }
    }

    #[test]
    fn test_fcvtzs() {
        // FCVTZS X0, D1
        let inst = mk(AArch64Opcode::FcvtzsRR, vec![preg(X0), preg(V1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct =
            encoding_fp::encode_fp_int_conv(true, FpSize::Double, FpConvOp::FcvtzsToInt, 1, 0)
                .unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_scvtf() {
        // SCVTF D0, X1
        let inst = mk(AArch64Opcode::ScvtfRR, vec![preg(V0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct =
            encoding_fp::encode_fp_int_conv(true, FpSize::Double, FpConvOp::ScvtfToFp, 1, 0)
                .unwrap();
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_sxtw() {
        // SXTW X0, X1 = SBFM X0, X1, #0, #31
        let inst = mk(AArch64Opcode::Sxtw, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = (1u32 << 31) | (0b100110 << 23) | (1 << 22) | (31 << 10) | (1 << 5);
        assert_eq!(enc, expected, "SXTW X0, X1 = {enc:#010X}");
    }

    #[test]
    fn test_lsl_rr() {
        // LSLV X0, X1, X2
        let inst = mk(AArch64Opcode::LslRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected =
            (1u32 << 31) | (0b0_0011010110 << 21) | (2 << 16) | (0b001000 << 10) | (1 << 5);
        assert_eq!(enc, expected, "LSLV X0, X1, X2 = {enc:#010X}");
    }

    #[test]
    fn test_lsr_rr() {
        let inst = mk(AArch64Opcode::LsrRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected =
            (1u32 << 31) | (0b0_0011010110 << 21) | (2 << 16) | (0b001001 << 10) | (1 << 5);
        assert_eq!(enc, expected);
    }

    #[test]
    fn test_asr_rr() {
        let inst = mk(AArch64Opcode::AsrRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected =
            (1u32 << 31) | (0b0_0011010110 << 21) | (2 << 16) | (0b001010 << 10) | (1 << 5);
        assert_eq!(enc, expected);
    }

    #[test]
    fn test_br() {
        let inst = mk(AArch64Opcode::Br, vec![preg(X30)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_branch_reg(0b0000, 30);
        assert_eq!(enc, direct);
    }

    #[test]
    fn test_pseudos_emit_nop() {
        for opcode in [
            AArch64Opcode::Phi,
            AArch64Opcode::StackAlloc,
            AArch64Opcode::Nop,
        ] {
            let inst = mk(opcode, vec![]);
            let enc = encode_instruction(&inst).unwrap();
            assert_eq!(enc, NOP, "{opcode:?} should emit NOP");
        }
    }

    #[test]
    fn test_all_opcodes_handled() {
        // Verify that every opcode in the enum produces a result (not an error).
        // We use minimal operands — the point is to verify dispatch coverage,
        // not encoding correctness (that's tested per-opcode above).
        let test_cases: Vec<(AArch64Opcode, Vec<MachOperand>)> = vec![
            (AArch64Opcode::AddRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::AddRI, vec![preg(X0), preg(X1), imm(0)]),
            (AArch64Opcode::SubRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::SubRI, vec![preg(X0), preg(X1), imm(0)]),
            (AArch64Opcode::MulRR, vec![preg(X0), preg(X1), preg(X2)]),
            (
                AArch64Opcode::Msub,
                vec![preg(X0), preg(X1), preg(X2), preg(X9)],
            ),
            (AArch64Opcode::Smull, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::Umull, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::SDiv, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::UDiv, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::Neg, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::AndRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::OrrRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::EorRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::OrnRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::LslRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::LsrRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::AsrRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::LslRI, vec![preg(X0), preg(X1), imm(3)]),
            (AArch64Opcode::LsrRI, vec![preg(X0), preg(X1), imm(3)]),
            (AArch64Opcode::AsrRI, vec![preg(X0), preg(X1), imm(3)]),
            (AArch64Opcode::RorRI, vec![preg(X0), preg(X1), imm(3)]),
            (AArch64Opcode::Rbit, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::CmpRR, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::CmpRI, vec![preg(X0), imm(0)]),
            (AArch64Opcode::Tst, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::MovR, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::CSet, vec![preg(X0), imm(1)]), // CSET W0, NE
            (AArch64Opcode::MovI, vec![preg(X0), imm(0)]),
            (AArch64Opcode::Movz, vec![preg(X0), imm(0)]),
            (AArch64Opcode::Movk, vec![preg(X0), imm(0)]),
            (AArch64Opcode::LdrRI, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::StrRI, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::LdrbRI, vec![preg(W0), preg(X1)]),
            (AArch64Opcode::LdrhRI, vec![preg(W0), preg(X1)]),
            (AArch64Opcode::LdrsbRI, vec![preg(W0), preg(X1)]),
            (AArch64Opcode::LdrshRI, vec![preg(W0), preg(X1)]),
            (AArch64Opcode::StrbRI, vec![preg(W0), preg(X1)]),
            (AArch64Opcode::StrhRI, vec![preg(W0), preg(X1)]),
            (AArch64Opcode::LdrLiteral, vec![preg(X0), imm(0)]),
            (AArch64Opcode::LdpRI, vec![preg(X0), preg(X1), sp()]),
            (AArch64Opcode::StpRI, vec![preg(X0), preg(X1), sp()]),
            (AArch64Opcode::B, vec![imm(0)]),
            (AArch64Opcode::BCond, vec![imm(0)]),
            (AArch64Opcode::Cbz, vec![preg(X0)]),
            (AArch64Opcode::Cbnz, vec![preg(X0)]),
            (AArch64Opcode::Tbz, vec![preg(X0), imm(0)]),
            (AArch64Opcode::Tbnz, vec![preg(X0), imm(0)]),
            (AArch64Opcode::Br, vec![preg(X0)]),
            (AArch64Opcode::Bl, vec![imm(0)]),
            (AArch64Opcode::Blr, vec![preg(X0)]),
            (AArch64Opcode::Ret, vec![]),
            (AArch64Opcode::Sxtw, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::Uxtw, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::Sxtb, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::Sxth, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::Uxtb, vec![preg(W0), preg(W1)]),
            (AArch64Opcode::Uxth, vec![preg(W0), preg(W1)]),
            (
                AArch64Opcode::Ubfm,
                vec![preg(X0), preg(X1), imm(0), imm(7)],
            ),
            (
                AArch64Opcode::Sbfm,
                vec![preg(X0), preg(X1), imm(0), imm(7)],
            ),
            (AArch64Opcode::Bfm, vec![preg(X0), preg(X1), imm(0), imm(7)]),
            (AArch64Opcode::LdrRO, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::StrRO, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::LdrGot, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::LdrTlvp, vec![preg(X0), preg(X1)]),
            (AArch64Opcode::FaddRR, vec![preg(V0), preg(V1), preg(V2)]),
            (AArch64Opcode::FsubRR, vec![preg(V0), preg(V1), preg(V2)]),
            (AArch64Opcode::FmulRR, vec![preg(V0), preg(V1), preg(V2)]),
            (AArch64Opcode::FdivRR, vec![preg(V0), preg(V1), preg(V2)]),
            (AArch64Opcode::FnegRR, vec![preg(V0), preg(V1)]),
            (AArch64Opcode::FabsRR, vec![preg(V0), preg(V1)]),
            (AArch64Opcode::FsqrtRR, vec![preg(V0), preg(V1)]),
            // Scalar FMOV has no Q-register form; the encoder now fail-closes
            // on V/Q operands (Q copies go through NeonOrrV), so exercise the
            // dispatch with the D form.
            (AArch64Opcode::FmovFprFpr, vec![preg(D0), preg(D1)]),
            (AArch64Opcode::Fcmp, vec![preg(V0), preg(V1)]),
            (AArch64Opcode::FcvtzsRR, vec![preg(X0), preg(V1)]),
            (AArch64Opcode::ScvtfRR, vec![preg(V0), preg(X1)]),
            (AArch64Opcode::Adrp, vec![preg(X0), imm(0)]),
            (AArch64Opcode::Adr, vec![preg(X0), imm(0)]),
            (AArch64Opcode::LdrswRO, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::AddPCRel, vec![preg(X0), preg(X1), imm(0)]),
            (AArch64Opcode::AddsRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::AddsRI, vec![preg(X0), preg(X1), imm(0)]),
            (AArch64Opcode::SubsRR, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::SubsRI, vec![preg(X0), preg(X1), imm(0)]),
            // i128 multi-register arithmetic
            (AArch64Opcode::Adc, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::Sbc, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::Umulh, vec![preg(X0), preg(X1), preg(X2)]),
            (AArch64Opcode::Smulh, vec![preg(X0), preg(X1), preg(X2)]),
            (
                AArch64Opcode::Madd,
                vec![preg(X0), preg(X1), preg(X2), preg(X3)],
            ),
            (AArch64Opcode::Brk, vec![]),
            (AArch64Opcode::TrapOverflow, vec![]),
            (AArch64Opcode::TrapBoundsCheck, vec![]),
            (AArch64Opcode::TrapNull, vec![]),
            (AArch64Opcode::TrapDivZero, vec![]),
            (AArch64Opcode::TrapShiftRange, vec![]),
            (AArch64Opcode::Retain, vec![]),
            (AArch64Opcode::Release, vec![]),
            (AArch64Opcode::Phi, vec![]),
            (AArch64Opcode::StackAlloc, vec![]),
            (AArch64Opcode::Nop, vec![]),
        ];

        for (opcode, ops) in test_cases {
            let inst = mk(opcode, ops);
            let result = encode_instruction(&inst);
            assert!(
                result.is_ok(),
                "Opcode {opcode:?} should encode successfully, got: {result:?}"
            );
        }
    }

    // =========================================================================
    // 32-bit encoding tests — verify sf=0 for W-register operands
    // =========================================================================

    #[test]
    fn test_sf_from_operand_w_register() {
        // W0 (encoding 32) should produce sf=0
        let inst = mk(AArch64Opcode::AddRR, vec![preg(W0), preg(W1), preg(W2)]);
        assert_eq!(sf_from_operand(&inst, 0), 0, "W0 should produce sf=0");

        // X0 (encoding 0) should produce sf=1
        let inst = mk(AArch64Opcode::AddRR, vec![preg(X0), preg(X1), preg(X2)]);
        assert_eq!(sf_from_operand(&inst, 0), 1, "X0 should produce sf=1");
    }

    #[test]
    fn test_add_rr_32bit() {
        // ADD W0, W1, W2 — must have sf=0 (bit 31 = 0)
        let inst = mk(AArch64Opcode::AddRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(0, 0, 0, 0, 2, 0, 1, 0);
        assert_eq!(
            enc, direct,
            "ADD W0, W1, W2: unified={enc:#010X}, direct={direct:#010X}"
        );
        // Verify bit 31 (sf) is 0
        assert_eq!(enc >> 31, 0, "ADD W0, W1, W2 must have sf=0 (bit 31 = 0)");
    }

    #[test]
    fn test_add_rr_64bit_has_sf_1() {
        // ADD X0, X1, X2 — must have sf=1 (bit 31 = 1)
        let inst = mk(AArch64Opcode::AddRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc >> 31, 1, "ADD X0, X1, X2 must have sf=1 (bit 31 = 1)");
    }

    #[test]
    fn test_add_ri_32bit() {
        // ADD W0, W1, #42 — sf=0
        let inst = mk(AArch64Opcode::AddRI, vec![preg(W0), preg(W1), imm(42)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_imm(0, 0, 0, 0, 42, 1, 0);
        assert_eq!(enc, direct, "ADD W0, W1, #42");
        assert_eq!(enc >> 31, 0, "ADD W0, W1, #42 must have sf=0");
    }

    #[test]
    fn test_sub_rr_32bit() {
        // SUB W0, W1, W2 — sf=0
        let inst = mk(AArch64Opcode::SubRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(0, 1, 0, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct, "SUB W0, W1, W2");
        assert_eq!(enc >> 31, 0, "SUB W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_sub_ri_32bit() {
        // SUB W0, W1, #10 — sf=0
        let inst = mk(AArch64Opcode::SubRI, vec![preg(W0), preg(W1), imm(10)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_imm(0, 1, 0, 0, 10, 1, 0);
        assert_eq!(enc, direct, "SUB W0, W1, #10");
        assert_eq!(enc >> 31, 0, "SUB W0, W1, #10 must have sf=0");
    }

    #[test]
    fn test_and_rr_32bit() {
        // AND W0, W1, W2 — sf=0
        let inst = mk(AArch64Opcode::AndRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(0, 0b00, 0, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct, "AND W0, W1, W2");
        assert_eq!(enc >> 31, 0, "AND W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_orr_rr_32bit() {
        // ORR W0, W1, W2 — sf=0
        let inst = mk(AArch64Opcode::OrrRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(0, 0b01, 0, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct, "ORR W0, W1, W2");
        assert_eq!(enc >> 31, 0, "ORR W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_eor_rr_32bit() {
        // EOR W0, W1, W2 — sf=0
        let inst = mk(AArch64Opcode::EorRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(0, 0b10, 0, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct, "EOR W0, W1, W2");
        assert_eq!(enc >> 31, 0, "EOR W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_mul_rr_32bit() {
        // MUL W0, W1, W2 = MADD W0, W1, W2, WZR — sf=0
        let inst = mk(AArch64Opcode::MulRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        // Expected: sf=0, 00 11011 000 Rm=2 0 Ra=31 Rn=1 Rd=0
        let expected = (0b11011 << 24) | (2 << 16) | (31 << 10) | (1 << 5);
        assert_eq!(enc, expected, "MUL W0, W1, W2 = {enc:#010X}");
        assert_eq!(enc >> 31, 0, "MUL W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_sdiv_32bit() {
        // SDIV W0, W1, W2 — sf=0
        let inst = mk(AArch64Opcode::SDiv, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b0_0011010110 << 21) | (2 << 16) | (0b000011 << 10) | (1 << 5);
        assert_eq!(enc, expected, "SDIV W0, W1, W2 = {enc:#010X}");
        assert_eq!(enc >> 31, 0, "SDIV W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_neg_32bit() {
        // NEG W0, W1 = SUB W0, WZR, W1 — sf=0
        let inst = mk(AArch64Opcode::Neg, vec![preg(W0), preg(W1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(0, 1, 0, 0, 1, 0, 31, 0);
        assert_eq!(enc, direct, "NEG W0, W1");
        assert_eq!(enc >> 31, 0, "NEG W0, W1 must have sf=0");
    }

    #[test]
    fn test_mov_r_32bit() {
        // MOV W0, W1 = ORR W0, WZR, W1 — sf=0
        let inst = mk(AArch64Opcode::MovR, vec![preg(W0), preg(W1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(0, 0b01, 0, 0, 1, 0, 31, 0);
        assert_eq!(enc, direct, "MOV W0, W1");
        assert_eq!(enc >> 31, 0, "MOV W0, W1 must have sf=0");
    }

    #[test]
    fn test_uxtw_uses_32bit_write_even_with_x_operands() {
        let inst = mk(AArch64Opcode::Uxtw, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(0, 0b01, 0, 0, 1, 0, 31, 0);
        assert_eq!(enc, direct, "UXTW X0, X1 must encode as MOV W0, W1");
        assert_eq!(enc >> 31, 0, "UXTW must use sf=0 to clear high bits");
        assert_eq!(enc, 0x2A0103E0);
    }

    #[test]
    fn test_movz_32bit() {
        // MOVZ W0, #0x1234 — sf=0
        let inst = mk(AArch64Opcode::Movz, vec![preg(W0), imm(0x1234)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_move_wide(0, 0b10, 0, 0x1234, 0);
        assert_eq!(enc, direct, "MOVZ W0, #0x1234");
        assert_eq!(enc >> 31, 0, "MOVZ W0, #0x1234 must have sf=0");
    }

    #[test]
    fn test_cmp_rr_32bit() {
        // CMP W0, W1 = SUBS WZR, W0, W1 — sf=0
        let inst = mk(AArch64Opcode::CmpRR, vec![preg(W0), preg(W1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(0, 1, 1, 0, 1, 0, 0, 31);
        assert_eq!(enc, direct, "CMP W0, W1");
        assert_eq!(enc >> 31, 0, "CMP W0, W1 must have sf=0");
    }

    #[test]
    fn test_cmp_ri_32bit() {
        // CMP W0, #42 = SUBS WZR, W0, #42 — sf=0
        let inst = mk(AArch64Opcode::CmpRI, vec![preg(W0), imm(42)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_imm(0, 1, 1, 0, 42, 0, 31);
        assert_eq!(enc, direct, "CMP W0, #42");
        assert_eq!(enc >> 31, 0, "CMP W0, #42 must have sf=0");
    }

    #[test]
    fn test_tst_32bit() {
        // TST W0, W1 = ANDS WZR, W0, W1 — sf=0
        let inst = mk(AArch64Opcode::Tst, vec![preg(W0), preg(W1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(0, 0b11, 0, 0, 1, 0, 0, 31);
        assert_eq!(enc, direct, "TST W0, W1");
        assert_eq!(enc >> 31, 0, "TST W0, W1 must have sf=0");
    }

    #[test]
    fn test_adds_rr_32bit() {
        // ADDS W0, W1, W2 — sf=0
        let inst = mk(AArch64Opcode::AddsRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(0, 0, 1, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct, "ADDS W0, W1, W2");
        assert_eq!(enc >> 31, 0, "ADDS W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_subs_rr_32bit() {
        // SUBS W0, W1, W2 — sf=0
        let inst = mk(AArch64Opcode::SubsRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_add_sub_shifted_reg(0, 1, 1, 0, 2, 0, 1, 0);
        assert_eq!(enc, direct, "SUBS W0, W1, W2");
        assert_eq!(enc >> 31, 0, "SUBS W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_lsl_rr_32bit() {
        // LSLV W0, W1, W2 — sf=0
        let inst = mk(AArch64Opcode::LslRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b0_0011010110 << 21) | (2 << 16) | (0b001000 << 10) | (1 << 5);
        assert_eq!(enc, expected, "LSLV W0, W1, W2 = {enc:#010X}");
        assert_eq!(enc >> 31, 0, "LSLV W0, W1, W2 must have sf=0");
    }

    #[test]
    fn test_cbz_32bit() {
        // CBZ W0, <+8> — sf=0
        let inst = mk(AArch64Opcode::Cbz, vec![preg(W0), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_cmp_branch(0, 0, 2, 0);
        assert_eq!(enc, direct, "CBZ W0, <+8>");
        assert_eq!(enc >> 31, 0, "CBZ W0, <+8> must have sf=0");
    }

    #[test]
    fn test_cbnz_32bit() {
        // CBNZ W0, <+8> — sf=0
        let inst = mk(AArch64Opcode::Cbnz, vec![preg(W0), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_cmp_branch(0, 1, 2, 0);
        assert_eq!(enc, direct, "CBNZ W0, <+8>");
        assert_eq!(enc >> 31, 0, "CBNZ W0, <+8> must have sf=0");
    }

    #[test]
    fn test_lsl_ri_32bit() {
        // LSL W0, W1, #3 — sf=0, regsize=32
        // UBFM W0, W1, #(-3 MOD 32)=29, #(32-1-3)=28
        let inst = mk(AArch64Opcode::LslRI, vec![preg(W0), preg(W1), imm(3)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc >> 31, 0, "LSL W0, W1, #3 must have sf=0");
        // N bit (bit 22) must be 0 for 32-bit
        assert_eq!((enc >> 22) & 1, 0, "LSL W0 must have N=0 for 32-bit");
    }

    #[test]
    fn test_fp_size_from_s_register() {
        // FADD S0, S1, S2 should use Single precision
        let inst = mk(AArch64Opcode::FaddRR, vec![preg(S0), preg(S1), preg(S2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_fp::encode_fp_arith(FpSize::Single, FpArithOp::Add, 2, 1, 0).unwrap();
        assert_eq!(enc, direct, "FADD S0, S1, S2 should use Single precision");
    }

    // =========================================================================
    // Byte/halfword load/store encoding tests
    // =========================================================================

    #[test]
    fn test_ldrb_ri() {
        // LDRB W0, [X1, #0] — size=00, V=0, opc=01
        let inst = mk(AArch64Opcode::LdrbRI, vec![preg(W0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b00, 0, 0b01, 0, 1, 0);
        assert_eq!(enc, direct, "LDRB W0, [X1] = {enc:#010X}");
        // Verify size field (bits 31:30) = 00
        assert_eq!((enc >> 30) & 0b11, 0b00, "LDRB must have size=00");
        // Verify opc field (bits 23:22) = 01 (load)
        assert_eq!((enc >> 22) & 0b11, 0b01, "LDRB must have opc=01");
    }

    #[test]
    fn test_ldrb_ri_with_offset() {
        // LDRB W0, [X1, #5] — byte-aligned offset, no scaling needed
        let inst = mk(AArch64Opcode::LdrbRI, vec![preg(W0), preg(X1), imm(5)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b00, 0, 0b01, 5, 1, 0);
        assert_eq!(enc, direct, "LDRB W0, [X1, #5] = {enc:#010X}");
    }

    #[test]
    fn test_ldrh_ri() {
        // LDRH W0, [X1, #0] — size=01, V=0, opc=01
        let inst = mk(AArch64Opcode::LdrhRI, vec![preg(W0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b01, 0, 0b01, 0, 1, 0);
        assert_eq!(enc, direct, "LDRH W0, [X1] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b01, "LDRH must have size=01");
        assert_eq!((enc >> 22) & 0b11, 0b01, "LDRH must have opc=01");
    }

    #[test]
    fn test_ldrh_ri_with_offset() {
        // LDRH W0, [X1, #4] — halfword offset 4 / 2 = 2 (scaled)
        let inst = mk(AArch64Opcode::LdrhRI, vec![preg(W0), preg(X1), imm(4)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b01, 0, 0b01, 2, 1, 0);
        assert_eq!(enc, direct, "LDRH W0, [X1, #4] = {enc:#010X}");
    }

    #[test]
    fn test_ldrsb_ri() {
        // LDRSB W0, [X1, #0] — size=00, V=0, opc=11 (sign-extend to 32-bit)
        let inst = mk(AArch64Opcode::LdrsbRI, vec![preg(W0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b00, 0, 0b11, 0, 1, 0);
        assert_eq!(enc, direct, "LDRSB W0, [X1] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b00, "LDRSB must have size=00");
        assert_eq!((enc >> 22) & 0b11, 0b11, "LDRSB to W must have opc=11");
    }

    #[test]
    fn test_ldrsh_ri() {
        // LDRSH W0, [X1, #0] — size=01, V=0, opc=11 (sign-extend to 32-bit)
        let inst = mk(AArch64Opcode::LdrshRI, vec![preg(W0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b01, 0, 0b11, 0, 1, 0);
        assert_eq!(enc, direct, "LDRSH W0, [X1] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b01, "LDRSH must have size=01");
        assert_eq!((enc >> 22) & 0b11, 0b11, "LDRSH to W must have opc=11");
    }

    #[test]
    fn test_ldrsb_ri_x_dst_is_64bit_sext() {
        // LDRSB X0, [X1, #0] — a Gpr64 destination selects opc=10 (sign-extend
        // to 64) while still reading exactly 1 byte (size=00). This is the width
        // the ext-addr sext fold emits when it folds a `Sxtb Xd, Wt` (64-bit).
        let inst = mk(AArch64Opcode::LdrsbRI, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b00, 0, 0b10, 0, 1, 0);
        assert_eq!(enc, direct, "LDRSB X0, [X1] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b00, "LDRSB must have size=00");
        assert_eq!((enc >> 22) & 0b11, 0b10, "LDRSB to X must have opc=10");
    }

    #[test]
    fn test_ldrsh_ri_x_dst_is_64bit_sext() {
        // LDRSH X0, [X1, #0] — Gpr64 destination -> opc=10 (sign-extend to 64),
        // size=01 (still reads 2 bytes).
        let inst = mk(AArch64Opcode::LdrshRI, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b01, 0, 0b10, 0, 1, 0);
        assert_eq!(enc, direct, "LDRSH X0, [X1] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b01, "LDRSH must have size=01");
        assert_eq!((enc >> 22) & 0b11, 0b10, "LDRSH to X must have opc=10");
    }

    #[test]
    fn test_strb_ri() {
        // STRB W0, [X1, #0] — size=00, V=0, opc=00
        let inst = mk(AArch64Opcode::StrbRI, vec![preg(W0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b00, 0, 0b00, 0, 1, 0);
        assert_eq!(enc, direct, "STRB W0, [X1] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b00, "STRB must have size=00");
        assert_eq!((enc >> 22) & 0b11, 0b00, "STRB must have opc=00");
    }

    #[test]
    fn test_strb_ri_with_offset() {
        // STRB W0, [X1, #3] — byte-aligned offset
        let inst = mk(AArch64Opcode::StrbRI, vec![preg(W0), preg(X1), imm(3)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b00, 0, 0b00, 3, 1, 0);
        assert_eq!(enc, direct, "STRB W0, [X1, #3] = {enc:#010X}");
    }

    #[test]
    fn test_strh_ri() {
        // STRH W0, [X1, #0] — size=01, V=0, opc=00
        let inst = mk(AArch64Opcode::StrhRI, vec![preg(W0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b01, 0, 0b00, 0, 1, 0);
        assert_eq!(enc, direct, "STRH W0, [X1] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b01, "STRH must have size=01");
        assert_eq!((enc >> 22) & 0b11, 0b00, "STRH must have opc=00");
    }

    #[test]
    fn test_strh_ri_with_offset() {
        // STRH W0, [X1, #6] — halfword offset 6 / 2 = 3 (scaled)
        let inst = mk(AArch64Opcode::StrhRI, vec![preg(W0), preg(X1), imm(6)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b01, 0, 0b00, 3, 1, 0);
        assert_eq!(enc, direct, "STRH W0, [X1, #6] = {enc:#010X}");
    }

    // =========================================================================
    // Immediate shift encoding tests — verified against system assembler
    // (xcrun as -arch arm64) ground truth. Fixes #134.
    //
    // LslRI/LsrRI/AsrRI are encoded via UBFM/SBFM bitfield instructions:
    //   LSL Rd, Rn, #shift  = UBFM Rd, Rn, #(-shift MOD regsize), #(regsize-1-shift)
    //   LSR Rd, Rn, #shift  = UBFM Rd, Rn, #shift, #(regsize-1)
    //   ASR Rd, Rn, #shift  = SBFM Rd, Rn, #shift, #(regsize-1)
    // =========================================================================

    #[test]
    fn test_lsl_ri_64bit_ground_truth() {
        // LSL X0, X1, #2 — verified: 0xD37EF420 (xcrun as)
        // = UBFM X0, X1, #62, #61
        let inst = mk(AArch64Opcode::LslRI, vec![preg(X0), preg(X1), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD37EF420, "LSL X0, X1, #2 = {enc:#010X}");
        // Must NOT be NOP
        assert_ne!(enc, NOP, "LSL X0, X1, #2 must not emit NOP");
    }

    #[test]
    fn test_lsr_ri_64bit_ground_truth() {
        // LSR X0, X1, #2 — verified: 0xD342FC20 (xcrun as)
        // = UBFM X0, X1, #2, #63
        let inst = mk(AArch64Opcode::LsrRI, vec![preg(X0), preg(X1), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD342FC20, "LSR X0, X1, #2 = {enc:#010X}");
        assert_ne!(enc, NOP, "LSR X0, X1, #2 must not emit NOP");
    }

    #[test]
    fn test_asr_ri_64bit_ground_truth() {
        // ASR X0, X1, #2 — verified: 0x9342FC20 (xcrun as)
        // = SBFM X0, X1, #2, #63
        let inst = mk(AArch64Opcode::AsrRI, vec![preg(X0), preg(X1), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9342FC20, "ASR X0, X1, #2 = {enc:#010X}");
        assert_ne!(enc, NOP, "ASR X0, X1, #2 must not emit NOP");
    }

    #[test]
    fn test_ror_ri_64bit_extr_alias_ground_truth() {
        // ROR X0, X1, #2 = EXTR X0, X1, X1, #2
        let inst = mk(AArch64Opcode::RorRI, vec![preg(X0), preg(X1), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x93C10820, "ROR X0, X1, #2 = {enc:#010X}");
        assert_ne!(enc, NOP, "ROR X0, X1, #2 must not emit NOP");
    }

    #[test]
    fn test_rbit_ground_truth() {
        let w = mk(AArch64Opcode::Rbit, vec![preg(W0), preg(W1)]);
        let x = mk(AArch64Opcode::Rbit, vec![preg(X2), preg(X3)]);

        assert_eq!(encode_instruction(&w).unwrap(), 0x5AC00020);
        assert_eq!(encode_instruction(&x).unwrap(), 0xDAC00062);
    }

    #[test]
    fn test_lsl_ri_32bit_ground_truth() {
        // LSL W0, W1, #3 — verified: 0x531D7020 (xcrun as)
        // = UBFM W0, W1, #29, #28
        let inst = mk(AArch64Opcode::LslRI, vec![preg(W0), preg(W1), imm(3)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x531D7020, "LSL W0, W1, #3 = {enc:#010X}");
        assert_ne!(enc, NOP, "LSL W0, W1, #3 must not emit NOP");
        assert_eq!(enc >> 31, 0, "LSL W0 must have sf=0");
        assert_eq!((enc >> 22) & 1, 0, "LSL W0 must have N=0 for 32-bit");
    }

    #[test]
    fn test_lsr_ri_32bit_ground_truth() {
        // LSR W0, W1, #3 — verified: 0x53037C20 (xcrun as)
        // = UBFM W0, W1, #3, #31
        let inst = mk(AArch64Opcode::LsrRI, vec![preg(W0), preg(W1), imm(3)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x53037C20, "LSR W0, W1, #3 = {enc:#010X}");
        assert_ne!(enc, NOP, "LSR W0, W1, #3 must not emit NOP");
        assert_eq!(enc >> 31, 0, "LSR W0 must have sf=0");
    }

    #[test]
    fn test_asr_ri_32bit_ground_truth() {
        // ASR W0, W1, #3 — verified: 0x13037C20 (xcrun as)
        // = SBFM W0, W1, #3, #31
        let inst = mk(AArch64Opcode::AsrRI, vec![preg(W0), preg(W1), imm(3)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x13037C20, "ASR W0, W1, #3 = {enc:#010X}");
        assert_ne!(enc, NOP, "ASR W0, W1, #3 must not emit NOP");
        assert_eq!(enc >> 31, 0, "ASR W0 must have sf=0");
    }

    #[test]
    fn test_ror_ri_32bit_extr_alias_ground_truth() {
        // ROR W0, W1, #3 = EXTR W0, W1, W1, #3
        let inst = mk(AArch64Opcode::RorRI, vec![preg(W0), preg(W1), imm(3)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x13810C20, "ROR W0, W1, #3 = {enc:#010X}");
        assert_ne!(enc, NOP, "ROR W0, W1, #3 must not emit NOP");
        assert_eq!(enc >> 31, 0, "ROR W0 must have sf=0");
        assert_eq!((enc >> 22) & 1, 0, "ROR W0 must have N=0 for 32-bit");
    }

    #[test]
    fn test_lsl_ri_ubfm_field_decomposition_64bit() {
        // Verify UBFM field placement for LSL X0, X1, #2
        let inst = mk(AArch64Opcode::LslRI, vec![preg(X0), preg(X1), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!((enc >> 31) & 1, 1, "sf=1 for 64-bit");
        assert_eq!((enc >> 29) & 0b11, 0b10, "opc=10 for UBFM");
        assert_eq!((enc >> 23) & 0b111111, 0b100110, "fixed bits");
        assert_eq!((enc >> 22) & 1, 1, "N=1 for 64-bit");
        assert_eq!((enc >> 16) & 0x3F, 62, "immr=(-2 MOD 64)=62");
        assert_eq!((enc >> 10) & 0x3F, 61, "imms=(63-2)=61");
        assert_eq!((enc >> 5) & 0x1F, 1, "Rn=X1");
        assert_eq!(enc & 0x1F, 0, "Rd=X0");
    }

    #[test]
    fn test_lsr_ri_ubfm_field_decomposition_64bit() {
        // Verify UBFM field placement for LSR X0, X1, #2
        let inst = mk(AArch64Opcode::LsrRI, vec![preg(X0), preg(X1), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!((enc >> 31) & 1, 1, "sf=1 for 64-bit");
        assert_eq!((enc >> 29) & 0b11, 0b10, "opc=10 for UBFM");
        assert_eq!((enc >> 22) & 1, 1, "N=1 for 64-bit");
        assert_eq!((enc >> 16) & 0x3F, 2, "immr=shift=2");
        assert_eq!((enc >> 10) & 0x3F, 63, "imms=63 for 64-bit");
        assert_eq!((enc >> 5) & 0x1F, 1, "Rn=X1");
        assert_eq!(enc & 0x1F, 0, "Rd=X0");
    }

    #[test]
    fn test_asr_ri_sbfm_field_decomposition_64bit() {
        // Verify SBFM field placement for ASR X0, X1, #2
        let inst = mk(AArch64Opcode::AsrRI, vec![preg(X0), preg(X1), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!((enc >> 31) & 1, 1, "sf=1 for 64-bit");
        assert_eq!((enc >> 29) & 0b11, 0b00, "opc=00 for SBFM");
        assert_eq!((enc >> 22) & 1, 1, "N=1 for 64-bit");
        assert_eq!((enc >> 16) & 0x3F, 2, "immr=shift=2");
        assert_eq!((enc >> 10) & 0x3F, 63, "imms=63 for 64-bit");
        assert_eq!((enc >> 5) & 0x1F, 1, "Rn=X1");
        assert_eq!(enc & 0x1F, 0, "Rd=X0");
    }

    #[test]
    fn test_zero_immediate_shifts_encode_as_mov_alias() {
        for opcode in [
            AArch64Opcode::LslRI,
            AArch64Opcode::LsrRI,
            AArch64Opcode::AsrRI,
            AArch64Opcode::RorRI,
        ] {
            let shift = mk(opcode, vec![preg(X0), preg(X1), imm(0)]);
            let mov = mk(AArch64Opcode::MovR, vec![preg(X0), preg(X1)]);
            assert_eq!(
                encode_instruction(&shift).unwrap(),
                encode_instruction(&mov).unwrap(),
                "{opcode:?} X0, X1, #0 should encode as MOV X0, X1"
            );

            let shift = mk(opcode, vec![preg(W0), preg(W1), imm(0)]);
            let mov = mk(AArch64Opcode::MovR, vec![preg(W0), preg(W1)]);
            assert_eq!(
                encode_instruction(&shift).unwrap(),
                encode_instruction(&mov).unwrap(),
                "{opcode:?} W0, W1, #0 should encode as MOV W0, W1"
            );
        }
    }

    #[test]
    fn test_shift_ri_boundary_values() {
        // LSL X0, X1, #0 (no shift) — should encode as a register move, not NOP.
        let inst = mk(AArch64Opcode::LslRI, vec![preg(X0), preg(X1), imm(0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_ne!(enc, NOP, "LSL X0, X1, #0 must not emit NOP");

        // LSL X0, X1, #63 (max shift for 64-bit)
        let inst = mk(AArch64Opcode::LslRI, vec![preg(X0), preg(X1), imm(63)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_ne!(enc, NOP, "LSL X0, X1, #63 must not emit NOP");
        assert_eq!((enc >> 16) & 0x3F, 1, "immr=(-63 MOD 64)=1");
        assert_eq!((enc >> 10) & 0x3F, 0, "imms=(63-63)=0");

        // LSR X0, X1, #63 (max shift)
        let inst = mk(AArch64Opcode::LsrRI, vec![preg(X0), preg(X1), imm(63)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_ne!(enc, NOP, "LSR X0, X1, #63 must not emit NOP");
        assert_eq!((enc >> 16) & 0x3F, 63, "immr=63");
        assert_eq!((enc >> 10) & 0x3F, 63, "imms=63");
    }

    // =========================================================================
    // Bitfield move instruction tests (UBFM, SBFM, BFM) — issue #137
    // =========================================================================

    #[test]
    fn test_ubfm_64bit() {
        // UBFM X0, X1, #0, #7 — extract bits [7:0] (alias: UXTB X0, X1)
        // ARM ARM: sf=1 opc=10 100110 N=1 immr=0 imms=7 Rn=1 Rd=0
        let inst = mk(
            AArch64Opcode::Ubfm,
            vec![preg(X0), preg(X1), imm(0), imm(7)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b10 << 29)
            | (0b100110 << 23)
            | (1 << 22)) // immr=0
            | (7 << 10) // imms=7
            | (1 << 5);
        assert_eq!(enc, expected, "UBFM X0, X1, #0, #7 = {enc:#010X}");
        // Verify fixed field: bits [28:23] = 100110
        assert_eq!((enc >> 23) & 0x3F, 0b100110);
    }

    #[test]
    fn test_ubfm_32bit() {
        // UBFM W0, W1, #0, #7 — sf=0, N=0
        let inst = mk(
            AArch64Opcode::Ubfm,
            vec![preg(W0), preg(W1), imm(0), imm(7)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc >> 31, 0, "UBFM W0 must have sf=0");
        assert_eq!((enc >> 22) & 1, 0, "UBFM W0 must have N=0 for 32-bit");
        assert_eq!((enc >> 29) & 0b11, 0b10, "UBFM opc must be 10");
    }

    #[test]
    fn test_ubfm_lsr_alias() {
        // LSR X0, X1, #3 is encoded as UBFM X0, X1, #3, #63
        // Verify that UBFM with immr=3, imms=63 matches the LSR encoding.
        let ubfm = mk(
            AArch64Opcode::Ubfm,
            vec![preg(X0), preg(X1), imm(3), imm(63)],
        );
        let lsr = mk(AArch64Opcode::LsrRI, vec![preg(X0), preg(X1), imm(3)]);
        let ubfm_enc = encode_instruction(&ubfm).unwrap();
        let lsr_enc = encode_instruction(&lsr).unwrap();
        assert_eq!(
            ubfm_enc, lsr_enc,
            "UBFM X0, X1, #3, #63 must match LSR X0, X1, #3"
        );
    }

    #[test]
    fn test_sbfm_64bit() {
        // SBFM X0, X1, #0, #31 — sign-extend bits [31:0] (alias: SXTW X0, X1)
        // ARM ARM: sf=1 opc=00 100110 N=1 immr=0 imms=31 Rn=1 Rd=0
        let inst = mk(
            AArch64Opcode::Sbfm,
            vec![preg(X0), preg(X1), imm(0), imm(31)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b100110 << 23)
            | (1 << 22)) // immr=0
            | (31 << 10) // imms=31
            | (1 << 5);
        assert_eq!(enc, expected, "SBFM X0, X1, #0, #31 = {enc:#010X}");
    }

    #[test]
    fn test_sbfm_sxtw_matches() {
        // SBFM X0, X1, #0, #31 must match the existing SXTW encoding
        let sbfm = mk(
            AArch64Opcode::Sbfm,
            vec![preg(X0), preg(X1), imm(0), imm(31)],
        );
        let sxtw = mk(AArch64Opcode::Sxtw, vec![preg(X0), preg(X1)]);
        let sbfm_enc = encode_instruction(&sbfm).unwrap();
        let sxtw_enc = encode_instruction(&sxtw).unwrap();
        assert_eq!(
            sbfm_enc, sxtw_enc,
            "SBFM X0, X1, #0, #31 must match SXTW X0, X1"
        );
    }

    #[test]
    fn test_sbfm_asr_alias() {
        // ASR X0, X1, #3 is encoded as SBFM X0, X1, #3, #63
        let sbfm = mk(
            AArch64Opcode::Sbfm,
            vec![preg(X0), preg(X1), imm(3), imm(63)],
        );
        let asr = mk(AArch64Opcode::AsrRI, vec![preg(X0), preg(X1), imm(3)]);
        let sbfm_enc = encode_instruction(&sbfm).unwrap();
        let asr_enc = encode_instruction(&asr).unwrap();
        assert_eq!(
            sbfm_enc, asr_enc,
            "SBFM X0, X1, #3, #63 must match ASR X0, X1, #3"
        );
    }

    #[test]
    fn test_sbfm_32bit() {
        // SBFM W0, W1, #0, #7 — sf=0, N=0, opc=00
        let inst = mk(
            AArch64Opcode::Sbfm,
            vec![preg(W0), preg(W1), imm(0), imm(7)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc >> 31, 0, "SBFM W0 must have sf=0");
        assert_eq!((enc >> 22) & 1, 0, "SBFM W0 must have N=0 for 32-bit");
        assert_eq!((enc >> 29) & 0b11, 0b00, "SBFM opc must be 00");
    }

    #[test]
    fn test_bfm_64bit() {
        // BFM X0, X1, #4, #11 — bitfield insert bits [11:4] of Rn into Rd
        // ARM ARM: sf=1 opc=01 100110 N=1 immr=4 imms=11 Rn=1 Rd=0
        let inst = mk(
            AArch64Opcode::Bfm,
            vec![preg(X0), preg(X1), imm(4), imm(11)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (1u32 << 31)
            | (0b01 << 29)
            | (0b100110 << 23)
            | (1 << 22) // N=1
            | (4 << 16) // immr=4
            | (11 << 10) // imms=11
            | (1 << 5);
        assert_eq!(enc, expected, "BFM X0, X1, #4, #11 = {enc:#010X}");
        assert_eq!((enc >> 29) & 0b11, 0b01, "BFM opc must be 01");
    }

    #[test]
    fn test_bfm_32bit() {
        // BFM W0, W1, #4, #11 — sf=0, N=0, opc=01
        let inst = mk(
            AArch64Opcode::Bfm,
            vec![preg(W0), preg(W1), imm(4), imm(11)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc >> 31, 0, "BFM W0 must have sf=0");
        assert_eq!((enc >> 22) & 1, 0, "BFM W0 must have N=0 for 32-bit");
        assert_eq!((enc >> 29) & 0b11, 0b01, "BFM opc must be 01");
    }

    #[test]
    fn test_bitfield_opc_encoding() {
        // Verify the opc field distinguishes UBFM/SBFM/BFM correctly
        let ubfm = mk(
            AArch64Opcode::Ubfm,
            vec![preg(X0), preg(X1), imm(0), imm(0)],
        );
        let sbfm = mk(
            AArch64Opcode::Sbfm,
            vec![preg(X0), preg(X1), imm(0), imm(0)],
        );
        let bfm = mk(AArch64Opcode::Bfm, vec![preg(X0), preg(X1), imm(0), imm(0)]);
        let ubfm_enc = encode_instruction(&ubfm).unwrap();
        let sbfm_enc = encode_instruction(&sbfm).unwrap();
        let bfm_enc = encode_instruction(&bfm).unwrap();
        assert_eq!((ubfm_enc >> 29) & 0b11, 0b10, "UBFM opc=10");
        assert_eq!((sbfm_enc >> 29) & 0b11, 0b00, "SBFM opc=00");
        assert_eq!((bfm_enc >> 29) & 0b11, 0b01, "BFM opc=01");
        // All three share the same fixed field at bits [28:23]
        assert_eq!((ubfm_enc >> 23) & 0x3F, 0b100110);
        assert_eq!((sbfm_enc >> 23) & 0x3F, 0b100110);
        assert_eq!((bfm_enc >> 23) & 0x3F, 0b100110);
    }

    // =========================================================================
    // Register-offset load/store tests (LdrRO, StrRO) — issue #137
    // =========================================================================

    #[test]
    fn test_ldr_ro_64bit() {
        // LDR X0, [X1, X2] — 64-bit register-offset load, default LSL, S=0
        // size=11, V=0, opc=01, Rm=2, option=011(LSL), S=0, Rn=1, Rt=0
        let inst = mk(AArch64Opcode::LdrRO, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Double,
            false,
            encoding_mem::LoadStoreOp::Load,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "LDR X0, [X1, X2] = {enc:#010X}");
    }

    #[test]
    fn test_ldr_ro_32bit() {
        // LDR W0, [X1, X2] — 32-bit register-offset load
        // size=10, V=0, opc=01, Rm=2, option=011(LSL), S=0, Rn=1, Rt=0
        let inst = mk(AArch64Opcode::LdrRO, vec![preg(W0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Word,
            false,
            encoding_mem::LoadStoreOp::Load,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "LDR W0, [X1, X2] = {enc:#010X}");
        // Verify size field (bits 31:30)
        assert_eq!((enc >> 30) & 0b11, 0b10, "LDR W must have size=10");
    }

    #[test]
    fn test_ldr_ro_with_shift() {
        // LDR X0, [X1, X2, LSL #3] — option=011, S=1
        // 4th operand packs extend info: (option << 1) | S = (0b011 << 1) | 1 = 7
        let inst = mk(
            AArch64Opcode::LdrRO,
            vec![preg(X0), preg(X1), preg(X2), imm(7)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Double,
            false,
            encoding_mem::LoadStoreOp::Load,
            2,
            encoding_mem::RegExtend::Lsl,
            true,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "LDR X0, [X1, X2, LSL #3] = {enc:#010X}");
    }

    #[test]
    fn test_ldr_ro_sxtw() {
        // LDR X0, [X1, W2, SXTW] — option=110, S=0
        // packed = (0b110 << 1) | 0 = 12
        let inst = mk(
            AArch64Opcode::LdrRO,
            vec![preg(X0), preg(X1), preg(X2), imm(12)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Double,
            false,
            encoding_mem::LoadStoreOp::Load,
            2,
            encoding_mem::RegExtend::Sxtw,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "LDR X0, [X1, W2, SXTW] = {enc:#010X}");
    }

    #[test]
    fn test_str_ro_64bit() {
        // STR X0, [X1, X2] — 64-bit register-offset store
        // size=11, V=0, opc=00, Rm=2, option=011(LSL), S=0, Rn=1, Rt=0
        let inst = mk(AArch64Opcode::StrRO, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Double,
            false,
            encoding_mem::LoadStoreOp::Store,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "STR X0, [X1, X2] = {enc:#010X}");
    }

    #[test]
    fn test_str_ro_32bit() {
        // STR W0, [X1, X2] — 32-bit register-offset store
        let inst = mk(AArch64Opcode::StrRO, vec![preg(W0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Word,
            false,
            encoding_mem::LoadStoreOp::Store,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "STR W0, [X1, X2] = {enc:#010X}");
    }

    #[test]
    fn test_str_ro_with_shift() {
        // STR X0, [X1, X2, LSL #3] — option=011, S=1 (packed=7)
        let inst = mk(
            AArch64Opcode::StrRO,
            vec![preg(X0), preg(X1), preg(X2), imm(7)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Double,
            false,
            encoding_mem::LoadStoreOp::Store,
            2,
            encoding_mem::RegExtend::Lsl,
            true,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "STR X0, [X1, X2, LSL #3] = {enc:#010X}");
    }

    #[test]
    fn test_ldr_ro_str_ro_differ_by_opc() {
        // LDR and STR with same operands should differ only in opc field
        let ldr = mk(AArch64Opcode::LdrRO, vec![preg(X0), preg(X1), preg(X2)]);
        let str_inst = mk(AArch64Opcode::StrRO, vec![preg(X0), preg(X1), preg(X2)]);
        let ldr_enc = encode_instruction(&ldr).unwrap();
        let str_enc = encode_instruction(&str_inst).unwrap();
        // opc is at bits [23:22]
        assert_eq!((ldr_enc >> 22) & 0b11, 0b01, "LDR opc=01");
        assert_eq!((str_enc >> 22) & 0b11, 0b00, "STR opc=00");
        // Everything else should be the same (mask out opc bits)
        let mask = !(0b11u32 << 22);
        assert_eq!(
            ldr_enc & mask,
            str_enc & mask,
            "LDR and STR should match except opc"
        );
    }

    // =========================================================================
    // FP register-offset load/store tests (LdrRO, StrRO) — issue #155
    // =========================================================================

    #[test]
    fn test_ldr_ro_fp_double() {
        // LDR D0, [X1, X2] — 64-bit FP register-offset load
        // size=11, V=1, opc=01
        let inst = mk(AArch64Opcode::LdrRO, vec![preg(D0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Double,
            true,
            encoding_mem::LoadStoreOp::Load,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "LDR D0, [X1, X2] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b11, "size must be 11 for Double");
        assert_eq!((enc >> 26) & 1, 1, "V must be 1 for FP");
    }

    #[test]
    fn test_ldr_ro_fp_single() {
        // LDR S0, [X1, X2] — 32-bit FP register-offset load
        // size=10, V=1, opc=01
        let inst = mk(AArch64Opcode::LdrRO, vec![preg(S0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Word,
            true,
            encoding_mem::LoadStoreOp::Load,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "LDR S0, [X1, X2] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b10, "size must be 10 for Single");
        assert_eq!((enc >> 26) & 1, 1, "V must be 1 for FP");
    }

    #[test]
    fn test_ldr_ro_fp_half() {
        // LDR H0, [X1, X2] — 16-bit FP register-offset load
        // size=01, V=1, opc=01
        let inst = mk(AArch64Opcode::LdrRO, vec![preg(H0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Half,
            true,
            encoding_mem::LoadStoreOp::Load,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "LDR H0, [X1, X2] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b01, "size must be 01 for Half");
        assert_eq!((enc >> 26) & 1, 1, "V must be 1 for FP");
    }

    #[test]
    fn test_str_ro_fp_double() {
        // STR D0, [X1, X2] — 64-bit FP register-offset store
        // size=11, V=1, opc=00
        let inst = mk(AArch64Opcode::StrRO, vec![preg(D0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Double,
            true,
            encoding_mem::LoadStoreOp::Store,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "STR D0, [X1, X2] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b11, "size must be 11 for Double");
        assert_eq!((enc >> 26) & 1, 1, "V must be 1 for FP");
    }

    #[test]
    fn test_str_ro_fp_single() {
        // STR S0, [X1, X2] — 32-bit FP register-offset store
        // size=10, V=1, opc=00
        let inst = mk(AArch64Opcode::StrRO, vec![preg(S0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Word,
            true,
            encoding_mem::LoadStoreOp::Store,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "STR S0, [X1, X2] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b10, "size must be 10 for Single");
        assert_eq!((enc >> 26) & 1, 1, "V must be 1 for FP");
    }

    #[test]
    fn test_str_ro_fp_half() {
        // STR H0, [X1, X2] — 16-bit FP register-offset store
        // size=01, V=1, opc=00
        let inst = mk(AArch64Opcode::StrRO, vec![preg(H0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding_mem::encode_ldr_str_register(
            encoding_mem::LoadStoreSize::Half,
            true,
            encoding_mem::LoadStoreOp::Store,
            2,
            encoding_mem::RegExtend::Lsl,
            false,
            1,
            0,
        )
        .unwrap();
        assert_eq!(enc, direct, "STR H0, [X1, X2] = {enc:#010X}");
        assert_eq!((enc >> 30) & 0b11, 0b01, "size must be 01 for Half");
        assert_eq!((enc >> 26) & 1, 1, "V must be 1 for FP");
    }

    #[test]
    fn test_ldr_ro_fp_sizes_differ() {
        // Verify that Half, Single, and Double produce different size fields
        let half = mk(AArch64Opcode::LdrRO, vec![preg(H0), preg(X1), preg(X2)]);
        let single = mk(AArch64Opcode::LdrRO, vec![preg(S0), preg(X1), preg(X2)]);
        let double = mk(AArch64Opcode::LdrRO, vec![preg(D0), preg(X1), preg(X2)]);
        let h_enc = encode_instruction(&half).unwrap();
        let s_enc = encode_instruction(&single).unwrap();
        let d_enc = encode_instruction(&double).unwrap();
        let h_size = (h_enc >> 30) & 0b11;
        let s_size = (s_enc >> 30) & 0b11;
        let d_size = (d_enc >> 30) & 0b11;
        assert_eq!(h_size, 0b01, "Half size=01");
        assert_eq!(s_size, 0b10, "Single size=10");
        assert_eq!(d_size, 0b11, "Double size=11");
        // All must have V=1
        assert_eq!((h_enc >> 26) & 1, 1, "Half V=1");
        assert_eq!((s_enc >> 26) & 1, 1, "Single V=1");
        assert_eq!((d_enc >> 26) & 1, 1, "Double V=1");
    }

    // =========================================================================
    // GOT/TLV load tests (LdrGot, LdrTlvp) — issue #137
    // =========================================================================

    #[test]
    fn test_ldr_got_zero_offset() {
        // LDR X0, [X1, #0] (GOT load with zero offset)
        let inst = mk(AArch64Opcode::LdrGot, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        // 64-bit load: size=11, V=0, opc=01, imm12=0, Rn=1, Rt=0
        let direct = encoding::encode_load_store_ui(0b11, 0, 0b01, 0, 1, 0);
        assert_eq!(enc, direct, "LDR X0, [X1] (GOT) = {enc:#010X}");
    }

    #[test]
    fn test_ldr_got_with_offset() {
        // LDR X0, [X1, #8] (GOT load, offset=8 -> scaled=1)
        let inst = mk(AArch64Opcode::LdrGot, vec![preg(X0), preg(X1), imm(8)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b11, 0, 0b01, 1, 1, 0);
        assert_eq!(enc, direct, "LDR X0, [X1, #8] (GOT) = {enc:#010X}");
    }

    #[test]
    fn test_ldr_tlvp_zero_offset() {
        // LDR X0, [X1, #0] (TLV descriptor load)
        let inst = mk(AArch64Opcode::LdrTlvp, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b11, 0, 0b01, 0, 1, 0);
        assert_eq!(enc, direct, "LDR X0, [X1] (TLV) = {enc:#010X}");
    }

    #[test]
    fn test_ldr_tlvp_with_offset() {
        // LDR X0, [X1, #16] (TLV load, offset=16 -> scaled=2)
        let inst = mk(AArch64Opcode::LdrTlvp, vec![preg(X0), preg(X1), imm(16)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_load_store_ui(0b11, 0, 0b01, 2, 1, 0);
        assert_eq!(enc, direct, "LDR X0, [X1, #16] (TLV) = {enc:#010X}");
    }

    #[test]
    fn test_ldr_got_and_tlvp_same_encoding() {
        // LdrGot and LdrTlvp with the same operands should produce identical encodings.
        // They differ only in relocation semantics, not in instruction encoding.
        let got = mk(AArch64Opcode::LdrGot, vec![preg(X0), preg(X1), imm(8)]);
        let tlvp = mk(AArch64Opcode::LdrTlvp, vec![preg(X0), preg(X1), imm(8)]);
        let got_enc = encode_instruction(&got).unwrap();
        let tlvp_enc = encode_instruction(&tlvp).unwrap();
        assert_eq!(
            got_enc, tlvp_enc,
            "LdrGot and LdrTlvp must produce identical encoding"
        );
    }

    // =========================================================================
    // ARM ARM bit-pattern verification against known encodings
    // =========================================================================

    #[test]
    fn test_ubfm_known_encoding() {
        // UBFM X0, X1, #16, #31 — extract unsigned bitfield [31:16]
        // ARM ARM: 1_10_100110_1_010000_011111_00001_00000
        let inst = mk(
            AArch64Opcode::Ubfm,
            vec![preg(X0), preg(X1), imm(16), imm(31)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (1u32 << 31) // sf=1
            | (0b10 << 29)         // opc=10
            | (0b100110 << 23)
            | (1 << 22)            // N=1
            | (16 << 16)           // immr=16
            | (31 << 10)           // imms=31
            | (1 << 5); // Rd=0
        assert_eq!(enc, expected, "UBFM X0, X1, #16, #31 = {enc:#010X}");
    }

    #[test]
    fn test_sbfm_sxtb_alias() {
        // SXTB X0, X1 = SBFM X0, X1, #0, #7
        // Both paths should produce identical encoding
        let sbfm = mk(
            AArch64Opcode::Sbfm,
            vec![preg(X0), preg(X1), imm(0), imm(7)],
        );
        let sxtb = mk(AArch64Opcode::Sxtb, vec![preg(X0), preg(X1)]);
        let sbfm_enc = encode_instruction(&sbfm).unwrap();
        let sxtb_enc = encode_instruction(&sxtb).unwrap();
        assert_eq!(
            sbfm_enc, sxtb_enc,
            "SBFM X0, X1, #0, #7 must match SXTB X0, X1"
        );
    }

    #[test]
    fn test_sbfm_sxth_alias() {
        // SXTH X0, X1 = SBFM X0, X1, #0, #15
        let sbfm = mk(
            AArch64Opcode::Sbfm,
            vec![preg(X0), preg(X1), imm(0), imm(15)],
        );
        let sxth = mk(AArch64Opcode::Sxth, vec![preg(X0), preg(X1)]);
        let sbfm_enc = encode_instruction(&sbfm).unwrap();
        let sxth_enc = encode_instruction(&sxth).unwrap();
        assert_eq!(
            sbfm_enc, sxth_enc,
            "SBFM X0, X1, #0, #15 must match SXTH X0, X1"
        );
    }

    // --- preg_hw returns Result (#174) ---

    #[test]
    fn test_preg_hw_valid_preg() {
        // Valid PReg operand should return Ok(hw_encoding)
        let inst = mk(AArch64Opcode::AddRR, vec![preg(X0), preg(X1), preg(X2)]);
        assert_eq!(preg_hw(&inst, 0).unwrap(), 0);
        assert_eq!(preg_hw(&inst, 1).unwrap(), 1);
        assert_eq!(preg_hw(&inst, 2).unwrap(), 2);
    }

    #[test]
    fn test_preg_hw_valid_special_sp() {
        let inst = mk(AArch64Opcode::MovR, vec![preg(X0), sp()]);
        assert_eq!(preg_hw(&inst, 1).unwrap(), 31);
    }

    #[test]
    fn test_preg_hw_valid_special_xzr() {
        let inst = mk(
            AArch64Opcode::CmpRR,
            vec![preg(X0), MachOperand::Special(SpecialReg::XZR)],
        );
        assert_eq!(preg_hw(&inst, 1).unwrap(), 31);
    }

    #[test]
    fn test_preg_hw_valid_special_wzr() {
        let inst = mk(
            AArch64Opcode::CmpRR,
            vec![preg(W0), MachOperand::Special(SpecialReg::WZR)],
        );
        assert_eq!(preg_hw(&inst, 1).unwrap(), 31);
    }

    #[test]
    fn test_preg_hw_rejects_imm() {
        // Imm operand where register expected should return Err(InvalidOperand)
        let inst = mk(AArch64Opcode::AddRR, vec![preg(X0), preg(X1), imm(42)]);
        let err = preg_hw(&inst, 2);
        assert!(err.is_err(), "Imm where register expected should error");
        let msg = err.unwrap_err().to_string();
        assert!(
            msg.contains("invalid operand"),
            "Expected InvalidOperand error, got: {msg}"
        );
    }

    #[test]
    fn test_preg_hw_rejects_missing_operand() {
        // Missing operand (index out of bounds) should return Err(MissingOperand)
        let inst = mk(AArch64Opcode::AddRR, vec![preg(X0), preg(X1)]);
        let err = preg_hw(&inst, 2);
        assert!(err.is_err(), "Missing operand should error");
        let msg = err.unwrap_err().to_string();
        assert!(
            msg.contains("missing"),
            "Expected MissingOperand error, got: {msg}"
        );
    }

    #[test]
    fn test_preg_hw_rejects_block_operand() {
        // Block operand where register expected should return Err(InvalidOperand)
        let inst = mk(
            AArch64Opcode::AddRR,
            vec![
                preg(X0),
                preg(X1),
                MachOperand::Block(trust_cg_ir::types::BlockId(0)),
            ],
        );
        let err = preg_hw(&inst, 2);
        assert!(
            err.is_err(),
            "Block operand where register expected should error"
        );
    }

    #[test]
    fn test_encode_add_rr_with_imm_operand_errors() {
        // Full encode_instruction call with wrong operand type should propagate error
        let inst = mk(AArch64Opcode::AddRR, vec![preg(X0), preg(X1), imm(42)]);
        let result = encode_instruction(&inst);
        assert!(
            result.is_err(),
            "AddRR with Imm where Rm expected must error, not default to XZR"
        );
    }

    #[test]
    fn test_encode_sub_rr_with_imm_operand_errors() {
        let inst = mk(AArch64Opcode::SubRR, vec![preg(X0), imm(10), preg(X2)]);
        let result = encode_instruction(&inst);
        assert!(
            result.is_err(),
            "SubRR with Imm where Rn expected must error"
        );
    }

    #[test]
    fn test_encode_add_sub_shifted_reg_rejects_sp_operand() {
        for (opcode, operands, bad_index) in [
            (AArch64Opcode::AddRR, vec![sp(), preg(X1), preg(X2)], 0),
            (AArch64Opcode::AddRR, vec![preg(X0), sp(), preg(X2)], 1),
            (AArch64Opcode::SubRR, vec![preg(X0), preg(X1), sp()], 2),
        ] {
            let inst = mk(opcode, operands);
            let err = encode_instruction(&inst).unwrap_err();
            assert!(
                matches!(
                    err,
                    EncodeError::InvalidOperand { index, .. } if index == bad_index
                ),
                "expected InvalidOperand at index {bad_index}, got {err:?}"
            );
            assert!(err.to_string().contains("shifted-register"));
        }
    }

    #[test]
    fn test_encode_mul_with_missing_operand_errors() {
        let inst = mk(AArch64Opcode::MulRR, vec![preg(X0), preg(X1)]);
        let result = encode_instruction(&inst);
        assert!(result.is_err(), "MulRR with missing Rm must error");
    }

    // =========================================================================
    // ARM Architecture Reference Manual (DDI 0487) encoding verification
    //
    // Each test verifies the full 32-bit instruction word against the expected
    // bit pattern derived from the ARM ARM encoding tables. These are not
    // cross-checked against internal helpers — they are independent ground
    // truth assertions.
    //
    // Encoding derivations follow the format:
    //   bit[31] | bit[30] | ... | bit[4:0]
    // with the ARM ARM section referenced for each instruction class.
    // =========================================================================

    // --- ADD/SUB register (ARM ARM C6.2.5/C6.2.294) ---
    // Add/Subtract (shifted register): sf|op|S|01011|shift|0|Rm|imm6|Rn|Rd

    #[test]
    fn test_arm_arm_add_x0_x1_x2() {
        // ADD X0, X1, X2
        // ARM ARM C6.2.5: sf=1 op=0 S=0 01011 shift=00 0 Rm=00010 imm6=000000 Rn=00001 Rd=00000
        // = 1_0_0_01011_00_0_00010_000000_00001_00000
        // = 0x8B020020
        let inst = mk(AArch64Opcode::AddRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x8B020020, "ADD X0, X1, X2 = {enc:#010X}");
    }

    #[test]
    fn test_arm_arm_add_w3_w4_w5() {
        // ADD W3, W4, W5
        // ARM ARM: sf=0 op=0 S=0 01011 shift=00 0 Rm=00101 imm6=000000 Rn=00100 Rd=00011
        // = 0_0_0_01011_00_0_00101_000000_00100_00011
        // = 0x0B050083
        let inst = mk(AArch64Opcode::AddRR, vec![preg(W3), preg(W4), preg(W5)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x0B050083, "ADD W3, W4, W5 = {enc:#010X}");
    }

    #[test]
    fn test_arm_arm_sub_x0_x1_x2() {
        // SUB X0, X1, X2
        // ARM ARM C6.2.294: sf=1 op=1 S=0 01011 00 0 Rm=00010 000000 Rn=00001 Rd=00000
        // = 1_1_0_01011_00_0_00010_000000_00001_00000
        // = 0xCB020020
        let inst = mk(AArch64Opcode::SubRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xCB020020, "SUB X0, X1, X2 = {enc:#010X}");
    }

    // --- ADD/SUB immediate (ARM ARM C6.2.4/C6.2.293) ---
    // sf|op|S|100010|sh|imm12|Rn|Rd

    #[test]
    fn test_arm_arm_add_x0_x1_imm100() {
        // ADD X0, X1, #100
        // ARM ARM C6.2.4: sf=1 op=0 S=0 100010 sh=0 imm12=000001100100 Rn=00001 Rd=00000
        // = 1_0_0_100010_0_000001100100_00001_00000
        // = 0x91019020
        let inst = mk(AArch64Opcode::AddRI, vec![preg(X0), preg(X1), imm(100)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x91019020, "ADD X0, X1, #100 = {enc:#010X}");
    }

    #[test]
    fn test_arm_arm_sub_x0_x1_imm100() {
        // SUB X0, X1, #100
        // ARM ARM C6.2.293: sf=1 op=1 S=0 100010 sh=0 imm12=000001100100 Rn=00001 Rd=00000
        // = 1_1_0_100010_0_000001100100_00001_00000
        // = 0xD1019020
        let inst = mk(AArch64Opcode::SubRI, vec![preg(X0), preg(X1), imm(100)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD1019020, "SUB X0, X1, #100 = {enc:#010X}");
    }

    // --- MOV register (ARM ARM C6.2.186) ---
    // MOV Xd, Xm is alias for ORR Xd, XZR, Xm
    // Logical shifted reg: sf|opc|01010|shift|N|Rm|imm6|Rn|Rd

    #[test]
    fn test_arm_arm_mov_x0_x1() {
        // MOV X0, X1 = ORR X0, XZR, X1
        // ARM ARM C6.2.186/C6.2.215: sf=1 opc=01 01010 shift=00 N=0 Rm=00001 imm6=000000 Rn=11111 Rd=00000
        // = 1_01_01010_00_0_00001_000000_11111_00000
        // = 0xAA0103E0
        let inst = mk(AArch64Opcode::MovR, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xAA0103E0, "MOV X0, X1 = {enc:#010X}");
    }

    // --- MOVZ (ARM ARM C6.2.191) ---
    // sf|opc=10|100101|hw|imm16|Rd

    #[test]
    fn test_arm_arm_movz_x0_0x1234() {
        // MOVZ X0, #0x1234
        // ARM ARM C6.2.191: sf=1 opc=10 100101 hw=00 imm16=0001001000110100 Rd=00000
        // Encoding: (1<<31)|(0b10<<29)|(0b100101<<23)|(0<<21)|(0x1234<<5)|0
        //         = 0x80000000|0x40000000|0x12800000|0x00024680
        //         = 0xD2824680
        let inst = mk(AArch64Opcode::Movz, vec![preg(X0), imm(0x1234)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD2824680, "MOVZ X0, #0x1234 = {enc:#010X}");
    }

    #[test]
    fn test_arm_arm_movz_w0_0x_ffff() {
        // MOVZ W0, #0xFFFF
        // ARM ARM: sf=0 opc=10 100101 hw=00 imm16=1111111111111111 Rd=00000
        // Encoding: (0<<31)|(0b10<<29)|(0b100101<<23)|(0<<21)|(0xFFFF<<5)|0
        //         = 0x00000000|0x40000000|0x12800000|0x001FFFE0
        //         = 0x529FFFE0
        let inst = mk(AArch64Opcode::Movz, vec![preg(W0), imm(0xFFFF)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x529FFFE0, "MOVZ W0, #0xFFFF = {enc:#010X}");
    }

    // --- MOVK (ARM ARM C6.2.189) ---
    // sf|opc=11|100101|hw|imm16|Rd

    #[test]
    fn test_arm_arm_movk_x0_0x5678() {
        // MOVK X0, #0x5678
        // ARM ARM C6.2.189: sf=1 opc=11 100101 hw=00 imm16=0101011001111000 Rd=00000
        // Encoding: (1<<31)|(0b11<<29)|(0b100101<<23)|(0<<21)|(0x5678<<5)|0
        //         = 0x80000000|0x60000000|0x12800000|0x000ACF00
        //         = 0xF28ACF00
        let inst = mk(AArch64Opcode::Movk, vec![preg(X0), imm(0x5678)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xF28ACF00, "MOVK X0, #0x5678 = {enc:#010X}");
    }

    // --- LDR unsigned immediate (ARM ARM C6.2.132) ---
    // size|111|V|01|opc|imm12|Rn|Rt

    #[test]
    fn test_arm_arm_ldr_x0_x1_imm16() {
        // LDR X0, [X1, #16]
        // ARM ARM C6.2.132: size=11 111 V=0 01 opc=01 imm12=000000000010 Rn=00001 Rt=00000
        // imm12 = byte_offset / 8 = 16 / 8 = 2
        // = 11_111_0_01_01_000000000010_00001_00000
        // = 0xF9400820
        let inst = mk(AArch64Opcode::LdrRI, vec![preg(X0), preg(X1), imm(16)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xF9400820, "LDR X0, [X1, #16] = {enc:#010X}");
    }

    #[test]
    fn test_arm_arm_ldr_w0_w1_imm0() {
        // LDR W0, [X1]  (no offset)
        // ARM ARM: size=10 111 V=0 01 opc=01 imm12=000000000000 Rn=00001 Rt=00000
        // = 10_111_0_01_01_000000000000_00001_00000
        // = 0xB9400020
        let inst = mk(AArch64Opcode::LdrRI, vec![preg(W0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xB9400020, "LDR W0, [X1] = {enc:#010X}");
    }

    // --- STR unsigned immediate (ARM ARM C6.2.280) ---
    // size|111|V|01|opc|imm12|Rn|Rt

    #[test]
    fn test_arm_arm_str_x0_x1_imm0() {
        // STR X0, [X1]
        // ARM ARM C6.2.280: size=11 111 V=0 01 opc=00 imm12=000000000000 Rn=00001 Rt=00000
        // = 11_111_0_01_00_000000000000_00001_00000
        // = 0xF9000020
        let inst = mk(AArch64Opcode::StrRI, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xF9000020, "STR X0, [X1] = {enc:#010X}");
    }

    #[test]
    fn test_arm_arm_str_x0_x1_imm8() {
        // STR X0, [X1, #8]
        // ARM ARM: size=11 111 V=0 01 opc=00 imm12=000000000001 Rn=00001 Rt=00000
        // imm12 = 8 / 8 = 1
        // = 11_111_0_01_00_000000000001_00001_00000
        // = 0xF9000420
        let inst = mk(AArch64Opcode::StrRI, vec![preg(X0), preg(X1), imm(8)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xF9000420, "STR X0, [X1, #8] = {enc:#010X}");
    }

    // --- B unconditional (ARM ARM C6.2.33) ---
    // op=0|00101|imm26

    #[test]
    fn test_arm_arm_b_offset4() {
        // B +16 (imm26 = 4, since offset is in units of 4 bytes)
        // ARM ARM C6.2.33: op=0 00101 imm26=00_0000_0000_0000_0000_0000_0100
        // = 0_00101_00000000000000000000000100
        // = 0x14000004
        let inst = mk(AArch64Opcode::B, vec![imm(4)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x14000004, "B +16 = {enc:#010X}");
    }

    // --- BL (ARM ARM C6.2.35) ---
    // op=1|00101|imm26

    #[test]
    fn test_arm_arm_bl_offset4() {
        // BL +16 (imm26 = 4)
        // ARM ARM C6.2.35: op=1 00101 imm26=00000000000000000000000100
        // = 1_00101_00000000000000000000000100
        // = 0x94000004
        let inst = mk(AArch64Opcode::Bl, vec![imm(4)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x94000004, "BL +16 = {enc:#010X}");
    }

    // --- CMP register (ARM ARM C6.2.68) ---
    // CMP Xn, Xm = SUBS XZR, Xn, Xm
    // sf|op=1|S=1|01011|shift|0|Rm|imm6|Rn|Rd=11111

    #[test]
    fn test_arm_arm_cmp_x1_x2() {
        // CMP X1, X2 = SUBS XZR, X1, X2
        // ARM ARM: sf=1 op=1 S=1 01011 00 0 Rm=00010 000000 Rn=00001 Rd=11111
        // = 1_1_1_01011_00_0_00010_000000_00001_11111
        // = 0xEB02003F
        let inst = mk(AArch64Opcode::CmpRR, vec![preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xEB02003F, "CMP X1, X2 = {enc:#010X}");
    }

    // --- CMP immediate (ARM ARM C6.2.69) ---
    // CMP Xn, #imm = SUBS XZR, Xn, #imm
    // sf|op=1|S=1|100010|sh|imm12|Rn|Rd=11111

    #[test]
    fn test_arm_arm_cmp_x1_imm10() {
        // CMP X1, #10 = SUBS XZR, X1, #10
        // ARM ARM: sf=1 op=1 S=1 100010 sh=0 imm12=000000001010 Rn=00001 Rd=11111
        // = 1_1_1_100010_0_000000001010_00001_11111
        // = 0xF100283F
        let inst = mk(AArch64Opcode::CmpRI, vec![preg(X1), imm(10)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xF100283F, "CMP X1, #10 = {enc:#010X}");
    }

    // --- AND register (ARM ARM C6.2.12) ---
    // Logical shifted register: sf|opc=00|01010|shift|N=0|Rm|imm6|Rn|Rd

    #[test]
    fn test_arm_arm_and_x0_x1_x2() {
        // AND X0, X1, X2
        // ARM ARM C6.2.12: sf=1 opc=00 01010 shift=00 N=0 Rm=00010 imm6=000000 Rn=00001 Rd=00000
        // = 1_00_01010_00_0_00010_000000_00001_00000
        // = 0x8A020020
        let inst = mk(AArch64Opcode::AndRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x8A020020, "AND X0, X1, X2 = {enc:#010X}");
    }

    // --- ORR register (ARM ARM C6.2.215) ---
    // sf|opc=01|01010|shift|N=0|Rm|imm6|Rn|Rd

    #[test]
    fn test_arm_arm_orr_x0_x1_x2() {
        // ORR X0, X1, X2
        // ARM ARM C6.2.215: sf=1 opc=01 01010 shift=00 N=0 Rm=00010 imm6=000000 Rn=00001 Rd=00000
        // = 1_01_01010_00_0_00010_000000_00001_00000
        // = 0xAA020020
        let inst = mk(AArch64Opcode::OrrRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xAA020020, "ORR X0, X1, X2 = {enc:#010X}");
    }

    // --- EOR register (ARM ARM C6.2.92) ---
    // sf|opc=10|01010|shift|N=0|Rm|imm6|Rn|Rd

    #[test]
    fn test_arm_arm_eor_x0_x1_x2() {
        // EOR X0, X1, X2
        // ARM ARM C6.2.92: sf=1 opc=10 01010 shift=00 N=0 Rm=00010 imm6=000000 Rn=00001 Rd=00000
        // = 1_10_01010_00_0_00010_000000_00001_00000
        // = 0xCA020020
        let inst = mk(AArch64Opcode::EorRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xCA020020, "EOR X0, X1, X2 = {enc:#010X}");
    }

    // --- ORN register (ARM ARM C6.2.213) ---
    // sf|opc=01|01010|shift|N=1|Rm|imm6|Rn|Rd

    #[test]
    fn test_arm_arm_orn_x0_x1_x2() {
        // ORN X0, X1, X2
        // ARM ARM C6.2.213: sf=1 opc=01 01010 shift=00 N=1 Rm=00010 imm6=000000 Rn=00001 Rd=00000
        // = 1_01_01010_00_1_00010_000000_00001_00000
        // = 0xAA220020
        let inst = mk(AArch64Opcode::OrnRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xAA220020, "ORN X0, X1, X2 = {enc:#010X}");
    }

    #[test]
    fn test_arm_arm_mvn_x0_x2() {
        // MVN X0, X2 = ORN X0, XZR, X2
        // sf=1 opc=01 01010 shift=00 N=1 Rm=00010 imm6=000000 Rn=11111 Rd=00000
        // = 1_01_01010_00_1_00010_000000_11111_00000
        // = 0xAA2203E0
        let inst = mk(AArch64Opcode::OrnRR, vec![preg(X0), xzr(), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(
            enc, 0xAA2203E0,
            "MVN X0, X2 = ORN X0, XZR, X2 = {enc:#010X}"
        );
    }

    // --- RET (ARM ARM C6.2.241) ---
    // 1101011|opc=0010|11111|000000|Rn|00000

    #[test]
    fn test_arm_arm_ret() {
        // RET (X30)
        // ARM ARM C6.2.241: 1101011 0010 11111 000000 Rn=11110 00000
        // = 1101011_0_0010_11111_000000_11110_00000
        // = 0xD65F03C0
        let inst = mk(AArch64Opcode::Ret, vec![]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD65F03C0, "RET = {enc:#010X}");
    }

    // --- BLR (ARM ARM C6.2.36) ---
    // 1101011|opc=0001|11111|000000|Rn|00000

    #[test]
    fn test_arm_arm_blr_x0() {
        // BLR X0
        // ARM ARM C6.2.36: 1101011 0001 11111 000000 Rn=00000 00000
        // = 1101011_0_0001_11111_000000_00000_00000
        // = 0xD63F0000
        let inst = mk(AArch64Opcode::Blr, vec![preg(X0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD63F0000, "BLR X0 = {enc:#010X}");
    }

    // --- NOP (ARM ARM C6.2.202) ---

    #[test]
    fn test_arm_arm_nop() {
        // NOP = 0xD503201F (system hint instruction)
        let inst = mk(AArch64Opcode::Nop, vec![]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD503201F, "NOP = {enc:#010X}");
    }

    // --- CSEL (ARM ARM C6.2.76) ---
    // sf|op=0|S=0|11010100|Rm|cond|op2=00|Rn|Rd

    #[test]
    fn test_arm_arm_csel_x0_x1_x2_eq() {
        // CSEL X0, X1, X2, EQ
        // ARM ARM C6.2.76: sf=1 op=0 S=0 11010100 Rm=00010 cond=0000 op2=00 Rn=00001 Rd=00000
        // = 1_0_0_11010100_00010_0000_00_00001_00000
        // = 0x9A820020
        let inst = mk(
            AArch64Opcode::Csel,
            vec![preg(X0), preg(X1), preg(X2), imm(0)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9A820020, "CSEL X0, X1, X2, EQ = {enc:#010X}");
    }

    // --- CSET (ARM ARM C6.2.70) ---
    // CSET Xd, cond = CSINC Xd, XZR, XZR, invert(cond)
    // sf|op=0|S=0|11010100|Rm=11111|inv_cond|op2=01|Rn=11111|Rd

    #[test]
    fn test_arm_arm_cset_x0_eq() {
        // CSET X0, EQ = CSINC X0, XZR, XZR, NE (inv of EQ=0000 is 0001)
        // ARM ARM: sf=1 0 0 11010100 Rm=11111 cond=0001 01 Rn=11111 Rd=00000
        // = 1_0_0_11010100_11111_0001_01_11111_00000
        // = 0x9A9F17E0
        let inst = mk(AArch64Opcode::CSet, vec![preg(X0), imm(0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9A9F17E0, "CSET X0, EQ = {enc:#010X}");
    }

    // --- B.cond (ARM ARM C6.2.34) ---
    // 01010100|imm19|0|cond

    #[test]
    fn test_arm_arm_b_eq_offset2() {
        // B.EQ +8 (imm19=2, in instruction units)
        // ARM ARM C6.2.34: 01010100 imm19=0000000000000000010 0 cond=0000
        // = 01010100_0000000000000000010_0_0000
        // = 0x54000040
        let inst = mk(AArch64Opcode::BCond, vec![imm(0), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x54000040, "B.EQ +8 = {enc:#010X}");
    }

    // --- CBZ (ARM ARM C6.2.44) ---
    // sf|011010|op=0|imm19|Rt

    #[test]
    fn test_arm_arm_cbz_x1_offset2() {
        // CBZ X1, +8 (imm19=2)
        // ARM ARM: sf=1 011010 op=0 imm19=0000000000000000010 Rt=00001
        // = 1_011010_0_0000000000000000010_00001
        // = 0xB4000041
        let inst = mk(AArch64Opcode::Cbz, vec![preg(X1), imm(2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xB4000041, "CBZ X1, +8 = {enc:#010X}");
    }

    // --- SXTW (ARM ARM C6.2.300) ---
    // SXTW Xd, Wn = SBFM Xd, Xn, #0, #31
    // sf=1|opc=00|100110|N=1|immr=000000|imms=011111|Rn|Rd

    #[test]
    fn test_arm_arm_sxtw_x0_x1() {
        // SXTW X0, X1 = SBFM X0, X1, #0, #31
        // ARM ARM: 1_00_100110_1_000000_011111_00001_00000
        // = 0x93407C20
        let inst = mk(AArch64Opcode::Sxtw, vec![preg(X0), preg(X1)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x93407C20, "SXTW X0, X1 = {enc:#010X}");
    }

    // --- MUL (ARM ARM C6.2.199) ---
    // MUL Xd, Xn, Xm = MADD Xd, Xn, Xm, XZR
    // sf|00|11011|000|Rm|o0=0|Ra=11111|Rn|Rd

    #[test]
    fn test_arm_arm_mul_x0_x1_x2() {
        // MUL X0, X1, X2 = MADD X0, X1, X2, XZR
        // ARM ARM: sf=1 00 11011 000 Rm=00010 o0=0 Ra=11111 Rn=00001 Rd=00000
        // = 1_00_11011_000_00010_0_11111_00001_00000
        // = 0x9B027C20
        let inst = mk(AArch64Opcode::MulRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9B027C20, "MUL X0, X1, X2 = {enc:#010X}");
    }

    // --- SDIV (ARM ARM C6.2.253) ---
    // sf|0|0011010110|Rm|000011|Rn|Rd

    #[test]
    fn test_arm_arm_sdiv_x0_x1_x2() {
        // SDIV X0, X1, X2
        // ARM ARM: sf=1 0 0011010110 Rm=00010 000011 Rn=00001 Rd=00000
        // = 1_0_0011010110_00010_000011_00001_00000
        // = 0x9AC20C20
        let inst = mk(AArch64Opcode::SDiv, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9AC20C20, "SDIV X0, X1, X2 = {enc:#010X}");
    }

    // --- TST register (ARM ARM C6.2.311) ---
    // TST Xn, Xm = ANDS XZR, Xn, Xm
    // sf|opc=11|01010|shift=00|N=0|Rm|imm6=000000|Rn|Rd=11111

    #[test]
    fn test_arm_arm_tst_x1_x2() {
        // TST X1, X2 = ANDS XZR, X1, X2
        // ARM ARM: sf=1 opc=11 01010 00 0 Rm=00010 000000 Rn=00001 Rd=11111
        // = 1_11_01010_00_0_00010_000000_00001_11111
        // = 0xEA02003F
        let inst = mk(AArch64Opcode::Tst, vec![preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xEA02003F, "TST X1, X2 = {enc:#010X}");
    }

    // --- BR (ARM ARM C6.2.38) ---
    // 1101011|opc=0000|11111|000000|Rn|00000

    #[test]
    fn test_arm_arm_br_x0() {
        // BR X0
        // ARM ARM: 1101011 0000 11111 000000 Rn=00000 00000
        // = 1101011_0_0000_11111_000000_00000_00000
        // = 0xD61F0000
        let inst = mk(AArch64Opcode::Br, vec![preg(X0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD61F0000, "BR X0 = {enc:#010X}");
    }

    // --- ADDS flag-setting (ARM ARM C6.2.6) ---
    // sf|op=0|S=1|01011|shift|0|Rm|imm6|Rn|Rd

    #[test]
    fn test_arm_arm_adds_x0_x1_x2() {
        // ADDS X0, X1, X2
        // ARM ARM: sf=1 op=0 S=1 01011 00 0 Rm=00010 000000 Rn=00001 Rd=00000
        // = 1_0_1_01011_00_0_00010_000000_00001_00000
        // = 0xAB020020
        let inst = mk(AArch64Opcode::AddsRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xAB020020, "ADDS X0, X1, X2 = {enc:#010X}");
    }

    // --- SUBS flag-setting (ARM ARM C6.2.297) ---
    // sf|op=1|S=1|01011|shift|0|Rm|imm6|Rn|Rd

    #[test]
    fn test_arm_arm_subs_x0_x1_x2() {
        // SUBS X0, X1, X2
        // ARM ARM: sf=1 op=1 S=1 01011 00 0 Rm=00010 000000 Rn=00001 Rd=00000
        // = 1_1_1_01011_00_0_00010_000000_00001_00000
        // = 0xEB020020
        let inst = mk(AArch64Opcode::SubsRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xEB020020, "SUBS X0, X1, X2 = {enc:#010X}");
    }

    // ===================================================================
    // Tests for newly-implemented opcodes (issue #187)
    // ===================================================================

    // --- BIC (Bitwise AND-NOT) ---
    // ARM ARM C6.2.38: sf|00|01010|shift(2)|1|Rm|imm6|Rn|Rd
    // BIC = AND with N=1 (inverted Rm)

    #[test]
    fn test_bic_x0_x1_x2() {
        // BIC X0, X1, X2
        // sf=1, opc=00, shift=00, N=1, Rm=2, imm6=0, Rn=1, Rd=0
        // 1_00_01010_00_1_00010_000000_00001_00000
        // = 0x8A220020
        let inst = mk(AArch64Opcode::BicRR, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(1, 0b00, 0, 1, 2, 0, 1, 0);
        assert_eq!(
            enc, direct,
            "BIC X0, X1, X2: unified={enc:#010X}, direct={direct:#010X}"
        );
        assert_eq!(enc, 0x8A220020, "BIC X0, X1, X2 ARM ARM = {enc:#010X}");
    }

    #[test]
    fn test_bic_w0_w1_w2() {
        // BIC W0, W1, W2 (32-bit)
        let inst = mk(AArch64Opcode::BicRR, vec![preg(W0), preg(W1), preg(W2)]);
        let enc = encode_instruction(&inst).unwrap();
        let direct = encoding::encode_logical_shifted_reg(0, 0b00, 0, 1, 2, 0, 1, 0);
        assert_eq!(enc, direct, "BIC W0, W1, W2 = {enc:#010X}");
    }

    // --- CSINC (Conditional Select Increment) ---
    // ARM ARM C6.2.78: sf|00|11010100|Rm|cond|01|Rn|Rd

    #[test]
    fn test_csinc_x0_x1_x2_eq() {
        // CSINC X0, X1, X2, EQ
        // sf=1, op=0, S=0, 11010100, Rm=2, cond=0000(EQ), op2=01, Rn=1, Rd=0
        // 1_00_11010100_00010_0000_01_00001_00000
        let inst = mk(
            AArch64Opcode::Csinc,
            vec![preg(X0), preg(X1), preg(X2), imm(0)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b11010100 << 21)
            | (2 << 16)) // EQ
            | (0b01 << 10)
            | (1 << 5);
        assert_eq!(enc, expected, "CSINC X0, X1, X2, EQ = {enc:#010X}");
    }

    #[test]
    fn test_csinc_w0_w1_w2_ne() {
        // CSINC W0, W1, W2, NE (32-bit)
        // sf=0, cond=0001(NE), op2=01
        let inst = mk(
            AArch64Opcode::Csinc,
            vec![preg(W0), preg(W1), preg(W2), imm(1)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b11010100u32 << 21)
            | (2 << 16)
            | (0b0001 << 12) // NE
            | (0b01 << 10)
            | (1 << 5);
        assert_eq!(enc, expected, "CSINC W0, W1, W2, NE = {enc:#010X}");
    }

    // --- CSINV (Conditional Select Invert) ---
    // ARM ARM C6.2.79: sf|10|11010100|Rm|cond|00|Rn|Rd

    #[test]
    fn test_csinv_x0_x1_x2_eq() {
        // CSINV X0, X1, X2, EQ
        // sf=1, op=1, S=0, 11010100, Rm=2, cond=0000(EQ), op2=00, Rn=1, Rd=0
        let inst = mk(
            AArch64Opcode::Csinv,
            vec![preg(X0), preg(X1), preg(X2), imm(0)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b10 << 29) // op=1, S=0
            | (0b11010100 << 21)
            | (2 << 16)) // op2=00
            | (1 << 5);
        assert_eq!(enc, expected, "CSINV X0, X1, X2, EQ = {enc:#010X}");
    }

    #[test]
    fn test_csinv_w0_w1_w2_lt() {
        // CSINV W0, W1, W2, LT (32-bit)
        // sf=0, cond=1011(LT)
        let inst = mk(
            AArch64Opcode::Csinv,
            vec![preg(W0), preg(W1), preg(W2), imm(0b1011)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected =
            ((0b10u32 << 29) | (0b11010100 << 21) | (2 << 16) | (0b1011 << 12)) | (1 << 5);
        assert_eq!(enc, expected, "CSINV W0, W1, W2, LT = {enc:#010X}");
    }

    // --- CSNEG (Conditional Select Negate) ---
    // ARM ARM C6.2.81: sf|10|11010100|Rm|cond|01|Rn|Rd

    #[test]
    fn test_csneg_x0_x1_x2_eq() {
        // CSNEG X0, X1, X2, EQ
        // sf=1, op=1, S=0, 11010100, Rm=2, cond=0000(EQ), op2=01, Rn=1, Rd=0
        let inst = mk(
            AArch64Opcode::Csneg,
            vec![preg(X0), preg(X1), preg(X2), imm(0)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b10 << 29) // op=1, S=0
            | (0b11010100 << 21)
            | (2 << 16)) // EQ
            | (0b01 << 10) // op2=01
            | (1 << 5);
        assert_eq!(enc, expected, "CSNEG X0, X1, X2, EQ = {enc:#010X}");
    }

    #[test]
    fn test_csneg_w0_w1_w2_ge() {
        // CSNEG W0, W1, W2, GE
        // sf=0, cond=1010(GE)
        let inst = mk(
            AArch64Opcode::Csneg,
            vec![preg(W0), preg(W1), preg(W2), imm(0b1010)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b10u32 << 29)
            | (0b11010100 << 21)
            | (2 << 16)
            | (0b1010 << 12) // GE
            | (0b01 << 10)
            | (1 << 5);
        assert_eq!(enc, expected, "CSNEG W0, W1, W2, GE = {enc:#010X}");
    }

    // --- MOVN (Move Wide with NOT) ---
    // ARM ARM C6.2.208: sf|00|100101|hw|imm16|Rd

    #[test]
    fn test_movn_x0_0() {
        // MOVN X0, #0 — encodes -1 (all ones)
        // sf=1, opc=00, hw=0, imm16=0, Rd=0
        // 1_00_100101_00_0000000000000000_00000
        // = 0x92800000
        let inst = mk(AArch64Opcode::Movn, vec![preg(X0), imm(0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x92800000, "MOVN X0, #0 = {enc:#010X}");
    }

    #[test]
    fn test_movn_x0_0xffff() {
        // MOVN X0, #0xFFFF — encodes ~0xFFFF = 0xFFFFFFFFFFFF0000
        let inst = mk(AArch64Opcode::Movn, vec![preg(X0), imm(0xFFFF)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = encoding::encode_move_wide(1, 0b00, 0, 0xFFFF, 0);
        assert_eq!(enc, expected, "MOVN X0, #0xFFFF = {enc:#010X}");
    }

    #[test]
    fn test_movn_w0_42() {
        // MOVN W0, #42
        // sf=0, opc=00, hw=0, imm16=42, Rd=0
        let inst = mk(AArch64Opcode::Movn, vec![preg(W0), imm(42)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = encoding::encode_move_wide(0, 0b00, 0, 42, 0);
        assert_eq!(enc, expected, "MOVN W0, #42 = {enc:#010X}");
    }

    // --- Logical immediate (AND/ORR/EOR) ---
    // ARM ARM C4.1.4: sf|opc(2)|100100|N|immr(6)|imms(6)|Rn(5)|Rd(5)
    // AND=00, ORR=01, EOR=10

    #[test]
    fn test_and_ri_x0_x1() {
        // AND X0, X1, #<bitmask>
        // Operands: [Rd=X0, Rn=X1, N=1, immr=0, imms=7]
        // This encodes AND X0, X1, #0xFF (byte mask)
        // sf=1, opc=00, 100100, N=1, immr=000000, imms=000111, Rn=1, Rd=0
        // 1_00_100100_1_000000_000111_00001_00000
        let inst = mk(
            AArch64Opcode::AndRI,
            vec![preg(X0), preg(X1), imm(1), imm(0), imm(7)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b100100 << 23)
            | (1 << 22)) // immr=0
            | (7 << 10) // imms=7
            | (1 << 5); // Rd=0
        assert_eq!(enc, expected, "AND X0, X1, #0xFF = {enc:#010X}");
    }

    #[test]
    fn test_orr_ri_x0_xzr() {
        // ORR X0, XZR, #<bitmask> — materialize bitmask constant
        // Operands: [Rd=X0, Rn=XZR, N=0, immr=0, imms=0]
        // sf=1, opc=01, 100100, N=0, immr=0, imms=0, Rn=31, Rd=0
        let inst = mk(
            AArch64Opcode::OrrRI,
            vec![
                preg(X0),
                MachOperand::Special(SpecialReg::XZR),
                imm(0),
                imm(0),
                imm(0),
            ],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = ((1u32 << 31)
            | (0b01 << 29) // ORR
            | (0b100100 << 23)) // imms=0
            | (31 << 5); // Rd=0
        assert_eq!(enc, expected, "ORR X0, XZR, #imm = {enc:#010X}");
    }

    #[test]
    fn test_eor_ri_x0_x1() {
        // EOR X0, X1, #<bitmask>
        // Operands: [Rd=X0, Rn=X1, N=1, immr=16, imms=31]
        // sf=1, opc=10, 100100, N=1, immr=010000, imms=011111, Rn=1, Rd=0
        let inst = mk(
            AArch64Opcode::EorRI,
            vec![preg(X0), preg(X1), imm(1), imm(16), imm(31)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (1u32 << 31)
            | (0b10 << 29) // EOR
            | (0b100100 << 23)
            | (1 << 22) // N=1
            | (16 << 16) // immr=16
            | (31 << 10) // imms=31
            | (1 << 5); // Rd=0
        assert_eq!(enc, expected, "EOR X0, X1, #imm = {enc:#010X}");
    }

    /// TST Rn,#imm = ANDS XZR,Rn,#imm. Every word below is ground truth from
    /// GNU `as` on aarch64, not hand-derived, so a bit-layout slip in the
    /// immediate path cannot pass by agreeing with my own arithmetic.
    ///
    ///     tst x2,  #1                    f240005f
    ///     tst x11, #1                    f240017f
    ///     tst w2,  #1                    7200005f
    ///     tst x2,  #0xff                 f2401c5f
    ///     tst x9,  #0x8000000000000000   f241013f
    ///     tst w5,  #0xffff               72003cbf
    #[test]
    fn test_tst_immediate_forms_match_assembler() {
        for (rn, m, expected, what) in [
            (X2, 1i64, 0xF240_005Fu32, "tst x2,#1"),
            (X11, 1, 0xF240_017F, "tst x11,#1"),
            (W2, 1, 0x7200_005F, "tst w2,#1"),
            (X2, 0xFF, 0xF240_1C5F, "tst x2,#0xff"),
            (X9, i64::MIN, 0xF241_013F, "tst x9,#0x8000000000000000"),
            (W5, 0xFFFF, 0x7200_3CBF, "tst w5,#0xffff"),
        ] {
            let inst = mk(AArch64Opcode::Tst, vec![preg(rn), imm(m)]);
            let enc = encode_instruction(&inst).unwrap_or_else(|e| panic!("{what}: {e:?}"));
            assert_eq!(
                enc, expected,
                "{what}: got {enc:#010X} want {expected:#010X}"
            );
        }
    }

    /// The register form must be untouched by the operand-shape dispatch.
    #[test]
    fn test_tst_register_form_still_encodes() {
        let inst = mk(AArch64Opcode::Tst, vec![preg(X2), preg(X3)]);
        assert_eq!(encode_instruction(&inst).unwrap(), 0xEA03_005F, "tst x2,x3");
    }

    #[test]
    fn test_tst_malformed_register_shapes_fail_closed() {
        for operands in [
            vec![preg(S0), preg(S1)],
            vec![preg(SP), preg(X1)],
            vec![sp(), preg(X1)],
            vec![preg(X0), preg(W1)],
            vec![preg(X0)],
            vec![preg(X0), preg(X1), imm(1)],
        ] {
            assert!(
                encode_instruction(&mk(AArch64Opcode::Tst, operands.clone())).is_err(),
                "malformed TST must fail closed: {operands:?}"
            );
        }
    }

    /// A mask with no logical-immediate encoding must FAIL, not silently encode
    /// some other instruction. 0 and all-ones are the classic unencodable cases.
    #[test]
    fn test_tst_unencodable_mask_fails_closed() {
        for bad in [0i64, -1] {
            let inst = mk(AArch64Opcode::Tst, vec![preg(X2), imm(bad)]);
            assert!(
                encode_instruction(&inst).is_err(),
                "mask {bad:#x} has no logical-immediate encoding and must fail closed"
            );
        }
    }

    #[test]
    fn test_and_ri_w0_w1_32bit() {
        // AND W0, W1, #0xF (32-bit)
        // sf=0, opc=00, N=0 (must be 0 for 32-bit), immr=0, imms=3
        let inst = mk(
            AArch64Opcode::AndRI,
            vec![preg(W0), preg(W1), imm(0), imm(0), imm(3)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b100100 << 23) // immr=0
            | (3 << 10) // imms=3
            | (1 << 5);
        assert_eq!(enc, expected, "AND W0, W1, #0xF = {enc:#010X}");
    }

    #[test]
    fn test_and_ri_raw_low_mask_32bit() {
        let inst = mk(AArch64Opcode::AndRI, vec![preg(W0), preg(W1), imm(0xffff)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x1200_3C20, "AND W0, W1, #0xffff = {enc:#010X}");

        let inst = mk(AArch64Opcode::AndRI, vec![preg(W0), preg(W1), imm(0xff)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x1200_1C20, "AND W0, W1, #0xff = {enc:#010X}");
    }

    #[test]
    fn test_and_ri_raw_low_mask_64bit() {
        let inst = mk(AArch64Opcode::AndRI, vec![preg(X0), preg(X1), imm(0xff)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9240_1C20, "AND X0, X1, #0xff = {enc:#010X}");
    }

    // --- FMOV immediate ---
    // ARM ARM C7.2.132: 0|0|0|11110|ftype(2)|1|imm8|100|00000|Rd

    #[test]
    fn test_fmov_imm_2_0_single() {
        // FMOV S0, #2.0
        // ftype=00 (single), imm8 encodes 2.0
        // 2.0 = sign=0, exp=128(biased)=1024(f64), mantissa=0
        // For f64: exp=1024 -> biased_3 = 1024-1020 = 4 = 0b100
        // NOT(b) = NOT(1) = 0, ccc[1:0] = 00
        // imm8 = 0_0_00_0000 = 0x00
        let inst = mk(
            AArch64Opcode::FmovImm,
            vec![preg(S0), MachOperand::FImm(2.0)],
        );
        let enc = encode_instruction(&inst).unwrap();
        // ftype=00, imm8=0x00
        let expected = ((0b00011110u32 << 24) // ftype=single
            | (1 << 21)) // imm8
            | (0b100 << 10); // Rd=S0
        assert_eq!(enc, expected, "FMOV S0, #2.0 = {enc:#010X}");
    }

    #[test]
    fn test_fmov_imm_1_0_double() {
        // FMOV D0, #1.0
        // 1.0f64: sign=0, exp=1023(biased), frac=0
        // biased_3 = 1023-1020 = 3 = 0b011
        // NOT(b) = NOT(0) = 1, ccc[1:0] = 11
        // imm8 = 0_1_11_0000 = 0x70
        let inst = mk(
            AArch64Opcode::FmovImm,
            vec![preg(D0), MachOperand::FImm(1.0)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b00011110u32 << 24)
            | (0b01 << 22) // ftype=double
            | (1 << 21)
            | (0x70u32 << 13) // imm8 = 0b01110000
            | (0b100 << 10); // Rd=D0
        assert_eq!(enc, expected, "FMOV D0, #1.0 = {enc:#010X}");
    }

    #[test]
    fn test_fmov_imm_neg_1_0() {
        // FMOV D0, #-1.0
        // -1.0f64: sign=1, exp=1023, frac=0
        // biased_3 = 3 => NOT(b)=1, cc=11
        // imm8 = 1_1_11_0000 = 0xF0
        let inst = mk(
            AArch64Opcode::FmovImm,
            vec![preg(D0), MachOperand::FImm(-1.0)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected = (0b00011110u32 << 24)
            | (0b01 << 22) // ftype=double
            | (1 << 21)
            | (0xF0u32 << 13) // imm8 = 0b11110000
            | (0b100 << 10);
        assert_eq!(enc, expected, "FMOV D0, #-1.0 = {enc:#010X}");
    }

    #[test]
    fn test_fmov_imm_0_5() {
        // FMOV D0, #0.5
        // 0.5f64: sign=0, exp=1022, frac=0
        // biased_3 = 1022-1020 = 2 = 0b010
        // NOT(b) = NOT(0) = 1, cc = 10
        // imm8 = 0_1_10_0000 = 0x60
        let inst = mk(
            AArch64Opcode::FmovImm,
            vec![preg(D0), MachOperand::FImm(0.5)],
        );
        let enc = encode_instruction(&inst).unwrap();
        let expected =
            (0b00011110u32 << 24) | (0b01 << 22) | (1 << 21) | (0x60u32 << 13) | (0b100 << 10);
        assert_eq!(enc, expected, "FMOV D0, #0.5 = {enc:#010X}");
    }

    // --- MOVN shift-zero publication subset ---

    #[test]
    fn test_movn_accepts_only_shift_zero() {
        let implicit = mk(AArch64Opcode::Movn, vec![preg(X0), imm(0x1234)]);
        let explicit = mk(AArch64Opcode::Movn, vec![preg(X0), imm(0x1234), imm(0)]);
        let expected = encoding::encode_move_wide(1, 0b00, 0, 0x1234, 0);
        assert_eq!(encode_instruction(&implicit).unwrap(), expected);
        assert_eq!(encode_instruction(&explicit).unwrap(), expected);

        for shift in [-16i64, 8, 16, 32, 48, 64] {
            let shifted = mk(AArch64Opcode::Movn, vec![preg(X0), imm(0x1234), imm(shift)]);
            assert!(
                matches!(
                    encode_instruction(&shifted),
                    Err(EncodeError::InvalidOperand { index: 2, .. })
                ),
                "MOVN shift {shift} must fail closed"
            );
        }
    }

    // --- CSEL already tested above, but verify relationship with CSINC ---

    #[test]
    fn test_csel_vs_csinc_encoding_diff() {
        // CSEL and CSINC differ only in op2 bits [11:10]
        // CSEL: op2=00, CSINC: op2=01
        let csel = mk(
            AArch64Opcode::Csel,
            vec![preg(X0), preg(X1), preg(X2), imm(0)],
        );
        let csinc = mk(
            AArch64Opcode::Csinc,
            vec![preg(X0), preg(X1), preg(X2), imm(0)],
        );
        let enc_sel = encode_instruction(&csel).unwrap();
        let enc_inc = encode_instruction(&csinc).unwrap();
        // The only difference should be in bits 11:10
        assert_eq!(
            enc_sel & !0xC00,
            enc_inc & !0xC00,
            "CSEL and CSINC should differ only in op2 bits"
        );
        assert_eq!((enc_sel >> 10) & 0b11, 0b00, "CSEL op2 = 00");
        assert_eq!((enc_inc >> 10) & 0b11, 0b01, "CSINC op2 = 01");
    }

    // --- CSINV vs CSNEG encoding difference ---

    #[test]
    fn test_csinv_vs_csneg_encoding_diff() {
        // CSINV and CSNEG share sf|10|11010100 prefix and differ in op2
        // CSINV: op2=00, CSNEG: op2=01
        let csinv = mk(
            AArch64Opcode::Csinv,
            vec![preg(X0), preg(X1), preg(X2), imm(0)],
        );
        let csneg = mk(
            AArch64Opcode::Csneg,
            vec![preg(X0), preg(X1), preg(X2), imm(0)],
        );
        let enc_inv = encode_instruction(&csinv).unwrap();
        let enc_neg = encode_instruction(&csneg).unwrap();
        assert_eq!(
            enc_inv & !0xC00,
            enc_neg & !0xC00,
            "CSINV and CSNEG should differ only in op2 bits"
        );
        assert_eq!((enc_inv >> 10) & 0b11, 0b00, "CSINV op2 = 00");
        assert_eq!((enc_neg >> 10) & 0b11, 0b01, "CSNEG op2 = 01");
    }

    // --- LLVM-style typed alias tests ---

    #[test]
    fn test_movwrr_alias() {
        // MOVWrr W0, W1 — should encode same as MovR with 32-bit regs
        let alias = mk(AArch64Opcode::MOVWrr, vec![preg(W0), preg(W1)]);
        let generic = mk(AArch64Opcode::MovR, vec![preg(W0), preg(W1)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "MOVWrr should match MovR for W registers"
        );
    }

    #[test]
    fn test_movxrr_alias() {
        // MOVXrr X0, X1
        let alias = mk(AArch64Opcode::MOVXrr, vec![preg(X0), preg(X1)]);
        let generic = mk(AArch64Opcode::MovR, vec![preg(X0), preg(X1)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "MOVXrr should match MovR for X registers"
        );
    }

    #[test]
    fn test_typed_move_width_overrides_allocated_register_view() {
        // Regalloc deliberately leaves this Gpr64 shape intact as a 32-bit
        // truncation idiom: MOVWrr must write Wd despite its X-register view.
        let movw_over_x = mk(AArch64Opcode::MOVWrr, vec![preg(X0), preg(X1)]);
        let movw = encode_instruction(&movw_over_x).unwrap();
        let generic_w = mk(AArch64Opcode::MovR, vec![preg(W0), preg(W1)]);
        assert_eq!(movw >> 31, 0, "MOVWrr must force sf=0");
        assert_eq!(
            movw,
            encode_instruction(&generic_w).unwrap(),
            "MOVWrr over Gpr64 must retain 32-bit truncation semantics"
        );

        // Symmetric control: MOVXrr stays the X-form even if a mismatched
        // producer supplied W-register views.
        let movx_over_w = mk(AArch64Opcode::MOVXrr, vec![preg(W0), preg(W1)]);
        let movx = encode_instruction(&movx_over_w).unwrap();
        let generic_x = mk(AArch64Opcode::MovR, vec![preg(X0), preg(X1)]);
        assert_eq!(movx >> 31, 1, "MOVXrr must force sf=1");
        assert_eq!(
            movx,
            encode_instruction(&generic_x).unwrap(),
            "MOVXrr must not inherit a W-register view"
        );
    }

    #[test]
    fn test_bl_alias() {
        // BL (typed) should match Bl
        let alias = mk(AArch64Opcode::BL, vec![imm(100)]);
        let generic = mk(AArch64Opcode::Bl, vec![imm(100)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "BL alias should match Bl"
        );
    }

    #[test]
    fn test_bl_alias_symbol_rejected_by_raw_encoder() {
        let inst = mk(
            AArch64Opcode::BL,
            vec![MachOperand::Symbol("_callee".to_string())],
        );
        assert!(matches!(
            encode_instruction(&inst),
            Err(EncodeError::InvalidOperand {
                opcode: AArch64Opcode::BL,
                index: 0,
                ..
            })
        ));
    }

    #[test]
    fn test_blr_alias() {
        // BLR (typed) should match Blr
        let alias = mk(AArch64Opcode::BLR, vec![preg(X0)]);
        let generic = mk(AArch64Opcode::Blr, vec![preg(X0)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "BLR alias should match Blr"
        );
    }

    #[test]
    fn test_cmpwrr_alias() {
        // CMPWrr W0, W1 should match CmpRR with 32-bit regs
        let alias = mk(AArch64Opcode::CMPWrr, vec![preg(W0), preg(W1)]);
        let generic = mk(AArch64Opcode::CmpRR, vec![preg(W0), preg(W1)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "CMPWrr should match CmpRR"
        );
    }

    #[test]
    fn test_cmpxrr_alias() {
        let alias = mk(AArch64Opcode::CMPXrr, vec![preg(X0), preg(X1)]);
        let generic = mk(AArch64Opcode::CmpRR, vec![preg(X0), preg(X1)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "CMPXrr should match CmpRR"
        );
    }

    #[test]
    fn test_cmpwri_alias() {
        let alias = mk(AArch64Opcode::CMPWri, vec![preg(W0), imm(42)]);
        let generic = mk(AArch64Opcode::CmpRI, vec![preg(W0), imm(42)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "CMPWri should match CmpRI"
        );
    }

    #[test]
    fn test_cmpxri_alias() {
        let alias = mk(AArch64Opcode::CMPXri, vec![preg(X0), imm(42)]);
        let generic = mk(AArch64Opcode::CmpRI, vec![preg(X0), imm(42)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "CMPXri should match CmpRI"
        );
    }

    #[test]
    fn test_movzwi_alias() {
        let alias = mk(AArch64Opcode::MOVZWi, vec![preg(W0), imm(0x1234)]);
        let generic = mk(AArch64Opcode::Movz, vec![preg(W0), imm(0x1234)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "MOVZWi should match Movz"
        );
    }

    #[test]
    fn test_movzxi_alias() {
        let alias = mk(AArch64Opcode::MOVZXi, vec![preg(X0), imm(0x5678)]);
        let generic = mk(AArch64Opcode::Movz, vec![preg(X0), imm(0x5678)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "MOVZXi should match Movz"
        );
    }

    #[test]
    fn test_bcc_alias() {
        // Bcc with cond=EQ, offset=2
        let alias = mk(AArch64Opcode::Bcc, vec![imm(0), imm(2)]);
        let generic = mk(AArch64Opcode::BCond, vec![imm(0), imm(2)]);
        assert_eq!(
            encode_instruction(&alias).unwrap(),
            encode_instruction(&generic).unwrap(),
            "Bcc should match BCond"
        );
    }

    #[test]
    fn test_strwui_alias() {
        // STRWui W0, [X1, #4] — 32-bit store unsigned offset
        // size=10, V=0, opc=00, imm12=4/4=1
        let inst = mk(AArch64Opcode::STRWui, vec![preg(W0), preg(X1), imm(4)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = encoding::encode_load_store_ui(0b10, 0, 0b00, 1, 1, 0);
        assert_eq!(enc, expected, "STRWui W0, [X1, #4] = {enc:#010X}");
    }

    #[test]
    fn test_strxui_alias() {
        // STRXui X0, [X1, #8] — 64-bit store unsigned offset
        // size=11, V=0, opc=00, imm12=8/8=1
        let inst = mk(AArch64Opcode::STRXui, vec![preg(X0), preg(X1), imm(8)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = encoding::encode_load_store_ui(0b11, 0, 0b00, 1, 1, 0);
        assert_eq!(enc, expected, "STRXui X0, [X1, #8] = {enc:#010X}");
    }

    #[test]
    fn test_strsui_alias() {
        // STRSui S0, [X1, #4] — 32-bit FP store unsigned offset
        // size=10, V=1, opc=00, imm12=4/4=1
        let inst = mk(AArch64Opcode::STRSui, vec![preg(S0), preg(X1), imm(4)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = encoding::encode_load_store_ui(0b10, 1, 0b00, 1, 1, 0);
        assert_eq!(enc, expected, "STRSui S0, [X1, #4] = {enc:#010X}");
    }

    #[test]
    fn test_strdui_alias() {
        // STRDui D0, [X1, #8] — 64-bit FP store unsigned offset
        // size=11, V=1, opc=00, imm12=8/8=1
        let inst = mk(AArch64Opcode::STRDui, vec![preg(D0), preg(X1), imm(8)]);
        let enc = encode_instruction(&inst).unwrap();
        let expected = encoding::encode_load_store_ui(0b11, 1, 0b00, 1, 1, 0);
        assert_eq!(enc, expected, "STRDui D0, [X1, #8] = {enc:#010X}");
    }

    // --- encode_fmov_imm8 unit tests ---

    #[test]
    fn test_encode_fmov_imm8_1_0() {
        // 1.0 = 0x3FF0_0000_0000_0000
        // exp=1023, biased_3=3=0b011, NOT(b)=1, cc=11, frac_top4=0
        // imm8 = 0_1_11_0000 = 0x70
        assert_eq!(encode_fmov_imm8(1.0), 0x70);
    }

    #[test]
    fn test_encode_fmov_imm8_2_0() {
        // 2.0 = 0x4000_0000_0000_0000
        // exp=1024, biased_3=4=0b100, NOT(b)=0, cc=00, frac_top4=0
        // imm8 = 0_0_00_0000 = 0x00
        assert_eq!(encode_fmov_imm8(2.0), 0x00);
    }

    #[test]
    fn test_encode_fmov_imm8_0_5() {
        // 0.5 = 0x3FE0_0000_0000_0000
        // exp=1022, biased_3=2=0b010, NOT(b)=1, cc=10, frac_top4=0
        // imm8 = 0_1_10_0000 = 0x60
        assert_eq!(encode_fmov_imm8(0.5), 0x60);
    }

    #[test]
    fn test_encode_fmov_imm8_neg_1_0() {
        // -1.0: sign=1
        // imm8 = 1_1_11_0000 = 0xF0
        assert_eq!(encode_fmov_imm8(-1.0), 0xF0);
    }

    #[test]
    fn test_encode_fmov_imm8_1_5() {
        // 1.5 = 0x3FF8_0000_0000_0000
        // exp=1023, biased_3=3, NOT(b)=1, cc=11, frac_top4=0b1000=8
        // imm8 = 0_1_11_1000 = 0x78
        assert_eq!(encode_fmov_imm8(1.5), 0x78);
    }

    // --- ARM ARM cross-check: logical immediate fixed bits ---

    #[test]
    fn test_logical_imm_fixed_bits() {
        // Bits 28:23 must be 100100 for logical immediate
        let inst = mk(
            AArch64Opcode::AndRI,
            vec![preg(X0), preg(X1), imm(0), imm(0), imm(0)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(
            (enc >> 23) & 0x3F,
            0b100100,
            "Logical imm fixed bits 28:23 = 100100"
        );
    }

    #[test]
    fn test_logical_imm_opc_differentiation() {
        // AND=00, ORR=01, EOR=10 in bits 30:29
        let and_inst = mk(
            AArch64Opcode::AndRI,
            vec![preg(X0), preg(X1), imm(0), imm(0), imm(0)],
        );
        let orr_inst = mk(
            AArch64Opcode::OrrRI,
            vec![preg(X0), preg(X1), imm(0), imm(0), imm(0)],
        );
        let eor_inst = mk(
            AArch64Opcode::EorRI,
            vec![preg(X0), preg(X1), imm(0), imm(0), imm(0)],
        );
        let enc_and = encode_instruction(&and_inst).unwrap();
        let enc_orr = encode_instruction(&orr_inst).unwrap();
        let enc_eor = encode_instruction(&eor_inst).unwrap();
        assert_eq!((enc_and >> 29) & 0b11, 0b00, "AND opc = 00");
        assert_eq!((enc_orr >> 29) & 0b11, 0b01, "ORR opc = 01");
        assert_eq!((enc_eor >> 29) & 0b11, 0b10, "EOR opc = 10");
    }

    // =======================================================================
    // i128 multi-register arithmetic encoding (ARM ARM references)
    // =======================================================================

    // --- ADC (ARM ARM C6.2.1) ---
    // sf|op=0|S=0|11010000|Rm|000000|Rn|Rd

    #[test]
    fn test_adc_x0_x1_x2() {
        // ADC X0, X1, X2
        // ARM ARM: sf=1 0 0 11010000 Rm=00010 000000 Rn=00001 Rd=00000
        // = 1_0_0_11010000_00010_000000_00001_00000
        // = 0x9A020020
        let inst = mk(AArch64Opcode::Adc, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9A020020, "ADC X0, X1, X2 = {enc:#010X}");
    }

    // --- SBC (ARM ARM C6.2.229) ---
    // sf|op=1|S=0|11010000|Rm|000000|Rn|Rd

    #[test]
    fn test_sbc_x0_x1_x2() {
        // SBC X0, X1, X2
        // ARM ARM: sf=1 1 0 11010000 Rm=00010 000000 Rn=00001 Rd=00000
        // = 1_1_0_11010000_00010_000000_00001_00000
        // = 0xDA020020
        let inst = mk(AArch64Opcode::Sbc, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xDA020020, "SBC X0, X1, X2 = {enc:#010X}");
    }

    // --- UMULH (ARM ARM C6.2.332) ---
    // 1|00|11011|110|Rm|0|11111|Rn|Rd

    #[test]
    fn test_umulh_x0_x1_x2() {
        // UMULH X0, X1, X2
        // ARM ARM: sf=1 00 11011 110 Rm=00010 0 Ra=11111 Rn=00001 Rd=00000
        // = 1_00_11011_110_00010_0_11111_00001_00000
        // = 0x9BC27C20
        let inst = mk(AArch64Opcode::Umulh, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9BC27C20, "UMULH X0, X1, X2 = {enc:#010X}");
    }

    // --- SMULH (ARM ARM C6.2.289) ---
    // 1|00|11011|010|Rm|0|11111|Rn|Rd
    // Distinguishing bit from UMULH: op31 = 010 (signed) vs 110 (unsigned).

    #[test]
    fn test_smulh_x0_x1_x2() {
        // SMULH X0, X1, X2
        // ARM ARM: sf=1 00 11011 010 Rm=00010 0 Ra=11111 Rn=00001 Rd=00000
        // = 1_00_11011_010_00010_0_11111_00001_00000
        // = 0x9B427C20
        let inst = mk(AArch64Opcode::Smulh, vec![preg(X0), preg(X1), preg(X2)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9B427C20, "SMULH X0, X1, X2 = {enc:#010X}");
    }

    #[test]
    fn test_smulh_x0_x3_x9() {
        // SMULH X0, X3, X9 — exercises non-zero Rn/Rm bits in upper fields
        // ARM ARM: sf=1 00 11011 010 Rm=01001 0 Ra=11111 Rn=00011 Rd=00000
        // = 1_00_11011_010_01001_0_11111_00011_00000
        // = 0x9B497C60
        let inst = mk(AArch64Opcode::Smulh, vec![preg(X0), preg(X3), preg(X9)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9B497C60, "SMULH X0, X3, X9 = {enc:#010X}");
    }

    // Sanity: SMULH and UMULH with identical operands differ only at bit 23
    // (op31 low bit). UMULH has op31=110, SMULH has op31=010.
    #[test]
    fn test_smulh_umulh_differ_only_bit23() {
        let smulh = mk(AArch64Opcode::Smulh, vec![preg(X0), preg(X1), preg(X2)]);
        let umulh = mk(AArch64Opcode::Umulh, vec![preg(X0), preg(X1), preg(X2)]);
        let s = encode_instruction(&smulh).unwrap();
        let u = encode_instruction(&umulh).unwrap();
        assert_eq!(
            s ^ u,
            1u32 << 23,
            "SMULH ^ UMULH must be exactly bit 23 (op31 toggle); got {:#010X} ^ {:#010X} = {:#010X}",
            s,
            u,
            s ^ u
        );
    }

    // --- MADD (ARM ARM C6.2.163) ---
    // sf|00|11011|000|Rm|o0=0|Ra|Rn|Rd
    // (Same encoding as MUL but Ra != XZR)

    #[test]
    fn test_madd_x0_x1_x2_x3() {
        // MADD X0, X1, X2, X3
        // ARM ARM: sf=1 00 11011 000 Rm=00010 0 Ra=00011 Rn=00001 Rd=00000
        // = 1_00_11011_000_00010_0_00011_00001_00000
        // = 0x9B020C20
        let inst = mk(
            AArch64Opcode::Madd,
            vec![preg(X0), preg(X1), preg(X2), preg(X3)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x9B020C20, "MADD X0, X1, X2, X3 = {enc:#010X}");
    }

    // --- Issue #366: encoder safety net ---
    //
    // `MovI`/`Movz` must NEVER silently truncate a wide immediate to its
    // low 16 bits. Passes that produce such instructions (historically,
    // a buggy constant folder) must materialize wide constants via
    // MOVZ + MOVK chains instead. If a wide `MovI` reaches the encoder,
    // fail loudly with `EncodeError::MovImmTooWide`.

    #[test]
    fn test_movi_rejects_wide_immediate() {
        // 0x165667919E3779F9 is the xxh3 avalanche prime — a canonical
        // wide constant from the miscompile in #366.
        let wide = 0x165667919E3779F9u64 as i64;
        let inst = mk(AArch64Opcode::MovI, vec![preg(X0), imm(wide)]);
        let err = encode_instruction(&inst)
            .expect_err("MovI with a wide immediate must NOT silently truncate (#366)");
        match err {
            EncodeError::MovImmTooWide { opcode, imm } => {
                assert_eq!(opcode, AArch64Opcode::MovI);
                assert_eq!(imm, wide as u64);
            }
            other => panic!("expected MovImmTooWide, got {:?}", other),
        }
    }

    #[test]
    fn test_movi_rejects_negative_immediate() {
        // Negative i64 values have wide two's-complement bit patterns
        // that cannot fit in a single 16-bit MOVZ field.
        let inst = mk(AArch64Opcode::MovI, vec![preg(X0), imm(-42)]);
        let err = encode_instruction(&inst)
            .expect_err("MovI with a negative immediate must error, not truncate");
        assert!(matches!(err, EncodeError::MovImmTooWide { .. }));
    }

    #[test]
    fn test_movz_rejects_wide_immediate() {
        // MOVZ only encodes a 16-bit field; a > 16-bit source must be
        // rejected rather than truncated.
        let inst = mk(AArch64Opcode::Movz, vec![preg(X0), imm(0x10000)]);
        let err = encode_instruction(&inst)
            .expect_err("Movz with imm >= 0x10000 must error, not truncate");
        assert!(matches!(err, EncodeError::MovImmTooWide { .. }));
    }

    #[test]
    fn test_movi_accepts_small_immediate() {
        // Boundary: 0x0000 and 0xFFFF must both encode cleanly.
        for v in &[0i64, 1, 42, 0xFFFE, 0xFFFF] {
            let inst = mk(AArch64Opcode::MovI, vec![preg(X0), imm(*v)]);
            encode_instruction(&inst)
                .unwrap_or_else(|e| panic!("MovI with imm={} should encode, got {:?}", v, e));
        }
    }

    // =========================================================================
    // MRS (move from system register) — issue #370
    //
    // Encoding: 1101 0101 001 <systemreg[15:0]> <Rt[4:0]>
    //
    // The 16-bit systemreg field packs op0/op1/CRn/CRm/op2 per
    // ARM ARM C6.2.169 and LLVM's AArch64SystemOperands.td class SysReg.
    // =========================================================================

    /// Encoding of TPIDR_EL0 as a 16-bit systemreg field.
    /// op0=11, op1=011, CRn=1101, CRm=0000, op2=010
    ///   [15:14]=11 [13:11]=011 [10:7]=1101 [6:3]=0000 [2:0]=010
    ///   = 0b1101_1110_1000_0010 = 0xDE82
    const SYSREG_TPIDR_EL0: i64 = 0xDE82;

    #[test]
    fn test_add_ri_shift12_x0_x1_1() {
        let inst = mk(
            AArch64Opcode::AddRIShift12,
            vec![preg(X0), preg(X1), imm(1)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x91400420, "ADD X0, X1, #1, LSL #12 = {enc:#010X}");
    }

    #[test]
    fn test_add_ri_shift12_x0_x0_0xabc() {
        let inst = mk(
            AArch64Opcode::AddRIShift12,
            vec![preg(X0), preg(X0), imm(0xABC)],
        );
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0x916AF000, "ADD X0, X0, #0xABC, LSL #12 = {enc:#010X}");
    }

    #[test]
    fn test_add_ri_shift12_not_equal_no_shift() {
        let shifted = mk(
            AArch64Opcode::AddRIShift12,
            vec![preg(X0), preg(X1), imm(5)],
        );
        let unshifted = mk(AArch64Opcode::AddRI, vec![preg(X0), preg(X1), imm(5)]);
        let shifted_enc = encode_instruction(&shifted).unwrap();
        let unshifted_enc = encode_instruction(&unshifted).unwrap();

        assert_ne!(shifted_enc, unshifted_enc);
        assert_eq!((shifted_enc >> 22) & 1, 1, "AddRIShift12 must set bit 22");
        assert_eq!((unshifted_enc >> 22) & 1, 0, "AddRI must clear bit 22");
    }

    #[test]
    fn test_add_sub_imm12_boundaries_encode() {
        let cases = [
            (AArch64Opcode::AddRI, vec![preg(X0), preg(X1), imm(0xFFF)]),
            (
                AArch64Opcode::AddRIShift12,
                vec![preg(X0), preg(X1), imm(0xFFF)],
            ),
            (AArch64Opcode::SubRI, vec![preg(X0), preg(X1), imm(0xFFF)]),
            (AArch64Opcode::CmpRI, vec![preg(X0), imm(0xFFF)]),
            (AArch64Opcode::AddsRI, vec![preg(X0), preg(X1), imm(0xFFF)]),
            (AArch64Opcode::SubsRI, vec![preg(X0), preg(X1), imm(0xFFF)]),
            (AArch64Opcode::CMPWri, vec![preg(W0), imm(0xFFF)]),
            (AArch64Opcode::CMPXri, vec![preg(X0), imm(0xFFF)]),
            (
                AArch64Opcode::AddPCRel,
                vec![preg(X0), preg(X1), imm(0xFFF)],
            ),
        ];
        for (opcode, operands) in cases {
            encode_instruction(&mk(opcode, operands))
                .unwrap_or_else(|err| panic!("{opcode:?} imm12 boundary should encode: {err}"));
        }

        let w_inst = mk(
            AArch64Opcode::AddRIShift12,
            vec![preg(W0), preg(W1), imm(1)],
        );
        let w_enc = encode_instruction(&w_inst).unwrap();
        assert_eq!((w_enc >> 31) & 1, 0, "W-class AddRIShift12 must clear sf");
    }

    #[test]
    fn test_add_sub_imm12_rejects_out_of_range() {
        let cases = [
            (
                AArch64Opcode::AddRI,
                vec![preg(X0), preg(X1), imm(0x1000)],
                2,
            ),
            (
                AArch64Opcode::AddRIShift12,
                vec![preg(X0), preg(X1), imm(0x12345)],
                2,
            ),
            (AArch64Opcode::SubRI, vec![preg(X0), preg(X1), imm(-1)], 2),
            (AArch64Opcode::CmpRI, vec![preg(X0), imm(0x1000)], 1),
            (
                AArch64Opcode::AddsRI,
                vec![preg(X0), preg(X1), imm(0x1000)],
                2,
            ),
            (AArch64Opcode::SubsRI, vec![preg(X0), preg(X1), imm(-1)], 2),
            (AArch64Opcode::CMPWri, vec![preg(W0), imm(0x1000)], 1),
            (AArch64Opcode::CMPXri, vec![preg(X0), imm(-1)], 1),
            (
                AArch64Opcode::AddPCRel,
                vec![preg(X0), preg(X1), imm(0x1000)],
                2,
            ),
        ];
        for (opcode, operands, expected_index) in cases {
            let err = match encode_instruction(&mk(opcode, operands)) {
                Ok(enc) => panic!("{opcode:?} out-of-range imm12 encoded as {enc:#010X}"),
                Err(err) => err,
            };
            match err {
                EncodeError::InvalidOperand {
                    opcode: actual_opcode,
                    index,
                    desc,
                } => {
                    assert_eq!(actual_opcode, opcode);
                    assert_eq!(index, expected_index);
                    assert!(desc.contains("out of range [0, 4095]"));
                }
                other => panic!("expected InvalidOperand for {opcode:?}, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_mrs_tpidr_el0_x0() {
        // MRS X0, TPIDR_EL0 = 0xD53BD040
        let inst = mk(AArch64Opcode::Mrs, vec![preg(X0), imm(SYSREG_TPIDR_EL0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD53BD040, "MRS X0, TPIDR_EL0 = {enc:#010X}");
    }

    #[test]
    fn test_mrs_tpidr_el0_x1() {
        // MRS X1, TPIDR_EL0 = 0xD53BD041
        let inst = mk(AArch64Opcode::Mrs, vec![preg(X1), imm(SYSREG_TPIDR_EL0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD53BD041, "MRS X1, TPIDR_EL0 = {enc:#010X}");
    }

    #[test]
    fn test_mrs_tpidr_el0_x15() {
        // MRS X15, TPIDR_EL0 = 0xD53BD04F
        // X15 is not imported at the top of the test module; construct via
        // PReg::new to avoid touching the shared import list.
        let x15: PReg = PReg::new(15);
        let inst = mk(AArch64Opcode::Mrs, vec![preg(x15), imm(SYSREG_TPIDR_EL0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD53BD04F, "MRS X15, TPIDR_EL0 = {enc:#010X}");
    }

    #[test]
    fn test_mrs_tpidr_el0_x30() {
        // MRS X30, TPIDR_EL0 = 0xD53BD05E
        let inst = mk(AArch64Opcode::Mrs, vec![preg(X30), imm(SYSREG_TPIDR_EL0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD53BD05E, "MRS X30, TPIDR_EL0 = {enc:#010X}");
    }

    #[test]
    fn test_mrs_is_not_nop() {
        // Regression: MRS must not emit a NOP.
        let inst = mk(AArch64Opcode::Mrs, vec![preg(X0), imm(SYSREG_TPIDR_EL0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_ne!(enc, 0xD503201F, "MRS must not emit NOP");
    }

    #[test]
    fn test_mrs_bit_layout_invariants() {
        // For ANY Rt and ANY 16-bit sysreg, the fixed bits must be:
        //   bits[31:22] = 0b1101010100
        //   bit 21      = 1 (L=MRS)
        let rt_values = [0u32, 1, 2, 15, 16, 30, 31];
        let sysreg_samples: [i64; 4] = [
            0x0000,           // (not a valid sysreg but exercises extremes)
            SYSREG_TPIDR_EL0, // 0xDE82 — op0=11
            0xDA20,           // FPCR (11 011 0100 0100 000)
            0xFFFF,           // all ones
        ];
        for &rt in &rt_values {
            for &sr in &sysreg_samples {
                let rt_reg = PReg::new(rt as u16);
                let inst = mk(AArch64Opcode::Mrs, vec![preg(rt_reg), imm(sr)]);
                let enc = encode_instruction(&inst).unwrap();
                // bits[31:22] == 0b1101010100
                assert_eq!(
                    (enc >> 22) & 0x3FF,
                    0b1101010100,
                    "MRS fixed high bits, Rt={rt}, sysreg={sr:#06X}"
                );
                // bit 21 (L) = 1
                assert_eq!((enc >> 21) & 1, 1, "MRS L bit, Rt={rt}, sysreg={sr:#06X}");
                // bits[20:5] == sysreg (masked to 16 bits)
                assert_eq!(
                    (enc >> 5) & 0xFFFF,
                    (sr as u32) & 0xFFFF,
                    "MRS sysreg field, Rt={rt}, sysreg={sr:#06X}"
                );
                // bits[4:0] == Rt
                assert_eq!(enc & 0x1F, rt, "MRS Rt field, Rt={rt}, sysreg={sr:#06X}");
            }
        }
    }

    #[test]
    fn test_mrs_sysreg_high_bit_not_clobbered() {
        // Earlier drafts masked the systemreg to 15 bits, which would
        // silently drop the op0 high bit and produce a different register
        // (e.g., TPIDR_EL0 → TPIDR_EL1 or undefined encoding). This test
        // pins the 16-bit behavior.
        //
        // TPIDR_EL0 has op0=11, so the 16-bit sysreg 0xDE82 has its top bit
        // set. If we were masking to 15 bits (0x7FFF), the encoding would
        // differ from 0xD53BD040.
        let inst = mk(AArch64Opcode::Mrs, vec![preg(X0), imm(SYSREG_TPIDR_EL0)]);
        let enc = encode_instruction(&inst).unwrap();
        assert_eq!(enc, 0xD53BD040, "TPIDR_EL0 sysreg high bit preserved");
    }

    #[test]
    fn scalar_ri_offset_encodable_agrees_with_encoder() {
        // The offset legalizer decides what to rewrite using
        // `scalar_ri_offset_encodable`; it MUST agree bit-for-bit with the
        // encoder's own accept/reject decision, otherwise legalization would
        // either miss a failing offset (bug persists) or rewrite an in-range one
        // (byte-identity broken). Sweep every access size across the boundaries.
        for scale in [1i64, 2, 4, 8, 16] {
            for offset in -600i64..=(4100 * scale + 8) {
                let predicate = scalar_ri_offset_encodable(offset, scale);
                // size/v/opc/rn/rt do not affect the range decision.
                let encoder_ok = encode_load_store_auto(0b11, 0, 0, scale, offset, 0, 0).is_ok();
                assert_eq!(
                    predicate, encoder_ok,
                    "disagreement at scale={scale} offset={offset}: predicate={predicate} encoder_ok={encoder_ok}"
                );
            }
        }
    }

    #[test]
    fn scalar_ri_mem_scale_matches_transfer_width() {
        // Integer widths follow the transfer class; narrow/typed opcodes are fixed.
        assert_eq!(
            scalar_ri_mem_scale(&mk(AArch64Opcode::StrRI, vec![preg(X0), preg(X1)])),
            Some(8)
        );
        assert_eq!(
            scalar_ri_mem_scale(&mk(AArch64Opcode::StrRI, vec![preg(W0), preg(X1)])),
            Some(4)
        );
        assert_eq!(
            scalar_ri_mem_scale(&mk(AArch64Opcode::StrbRI, vec![preg(W0), preg(X1)])),
            Some(1)
        );
        assert_eq!(
            scalar_ri_mem_scale(&mk(AArch64Opcode::StrhRI, vec![preg(W0), preg(X1)])),
            Some(2)
        );
        // Not a scalar RI load/store form.
        assert_eq!(
            scalar_ri_mem_scale(&mk(AArch64Opcode::AddRI, vec![preg(X0), preg(X1), imm(4)])),
            None
        );
    }
}
