// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Direct source-to-byte correspondence for bounded scalar affine values and
//! integer predicates.
//!
//! The decoder below reads the actual little-endian A64 words independently
//! of the production encoder and MachIR. Register operands, immediates and
//! widths come only from those words. No producer origin or digest decides
//! equality. The complete stream must return through unchanged LR, preserve
//! SP and callee-saved registers, and have no externally addressed effects.
//!
//! The optional standard frame has exactly sixteen bytes: STP X29,X30 with
//! pre-decrement, MOV X29,SP, and matching post-increment LDP. Its claim assumes
//! the incoming SP is 16-byte aligned with sixteen writable private stack
//! bytes below it. Frame stores modify only that scratch area; they do not
//! promise equality of otherwise dead stack contents after return. The body
//! cannot access SP, frame memory, X18, callee-saved registers or LR.
//! NZCV is an ABI-clobbered output, not an unchanged-state guarantee. Every
//! admitted flag producer is interpreted even when its flags are later dead.
//! A bounded direct-control stream may have one conditional fork and a common
//! restore/return footer before a later laid-out arm. Both complete paths are
//! interpreted independently with this same scalar word evaluator.
//!
//! This is an executable semantic check, not a machine-checked refinement of
//! this Rust implementation. The private borrowed owner grants no proof-grade
//! JIT installation, serialization or cache authority. Any subsequent byte
//! mutation, including fixup application, requires another check.
//!
//! Decoder reference: Arm's A64 ISA, aarchmrs v2025-03_rel, instructions
//! ADD/SUB and CMP (immediate/shifted register), CSET/CSINC, MOV (register),
//! MOVN/MOVZ/MOVK, UBFM/LSL (immediate), STP/LDP and RET:
//! <https://documentation-service.arm.com/static/67e40f3398aa3c3b6eea6a85>.

use super::super::{
    Affine, AffineLoweringError, ComparisonFlags, Function, ScalarType, ScalarValue,
    source_contract,
};
use super::{TrustIrAffineLoweringError, trust_ir_contract};
use trust_ir::Module;

#[path = "aarch64_affine_byte_control.rs"]
mod control;

/// Source-domain refusal stays distinct from an unmodeled or invalid target.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AffineByteError {
    #[error("source contract rejected: {0}")]
    Source(#[from] TrustIrAffineLoweringError),
    #[error("invalid affine AArch64 bytes at {offset}: {reason}")]
    InvalidBytes { offset: usize, reason: String },
    #[error("unsupported affine AArch64 word {word:#010x} at byte {offset}")]
    UnsupportedBytes { offset: usize, word: u32 },
    #[error("TrustIR/LIR and final AArch64 bytes return different scalar values")]
    ReturnMismatch,
}

/// Counts of actual work and the explicitly modeled private stack footprint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AffineByteStatistics {
    pub trust_ir_instructions: usize,
    pub lir_instructions: usize,
    pub machine_instructions: usize,
    pub parameter_count: usize,
    pub private_stack_bytes: usize,
}

/// Immutable exact endpoints of a direct comparison, without publication authority.
///
/// The byte array cannot change while its checked owner is used:
///
/// ```compile_fail
/// use trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes;
/// fn mutate(module: &trust_ir::Module, lir: &trust_cg_lower::Function, bytes: &mut [u8]) {
///     let checked = check_aarch64_trust_ir_affine_bytes(module, 0, lir, bytes).unwrap();
///     bytes[0] ^= 1;
///     assert!(!checked.code().is_empty());
/// }
/// ```
#[derive(Debug)]
pub struct CheckedAarch64TrustIrAffineBytes<'a> {
    module: &'a Module,
    source: &'a trust_ir::Function,
    lir: &'a Function,
    code: &'a [u8],
    statistics: AffineByteStatistics,
    // The existing independent source/LIR/word comparison's exact result.
    // Kept private; a composed callee may retain this finite normal form only
    // after separately checking captured proof/request custody.
    result: Option<ScalarValue>,
}

impl<'a> CheckedAarch64TrustIrAffineBytes<'a> {
    pub(super) fn scalar_result(&self) -> Option<ScalarValue> {
        self.result
    }
    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        self.source
    }
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    pub fn code(&self) -> &'a [u8] {
        self.code
    }
    pub fn statistics(&self) -> AffineByteStatistics {
        self.statistics
    }
}

fn invalid(offset: usize, reason: impl Into<String>) -> AffineByteError {
    AffineByteError::InvalidBytes {
        offset,
        reason: reason.into(),
    }
}

fn word(code: &[u8], index: usize) -> u32 {
    let start = index * 4;
    u32::from_le_bytes([
        code[start],
        code[start + 1],
        code[start + 2],
        code[start + 3],
    ])
}

#[derive(Clone)]
struct Registers {
    values: [Option<ScalarValue>; 18],
}

impl Registers {
    fn read(&self, index: usize, bits: u32, offset: usize) -> Result<ScalarValue, AffineByteError> {
        if index == 31 {
            return Ok(integer(bits, Affine::constant(0, width_mask(bits))));
        }
        let value = self.values.get(index).copied().flatten().ok_or_else(|| {
            invalid(
                offset,
                format!("read of undefined or reserved register {index}"),
            )
        })?;
        // W writes zero the high half of X. Canonical Boolean values therefore
        // have the same meaning at either width. General 32-bit modular affine
        // values do not have an affine 64-bit interpretation; never widen them
        // by merely reusing their coefficients. Incoming I32 ABI high bits are
        // unknown as well, so the formal live-in initially has only W meaning.
        value
            .at_width(bits)
            .or_else(|| value.as_bool().map(ScalarValue::Bool))
            .ok_or_else(|| invalid(offset, "register width has no exact scalar interpretation"))
    }

    fn read_integer(
        &self,
        index: usize,
        bits: u32,
        offset: usize,
    ) -> Result<Affine, AffineByteError> {
        self.read(index, bits, offset)?
            .for_type(ScalarType::Integer(bits))
            .and_then(|value| value.as_affine(bits))
            .ok_or_else(|| invalid(offset, "integer operand is not an affine value"))
    }

    fn write(
        &mut self,
        index: usize,
        value: ScalarValue,
        offset: usize,
    ) -> Result<(), AffineByteError> {
        // Register 31 is ZR for every admitted body instruction. Immediate
        // ADD/SUB checks its different SP meaning before reaching this method.
        if index == 31 {
            return Ok(());
        }
        let slot = self.values.get_mut(index).ok_or_else(|| {
            invalid(
                offset,
                format!("write to reserved or callee-saved register {index}"),
            )
        })?;
        *slot = Some(value);
        Ok(())
    }
}

fn width_mask(bits: u32) -> u64 {
    if bits == 32 {
        u64::from(u32::MAX)
    } else {
        u64::MAX
    }
}

fn integer(bits: u32, value: Affine) -> ScalarValue {
    ScalarValue::Integer { bits, value }
}

/// The same actual-word evaluator serves straight-line code and both paths of
/// the bounded control driver. A clone copies only fixed-size scalar normal
/// forms; no source terms, opcode intent or producer provenance are consulted.
#[derive(Clone)]
struct ByteState {
    bits: u32,
    registers: Registers,
    comparison_flags: Option<ComparisonFlags>,
}

impl ByteState {
    fn new(bits: u32, parameter_count: usize) -> Result<Self, AffineByteError> {
        if !matches!(bits, 32 | 64) || parameter_count > 8 {
            return Err(invalid(
                0,
                "requires a 32/64-bit domain and at most eight register parameters",
            ));
        }
        let mut registers = Registers { values: [None; 18] };
        for (index, register) in registers.values[..parameter_count].iter_mut().enumerate() {
            *register = Some(integer(bits, Affine::parameter(index)));
        }
        Ok(Self {
            bits,
            registers,
            comparison_flags: None,
        })
    }

    fn step_word(&mut self, offset: usize, instruction: u32) -> Result<(), AffineByteError> {
        let bits = self.bits;
        let mask = width_mask(bits);
        let registers = &mut self.registers;
        let comparison_flags = &mut self.comparison_flags;
        if instruction == 0xd503201f {
            return Ok(());
        } // NOP, no register/world effect.
        let width = if instruction >> 31 != 0 { 64 } else { 32 };
        let rd = (instruction & 31) as usize;
        let rn = ((instruction >> 5) & 31) as usize;
        let rm = ((instruction >> 16) & 31) as usize;
        let family = instruction & 0x7f800000;
        if instruction & 0x7f20001f == 0x6b00001f {
            // CMP shifted register is SUBS ZR,Rn,Rm. These fields are decoded
            // from the ISA, not checked against an encoder-provided intent.
            // Only LSL preserves this bounded affine operand representation.
            if width != bits {
                return Err(invalid(offset, "CMP width differs from source domain"));
            }
            if (instruction >> 22) & 3 != 0 {
                return Err(AffineByteError::UnsupportedBytes {
                    offset,
                    word: instruction,
                });
            }
            let shift = (instruction >> 10) & 63;
            if shift >= width {
                return Err(invalid(offset, "reserved CMP register shift"));
            }
            let lhs = registers.read_integer(rn, width, offset)?;
            let mut rhs = registers.read_integer(rm, width, offset)?;
            for coefficient in &mut rhs.0 {
                *coefficient = coefficient.wrapping_shl(shift) & mask;
            }
            *comparison_flags = Some(ComparisonFlags::new(width, lhs, rhs));
            return Ok(());
        }
        if instruction & 0x7f80001f == 0x7100001f {
            // SUBS ZR,Rn,#imm: unlike register CMP, Rn=31 denotes SP.
            let lhs_value = registers.read(rn, width, offset)?;
            // W-width literal/copy 0/1 can retain its integer carrier rather
            // than the Bool enum case. Use the reaching value, not its enum
            // spelling, and preserve the actual width for subtraction NZCV.
            if width != bits && lhs_value.as_bool().is_none() {
                return Err(invalid(
                    offset,
                    "immediate CMP width differs from source domain",
                ));
            }
            if rn == 31 {
                return Err(invalid(offset, "body immediate CMP reads SP"));
            }
            let shift = if instruction & (1 << 22) != 0 { 12 } else { 0 };
            let immediate = u64::from((instruction >> 10) & 0xfff) << shift;
            *comparison_flags = Some(
                ComparisonFlags::from_values(
                    width,
                    lhs_value,
                    integer(width, Affine::constant(immediate, mask)),
                )
                .ok_or_else(|| {
                    invalid(offset, "CMP needs affine values or Boolean against zero")
                })?,
            );
            return Ok(());
        }
        let value = if instruction & 0x7fe0ffe0 == 0x2a0003e0 {
            // MOV register is precisely ORR Rd,ZR,Rm,LSL #0.
            registers.read(rm, width, offset)?
        } else if instruction & 0x7fff0fe0 == 0x1a9f07e0 {
            // CSINC Rd,ZR,ZR,cond yields the Boolean of the inverse condition.
            // The source comparison's width belongs to its NZCV producer, not
            // the destination: both W-CSET and X-CSET produce exact zero/one.
            let encoded_condition = ((instruction >> 12) & 15) as u8;
            if encoded_condition >= 14 {
                return Err(invalid(offset, "AL/NV is not a CSET condition"));
            }
            let predicate = comparison_flags
                .as_ref()
                .and_then(|flags| flags.condition(encoded_condition ^ 1))
                .ok_or_else(|| invalid(offset, "CSET lacks modeled CMP flags or condition"))?;
            ScalarValue::Bool(predicate)
        } else if let Ok(select) =
            crate::aarch64_csel_semantics::DecodedConditionalSelect::decode(instruction)
        {
            use crate::aarch64_csel_semantics::ConditionalSelectOperation;
            if width != bits {
                return Err(invalid(
                    offset,
                    "conditional select width differs from source domain",
                ));
            }
            let predicate = comparison_flags
                .as_ref()
                .and_then(|flags| flags.condition(select.condition()))
                .ok_or_else(|| {
                    invalid(
                        offset,
                        "conditional select lacks modeled CMP flags or condition",
                    )
                })?;
            let then_value = registers.read_integer(rn, width, offset)?;
            let mut else_value = registers.read_integer(rm, width, offset)?;
            match select.operation() {
                ConditionalSelectOperation::Csel => {}
                ConditionalSelectOperation::Csinc => {
                    else_value = else_value.combine(Affine::constant(1, mask), false, mask)
                }
                ConditionalSelectOperation::Csinv => {
                    else_value = Affine::constant(mask, mask).combine(else_value, true, mask)
                }
                ConditionalSelectOperation::Csneg => {
                    else_value = Affine::constant(0, mask).combine(else_value, true, mask)
                }
            }
            ScalarValue::select(width, predicate, then_value, else_value)
        } else if matches!(family, 0x12800000 | 0x52800000 | 0x72800000) {
            let shift = ((instruction >> 21) & 3) * 16;
            if shift >= width {
                return Err(invalid(offset, "reserved move-wide halfword"));
            }
            let immediate = u64::from((instruction >> 5) & 0xffff) << shift;
            let constant = match family {
                0x12800000 => !immediate, // MOVN
                0x52800000 => immediate,  // MOVZ
                _ => {
                    let old = registers.read(rd, width, offset)?.as_constant().ok_or(
                        AffineByteError::UnsupportedBytes {
                            offset,
                            word: instruction,
                        },
                    )?;
                    (old & !(0xffff_u64 << shift)) | immediate // MOVK
                }
            };
            integer(width, Affine::constant(constant, width_mask(width)))
        } else if family == 0x53000000 {
            // UBFM aliases LSL when imms+1 == immr. The zero shift is the
            // identity UBFM #0,#(width-1), commonly printed as LSR #0.
            // Other bitfield forms are not affine over the complete input.
            let n = (instruction >> 22) & 1;
            let immr = (instruction >> 16) & 63;
            let imms = (instruction >> 10) & 63;
            if width != bits || n != (width == 64) as u32 || immr >= width || imms >= width {
                return Err(invalid(offset, "reserved or mismatched UBFM width"));
            }
            let shift = if immr == 0 && imms == width - 1 {
                0
            } else if imms + 1 == immr {
                width - immr
            } else {
                return Err(AffineByteError::UnsupportedBytes {
                    offset,
                    word: instruction,
                });
            };
            let mut value = registers.read_integer(rn, width, offset)?;
            for coefficient in &mut value.0 {
                *coefficient = coefficient.wrapping_shl(shift) & mask;
            }
            integer(width, value)
        } else if matches!(instruction & 0x7f200000, 0x0b000000 | 0x4b000000) {
            // ADD/SUB shifted register, S=0; only left shifts are affine.
            if width != bits {
                return Err(invalid(
                    offset,
                    "arithmetic width differs from source domain",
                ));
            }
            if (instruction >> 22) & 3 != 0 {
                return Err(AffineByteError::UnsupportedBytes {
                    offset,
                    word: instruction,
                });
            }
            let shift = (instruction >> 10) & 63;
            if shift >= width {
                return Err(invalid(offset, "reserved register shift"));
            }
            let mut rhs = registers.read_integer(rm, width, offset)?;
            for coefficient in &mut rhs.0 {
                *coefficient = coefficient.wrapping_shl(shift) & mask;
            }
            integer(
                width,
                registers.read_integer(rn, width, offset)?.combine(
                    rhs,
                    instruction & (1 << 30) != 0,
                    mask,
                ),
            )
        } else if matches!(family, 0x11000000 | 0x51000000) {
            if width != bits {
                return Err(invalid(
                    offset,
                    "immediate arithmetic width differs from source domain",
                ));
            }
            if rn == 31 || rd == 31 {
                return Err(invalid(
                    offset,
                    "body immediate arithmetic reads or writes SP",
                ));
            }
            let shift = if instruction & (1 << 22) != 0 { 12 } else { 0 };
            let immediate = u64::from((instruction >> 10) & 0xfff) << shift;
            integer(
                width,
                registers.read_integer(rn, width, offset)?.combine(
                    Affine::constant(immediate, mask),
                    instruction & (1 << 30) != 0,
                    mask,
                ),
            )
        } else {
            return Err(AffineByteError::UnsupportedBytes {
                offset,
                word: instruction,
            });
        };
        registers.write(rd, value, offset)
    }

    fn result(
        &self,
        return_type: Option<ScalarType>,
        offset: usize,
    ) -> Result<Option<ScalarValue>, AffineByteError> {
        let Some(return_type) = return_type else {
            return Ok(None);
        };
        let return_width = match return_type {
            ScalarType::Integer(width) => width,
            ScalarType::Bool => 64,
        };
        Ok(Some(
            self.registers
                .read(0, return_width, offset)?
                .for_type(return_type)
                .ok_or(AffineByteError::ReturnMismatch)?,
        ))
    }
}

/// Shared exact standard envelope, including the return register. A nonempty
/// frame saves entry FP/LR before any body effect and restores both afterward.
fn linear_envelope(code: &[u8]) -> Result<(usize, usize, usize), AffineByteError> {
    if code.is_empty() || !code.len().is_multiple_of(4) {
        return Err(invalid(code.len(), "nonempty complete A64 words required"));
    }
    let count = code.len() / 4;
    if word(code, count - 1) != 0xd65f03c0 {
        return Err(invalid(code.len() - 4, "final instruction must be RET X30"));
    }
    if word(code, 0) == 0xa9bf7bfd {
        if count < 4 || word(code, 1) != 0x910003fd || word(code, count - 2) != 0xa8c17bfd {
            return Err(invalid(0, "unmatched sixteen-byte frame envelope"));
        }
        Ok((2, count - 2, 16))
    } else {
        Ok((0, count - 1, 0))
    }
}

#[path = "aarch64_defined_call_bytes.rs"]
mod defined_call;
pub use defined_call::{CheckedAarch64DefinedCallBytes, check_aarch64_defined_call_bytes};

fn byte_result(
    code: &[u8],
    bits: u32,
    parameter_count: usize,
    return_type: Option<ScalarType>,
) -> Result<(Option<ScalarValue>, usize), AffineByteError> {
    if code.is_empty() || !code.len().is_multiple_of(4) {
        return Err(invalid(code.len(), "nonempty complete A64 words required"));
    }
    if control::has_direct_control(code) {
        return control::evaluate(code, bits, parameter_count, return_type);
    }
    // Keep the existing linear/frameless envelope and all its refusals. Only
    // streams with direct branches use the bounded control-layout driver.
    let (start, end, private_stack_bytes) = linear_envelope(code)?;
    let mut state = ByteState::new(bits, parameter_count)?;
    for index in start..end {
        state.step_word(index * 4, word(code, index))?;
    }
    Ok((
        state.result(return_type, code.len() - 4)?,
        private_stack_bytes,
    ))
}

/// Compare the exact module-owned source, actual LIR and complete final bytes.
///
/// Source applicability is determined first. A supported source paired with an
/// unsupported target yields `UnsupportedBytes`, never `UnsupportedTrustIr`.
/// This API does not take pending fixups: its claim is about the exact supplied
/// bytes, and any relocation or patch invalidates that claim until rechecked.
pub fn check_aarch64_trust_ir_affine_bytes<'a>(
    module: &'a Module,
    function_ordinal: usize,
    lir: &'a Function,
    code: &'a [u8],
) -> Result<CheckedAarch64TrustIrAffineBytes<'a>, AffineByteError> {
    let selected = module.functions.get(function_ordinal).ok_or_else(|| {
        TrustIrAffineLoweringError::InvalidTrustIr("function ordinal is outside the module".into())
    })?;
    if selected.name != lir.name {
        return Err(TrustIrAffineLoweringError::TrustIrLirMismatch.into());
    }
    let source = trust_ir_contract(module, selected)?;
    let lowering_view;
    let lowering_source = if selected.blocks.len() == 4 {
        lowering_view = crate::source_bound_frame::raw_source_view(lir).ok_or_else(|| {
            TrustIrAffineLoweringError::Lowering(AffineLoweringError::UnsupportedMachine(
                "requires a bounded pure LIR chain or integer diamond".into(),
            ))
        })?;
        &lowering_view
    } else {
        // Keep the common scalar source borrowed. Control normalization must
        // not add a full LIR clone to every already-supported straight leaf.
        lir
    };
    let lowering = source_contract(lowering_source).map_err(TrustIrAffineLoweringError::from)?;
    if source.signature.params.len() != lir.signature.params.len()
        || source.signature.returns.len() != lir.signature.returns.len()
        || source.bits != lowering.bits
        || lowering
            .param_bits
            .iter()
            .any(|&bits| bits != lowering.bits)
        || source.return_type != lowering.return_type
        || source.result != lowering.result
    {
        return Err(TrustIrAffineLoweringError::TrustIrLirMismatch.into());
    }
    let (actual, private_stack_bytes) = byte_result(
        code,
        source.bits,
        source.signature.params.len(),
        source.return_type,
    )?;
    if actual != source.result {
        return Err(AffineByteError::ReturnMismatch);
    }
    Ok(CheckedAarch64TrustIrAffineBytes {
        module,
        source: selected,
        lir,
        code,
        statistics: AffineByteStatistics {
            trust_ir_instructions: source.instruction_count,
            lir_instructions: lir
                .blocks
                .values()
                .map(|block| block.instructions.len())
                .sum(),
            machine_instructions: code.len() / 4,
            parameter_count: source.signature.params.len(),
            private_stack_bytes,
        },
        result: source.result,
    })
}

#[cfg(test)]
mod tests {
    use super::super::super::{CompareKind, Predicate};
    use super::*;

    fn words(instructions: &[u32]) -> Vec<u8> {
        instructions
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect()
    }

    #[test]
    fn independently_assembled_lsl_immediates_match_modular_affine_values() {
        // GNU AArch64 as controls, using Rn=1 and Rd=0. Zero is printed LSR.
        for (bits, shift, instruction) in [
            (32, 0, 0x53007c20),
            (32, 1, 0x531f7820),
            (32, 31, 0x53010020),
            (64, 0, 0xd340fc20),
            (64, 1, 0xd37ff820),
            (64, 63, 0xd3410020),
        ] {
            let (actual, stack) = byte_result(
                &words(&[instruction, 0xd65f03c0]),
                bits,
                2,
                Some(ScalarType::Integer(bits)),
            )
            .unwrap();
            let mut value = Affine::parameter(1);
            for coefficient in &mut value.0 {
                *coefficient = coefficient.wrapping_shl(shift) & width_mask(bits);
            }
            assert_eq!(actual, Some(integer(bits, value)));
            assert_eq!(stack, 0);
        }
    }

    #[test]
    fn lsl_bytes_reject_reserved_width_fields_and_non_affine_bitfields() {
        for (bits, instruction) in [(32, 0x531f7820), (64, 0xd37ff820)] {
            for altered in [
                instruction ^ (1 << 22),                // N disagrees with sf.
                instruction ^ (1 << 31),                // sf disagrees with N/source.
                instruction ^ (1 << 10),                // Not a complete left shift.
                instruction ^ (1 << 16),                // Not a complete left shift.
                instruction | (1 << 29),                // BFM, not UBFM.
                (instruction & !(31 << 5)) | (18 << 5), // Reserved live-in.
                (instruction & !31) | 19,               // Callee-saved destination.
            ] {
                assert!(
                    byte_result(
                        &words(&[altered, 0xd65f03c0]),
                        bits,
                        2,
                        Some(ScalarType::Integer(bits))
                    )
                    .is_err(),
                    "{bits}/{altered:08x}"
                );
            }
        }
        for instruction in [0x531f7820 | (1 << 21), 0x531f7820 | (1 << 15)] {
            assert!(
                byte_result(
                    &words(&[instruction, 0xd65f03c0]),
                    32,
                    2,
                    Some(ScalarType::Integer(32))
                )
                .is_err()
            );
        }
    }

    fn boolean_result(instructions: &[u32], bits: u32, parameters: usize) -> ScalarValue {
        let (result, stack) = byte_result(
            &words(instructions),
            bits,
            parameters,
            Some(ScalarType::Bool),
        )
        .unwrap();
        assert_eq!(stack, 0);
        result.unwrap()
    }

    fn predicate(bits: u32, kind: CompareKind, lhs: Affine, rhs: Affine) -> ScalarValue {
        ScalarValue::Bool(Predicate::compare(kind, lhs, rhs, false, bits))
    }

    #[test]
    fn independently_assembled_cmp_and_cset_keep_producer_and_result_widths_separate() {
        // Literal controls were assembled with GNU AArch64 as. In particular,
        // both `cset w0,eq` and `cset x0,eq` implement the same canonical Bool.
        for (bits, cmp) in [(32, 0x6b01001f), (64, 0xeb01001f)] {
            let expected = predicate(
                bits,
                CompareKind::Equal,
                Affine::parameter(0),
                Affine::parameter(1),
            );
            for cset in [0x1a9f17e0, 0x9a9f17e0] {
                assert_eq!(boolean_result(&[cmp, cset, 0xd65f03c0], bits, 2), expected);
            }
        }
        // A source I32 live-in does not promise anything about incoming X0's
        // high half. An X-width CMP must not silently reuse its W meaning.
        assert!(
            byte_result(
                &words(&[0xeb01001f, 0x9a9f17e0, 0xd65f03c0]),
                32,
                2,
                Some(ScalarType::Bool)
            )
            .is_err()
        );
        assert!(
            byte_result(
                &words(&[0x6b01001f, 0x9a9f17e0, 0xd65f03c0]),
                64,
                2,
                Some(ScalarType::Bool)
            )
            .is_err()
        );
    }

    #[test]
    fn cmp_flags_snapshot_survives_moves_and_is_replaced_by_the_next_cmp() {
        let expected = predicate(
            64,
            CompareKind::SignedLess,
            Affine::parameter(0),
            Affine::parameter(1),
        );
        // cmp x0,x1; mov x0,x2; nop; cset x0,lt; ret.
        assert_eq!(
            boolean_result(
                &[0xeb01001f, 0xaa0203e0, 0xd503201f, 0x9a9fa7e0, 0xd65f03c0],
                64,
                3
            ),
            expected
        );
        // The second CMP reads the changed X0, and becomes the sole producer.
        assert_eq!(
            boolean_result(
                &[0xeb01001f, 0xaa0203e0, 0xeb01001f, 0x9a9fa7e0, 0xd65f03c0],
                64,
                3
            ),
            predicate(
                64,
                CompareKind::SignedLess,
                Affine::parameter(2),
                Affine::parameter(1)
            )
        );
        // Non-flag-setting ADD changes its destination without changing NZCV.
        assert_eq!(
            boolean_result(&[0xeb01001f, 0x8b010000, 0x9a9fa7e0, 0xd65f03c0], 64, 2),
            expected
        );
        // An unmodeled ADDS cannot be ignored, even if CSET still follows it.
        assert!(matches!(
            byte_result(
                &words(&[0xeb01001f, 0xab010009, 0x9a9fa7e0, 0xd65f03c0]),
                64,
                2,
                Some(ScalarType::Bool)
            ),
            Err(AffineByteError::UnsupportedBytes { offset: 4, .. })
        ));
        assert!(
            byte_result(
                &words(&[0x9a9f17e0, 0xd65f03c0]),
                64,
                2,
                Some(ScalarType::Bool)
            )
            .is_err()
        );
    }

    #[test]
    fn byte_boolean_transport_requires_known_zero_or_one_and_never_unknown_high_bits() {
        for mov in [0x52800020, 0xd2800020] {
            // mov w0,#1 / mov x0,#1
            assert_eq!(
                boolean_result(&[mov, 0xd65f03c0], 64, 0),
                ScalarValue::Bool(Predicate::Constant(true))
            );
        }
        // MOV W9,W0 zero-extends at runtime, but arbitrary modular32 values
        // cannot be reinterpreted as affine64 coefficients by MOV X0,X9.
        assert!(
            byte_result(
                &words(&[0x2a0003e9, 0xaa0903e0, 0xd65f03c0]),
                32,
                1,
                Some(ScalarType::Bool)
            )
            .is_err()
        );
        // mov w0,#2 is not a canonical Boolean despite its known upper bits.
        assert!(
            byte_result(
                &words(&[0x52800040, 0xd65f03c0]),
                64,
                0,
                Some(ScalarType::Bool)
            )
            .is_err()
        );
        // W-CSET followed by X-MOV is instead exact at both widths.
        assert_eq!(
            boolean_result(&[0x6b01001f, 0x1a9f17e9, 0xaa0903e0, 0xd65f03c0], 32, 2),
            predicate(
                32,
                CompareKind::Equal,
                Affine::parameter(0),
                Affine::parameter(1)
            )
        );
    }

    #[test]
    fn cmp_immediate_and_register_31_have_distinct_meanings() {
        for (bits, immediate, zero_register, sp) in [
            (32, 0x717ffc1f, 0x6b1f001f, 0x710003ff),
            (64, 0xf17ffc1f, 0xeb1f001f, 0xf10003ff),
        ] {
            assert_eq!(
                boolean_result(&[immediate, 0x9a9f17e0, 0xd65f03c0], bits, 1),
                predicate(
                    bits,
                    CompareKind::Equal,
                    Affine::parameter(0),
                    Affine::constant(0xfff000, width_mask(bits))
                )
            );
            assert_eq!(
                boolean_result(&[zero_register, 0x9a9f17e0, 0xd65f03c0], bits, 1),
                predicate(
                    bits,
                    CompareKind::Equal,
                    Affine::parameter(0),
                    Affine::constant(0, width_mask(bits))
                )
            );
            // SP/WSP immediate CMP is a valid ISA encoding, but outside this
            // checker's no-SP body contract, not an architectural ZR operand.
            assert!(matches!(
                byte_result(
                    &words(&[sp, 0x9a9f17e0, 0xd65f03c0]),
                    bits,
                    1,
                    Some(ScalarType::Bool)
                ),
                Err(AffineByteError::InvalidBytes { offset: 0, .. })
            ));
        }
    }

    #[test]
    fn reserved_cmp_fields_and_unmodeled_cset_conditions_fail_closed() {
        for cmp in [
            0x6b01801f, // W shift #32 is reserved.
            0xebc1001f, // Shift kind 11 is reserved.
            0xeb41001f, // LSR is valid ISA, but not affine in this domain.
            0xeb81001f, // ASR is likewise outside the modeled LSL domain.
            0xeb21001f, // Extended-register form is not shifted-register CMP.
        ] {
            assert!(
                byte_result(
                    &words(&[cmp, 0x9a9f17e0, 0xd65f03c0]),
                    if cmp >> 31 == 0 { 32 } else { 64 },
                    2,
                    Some(ScalarType::Bool)
                )
                .is_err(),
                "{cmp:08x}"
            );
        }
        for condition in [4, 5, 6, 7, 14, 15] {
            let cset = 0x9a9f07e0 | ((condition ^ 1) << 12);
            assert!(
                byte_result(
                    &words(&[0xeb01001f, cset, 0xd65f03c0]),
                    64,
                    2,
                    Some(ScalarType::Bool)
                )
                .is_err(),
                "condition {condition}"
            );
        }
        // A non-ZR CSINC operand is not a CSET, even if an intent says it is.
        for cset in [0x9a8017e0, 0x9a9f1000] {
            assert!(
                byte_result(
                    &words(&[0xeb01001f, cset, 0xd65f03c0]),
                    64,
                    2,
                    Some(ScalarType::Bool)
                )
                .is_err()
            );
        }
        // CSNEG X0,ZR,ZR,NE is a valid constant-zero computation, not CSET.
        // The general select decoder may model it, but cannot confuse that
        // result with the original source equality predicate.
        let zero = boolean_result(&[0xeb01001f, 0xda9f17e0, 0xd65f03c0], 64, 2);
        assert_eq!(zero, ScalarValue::Bool(Predicate::Constant(false)));
        assert_ne!(
            zero,
            predicate(
                64,
                CompareKind::Equal,
                Affine::parameter(0),
                Affine::parameter(1)
            )
        );
    }
}
