//! Exact post-allocation operand/word binding for the existing conditional
//! select model. This is neither a proof verdict nor a source-operation rule.

use super::{ConditionalSelectOperation as Op, DecodedConditionalSelect};
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, SpecialReg};

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ConditionalSelectBindingError {
    #[error("conditional-select intent: {0}")]
    Intent(&'static str),
    #[error(transparent)]
    Decode(#[from] super::ConditionalSelectError),
    #[error("conditional-select {field}: word {actual}, intent {expected}")]
    Field {
        field: &'static str,
        actual: u32,
        expected: u32,
    },
}

/// Return the actual `(sf, register)` fields for W/X GPR or zero-register
/// operands. SP, WSP, virtual registers and every other bank refuse. Encoding
/// 31 is accepted only with an explicit zero-register identity.
pub fn conditional_select_register_fields(operand: &MachOperand) -> Option<(u32, u32)> {
    match operand {
        MachOperand::PReg(p) => match p.encoding() {
            0..=30 => Some((1, u32::from(p.encoding()))),
            32..=62 => Some((0, u32::from(p.encoding() - 32))),
            160 => Some((1, 31)),
            161 => Some((0, 31)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some((1, 31)),
        MachOperand::Special(SpecialReg::WZR) => Some((0, 31)),
        _ => None,
    }
}

/// Bind every field of the supplied word to the actual machine operands,
/// returning the existing independently decoded semantics. CSET keeps its
/// architectural CSINC alias and excludes AL/NV inversion; ordinary select
/// variants retain conditions 0..15 and explicit discarded ZR destinations.
/// No reaching flag producer, source correspondence or proof credit follows.
pub fn bind_conditional_select_word(
    intent: &MachInst,
    word: u32,
) -> Result<DecodedConditionalSelect, ConditionalSelectBindingError> {
    use ConditionalSelectBindingError as E;
    let condition = |operand: &MachOperand, maximum| match operand {
        MachOperand::Imm(value) if (0..=maximum).contains(value) => Ok(*value as u32),
        _ => Err(E::Intent("invalid condition immediate")),
    };
    let register = |operand| {
        conditional_select_register_fields(operand)
            .ok_or(E::Intent("requires W/X GPR or ZR, not SP or another bank"))
    };
    let (operation, (sf, rd), rn, rm, cond) = match (intent.opcode, intent.operands.as_slice()) {
        (AArch64Opcode::CSet, [rd, cc]) => {
            (Op::Csinc, register(rd)?, 31, 31, condition(cc, 13)? ^ 1)
        }
        (
            AArch64Opcode::Csel
            | AArch64Opcode::Csinc
            | AArch64Opcode::Csinv
            | AArch64Opcode::Csneg,
            [rd, rn, rm, cc],
        ) => {
            let (sf, rd) = register(rd)?;
            let (rn_sf, rn) = register(rn)?;
            let (rm_sf, rm) = register(rm)?;
            if sf != rn_sf || sf != rm_sf {
                return Err(E::Intent("requires equal-width register operands"));
            }
            let op = match intent.opcode {
                AArch64Opcode::Csel => Op::Csel,
                AArch64Opcode::Csinc => Op::Csinc,
                AArch64Opcode::Csinv => Op::Csinv,
                AArch64Opcode::Csneg => Op::Csneg,
                _ => return Err(E::Intent("unsupported select operation")),
            };
            (op, (sf, rd), rn, rm, condition(cc, 15)?)
        }
        _ => return Err(E::Intent("unsupported opcode or operand count")),
    };
    let decoded = DecodedConditionalSelect::decode(word)?;
    if decoded.operation() != operation {
        return Err(E::Intent("decoded operation differs"));
    }
    let (actual_rd, actual_rn, actual_rm) = decoded.registers();
    for (field, actual, expected) in [
        ("sf", u32::from(decoded.width().bits() == 64), sf),
        ("Rd", u32::from(actual_rd), rd),
        ("Rn", u32::from(actual_rn), rn),
        ("Rm", u32::from(actual_rm), rm),
        ("condition", u32::from(decoded.condition()), cond),
    ] {
        if actual != expected {
            return Err(E::Field {
                field,
                actual,
                expected,
            });
        }
    }
    Ok(decoded)
}

#[cfg(test)]
#[path = "aarch64_csel_binding_tests.rs"]
mod tests;
