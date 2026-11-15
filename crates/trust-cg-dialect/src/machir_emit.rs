// trust-cg-dialect - machir.* -> trust_cg_ir::MachFunction adapter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Translate the straight-line `machir.*` facade into `trust_cg_ir::MachFunction`.
//! The public boundary checks layout, SSA definition order, canonical opcode
//! types and return shape independently of conversion/legality passes.
//!
//! Only ops from the `machir` dialect are accepted. Encountering any other
//! dialect is an [`EmitError::UnexpectedDialect`]. Variants not yet
//! implemented by the dedicated emitters raise [`EmitError::Unsupported`].
//! Multiple blocks, block parameters and block-reference attributes are not
//! implemented here and are refused instead of flattened or dropped. This
//! adapter supports I64 parameters and an optional I64 return: it inserts entry
//! transfers from X0–X7 or incoming stack slots, and moves a result to X0 before
//! RET. Full-width constants expand into MOVZ/MOVK halfwords. Allocation, frame
//! lowering and encoding remain downstream; other ABI types are unsupported.

use std::collections::BTreeMap;

use trust_cg_ir::regs::{ARG_GPRS, FP, RegClass, X0};
use trust_cg_ir::{
    AArch64Opcode, BlockId as MachBlockId, MachFunction, MachInst, MachOperand, Signature, VReg,
};

use crate::dialect::Dialect;
use crate::dialects::machir::{self, MACHIR_ADD_RR, MACHIR_EOR_RR, MACHIR_MOVZ_I64, MACHIR_RET};
use crate::id::{DialectId, ValueId};
use crate::module::{DialectFunction, DialectModule};
use crate::op::Attribute;
use crate::pass::validate_type_constraints_with_env;

/// Error returned by [`emit_mach_function`].
#[derive(Debug, Clone)]
pub enum EmitError {
    /// Public function index is outside the module's function list.
    MissingFunction { index: usize, functions: usize },
    /// Invalid layout or SSA/return shape for the straight-line facade.
    InvalidFunction(String),
    /// No fresh machine register ID can be issued.
    VirtualRegisterExhausted,
    /// Instruction expansion exceeded the machine arena's ID domain.
    InstructionIdExhausted,
    /// Encountered an op belonging to a dialect other than `machir`.
    UnexpectedDialect {
        expected: DialectId,
        got: DialectId,
        op_name: String,
    },
    /// An opcode, ABI type or machine-emission shape is not implemented.
    Unsupported(String),
    /// Op has an unexpected shape (wrong operand count / missing attribute).
    Malformed(String),
    /// Referenced a SSA value that no preceding op defined.
    UndefinedValue(ValueId),
}

impl std::fmt::Display for EmitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EmitError::MissingFunction { index, functions } => write!(
                f,
                "function index {index} is outside module with {functions} function(s)"
            ),
            EmitError::InvalidFunction(m) => write!(f, "invalid machir function: {m}"),
            EmitError::VirtualRegisterExhausted => {
                write!(f, "machine virtual-register ID space exhausted")
            }
            EmitError::InstructionIdExhausted => {
                write!(f, "machine instruction ID space exhausted")
            }
            EmitError::UnexpectedDialect {
                expected,
                got,
                op_name,
            } => write!(
                f,
                "expected machir dialect {:?}, got {:?} for op {}",
                expected, got, op_name
            ),
            EmitError::Unsupported(m) => write!(f, "unsupported machir op: {}", m),
            EmitError::Malformed(m) => write!(f, "malformed machir op: {}", m),
            EmitError::UndefinedValue(v) => write!(f, "undefined SSA value {:?}", v),
        }
    }
}

impl std::error::Error for EmitError {}

/// Translate a fully-lowered `machir.*` [`DialectFunction`] into a
/// `MachFunction`. Requires one block with a final return and no block arguments
/// or references. I64 parameters map to the first N fresh VRegs regardless of
/// their SSA IDs, with explicit ABI entry transfers. Returns are void or I64.
/// The module is borrowed immutably; an error publishes no partial machine
/// function. Register and instruction-ID exhaustion are diagnostic.
pub fn emit_mach_function(
    module: &DialectModule,
    func_index: usize,
) -> Result<MachFunction, EmitError> {
    let func = module
        .functions
        .get(func_index)
        .ok_or(EmitError::MissingFunction {
            index: func_index,
            functions: module.functions.len(),
        })?;
    let machir_id = module
        .registry
        .by_name("machir")
        .ok_or_else(|| EmitError::Malformed("machir dialect is not registered".to_string()))?;
    func.validate_structure()
        .map_err(EmitError::InvalidFunction)?;
    validate_emission_input(module, func, machir_id)?;

    let sig = Signature::new(
        func.params.iter().map(|(_, t)| t.clone()).collect(),
        func.results.clone(),
    );
    let mut mf = MachFunction::new(func.name.clone(), sig);
    let entry = mf.entry;

    // Admitted I64 parameters map to fresh VReg IDs 0..N-1.
    let mut value_to_vreg: BTreeMap<ValueId, VReg> = BTreeMap::new();
    let register_params = func.params.len().min(ARG_GPRS.len());
    for (index, (src, ty)) in func.params.iter().enumerate() {
        let id = mf
            .try_alloc_vreg()
            .ok_or(EmitError::VirtualRegisterExhausted)?;
        let class = RegClass::for_type(ty);
        let destination = VReg::new(id, class);
        value_to_vreg.insert(*src, destination);
        let inst = if let Some(&source) = ARG_GPRS.get(index) {
            // Keep later ABI inputs live while this prefix is allocated. A
            // temporary must not overwrite Xn before its own entry copy reads it.
            MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::VReg(destination), MachOperand::PReg(source)],
            )
            .with_implicit_uses(&ARG_GPRS[index + 1..register_params])
        } else {
            let offset = stack_argument_offset(index)?;
            MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::VReg(destination),
                    MachOperand::PReg(FP),
                    MachOperand::IncomingArg(offset),
                ],
            )
        };
        append(&mut mf, entry, inst)?;
    }

    for op in func.iter_ops() {
        match op.op.op {
            MACHIR_MOVZ_I64 => emit_movz(op, &mut mf, &mut value_to_vreg, entry)?,
            MACHIR_ADD_RR => {
                emit_binary(op, &mut mf, &mut value_to_vreg, entry, AArch64Opcode::AddRR)?
            }
            MACHIR_EOR_RR => {
                emit_binary(op, &mut mf, &mut value_to_vreg, entry, AArch64Opcode::EorRR)?
            }
            MACHIR_RET => emit_ret(op, &mut mf, &value_to_vreg, entry)?,
            other => {
                // An opcode mapping alone is not an emitter: refuse rather
                // than inventing an instruction with unspecified operands.
                if let Some(opcode) = machir::to_aarch64(other) {
                    return Err(EmitError::Unsupported(format!(
                        "no dedicated emitter for machir op {:?} ({:?})",
                        other, opcode
                    )));
                }
                return Err(EmitError::Unsupported(format!(
                    "unknown machir opcode {:?}",
                    other
                )));
            }
        }
    }

    Ok(mf)
}

/// Layout has already been checked. Validate only this function, using the
/// canonical facade definitions that the hard-coded emitters actually implement,
/// not potentially replaced registry metadata with the same namespace.
fn validate_emission_input(
    module: &DialectModule,
    func: &DialectFunction,
    machir_id: DialectId,
) -> Result<(), EmitError> {
    if func
        .params
        .iter()
        .any(|(_, ty)| *ty != trust_cg_ir::Type::I64)
    {
        return Err(EmitError::Unsupported(
            "machine facade parameters must be I64".into(),
        ));
    }
    if func.blocks.len() != 1 || func.blocks.iter().any(|block| !block.params.is_empty()) {
        return Err(EmitError::Unsupported(
            "machine emission requires one block without block parameters".into(),
        ));
    }
    let invalid = |message: String| EmitError::InvalidFunction(format!("{}: {message}", func.name));
    let mut values = BTreeMap::new();
    for (value, ty) in &func.params {
        if values.insert(*value, ty.clone()).is_some() {
            return Err(invalid(format!("duplicate SSA definition {value:?}")));
        }
    }
    let canonical = machir::MachirDialect::new();
    let mut returned = false;
    for op in func.iter_ops() {
        if returned {
            return Err(invalid(format!("operation {:?} follows machir.ret", op.id)));
        }
        if op.op.dialect != machir_id {
            return Err(EmitError::UnexpectedDialect {
                expected: machir_id,
                got: op.op.dialect,
                op_name: module
                    .resolve(op.op)
                    .map(|def| def.name.to_string())
                    .unwrap_or_else(|| format!("<unregistered op {:?}>", op.op)),
            });
        }
        if !op.block_refs().is_empty() {
            return Err(EmitError::Unsupported(format!(
                "block references on {:?}",
                op.id
            )));
        }
        let definition = canonical.op_def(op.op.op).ok_or_else(|| {
            EmitError::Unsupported(format!("unknown machir opcode {:?}", op.op.op))
        })?;
        for operand in &op.operands {
            if !values.contains_key(operand) {
                return Err(EmitError::UndefinedValue(*operand));
            }
        }
        validate_type_constraints_with_env(op, definition, &values)
            .map_err(|error| EmitError::Malformed(error.to_string()))?;
        if op.op.op == MACHIR_RET {
            if op.operands.len() != func.results.len()
                || op
                    .operands
                    .iter()
                    .zip(&func.results)
                    .any(|(value, ty)| values.get(value) != Some(ty))
            {
                return Err(invalid(
                    "return does not match the function signature".into(),
                ));
            }
            returned = true;
        }
        for (value, ty) in &op.results {
            if values.insert(*value, ty.clone()).is_some() {
                return Err(invalid(format!("duplicate SSA definition {value:?}")));
            }
        }
    }
    if !returned {
        return Err(invalid("missing final machir.ret".into()));
    }
    Ok(())
}

fn emit_movz(
    op: &crate::op::DialectOp,
    mf: &mut MachFunction,
    value_to_vreg: &mut BTreeMap<ValueId, VReg>,
    block: MachBlockId,
) -> Result<(), EmitError> {
    if op.results.len() != 1 || !op.operands.is_empty() {
        return Err(EmitError::Malformed(
            "machir.movz.i64 expects 0 operands and 1 result".to_string(),
        ));
    }
    let (src_result, ty) = op.results[0].clone();
    let imm = op
        .attr("value")
        .and_then(|a| match a {
            Attribute::U64(v) => Some(*v as i64),
            Attribute::I64(v) => Some(*v),
            _ => None,
        })
        .ok_or_else(|| {
            EmitError::Malformed("machir.movz.i64 missing i64/u64 `value` attribute".to_string())
        })?;

    let dst = mf
        .try_alloc_vreg()
        .ok_or(EmitError::VirtualRegisterExhausted)?;
    let dst_reg = VReg::new(dst, RegClass::for_type(&ty));
    value_to_vreg.insert(src_result, dst_reg);

    let bits = imm as u64;
    let inst = MachInst::new(
        AArch64Opcode::Movz,
        vec![
            MachOperand::VReg(dst_reg),
            MachOperand::Imm((bits & 0xffff) as i64),
        ],
    );
    append(mf, block, inst)?;
    // MOVZ at shift zero establishes every high bit as zero. Only nonzero
    // remaining halfwords need MOVK; signed inputs retain their full bit pattern.
    for shift in [16, 32, 48] {
        let halfword = ((bits >> shift) & 0xffff) as i64;
        if halfword != 0 {
            append(
                mf,
                block,
                MachInst::new(
                    AArch64Opcode::Movk,
                    vec![
                        MachOperand::VReg(dst_reg),
                        MachOperand::Imm(halfword),
                        MachOperand::Imm(shift),
                    ],
                ),
            )?;
        }
    }
    Ok(())
}

fn emit_binary(
    op: &crate::op::DialectOp,
    mf: &mut MachFunction,
    value_to_vreg: &mut BTreeMap<ValueId, VReg>,
    block: MachBlockId,
    opcode: AArch64Opcode,
) -> Result<(), EmitError> {
    if op.operands.len() != 2 || op.results.len() != 1 {
        return Err(EmitError::Malformed(format!(
            "{:?} expects 2 operands and 1 result",
            opcode
        )));
    }
    let a = *value_to_vreg
        .get(&op.operands[0])
        .ok_or(EmitError::UndefinedValue(op.operands[0]))?;
    let b = *value_to_vreg
        .get(&op.operands[1])
        .ok_or(EmitError::UndefinedValue(op.operands[1]))?;
    let (src_result, ty) = op.results[0].clone();
    let dst_id = mf
        .try_alloc_vreg()
        .ok_or(EmitError::VirtualRegisterExhausted)?;
    let dst_reg = VReg::new(dst_id, RegClass::for_type(&ty));
    value_to_vreg.insert(src_result, dst_reg);

    let inst = MachInst::new(
        opcode,
        vec![
            MachOperand::VReg(dst_reg),
            MachOperand::VReg(a),
            MachOperand::VReg(b),
        ],
    );
    append(mf, block, inst)?;
    Ok(())
}

fn emit_ret(
    op: &crate::op::DialectOp,
    mf: &mut MachFunction,
    value_to_vreg: &BTreeMap<ValueId, VReg>,
    block: MachBlockId,
) -> Result<(), EmitError> {
    if op.operands.len() > 1 {
        return Err(EmitError::Malformed(
            "machir.ret expects 0 or 1 operands".to_string(),
        ));
    }
    // RET only transfers control. Make the ABI value transfer explicit and
    // keep X0 live through the return so later allocation/cleanup preserves it.
    if let Some(val) = op.operands.first() {
        let vreg = *value_to_vreg
            .get(val)
            .ok_or(EmitError::UndefinedValue(*val))?;
        append(
            mf,
            block,
            MachInst::new(
                AArch64Opcode::MovR,
                vec![MachOperand::PReg(X0), MachOperand::VReg(vreg)],
            ),
        )?;
    }
    let inst = MachInst::new(AArch64Opcode::Ret, vec![])
        .with_implicit_uses(if op.operands.is_empty() { &[] } else { &[X0] });
    append(mf, block, inst)?;
    Ok(())
}

fn append(mf: &mut MachFunction, block: MachBlockId, inst: MachInst) -> Result<(), EmitError> {
    let inst_id = mf
        .try_push_inst(inst)
        .ok_or(EmitError::InstructionIdExhausted)?;
    mf.append_inst(block, inst_id);
    Ok(())
}

fn stack_argument_offset(index: usize) -> Result<i64, EmitError> {
    index
        .checked_sub(ARG_GPRS.len())
        .and_then(|slot| i64::try_from(slot).ok())
        .and_then(|slot| slot.checked_mul(8))
        .ok_or_else(|| {
            EmitError::Unsupported("incoming I64 argument offset exceeds the machine domain".into())
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{DialectOpId, OpId};
    use crate::op::DialectOp;
    use trust_cg_ir::{InstId, Type};

    #[test]
    fn emission_boundary_stack_argument_offset_is_checked() {
        assert_eq!(stack_argument_offset(8).unwrap(), 0);
        assert_eq!(stack_argument_offset(9).unwrap(), 8);
        assert!(stack_argument_offset(7).is_err());
        let first_overflow = i64::MAX as u64 / 8 + 9;
        if let Ok(index) = usize::try_from(first_overflow) {
            assert!(stack_argument_offset(index).is_err());
            assert!(stack_argument_offset(usize::MAX).is_err());
        }
    }

    #[test]
    fn emission_boundary_movz_exhaustion_preserves_state() {
        let mut mf = MachFunction::new("exhausted".into(), Signature::new(vec![], vec![]));
        mf.next_vreg = u32::MAX;
        let entry = mf.entry;
        let mut values = BTreeMap::new();
        let op = DialectOp {
            id: OpId(0),
            op: DialectOpId::new(DialectId(0), MACHIR_MOVZ_I64),
            results: vec![(ValueId(0), Type::I64)],
            operands: vec![],
            attrs: vec![("value".into(), Attribute::U64(7))],
            source: None,
        };
        let before = format!("{mf:?}");
        assert!(matches!(
            emit_movz(&op, &mut mf, &mut values, entry),
            Err(EmitError::VirtualRegisterExhausted)
        ));
        assert_eq!(format!("{mf:?}"), before);
        assert!(values.is_empty());
    }

    #[test]
    fn emission_boundary_binary_exhaustion_preserves_state() {
        let mut mf = MachFunction::new("exhausted".into(), Signature::new(vec![], vec![]));
        mf.next_vreg = u32::MAX;
        let entry = mf.entry;
        let mut values = BTreeMap::from([(ValueId(0), VReg::new(0, RegClass::Gpr64))]);
        let op = DialectOp {
            id: OpId(0),
            op: DialectOpId::new(DialectId(0), MACHIR_ADD_RR),
            results: vec![(ValueId(1), Type::I64)],
            operands: vec![ValueId(0), ValueId(0)],
            attrs: vec![],
            source: None,
        };
        let before = format!("{mf:?}");
        let before_values = values.clone();
        assert!(matches!(
            emit_binary(&op, &mut mf, &mut values, entry, AArch64Opcode::AddRR),
            Err(EmitError::VirtualRegisterExhausted)
        ));
        assert_eq!(format!("{mf:?}"), before);
        assert_eq!(values, before_values);
    }

    #[test]
    fn emission_boundary_last_register_is_usable_by_both_emitters() {
        for binary in [false, true] {
            let mut mf = MachFunction::new("last_register".into(), Signature::new(vec![], vec![]));
            mf.next_vreg = u32::MAX - 1;
            let entry = mf.entry;
            let mut values = BTreeMap::from([(ValueId(0), VReg::new(0, RegClass::Gpr64))]);
            let op = DialectOp {
                id: OpId(0),
                op: DialectOpId::new(
                    DialectId(0),
                    if binary {
                        MACHIR_ADD_RR
                    } else {
                        MACHIR_MOVZ_I64
                    },
                ),
                results: vec![(ValueId(1), Type::I64)],
                operands: if binary {
                    vec![ValueId(0), ValueId(0)]
                } else {
                    vec![]
                },
                attrs: vec![("value".into(), Attribute::U64(7))],
                source: None,
            };
            if binary {
                emit_binary(&op, &mut mf, &mut values, entry, AArch64Opcode::AddRR).unwrap();
            } else {
                emit_movz(&op, &mut mf, &mut values, entry).unwrap();
            }
            let expected = VReg::new(u32::MAX - 1, RegClass::Gpr64);
            assert_eq!(values[&ValueId(1)], expected);
            assert_eq!(mf.next_vreg, u32::MAX);
            assert_eq!(mf.insts.len(), 1);
            assert_eq!(mf.insts[0].operands[0], MachOperand::VReg(expected));
            assert_eq!(mf.blocks[0].insts, [InstId(0)]);
        }
    }

    #[test]
    fn emission_boundary_return_needs_no_fresh_register() {
        let mut mf = MachFunction::new("return".into(), Signature::new(vec![], vec![]));
        mf.next_vreg = u32::MAX;
        let entry = mf.entry;
        let op = DialectOp {
            id: OpId(0),
            op: DialectOpId::new(DialectId(0), MACHIR_RET),
            results: vec![],
            operands: vec![],
            attrs: vec![],
            source: None,
        };
        emit_ret(&op, &mut mf, &BTreeMap::new(), entry).unwrap();
        assert_eq!(mf.next_vreg, u32::MAX);
        assert_eq!(mf.insts.len(), 1);
        assert_eq!(mf.insts[0].opcode, AArch64Opcode::Ret);
    }
}
