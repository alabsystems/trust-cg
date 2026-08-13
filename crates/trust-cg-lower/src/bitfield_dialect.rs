// trust-cg-lower/bitfield_dialect.rs - Trust Codegen-owned typed trust_ir bitfield dialect
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Small typed trust_ir dialect surface for Trust Codegen-local operations.
//!
//! The pinned core `trust_ir` crate does not currently expose first-class
//! `ExtractBits` / `SextractBits` / `InsertBits` instructions or compact
//! vector mask-to-scalar extraction. This dialect gives the public typed trust_ir
//! compile path a structured, validated route to those Trust Codegen LIR opcodes.

use trust_ir::dialect::{AttrValue, Dialect, DialectError, DialectInst};
use trust_ir::{Ty, ValueId};

pub const DIALECT: &str = "trust-cg";
pub const EXTRACT_OP: &str = "bitfield.extract";
pub const SEXTRACT_OP: &str = "bitfield.sextract";
pub const INSERT_OP: &str = "bitfield.insert";
pub const V4I32_MASK_EXTRACT_OP: &str = "mask.v4i32.extract";
pub const V2I64_MASK_EXTRACT_OP: &str = "mask.v2i64.extract";
pub const V2I64_BOOL_MASK_EXTRACT_OP: &str = "mask.v2i64.bool.extract";

const BITFIELD_OPS: &[&str] = &[EXTRACT_OP, SEXTRACT_OP, INSERT_OP];
const OPS: &[&str] = &[
    EXTRACT_OP,
    SEXTRACT_OP,
    INSERT_OP,
    V4I32_MASK_EXTRACT_OP,
    V2I64_MASK_EXTRACT_OP,
    V2I64_BOOL_MASK_EXTRACT_OP,
];
const VALIDATE_PASS: &str = "trust-cg.local.validate";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitfieldKind {
    Extract,
    Sextract,
    Insert,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitfieldSpec {
    pub kind: BitfieldKind,
    pub ty: Ty,
    pub lsb: u8,
    pub width: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct V4I32MaskExtractSpec {
    pub result_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct V2I64MaskExtractSpec {
    pub result_ty: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct V2I64BoolMaskExtractSpec {
    pub result_ty: Ty,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct BitfieldDialect;

impl Dialect for BitfieldDialect {
    fn name(&self) -> &'static str {
        DIALECT
    }

    fn version(&self) -> u32 {
        1
    }

    fn ops(&self) -> &'static [&'static str] {
        OPS
    }

    fn validate(&self, inst: &DialectInst) -> Result<(), DialectError> {
        if inst.dialect != self.name() {
            return Err(DialectError::NameMismatch {
                expected: self.name(),
                got: inst.dialect.clone(),
            });
        }
        if !self.has_op(&inst.op) {
            return Err(DialectError::UnknownOp {
                dialect: self.name(),
                op: inst.op.clone(),
            });
        }
        if is_bitfield_op(inst) {
            decode(inst)
                .map(|_| ())
                .map_err(|reason| DialectError::LoweringFailed {
                    pass: VALIDATE_PASS.to_string(),
                    reason,
                })
        } else if is_v4i32_mask_extract_op(inst)
            || is_v2i64_mask_extract_op(inst)
            || is_v2i64_bool_mask_extract_op(inst)
        {
            decode_mask_extract(inst)
                .map(|_| ())
                .map_err(|reason| DialectError::LoweringFailed {
                    pass: VALIDATE_PASS.to_string(),
                    reason,
                })
        } else {
            Err(DialectError::UnknownOp {
                dialect: self.name(),
                op: inst.op.clone(),
            })
        }
    }
}

pub fn extract_bits(ty: Ty, operand: ValueId, lsb: u8, width: u8) -> DialectInst {
    base_op(EXTRACT_OP, ty, lsb, width).with_operand(operand)
}

pub fn sextract_bits(ty: Ty, operand: ValueId, lsb: u8, width: u8) -> DialectInst {
    base_op(SEXTRACT_OP, ty, lsb, width).with_operand(operand)
}

pub fn insert_bits(ty: Ty, dst: ValueId, src: ValueId, lsb: u8, width: u8) -> DialectInst {
    base_op(INSERT_OP, ty, lsb, width).with_operands([dst, src])
}

/// Extract a canonical `<4 x i32>` lane mask into the low four bits of `i32`.
///
/// Operand contract: each i32 lane is a canonical mask lane (`0` or `-1`).
/// Result bit `i` is set when lane `i` is true; bits 4..31 are zero.
pub fn v4i32_mask_extract(mask: ValueId) -> DialectInst {
    DialectInst::new(DIALECT, V4I32_MASK_EXTRACT_OP)
        .with_result_ty(Ty::I32)
        .with_operand(mask)
}

/// Extract a canonical `<2 x i64>` lane mask into scalar low bits.
///
/// Operand contract: each i64 lane is a canonical mask lane (`0` or `-1`).
/// Result bit `i` is set when lane `i` is true. Supported result types are
/// `i32` and `i64`; all bits above bit 1 are zero.
pub fn v2i64_mask_extract(mask: ValueId, result_ty: Ty) -> DialectInst {
    DialectInst::new(DIALECT, V2I64_MASK_EXTRACT_OP)
        .with_result_ty(result_ty)
        .with_operand(mask)
}

/// Extract a canonical `<2 x bool>` v2i64 compare mask into scalar low bits.
///
/// Operand contract: the logical bool vector is represented by the Trust Codegen x86
/// v2i64 compare lowering as canonical i64 mask lanes (`0` or `-1`). Result bit
/// `i` is set when lane `i` is true. Supported result types are `i32` and
/// `i64`; all bits above bit 1 are zero.
pub fn v2i64_bool_mask_extract(mask: ValueId, result_ty: Ty) -> DialectInst {
    DialectInst::new(DIALECT, V2I64_BOOL_MASK_EXTRACT_OP)
        .with_result_ty(result_ty)
        .with_operand(mask)
}

pub fn is_bitfield_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && BITFIELD_OPS.contains(&inst.op.as_str())
}

pub fn is_v4i32_mask_extract_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == V4I32_MASK_EXTRACT_OP
}

pub fn is_v2i64_mask_extract_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == V2I64_MASK_EXTRACT_OP
}

pub fn is_v2i64_bool_mask_extract_op(inst: &DialectInst) -> bool {
    inst.dialect == DIALECT && inst.op == V2I64_BOOL_MASK_EXTRACT_OP
}

pub fn decode(inst: &DialectInst) -> Result<BitfieldSpec, String> {
    if inst.dialect != DIALECT {
        return Err(format!(
            "expected {DIALECT:?} dialect bitfield op, got {:?}",
            inst.dialect
        ));
    }
    if inst.version != 1 {
        return Err(format!(
            "{} version {} is unsupported; expected version 1",
            inst.qualified_name(),
            inst.version
        ));
    }

    let kind = match inst.op.as_str() {
        EXTRACT_OP => BitfieldKind::Extract,
        SEXTRACT_OP => BitfieldKind::Sextract,
        INSERT_OP => BitfieldKind::Insert,
        other => {
            return Err(format!(
                "unknown {DIALECT} bitfield op {other:?}; expected one of {OPS:?}"
            ));
        }
    };

    let expected_operands = match kind {
        BitfieldKind::Extract | BitfieldKind::Sextract => 1,
        BitfieldKind::Insert => 2,
    };
    if inst.operands.len() != expected_operands {
        return Err(format!(
            "{} expects {expected_operands} operand(s), got {}",
            inst.qualified_name(),
            inst.operands.len()
        ));
    }
    if inst.result_tys.len() != 1 {
        return Err(format!(
            "{} expects exactly one result type, got {}",
            inst.qualified_name(),
            inst.result_tys.len()
        ));
    }

    let ty = inst.result_tys[0].clone();
    let lsb = attr_u8(inst, "lsb")?;
    let width = attr_u8(inst, "width")?;
    validate_range(inst, &ty, lsb, width)?;

    Ok(BitfieldSpec {
        kind,
        ty,
        lsb,
        width,
    })
}

pub fn decode_v4i32_mask_extract(inst: &DialectInst) -> Result<V4I32MaskExtractSpec, String> {
    let result_ty = decode_mask_extract_with_op(inst, V4I32_MASK_EXTRACT_OP, "v4i32", &[Ty::I32])?;
    Ok(V4I32MaskExtractSpec { result_ty })
}

pub fn decode_v2i64_mask_extract(inst: &DialectInst) -> Result<V2I64MaskExtractSpec, String> {
    let result_ty =
        decode_mask_extract_with_op(inst, V2I64_MASK_EXTRACT_OP, "v2i64", &[Ty::I32, Ty::I64])?;
    Ok(V2I64MaskExtractSpec { result_ty })
}

pub fn decode_v2i64_bool_mask_extract(
    inst: &DialectInst,
) -> Result<V2I64BoolMaskExtractSpec, String> {
    let result_ty = decode_mask_extract_with_op(
        inst,
        V2I64_BOOL_MASK_EXTRACT_OP,
        "v2i64 bool",
        &[Ty::I32, Ty::I64],
    )?;
    Ok(V2I64BoolMaskExtractSpec { result_ty })
}

fn decode_mask_extract(inst: &DialectInst) -> Result<Ty, String> {
    if inst.op == V4I32_MASK_EXTRACT_OP {
        return decode_v4i32_mask_extract(inst).map(|spec| spec.result_ty);
    }
    if inst.op == V2I64_MASK_EXTRACT_OP {
        return decode_v2i64_mask_extract(inst).map(|spec| spec.result_ty);
    }
    if inst.op == V2I64_BOOL_MASK_EXTRACT_OP {
        return decode_v2i64_bool_mask_extract(inst).map(|spec| spec.result_ty);
    }
    Err(format!(
        "unknown {DIALECT} mask op {:?}; expected {V4I32_MASK_EXTRACT_OP:?}, {V2I64_MASK_EXTRACT_OP:?}, or {V2I64_BOOL_MASK_EXTRACT_OP:?}",
        inst.op
    ))
}

fn decode_mask_extract_with_op(
    inst: &DialectInst,
    expected_op: &str,
    label: &str,
    supported_result_tys: &[Ty],
) -> Result<Ty, String> {
    if inst.dialect != DIALECT {
        return Err(format!(
            "expected {DIALECT:?} dialect {label} mask extract op, got {:?}",
            inst.dialect
        ));
    }
    if inst.version != 1 {
        return Err(format!(
            "{} version {} is unsupported; expected version 1",
            inst.qualified_name(),
            inst.version
        ));
    }
    if inst.op != expected_op {
        return Err(format!(
            "unknown {DIALECT} mask op {:?}; expected {expected_op:?}",
            inst.op
        ));
    }
    if inst.operands.len() != 1 {
        return Err(format!(
            "{} expects 1 operand, got {}",
            inst.qualified_name(),
            inst.operands.len()
        ));
    }
    if inst.result_tys.len() != 1 {
        return Err(format!(
            "{} expects exactly one result type, got {}",
            inst.qualified_name(),
            inst.result_tys.len()
        ));
    }
    if !inst.attrs.is_empty() {
        return Err(format!(
            "{} expects no attributes, got {}",
            inst.qualified_name(),
            inst.attrs.len()
        ));
    }

    let result_ty = inst.result_tys[0].clone();
    if !supported_result_tys.contains(&result_ty) {
        return Err(format!(
            "{} result type {result_ty:?} is unsupported; expected one of {:?}",
            inst.qualified_name(),
            supported_result_tys
        ));
    }

    Ok(result_ty)
}

pub fn scalar_integer_bits(ty: &Ty) -> Option<u8> {
    match ty {
        Ty::I8 | Ty::U8 => Some(8),
        Ty::I16 | Ty::U16 => Some(16),
        Ty::I32 | Ty::U32 => Some(32),
        Ty::I64 | Ty::U64 => Some(64),
        _ => None,
    }
}

fn base_op(op: &str, ty: Ty, lsb: u8, width: u8) -> DialectInst {
    DialectInst::new(DIALECT, op)
        .with_result_ty(ty)
        .with_attr("lsb", AttrValue::U64(u64::from(lsb)))
        .with_attr("width", AttrValue::U64(u64::from(width)))
}

fn attr_u8(inst: &DialectInst, name: &str) -> Result<u8, String> {
    let mut matches = inst.attrs.iter().filter(|attr| attr.name == name);
    let attr = matches.next().ok_or_else(|| {
        format!(
            "{} is missing required {name:?} attribute",
            inst.qualified_name()
        )
    })?;
    if matches.next().is_some() {
        return Err(format!(
            "{} has duplicate {name:?} attributes",
            inst.qualified_name()
        ));
    }

    let raw = match &attr.value {
        AttrValue::U64(value) => *value,
        AttrValue::I64(value) if *value >= 0 => *value as u64,
        other => {
            return Err(format!(
                "{} attribute {name:?} must be a non-negative integer, got {other:?}",
                inst.qualified_name()
            ));
        }
    };

    u8::try_from(raw).map_err(|_| {
        format!(
            "{} attribute {name:?} value {raw} does not fit in u8",
            inst.qualified_name()
        )
    })
}

fn validate_range(inst: &DialectInst, ty: &Ty, lsb: u8, width: u8) -> Result<(), String> {
    let Some(type_bits) = scalar_integer_bits(ty) else {
        return Err(format!(
            "{} result type {ty:?} is unsupported; expected I8/I16/I32/I64 or unsigned equivalents",
            inst.qualified_name()
        ));
    };
    if width == 0 || u16::from(lsb) + u16::from(width) > u16::from(type_bits) {
        return Err(format!(
            "{} has invalid bitfield range lsb={lsb} width={width} for {type_bits}-bit type",
            inst.qualified_name()
        ));
    }
    Ok(())
}
