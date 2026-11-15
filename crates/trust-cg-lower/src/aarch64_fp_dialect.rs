//! Typed AArch64 scalar FP instructions, preserving the instruction's rounding
//! and NaN behavior. These operations are not portable arithmetic identities.
use trust_ir::dialect::{Dialect, DialectError, DialectInst};
use trust_ir::{Ty, ValueId};

pub const DIALECT: &str = "trust-cg-aarch64-fp";
const OPS: &[&str] = &["fmadd", "fsqrt", "frintn"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    Fmadd,
    Fsqrt,
    Frintn,
}

impl Operation {
    pub fn name(self) -> &'static str {
        match self {
            Self::Fmadd => "fmadd",
            Self::Fsqrt => "fsqrt",
            Self::Frintn => "frintn",
        }
    }

    pub fn inputs(self) -> usize {
        if self == Self::Fmadd { 3 } else { 1 }
    }
}

pub fn instruction(op: Operation, ty: Ty, inputs: &[ValueId]) -> DialectInst {
    DialectInst::new(DIALECT, op.name())
        .with_result_ty(ty)
        .with_operands(inputs.iter().copied())
}

pub fn decode(inst: &DialectInst) -> Result<(Operation, Ty), String> {
    if inst.dialect != DIALECT {
        return Err("AArch64 FP dialect name mismatch".into());
    }
    let op = match inst.op.as_str() {
        "fmadd" => Operation::Fmadd,
        "fsqrt" => Operation::Fsqrt,
        "frintn" => Operation::Frintn,
        _ => return Err("unknown AArch64 FP instruction".into()),
    };
    if inst.result_tys.len() != 1
        || !matches!(inst.result_tys[0], Ty::F32 | Ty::F64)
        || inst.operands.len() != op.inputs()
        || !inst.attrs.is_empty()
    {
        return Err(
            "AArch64 FP instruction requires f32/f64, exact operands, and no attributes".into(),
        );
    }
    Ok((op, inst.result_tys[0].clone()))
}

#[derive(Debug)]
pub struct Aarch64FpDialect;

impl Dialect for Aarch64FpDialect {
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
        decode(inst)
            .map(|_| ())
            .map_err(|reason| DialectError::LoweringFailed {
                pass: "trust-cg-aarch64-fp.validate".into(),
                reason,
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::dialect::AttrValue;

    #[test]
    fn aarch64_fp_dialect_rejects_malformed_contracts() {
        for op in [Operation::Fmadd, Operation::Fsqrt, Operation::Frintn] {
            let args: Vec<_> = (0..op.inputs()).map(|i| ValueId::new(i as u32)).collect();
            for ty in [Ty::F32, Ty::F64] {
                let valid = instruction(op, ty.clone(), &args);
                assert_eq!(decode(&valid).unwrap(), (op, ty));
                let mut bad = valid.clone();
                bad.operands.pop();
                assert!(decode(&bad).is_err());
                let mut bad = valid.clone();
                bad.operands.push(ValueId::new(99));
                assert!(decode(&bad).is_err());
                let mut bad = valid.clone();
                bad.result_tys.push(Ty::F64);
                assert!(decode(&bad).is_err());
                let mut bad = valid.clone();
                bad.result_tys.clear();
                assert!(decode(&bad).is_err());
                let bad = valid.clone().with_attr("fast_math", AttrValue::Bool(true));
                assert!(decode(&bad).is_err());
                let mut bad = valid.clone();
                bad.op = "frinti".into();
                assert!(decode(&bad).is_err());
                let mut bad = valid;
                bad.dialect = "other".into();
                assert!(decode(&bad).is_err());
            }
            for ty in [Ty::I32, Ty::I64, Ty::F16] {
                assert!(decode(&instruction(op, ty, &args)).is_err());
            }
        }
    }
}
