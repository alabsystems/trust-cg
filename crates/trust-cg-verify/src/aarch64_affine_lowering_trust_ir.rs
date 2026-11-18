// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independently bind exact module-owned TrustIR to the raw affine/predicate pair.
//!
//! TrustIR determines applicability before either lowered representation is
//! inspected. An unsupported target cannot turn a supported source into an
//! uncredited coverage skip. This local semantic check does not replace Core
//! admission's module validation, discharge source proof annotations, or prove
//! any optimization, allocation, encoding, or executable publication step.

use super::{
    Affine, AffineLoweringError, AffineLoweringStatistics, CompareKind, Function, MachFunction,
    Predicate, ScalarType, ScalarValue, machine_result, source_contract,
};
use std::collections::HashMap;
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::value::ValueId;
use trust_ir::{ArgExt, CallingConv, Constant, FuncTy, Module, Ty};

#[path = "aarch64_affine_bytes.rs"]
mod final_bytes;
pub use final_bytes::{
    AffineByteError, AffineByteStatistics, CheckedAarch64DefinedCallBytes,
    CheckedAarch64TrustIrAffineBytes, check_aarch64_defined_call_bytes,
    check_aarch64_trust_ir_affine_bytes,
};

#[path = "aarch64_defined_callee.rs"]
mod defined_callee;
#[cfg(feature = "source-defined-call")]
pub(crate) use defined_callee::scalar_abi as check_plain_integer_entry_abi;
pub use defined_callee::{
    AttachedDefinedAffineCallee, DefinedAffineCallee, DefinedAffineCalleeError,
    DefinedCalleeEffects, DefinedCalleeScalarType,
};

#[path = "aarch64_defined_peer.rs"]
mod defined_peer;
pub use defined_peer::{
    CheckedDefinedPeerCall, ConditionalPeerEntryRequirement, ConditionallyReplayedDefinedPeer,
    DefinedPeerCallError,
};

/// Only `UnsupportedTrustIr` denotes source-domain coverage. Every target-side
/// refusal is wrapped in `Lowering`, including unsupported LIR or MachIR.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TrustIrAffineLoweringError {
    #[error("invalid affine TrustIR: {0}")]
    InvalidTrustIr(String),
    #[error("unsupported affine TrustIR: {0}")]
    UnsupportedTrustIr(String),
    #[error("TrustIR and LIR signatures, affine values or Boolean predicates disagree")]
    TrustIrLirMismatch,
    #[error("source-bound affine lowering rejected: {0}")]
    Lowering(#[from] AffineLoweringError),
}

/// Work actually checked at each source boundary, never publication credit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TrustIrAffineLoweringStatistics {
    pub trust_ir_instructions: usize,
    /// `source_instructions` retains its existing meaning: LIR instructions.
    pub lowering: AffineLoweringStatistics,
}

/// Privately constructed binding to the exact immutable module-owned source,
/// LIR and raw machine program. No serialized or final-code receipt is minted.
#[derive(Debug)]
pub struct CheckedAarch64TrustIrAffineLowering<'a> {
    module: &'a Module,
    source: &'a trust_ir::Function,
    lir: &'a Function,
    machine: &'a MachFunction,
    statistics: TrustIrAffineLoweringStatistics,
}

impl<'a> CheckedAarch64TrustIrAffineLowering<'a> {
    pub fn module(&self) -> &'a Module {
        self.module
    }

    pub fn source(&self) -> &'a trust_ir::Function {
        self.source
    }

    pub fn lir(&self) -> &'a Function {
        self.lir
    }

    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }

    pub fn statistics(&self) -> TrustIrAffineLoweringStatistics {
        self.statistics
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IntegerType {
    I32,
    U32,
    I64,
    U64,
}

impl IntegerType {
    fn from_ty(ty: &Ty) -> Result<Self, TrustIrAffineLoweringError> {
        match ty {
            Ty::I32 => Ok(Self::I32),
            Ty::U32 => Ok(Self::U32),
            Ty::I64 => Ok(Self::I64),
            Ty::U64 => Ok(Self::U64),
            _ => Err(TrustIrAffineLoweringError::UnsupportedTrustIr(
                "requires scalar I32/U32/I64/U64 types".into(),
            )),
        }
    }

    fn bits(self) -> u32 {
        match self {
            Self::I32 | Self::U32 => 32,
            Self::I64 | Self::U64 => 64,
        }
    }

    fn mask(self) -> u64 {
        match self.bits() {
            32 => u64::from(u32::MAX),
            _ => u64::MAX,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SourceType {
    Integer(IntegerType),
    Bool,
}

impl SourceType {
    fn from_ty(ty: &Ty) -> Result<Self, TrustIrAffineLoweringError> {
        if ty == &Ty::Bool {
            Ok(Self::Bool)
        } else {
            IntegerType::from_ty(ty).map(Self::Integer)
        }
    }

    fn scalar_type(self) -> ScalarType {
        match self {
            Self::Integer(ty) => ScalarType::Integer(ty.bits()),
            Self::Bool => ScalarType::Bool,
        }
    }
}

fn admit_type(
    domain: &mut Option<IntegerType>,
    ty: IntegerType,
) -> Result<(), TrustIrAffineLoweringError> {
    if domain.is_some_and(|previous| previous != ty) {
        return Err(TrustIrAffineLoweringError::UnsupportedTrustIr(
            "mixed scalar types require a broader source contract".into(),
        ));
    }
    *domain = Some(ty);
    Ok(())
}

struct TrustIrContract<'a> {
    source: &'a trust_ir::Function,
    signature: &'a FuncTy,
    bits: u32,
    return_type: Option<ScalarType>,
    result: Option<ScalarValue>,
    instruction_count: usize,
}

#[path = "aarch64_affine_core_control.rs"]
mod core_control;

fn trust_ir_contract<'a>(
    module: &'a Module,
    source: &'a trust_ir::Function,
) -> Result<TrustIrContract<'a>, TrustIrAffineLoweringError> {
    use TrustIrAffineLoweringError::{
        InvalidTrustIr as Invalid, UnsupportedTrustIr as Unsupported,
    };

    if source.blocks.is_empty() {
        return Err(Invalid(
            "selected source is a declaration without a body".into(),
        ));
    }
    let signature = module
        .func_types
        .get(source.ty.index() as usize)
        .ok_or_else(|| Invalid("function signature index is outside the module".into()))?;
    if source.attrs.params.len() > signature.params.len() {
        return Err(Invalid(
            "parameter attributes exceed signature arity".into(),
        ));
    }
    if source.calling_conv != CallingConv::C
        || signature.is_vararg
        || signature.params.len() > 8
        || signature.returns.len() > 1
        || source
            .attrs
            .params
            .iter()
            .any(|attr| attr.byval || attr.sret || attr.ext != ArgExt::None || attr.pass.is_some())
        || !source.attrs.ret.is_empty()
    {
        return Err(Unsupported(
            "requires nonvariadic C ABI, at most eight scalar parameters and one return, without byval/sret or explicit ABI slot facts".into(),
        ));
    }
    if !matches!(source.blocks.len(), 1 | 4) {
        return Err(Unsupported(
            "requires a scalar block or one arithmetic diamond".into(),
        ));
    }
    let block = source
        .entry_block()
        .ok_or_else(|| Invalid("missing declared entry block".into()))?;
    if block.params.len() != signature.params.len() {
        return Err(Invalid(
            "entry parameter arity disagrees with signature".into(),
        ));
    }

    let mut domain = None;
    let mut values: HashMap<ValueId, (SourceType, ScalarValue)> = HashMap::new();
    for (index, ((value, entry_ty), signature_ty)) in
        block.params.iter().zip(&signature.params).enumerate()
    {
        if entry_ty != signature_ty {
            return Err(Invalid(format!(
                "entry parameter {index} type disagrees with signature"
            )));
        }
        let ty = IntegerType::from_ty(signature_ty)?;
        admit_type(&mut domain, ty)?;
        if values
            .insert(
                *value,
                (
                    SourceType::Integer(ty),
                    ScalarValue::Integer {
                        bits: ty.bits(),
                        value: Affine::parameter(index),
                    },
                ),
            )
            .is_some()
        {
            return Err(Invalid("duplicate entry parameter value".into()));
        }
    }
    let return_type = signature
        .returns
        .first()
        .map(SourceType::from_ty)
        .transpose()?;
    if let Some(SourceType::Integer(ty)) = return_type {
        admit_type(&mut domain, ty)?;
    }

    let (result, instruction_count) = if source.blocks.len() == 1 {
        let (returned, result) = evaluate_nodes(
            &block.body,
            signature,
            return_type,
            &mut domain,
            &mut values,
            module.pointer_bits(),
        )?;
        if !returned {
            return Err(Invalid("missing return".into()));
        }
        (result, block.body.len())
    } else {
        core_control::diamond_result(
            source,
            signature,
            return_type,
            &mut domain,
            values,
            module.pointer_bits(),
        )?
    };
    Ok(TrustIrContract {
        source,
        signature,
        bits: domain.map_or(64, IntegerType::bits),
        return_type: return_type.map(SourceType::scalar_type),
        result,
        instruction_count,
    })
}

type SourceValues = HashMap<ValueId, (SourceType, ScalarValue)>;

/// One evaluator for admitted scalar nodes on every original-source path.
/// Control drivers cannot remove guards, annotations or type/SSA validation.
fn evaluate_nodes(
    body: &[trust_ir::InstrNode],
    signature: &FuncTy,
    return_type: Option<SourceType>,
    domain: &mut Option<IntegerType>,
    values: &mut SourceValues,
    pointer_bits: u32,
) -> Result<(bool, Option<ScalarValue>), TrustIrAffineLoweringError> {
    use TrustIrAffineLoweringError::{
        InvalidTrustIr as Invalid, UnsupportedTrustIr as Unsupported,
    };
    let mut returned = false;
    let mut result = None;
    for (index, node) in body.iter().enumerate() {
        if returned {
            return Err(Invalid(format!("instruction {index} follows return")));
        }
        // The frontend/adapter contract gives InBounds ICmp probes trapping
        // guard semantics, including the resultless carrier form. Ignoring
        // that marker would turn a guard-deleting target into a pure-comparison
        // match. Do not reproduce the adapter's recognizer or trust the claim:
        // every such probe is outside this side-effect-free source domain.
        if matches!(node.inst, Inst::ICmp { .. })
            && node
                .proofs
                .iter()
                .any(|proof| matches!(proof, trust_ir::ProofAnnotation::InBounds))
        {
            return Err(Unsupported(format!(
                "instruction {index}: InBounds comparison guard semantics are outside the pure affine/predicate domain"
            )));
        }
        let result_arity = match &node.inst {
            Inst::Const { .. } | Inst::Copy { .. } | Inst::ICmp { .. } | Inst::Select { .. } => 1,
            Inst::BinOp {
                op: BinOp::Add | BinOp::Sub,
                ..
            } => 1,
            Inst::Return { .. } => 0,
            _ => {
                return Err(Unsupported(format!(
                    "instruction {index} is outside constants/copies/wrapping add/subtract/integer comparison/flat select/return"
                )));
            }
        };
        if node.results.len() != result_arity {
            return Err(Invalid(format!(
                "instruction {index} has wrong result arity"
            )));
        }
        // A call-only sidecar on an admitted non-call instruction is malformed.
        // Other proof annotations are not used for acceptance or proof credit.
        if node.proof_context.is_some() {
            return Err(Invalid(format!(
                "instruction {index} has a non-call proof context"
            )));
        }
        let read = |id: ValueId, expected: SourceType| {
            let (ty, value) = values
                .get(&id)
                .copied()
                .ok_or_else(|| Invalid(format!("instruction {index} uses undefined {id:?}")))?;
            if ty != expected {
                return Err(Invalid(format!(
                    "instruction {index} operand {id:?} has the wrong type"
                )));
            }
            Ok(value)
        };
        let (ty, value) = match &node.inst {
            Inst::Const { ty, value } => {
                if ty == &Ty::Bool {
                    let Constant::Bool(value) = value else {
                        return Err(Invalid(format!(
                            "instruction {index} requires the canonical Boolean literal carrier"
                        )));
                    };
                    (
                        SourceType::Bool,
                        ScalarValue::Bool(Predicate::Constant(*value)),
                    )
                } else {
                    let integer_ty = IntegerType::from_ty(ty)?;
                    let Constant::Int(integer) = value else {
                        return Err(Invalid(format!(
                            "instruction {index} requires the canonical integer literal carrier"
                        )));
                    };
                    // Source-language range validation, NOT the adapter's more
                    // permissive bit-pattern ranges or in-band address-stub path,
                    // at the module's own pointer width (trust-ir's rule; the
                    // admitted types are fixed-width, so it cannot widen one).
                    if !value.value_matches_ty(ty, pointer_bits) {
                        return Err(Invalid(format!(
                            "instruction {index} integer literal is outside its declared range"
                        )));
                    }
                    (
                        SourceType::Integer(integer_ty),
                        ScalarValue::Integer {
                            bits: integer_ty.bits(),
                            value: Affine::constant(*integer as u64, integer_ty.mask()),
                        },
                    )
                }
            }
            Inst::Copy { ty, operand } => {
                let ty = SourceType::from_ty(ty)?;
                (ty, read(*operand, ty)?)
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                let ty = IntegerType::from_ty(ty)?;
                let source_ty = SourceType::Integer(ty);
                let integer = |operand| -> Result<Affine, TrustIrAffineLoweringError> {
                    read(operand, source_ty)?
                        .as_affine(ty.bits())
                        .ok_or_else(|| {
                            Unsupported(format!(
                                "instruction {index}: arithmetic of selections needs a richer value domain"
                            ))
                        })
                };
                let value = integer(*lhs)?.combine(integer(*rhs)?, *op == BinOp::Sub, ty.mask());
                (
                    source_ty,
                    ScalarValue::Integer {
                        bits: ty.bits(),
                        value,
                    },
                )
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                // Signedness is selected by the operation, not inferred from
                // the signed/unsigned source carrier. Both operands must
                // independently have the exact declared source type.
                let ty = IntegerType::from_ty(ty)?;
                admit_type(domain, ty)?;
                let integer = |operand| -> Result<Affine, TrustIrAffineLoweringError> {
                    read(operand, SourceType::Integer(ty))?
                        .as_affine(ty.bits())
                        .ok_or_else(|| {
                            Unsupported(format!(
                                "instruction {index}: comparison of selections needs a richer value domain"
                            ))
                        })
                };
                let (a, b) = (integer(*lhs)?, integer(*rhs)?);
                use CompareKind::{Equal, SignedLess, UnsignedLess};
                let (kind, swap, negated) = match op {
                    ICmpOp::Eq => (Equal, false, false),
                    ICmpOp::Ne => (Equal, false, true),
                    ICmpOp::Slt => (SignedLess, false, false),
                    ICmpOp::Sge => (SignedLess, false, true),
                    ICmpOp::Sgt => (SignedLess, true, false),
                    ICmpOp::Sle => (SignedLess, true, true),
                    ICmpOp::Ult => (UnsignedLess, false, false),
                    ICmpOp::Uge => (UnsignedLess, false, true),
                    ICmpOp::Ugt => (UnsignedLess, true, false),
                    ICmpOp::Ule => (UnsignedLess, true, true),
                };
                let (lhs, rhs) = if swap { (b, a) } else { (a, b) };
                (
                    SourceType::Bool,
                    ScalarValue::Bool(Predicate::compare(kind, lhs, rhs, negated, ty.bits())),
                )
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                let ty = IntegerType::from_ty(ty)?;
                admit_type(domain, ty)?;
                let source_ty = SourceType::Integer(ty);
                let ScalarValue::Bool(predicate) = read(*cond, SourceType::Bool)? else {
                    return Err(Invalid(format!(
                        "instruction {index}: noncanonical Boolean select condition"
                    )));
                };
                let then_value = read(*then_val, source_ty)?.as_affine(ty.bits());
                let else_value = read(*else_val, source_ty)?.as_affine(ty.bits());
                let (Some(then_value), Some(else_value)) = (then_value, else_value) else {
                    return Err(Unsupported(format!(
                        "instruction {index}: nested integer selection needs a richer value domain"
                    )));
                };
                (
                    source_ty,
                    ScalarValue::select(ty.bits(), predicate, then_value, else_value),
                )
            }
            Inst::Return { values: operands } => {
                if operands.len() != signature.returns.len() {
                    return Err(Invalid(format!(
                        "instruction {index} has wrong return arity"
                    )));
                }
                result = match return_type {
                    Some(ty) => Some(read(operands[0], ty)?),
                    None => None,
                };
                returned = true;
                continue;
            }
            // Keep the checker total even if the admission match is extended
            // without a corresponding evaluator arm in a later revision.
            _ => {
                return Err(Invalid(format!(
                    "instruction {index} has no admitted affine evaluator"
                )));
            }
        };
        if let SourceType::Integer(ty) = ty {
            admit_type(domain, ty)?;
        }
        if values.insert(node.results[0], (ty, value)).is_some() {
            return Err(Invalid(format!(
                "instruction {index} redefines an SSA value"
            )));
        }
    }
    Ok((returned, result))
}

/// Independently check the selected TrustIR, actual LIR and raw AArch64 once
/// each. Only unsupported TrustIR is a source-domain coverage refusal; target
/// errors after supported source are hard lowering failures.
pub fn check_aarch64_trust_ir_affine_lowering<'a>(
    module: &'a Module,
    function_ordinal: usize,
    lir: &'a Function,
    machine: &'a MachFunction,
) -> Result<CheckedAarch64TrustIrAffineLowering<'a>, TrustIrAffineLoweringError> {
    // Authenticate module membership and source pairing before classifying
    // coverage. A wrong ordinal selecting an unsupported declaration must not
    // turn an indexing bug into a successful uncredited preparation.
    let selected = module.functions.get(function_ordinal).ok_or_else(|| {
        TrustIrAffineLoweringError::InvalidTrustIr("function ordinal is outside the module".into())
    })?;
    if selected.name != lir.name {
        return Err(TrustIrAffineLoweringError::TrustIrLirMismatch);
    }
    let source = trust_ir_contract(module, selected)?;
    let view;
    let lowering_source = if selected.blocks.len() == 4 {
        view = crate::source_bound_frame::raw_source_view(lir).ok_or_else(|| {
            AffineLoweringError::UnsupportedMachine(
                "LIR is outside the connected source-control domain".into(),
            )
        })?;
        &view
    } else {
        lir
    };
    let lowering = source_contract(lowering_source)?;
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
        return Err(TrustIrAffineLoweringError::TrustIrLirMismatch);
    }
    if selected.blocks.len() == 4 {
        super::check_raw_aarch64_control(lowering_source, machine)?;
    } else {
        let actual = machine_result(lir, machine, &lowering)?;
        if actual != lowering.result {
            return Err(AffineLoweringError::ReturnMismatch.into());
        }
    }
    Ok(CheckedAarch64TrustIrAffineLowering {
        module,
        source: source.source,
        lir,
        machine,
        statistics: TrustIrAffineLoweringStatistics {
            trust_ir_instructions: source.instruction_count,
            lowering: AffineLoweringStatistics {
                source_instructions: lir
                    .blocks
                    .values()
                    .map(|block| block.instructions.len())
                    .sum(),
                machine_instructions: machine.insts.len(),
                parameter_count: source.signature.params.len(),
            },
        },
    })
}
