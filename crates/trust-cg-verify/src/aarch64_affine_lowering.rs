// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independent, exact LIR-to-AArch64 checking for affine integer values and
//! scalar integer comparisons with Boolean results.
//!
//! The two instruction streams are interpreted independently as affine forms
//! over Z/(2^W), W = 32 or 64. Equality of their constant and input coefficients
//! establishes equal integer operands for every input, not just sampled inputs.
//! Boolean results retain exact equality or signed/unsigned ordering predicates
//! over those operands. Actual CMP operands and reaching flags determine CSET;
//! no comparison is justified merely by its opcode or source position.
//! No selector value map, provenance stamp, source-op reconstruction, solver,
//! hash collision, or producer proof annotation participates in acceptance.
//!
//! The domain covers one-block, homogeneous integer functions with at most eight ABI
//! register parameters and zero or one return: constants, copies, wrapping add
//! and subtract, all ten integer comparisons, flat integer selects over their
//! Boolean results, and Boolean constants/copies and returns, including actual
//! immediate and MOVZ/MOVN/MOVK expansions.
//! Every instruction is checked, including dead computations and ABI glue;
//! unknown effects, control flow, stack/EH, Boolean arguments, Boolean logic and
//! mixed integer widths fail closed. Proven Boolean 0/1 carriers may cross W/X.
//! Physical registers are mutable, and X/W aliases share their low-bit state.
//! Only the return register may be overwritten; LR and callee-saves cannot be.
//!
//! The pair API establishes a **pre-optimization LIR/MachIR** claim, not
//! TrustIR-to-LIR translation. [`check_aarch64_trust_ir_affine_lowering`] also
//! independently checks the exact module-owned TrustIR source first. Neither
//! establishes register allocation, encoding or executable publication.
//! Liveness-only implicit uses are checked for their supported register domain,
//! not proved sufficient for a future allocator. Successful owners immutably
//! borrow their exact inputs, so they cannot survive mutation or be paired with
//! different code. There is deliberately no public receipt constructor,
//! serialization, or conversion to a JIT certificate.
//!
//! [`check_aarch64_trust_ir_affine_bytes`] separately compares the source with
//! actual final bytes for a bounded leaf/standard-frame domain. Its private
//! owner also grants no publication or machine-checked implementation claim.

use std::collections::{HashMap, HashSet};
use trust_cg_ir::function::StackProtectorMode;
use trust_cg_ir::regs::{LR, PReg, RegClass, SpecialReg};
use trust_cg_ir::{AArch64Opcode as M, InstFlags, MachFunction, MachOperand};
use trust_cg_lower::instructions::{Opcode as L, Value};
use trust_cg_lower::{Function, Type};

#[path = "aarch64_affine_values.rs"]
mod scalar_values;
pub(crate) use scalar_values::Affine;
use scalar_values::{CompareKind, ComparisonFlags, Predicate, ScalarType, ScalarValue};

#[path = "aarch64_affine_lowering_trust_ir.rs"]
mod trust_ir_binding;

pub use trust_ir_binding::{
    AffineByteError, AffineByteStatistics, AttachedDefinedAffineCallee,
    CheckedAarch64DefinedCallBytes, CheckedAarch64TrustIrAffineBytes,
    CheckedAarch64TrustIrAffineLowering, CheckedDefinedPeerCall, ConditionalPeerEntryRequirement,
    ConditionallyReplayedDefinedPeer, DefinedAffineCallee, DefinedAffineCalleeError,
    DefinedCalleeEffects, DefinedCalleeScalarType, DefinedPeerCallError,
    TrustIrAffineLoweringError, TrustIrAffineLoweringStatistics, check_aarch64_defined_call_bytes,
    check_aarch64_trust_ir_affine_bytes, check_aarch64_trust_ir_affine_lowering,
};

/// Located refusal; unsupported coverage is distinct from invalid inputs and
/// unequal observable results. None of these errors grants weaker authority.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AffineLoweringError {
    #[error("invalid affine LIR: {0}")]
    InvalidSource(String),
    #[error("unsupported affine LIR: {0}")]
    UnsupportedSource(String),
    #[error("invalid affine AArch64: {0}")]
    InvalidMachine(String),
    #[error("unsupported affine AArch64: {0}")]
    UnsupportedMachine(String),
    #[error("LIR and AArch64 return different affine values or integer predicates")]
    ReturnMismatch,
}

/// Work actually checked, not instruction-level formal proof credits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AffineLoweringStatistics {
    pub source_instructions: usize,
    pub machine_instructions: usize,
    pub parameter_count: usize,
}

/// Non-constructible, immutable binding to the exact checked pair.
#[derive(Debug)]
pub struct CheckedAarch64AffineLowering<'a> {
    source: &'a Function,
    machine: &'a MachFunction,
    statistics: AffineLoweringStatistics,
}

impl<'a> CheckedAarch64AffineLowering<'a> {
    pub fn source(&self) -> &'a Function {
        self.source
    }

    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }

    pub fn statistics(&self) -> AffineLoweringStatistics {
        self.statistics
    }
}

struct SourceContract {
    bits: u32,
    /// Each register parameter's own width. A parameter the body never reads
    /// may differ from `bits`; every value the body observes has `bits`.
    param_bits: Vec<u32>,
    return_type: Option<ScalarType>,
    result: Option<ScalarValue>,
    instruction_count: usize,
}

/// Refusal guard only: OD-35 excludes semantic parameter identities from
/// whole-body copy credit, including identities obscured by arithmetic.
/// Never serialize this normal form or use it as replay evidence.
pub(crate) fn affine_return_is_parameter(source: &Function) -> Option<bool> {
    let contract = source_contract(source).ok()?;
    Some(match contract.result {
        Some(ScalarValue::Integer { value, .. }) => {
            (0..source.signature.params.len()).any(|i| value == Affine::parameter(i))
        }
        _ => false,
    })
}

fn source_contract(source: &Function) -> Result<SourceContract, AffineLoweringError> {
    use AffineLoweringError::{InvalidSource as Invalid, UnsupportedSource as Unsupported};
    if source.blocks.len() != 1
        || !source.stack_slots.is_empty()
        || !source.eh_info.is_empty()
        || source.stack_protector != StackProtectorMode::None
        || !source.param_pointee_types.is_empty()
        || source.abi_sret_param.is_some()
        || !source.sret_arg_callees.is_empty()
    {
        return Err(Unsupported(
            "requires one block without stack, EH or aggregate ABI metadata".into(),
        ));
    }
    let block = source
        .blocks
        .get(&source.entry_block)
        .ok_or_else(|| Invalid("missing entry block".into()))?;
    if !source.block_order.is_empty() && source.block_order != [source.entry_block] {
        return Err(Invalid("invalid single-block layout".into()));
    }
    let signature = &source.signature;
    if signature.params.len() > 8 || signature.returns.len() > 1 {
        return Err(Unsupported(
            "requires at most eight register parameters and one return".into(),
        ));
    }
    let scalar_type = |ty: &Type| match ty {
        Type::I32 => Ok(ScalarType::Integer(32)),
        Type::I64 => Ok(ScalarType::Integer(64)),
        Type::B1 => Ok(ScalarType::Bool),
        _ => Err(Unsupported(format!("non-I32/I64/B1 type {ty:?}"))),
    };
    let mut bits = None;
    let admit_type = |bits: &mut Option<u32>, ty: ScalarType| -> Result<(), AffineLoweringError> {
        if let ScalarType::Integer(next) = ty {
            if bits.is_some_and(|previous| previous != next) {
                return Err(Unsupported("mixed-width function".into()));
            }
            *bits = Some(next);
        }
        Ok(())
    };
    let mut param_bits = Vec::with_capacity(signature.params.len());
    for ty in &signature.params {
        let ScalarType::Integer(width) = scalar_type(ty)? else {
            return Err(Unsupported(
                "Boolean parameters are outside this domain".into(),
            ));
        };
        param_bits.push(width);
    }
    // A parameter no instruction reads is ABI glue only, so its width does
    // not join the domain's: `fn(*const T) -> i32 { 0 }` has one. Every value
    // the body observes (read parameters, constants, the return) still shares
    // one width, and each parameter's register is seeded at its own width, so
    // no machine read can narrow or widen it unnoticed.
    let read: HashSet<Value> = block
        .instructions
        .iter()
        .flat_map(|inst| inst.args.iter().copied())
        .collect();
    for (index, &width) in param_bits.iter().enumerate() {
        if read.contains(&Value(index as u32)) {
            admit_type(&mut bits, ScalarType::Integer(width))?;
        }
    }
    let return_type = signature.returns.first().map(scalar_type).transpose()?;
    if let Some(ty) = return_type {
        admit_type(&mut bits, ty)?;
    }
    for inst in &block.instructions {
        if let L::Iconst { ty, .. } = &inst.opcode {
            admit_type(&mut bits, scalar_type(ty)?)?;
        }
    }
    if bits.is_none() {
        // Nothing observed fixes a width: every parameter must agree.
        for &width in &param_bits {
            admit_type(&mut bits, ScalarType::Integer(width))?;
        }
    }
    let bits = bits.unwrap_or(64); // () -> () has no observable integer width.
    let mask = if bits == 32 {
        u64::from(u32::MAX)
    } else {
        u64::MAX
    };
    if !block.params.is_empty()
        && (block.params.len() != signature.params.len()
            || block
                .params
                .iter()
                .enumerate()
                .any(|(i, (value, param_ty))| {
                    value.0 as usize != i || param_ty != &signature.params[i]
                }))
    {
        return Err(Invalid(
            "entry parameters disagree with Value(0..n) signature convention".into(),
        ));
    }
    let mut values = HashMap::new();
    for (i, &width) in param_bits.iter().enumerate() {
        values.insert(
            Value(i as u32),
            ScalarValue::Integer {
                bits: width,
                value: Affine::parameter(i),
            },
        );
    }
    let mut returned = false;
    let mut result = None;
    for (index, inst) in block.instructions.iter().enumerate() {
        if returned {
            return Err(Invalid(format!("instruction {index} follows return")));
        }
        let arity = match inst.opcode {
            L::Iconst { .. } => (0, 1),
            L::Copy => (1, 1),
            L::Iadd | L::Isub | L::Icmp { .. } => (2, 1),
            L::Select { .. } => (3, 1),
            L::Return => (signature.returns.len(), 0),
            _ => {
                return Err(Unsupported(format!(
                    "instruction {index}: {:?}",
                    inst.opcode
                )));
            }
        };
        if (inst.args.len(), inst.results.len()) != arity {
            return Err(Invalid(format!(
                "instruction {index} has wrong operand/result arity"
            )));
        }
        let read = |value: Value| {
            values
                .get(&value)
                .copied()
                .ok_or_else(|| Invalid(format!("instruction {index} uses undefined {value:?}")))
        };
        let integer = |value: ScalarValue| {
            if matches!(value, ScalarValue::Select { .. }) {
                return Err(Unsupported(format!(
                    "instruction {index}: arithmetic/comparison of selections needs a richer value domain"
                )));
            }
            value.as_affine(bits).ok_or_else(|| {
                Invalid(format!(
                    "instruction {index} requires an integer operand at width {bits}"
                ))
            })
        };
        let value = match &inst.opcode {
            L::Iconst { imm, ty } => match scalar_type(ty)? {
                ScalarType::Bool if matches!(*imm, 0 | 1) => {
                    ScalarValue::Bool(Predicate::Constant(*imm == 1))
                }
                ScalarType::Bool => {
                    return Err(Invalid(format!(
                        "instruction {index} has a noncanonical Boolean literal"
                    )));
                }
                ScalarType::Integer(_) => ScalarValue::Integer {
                    bits,
                    value: Affine::constant(*imm as u64, mask),
                },
            },
            L::Copy => read(inst.args[0])?,
            L::Iadd | L::Isub => ScalarValue::Integer {
                bits,
                value: integer(read(inst.args[0])?)?.combine(
                    integer(read(inst.args[1])?)?,
                    matches!(inst.opcode, L::Isub),
                    mask,
                ),
            },
            L::Icmp { cond } => {
                use CompareKind::{Equal, SignedLess, UnsignedLess};
                use trust_cg_lower::instructions::IntCC;
                let (kind, swap, negated) = match cond {
                    IntCC::Equal => (Equal, false, false),
                    IntCC::NotEqual => (Equal, false, true),
                    IntCC::SignedLessThan => (SignedLess, false, false),
                    IntCC::SignedGreaterThanOrEqual => (SignedLess, false, true),
                    IntCC::SignedGreaterThan => (SignedLess, true, false),
                    IntCC::SignedLessThanOrEqual => (SignedLess, true, true),
                    IntCC::UnsignedLessThan => (UnsignedLess, false, false),
                    IntCC::UnsignedGreaterThanOrEqual => (UnsignedLess, false, true),
                    IntCC::UnsignedGreaterThan => (UnsignedLess, true, false),
                    IntCC::UnsignedLessThanOrEqual => (UnsignedLess, true, true),
                };
                let a = integer(read(inst.args[0])?)?;
                let b = integer(read(inst.args[1])?)?;
                let (lhs, rhs) = if swap { (b, a) } else { (a, b) };
                ScalarValue::Bool(Predicate::compare(kind, lhs, rhs, negated, bits))
            }
            L::Select { cond } => {
                use trust_cg_lower::instructions::IntCC;
                let ScalarValue::Bool(mut predicate) = read(inst.args[0])? else {
                    return Err(Unsupported(format!(
                        "instruction {index}: select needs a canonical Boolean condition"
                    )));
                };
                match cond {
                    IntCC::NotEqual => {}
                    IntCC::Equal => predicate = predicate.inverted(),
                    _ => {
                        return Err(Unsupported(format!(
                            "instruction {index}: select condition is outside Eq/Ne"
                        )));
                    }
                }
                let then_value = read(inst.args[1])?.as_affine(bits);
                let else_value = read(inst.args[2])?.as_affine(bits);
                let (Some(then_value), Some(else_value)) = (then_value, else_value) else {
                    return Err(Unsupported(format!(
                        "instruction {index}: select needs two flat integer arms"
                    )));
                };
                ScalarValue::select(bits, predicate, then_value, else_value)
            }
            L::Return => {
                result = inst.args.first().map(|v| read(*v)).transpose()?;
                if result.map(ScalarValue::ty) != return_type {
                    return Err(Invalid(
                        "return type disagrees with inferred source value".into(),
                    ));
                }
                returned = true;
                continue;
            }
            _ => unreachable!("opcode admitted above"),
        };
        if values.insert(inst.results[0], value).is_some() {
            return Err(Invalid(format!(
                "instruction {index} redefines an SSA value"
            )));
        }
    }
    if !returned {
        return Err(Invalid("missing return".into()));
    }
    // Sidecar types are checked against independently inferred types. Never
    // inherit ISel's default-I64 behavior or accept a hint for an absent value.
    for (value, hint) in &source.value_types {
        let expected = values.get(value).map(|value| match value.ty() {
            ScalarType::Integer(32) => Type::I32,
            ScalarType::Integer(_) => Type::I64,
            ScalarType::Bool => Type::B1,
        });
        if expected.as_ref() != Some(hint) {
            return Err(Invalid(format!("inconsistent type hint for {value:?}")));
        }
    }
    Ok(SourceContract {
        bits,
        param_bits,
        return_type,
        result,
        instruction_count: block.instructions.len(),
    })
}

struct MachineState {
    mask: u64,
    next_vreg: u32,
    virtuals: HashMap<u32, ScalarValue>,
    virtual_classes: HashMap<u32, RegClass>,
    // One slot per X/W alias pair. Integers keep their actual defined width;
    // canonical Boolean values are the only general cross-width carrier.
    physical: [Option<ScalarValue>; 18],
    allocated: bool,
}

impl MachineState {
    fn new(bits: u32, param_bits: &[u32], next_vreg: u32, allocated: bool) -> Self {
        let mut physical = [None; 18];
        for (index, (value, &width)) in physical.iter_mut().zip(param_bits).enumerate() {
            *value = Some(ScalarValue::Integer {
                bits: width,
                value: Affine::parameter(index),
            });
        }
        Self {
            mask: if bits == 32 {
                u32::MAX.into()
            } else {
                u64::MAX
            },
            next_vreg,
            virtuals: HashMap::new(),
            virtual_classes: HashMap::new(),
            physical,
            allocated,
        }
    }

    fn check_vreg(&self, id: u32, class: RegClass) -> Result<(), AffineLoweringError> {
        if !matches!(class, RegClass::Gpr32 | RegClass::Gpr64)
            || id >= self.next_vreg
            || self
                .virtual_classes
                .get(&id)
                .is_some_and(|previous| *previous != class)
        {
            return Err(AffineLoweringError::InvalidMachine(
                "wrong-width or out-of-arena virtual register".into(),
            ));
        }
        Ok(())
    }

    fn physical_index(&self, reg: PReg) -> Result<usize, AffineLoweringError> {
        let encoding = reg.encoding();
        let index = match encoding {
            0..=17 if self.allocated || encoding <= 7 => encoding,
            32..=49 if self.allocated || encoding <= 39 => encoding - 32,
            _ => {
                return Err(AffineLoweringError::InvalidMachine(format!(
                    "unsupported or wrong-width register {reg:?}"
                )));
            }
        };
        Ok(usize::from(index))
    }

    fn operand_width(&self, op: &MachOperand) -> Result<u32, AffineLoweringError> {
        match op {
            MachOperand::VReg(reg) => {
                if self.allocated {
                    return Err(AffineLoweringError::InvalidMachine(
                        "unallocated register in final scalar body".into(),
                    ));
                }
                self.check_vreg(reg.id, reg.class)?;
                Ok(if reg.class == RegClass::Gpr32 { 32 } else { 64 })
            }
            MachOperand::PReg(reg) => {
                self.physical_index(*reg)?;
                Ok(if reg.encoding() >= 32 { 32 } else { 64 })
            }
            MachOperand::Special(SpecialReg::XZR) => Ok(64),
            MachOperand::Special(SpecialReg::WZR) => Ok(32),
            _ => Err(AffineLoweringError::InvalidMachine(format!(
                "unsupported register operand {op:?}"
            ))),
        }
    }

    fn read(
        &self,
        op: &MachOperand,
        formal_copy: bool,
    ) -> Result<ScalarValue, AffineLoweringError> {
        use AffineLoweringError::InvalidMachine as Invalid;
        let width = self.operand_width(op)?;
        let value = match op {
            MachOperand::VReg(reg) => {
                self.check_vreg(reg.id, reg.class)?;
                self.virtuals.get(&reg.id).copied()
            }
            MachOperand::PReg(reg) => self.physical[self.physical_index(*reg)?],
            MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR) => Some(ScalarValue::Integer {
                bits: width,
                value: Affine::constant(0, u64::MAX),
            }),
            _ => return Err(Invalid(format!("unsupported register operand {op:?}"))),
        };
        let value = value.ok_or_else(|| Invalid(format!("read of undefined register {op:?}")))?;
        if let Some(value) = value.at_width(width) {
            return Ok(value);
        }
        // Raw ISel names integer formals Xn even for a W destination. Only
        // an actual W-destination Copy may observe that truncated convention,
        // and only of a value that is itself 32 bits wide.
        if formal_copy
            && width == 64
            && matches!(op, MachOperand::PReg(_))
            && value.ty() == ScalarType::Integer(32)
        {
            return Ok(value);
        }
        // A stored literal 0/1 has no unknown upper bits: unlike parameter
        // forms it arose from a fully checked value-producing instruction.
        value
            .as_bool()
            .map(ScalarValue::Bool)
            .ok_or_else(|| Invalid(format!("wrong-width read of {op:?}")))
    }

    fn write(&mut self, op: &MachOperand, value: ScalarValue) -> Result<(), AffineLoweringError> {
        let width = self.operand_width(op)?;
        let value = value
            .at_width(width)
            .or_else(|| value.as_bool().map(ScalarValue::Bool))
            .ok_or_else(|| {
                AffineLoweringError::InvalidMachine("wrong-width register write".into())
            })?;
        match op {
            MachOperand::VReg(reg) => {
                self.check_vreg(reg.id, reg.class)?;
                self.virtual_classes.insert(reg.id, reg.class);
                self.virtuals.insert(reg.id, value);
            }
            MachOperand::PReg(reg) if self.allocated || self.physical_index(*reg)? == 0 => {
                let index = self.physical_index(*reg)?;
                self.physical[index] = Some(value);
            }
            _ => {
                return Err(AffineLoweringError::InvalidMachine(
                    "write outside virtual or exact ABI return register".into(),
                ));
            }
        }
        Ok(())
    }
}

fn machine_result(
    source: &Function,
    machine: &MachFunction,
    contract: &SourceContract,
) -> Result<Option<ScalarValue>, AffineLoweringError> {
    machine_result_with_allocation(source, machine, contract, false)
}

fn machine_result_with_allocation(
    source: &Function,
    machine: &MachFunction,
    contract: &SourceContract,
    allocated: bool,
) -> Result<Option<ScalarValue>, AffineLoweringError> {
    use AffineLoweringError::{InvalidMachine as Invalid, UnsupportedMachine as Unsupported};
    if source.name != machine.name {
        return Err(Invalid("source/machine function name mismatch".into()));
    }
    let machine_type = |bits: u32| {
        if bits == 32 {
            trust_cg_ir::function::Type::I32
        } else {
            trust_cg_ir::function::Type::I64
        }
    };
    let expected_return = contract.return_type.map(|ty| match ty {
        ScalarType::Integer(32) => trust_cg_ir::function::Type::I32,
        ScalarType::Integer(_) => trust_cg_ir::function::Type::I64,
        ScalarType::Bool => trust_cg_ir::function::Type::B1,
    });
    if machine.signature.params.len() != source.signature.params.len()
        || machine.signature.returns.len() != source.signature.returns.len()
        || machine
            .signature
            .params
            .iter()
            .zip(&contract.param_bits)
            .any(|(ty, &bits)| ty != &machine_type(bits))
        || machine.signature.returns.first() != expected_return.as_ref()
    {
        return Err(Invalid("source/machine signature mismatch".into()));
    }
    if machine.blocks.len() != 1
        || machine.entry.0 != 0
        || machine.block_order != [machine.entry]
        || !machine.blocks[0].preds.is_empty()
        || !machine.blocks[0].succs.is_empty()
        || !machine.stack_slots.is_empty()
        || machine.eh_metadata.has_eh_info()
        || machine.stack_protector != StackProtectorMode::None
        || machine.stack_protector_slot.is_some()
        || !machine.jump_tables.is_empty()
    {
        return Err(Unsupported(
            "requires raw single-block code without stack, EH or CFG edges".into(),
        ));
    }
    let mut seen = vec![false; machine.insts.len()];
    let mut state = MachineState::new(
        contract.bits,
        &contract.param_bits,
        machine.next_vreg,
        allocated,
    );
    let mut returned = false;
    let mut result = None;
    let mut comparison_flags: Option<ComparisonFlags> = None;
    for (position, id) in machine.blocks[0].insts.iter().enumerate() {
        if returned {
            return Err(Invalid(format!(
                "instruction at position {position} follows return"
            )));
        }
        let inst = machine
            .insts
            .get(id.0 as usize)
            .ok_or_else(|| Invalid(format!("dangling instruction {id:?}")))?;
        if std::mem::replace(&mut seen[id.0 as usize], true) {
            return Err(Invalid(format!("duplicate instruction occurrence {id:?}")));
        }
        let expected_flags = match inst.opcode {
            M::Copy if !allocated => InstFlags::IS_PSEUDO,
            M::MOVWrr | M::MOVXrr if allocated => InstFlags::EMPTY,
            M::Ret => InstFlags::IS_RETURN.union(InstFlags::IS_TERMINATOR),
            M::CmpRR | M::CmpRI => InstFlags::HAS_SIDE_EFFECTS,
            M::MovR
            | M::Movz
            | M::Movn
            | M::Movk
            | M::AddRR
            | M::SubRR
            | M::AddRI
            | M::AddRIShift12
            | M::LslRI
            | M::SubRI
            | M::CSet
            | M::Csel
            | M::Csinc
            | M::Csinv
            | M::Csneg => InstFlags::EMPTY,
            _ => {
                return Err(Unsupported(format!(
                    "instruction {id:?}: {:?}",
                    inst.opcode
                )));
            }
        };
        if inst.flags != expected_flags || !inst.implicit_defs.is_empty() {
            return Err(Unsupported(format!(
                "instruction {id:?}: unsupported flags or implicit clobbers"
            )));
        }
        if inst
            .implicit_uses
            .iter()
            .any(|reg| state.physical_index(*reg).is_err())
        {
            return Err(Unsupported(format!(
                "instruction {id:?}: unsupported implicit register use"
            )));
        }
        let operands = &inst.operands;
        if allocated && matches!(inst.opcode, M::MOVWrr | M::MOVXrr) {
            let [MachOperand::PReg(destination), MachOperand::PReg(input)] = operands.as_slice()
            else {
                return Err(Invalid(format!(
                    "instruction {id:?}: invalid allocated move"
                )));
            };
            // These opcodes fix the architectural width even when an operand
            // retains the other view of its X/W alias after allocation.
            let view = if inst.opcode == M::MOVWrr { 32 } else { 0 };
            let destination =
                MachOperand::PReg(PReg::new(state.physical_index(*destination)? as u16 + view));
            let input = MachOperand::PReg(PReg::new(state.physical_index(*input)? as u16 + view));
            let value = state.read(&input, false)?;
            state.write(&destination, value)?;
            continue;
        }
        let arity = match inst.opcode {
            M::Ret => 1,
            M::Copy | M::MovR | M::CmpRR | M::CmpRI | M::CSet => 2,
            M::Csel | M::Csinc | M::Csinv | M::Csneg => 4,
            M::Movz | M::Movn => {
                if !(2..=3).contains(&operands.len()) {
                    return Err(Invalid(format!(
                        "instruction {id:?}: invalid move-wide arity"
                    )));
                }
                operands.len()
            }
            _ => 3,
        };
        if operands.len() != arity {
            return Err(Invalid(format!("instruction {id:?}: wrong operand arity")));
        }
        let immediate = |index: usize, max: i64| -> Result<u64, AffineLoweringError> {
            match operands.get(index) {
                Some(MachOperand::Imm(value)) if (0..=max).contains(value) => Ok(*value as u64),
                _ => Err(Invalid(format!(
                    "instruction {id:?}: invalid immediate at {index}"
                ))),
            }
        };
        let integer = |op: &MachOperand, bits: u32| -> Result<Affine, AffineLoweringError> {
            if state.operand_width(op)? != bits {
                return Err(Invalid(format!(
                    "instruction {id:?}: mismatched operand width"
                )));
            }
            state
                .read(op, false)?
                .for_type(ScalarType::Integer(bits))
                .and_then(|value| value.as_affine(bits))
                .ok_or_else(|| Invalid(format!("instruction {id:?}: noninteger operand")))
        };
        let value = match inst.opcode {
            M::Ret => {
                if operands[0] != MachOperand::PReg(LR) {
                    return Err(Invalid("return does not branch to unchanged LR".into()));
                }
                if let Some(ty) = contract.return_type {
                    result = Some(
                        state.physical[0]
                            .ok_or_else(|| Invalid("undefined return register".into()))?
                            .for_type(ty)
                            .ok_or_else(|| {
                                Invalid(
                                    "return register has wrong type or noncanonical Boolean bits"
                                        .into(),
                                )
                            })?,
                    );
                }
                returned = true;
                continue;
            }
            M::Copy | M::MovR => {
                // The X-to-W formal convention belongs to raw Copy, not every
                // instruction that happens to look like a move.
                let formal_copy = inst.opcode == M::Copy
                    && matches!(operands[0], MachOperand::VReg(_))
                    && state.operand_width(&operands[0])? == 32;
                state.read(&operands[1], formal_copy)?
            }
            M::CmpRR | M::CmpRI => {
                let width = state.operand_width(&operands[0])?;
                let lhs_value = state.read(&operands[0], false)?;
                // A W literal/copy can carry a canonical Boolean as an
                // Integer(32) rather than the Bool enum case. Admit only a
                // reaching value independently known to be 0/1; an arbitrary
                // cross-width affine value or unknown ABI high bits still
                // refuses. Keep its actual carrier width/value for NZCV.
                if width != contract.bits && lhs_value.as_bool().is_none() {
                    return Err(Invalid(format!(
                        "instruction {id:?}: comparison width differs from integer domain"
                    )));
                }
                if inst.opcode == M::CmpRI && matches!(operands[0], MachOperand::Special(_)) {
                    return Err(Invalid(format!(
                        "instruction {id:?}: immediate CMP cannot read a zero/special register"
                    )));
                }
                let rhs = if inst.opcode == M::CmpRI {
                    ScalarValue::Integer {
                        bits: width,
                        value: Affine::constant(immediate(1, 0xfff)?, state.mask),
                    }
                } else {
                    ScalarValue::Integer {
                        bits: width,
                        value: integer(&operands[1], width)?,
                    }
                };
                comparison_flags = Some(
                    ComparisonFlags::from_values(width, lhs_value, rhs).ok_or_else(|| {
                        Unsupported(format!(
                            "instruction {id:?}: CMP needs affine integers or Boolean against zero"
                        ))
                    })?,
                );
                continue;
            }
            M::CSet => {
                let cc = immediate(1, 13)? as u8;
                let predicate = comparison_flags
                    .and_then(|flags| flags.condition(cc))
                    .ok_or_else(|| {
                        Unsupported(format!(
                            "instruction {id:?}: missing CMP flags or unsupported CSET predicate"
                        ))
                    })?;
                ScalarValue::Bool(predicate)
            }
            M::Csel | M::Csinc | M::Csinv | M::Csneg => {
                let width = state.operand_width(&operands[0])?;
                if width != contract.bits {
                    return Err(Invalid(format!(
                        "instruction {id:?}: select width differs from source domain"
                    )));
                }
                let cc = immediate(3, 13)? as u8;
                let predicate = comparison_flags
                    .and_then(|flags| flags.condition(cc))
                    .ok_or_else(|| {
                        Unsupported(format!(
                            "instruction {id:?}: select lacks CMP flags or a modeled condition"
                        ))
                    })?;
                let then_value = integer(&operands[1], width)?;
                let mut else_value = integer(&operands[2], width)?;
                match inst.opcode {
                    M::Csinc => {
                        else_value =
                            else_value.combine(Affine::constant(1, state.mask), false, state.mask)
                    }
                    M::Csinv => {
                        else_value = Affine::constant(state.mask, state.mask)
                            .combine(else_value, true, state.mask)
                    }
                    M::Csneg => {
                        else_value =
                            Affine::constant(0, state.mask).combine(else_value, true, state.mask)
                    }
                    _ => {}
                }
                ScalarValue::select(width, predicate, then_value, else_value)
            }
            M::Movz | M::Movn | M::Movk => {
                let width = state.operand_width(&operands[0])?;
                let mask = if width == 32 {
                    u32::MAX as u64
                } else {
                    u64::MAX
                };
                let imm = immediate(1, 0xffff)?;
                let shift = if operands.len() == 3 {
                    immediate(2, 48)? as u32
                } else {
                    0
                };
                if shift % 16 != 0 || shift >= width {
                    return Err(Invalid(format!(
                        "instruction {id:?}: move-wide shift exceeds width"
                    )));
                }
                let shifted = imm << shift;
                let value = match inst.opcode {
                    M::Movz => shifted,
                    M::Movn => !shifted,
                    M::Movk => {
                        let previous =
                            state
                                .read(&operands[0], false)?
                                .as_constant()
                                .ok_or_else(|| {
                                    Unsupported(format!(
                                        "instruction {id:?}: MOVK patches a nonconstant"
                                    ))
                                })?;
                        (previous & !(0xffff_u64 << shift)) | shifted
                    }
                    _ => unreachable!(),
                };
                ScalarValue::Integer {
                    bits: width,
                    value: Affine::constant(value, mask),
                }
            }
            M::AddRR | M::SubRR => {
                if state.operand_width(&operands[0])? != contract.bits {
                    return Err(Invalid(format!(
                        "instruction {id:?}: arithmetic width differs from domain"
                    )));
                }
                ScalarValue::Integer {
                    bits: contract.bits,
                    value: integer(&operands[1], contract.bits)?.combine(
                        integer(&operands[2], contract.bits)?,
                        inst.opcode == M::SubRR,
                        state.mask,
                    ),
                }
            }
            M::LslRI => {
                let width = state.operand_width(&operands[0])?;
                if width != contract.bits {
                    return Err(Invalid(format!(
                        "instruction {id:?}: shift width differs from domain"
                    )));
                }
                let shift = immediate(2, i64::from(width - 1))? as u32;
                let mut value = integer(&operands[1], width)?;
                for coefficient in &mut value.0 {
                    *coefficient = coefficient.wrapping_shl(shift) & state.mask;
                }
                ScalarValue::Integer { bits: width, value }
            }
            M::AddRI | M::AddRIShift12 | M::SubRI => {
                // Unlike register-register arithmetic, Rn=31 in these
                // encodings denotes SP, never ZR. Do not interpret a public
                // Special(XZR/WZR) operand as zero and certify SP+imm.
                if matches!(operands[1], MachOperand::Special(_)) {
                    return Err(Invalid(format!(
                        "instruction {id:?}: immediate arithmetic cannot read a zero/special register"
                    )));
                }
                let mut imm = immediate(2, 0xfff)?;
                if inst.opcode == M::AddRIShift12 {
                    imm <<= 12;
                }
                if state.operand_width(&operands[0])? != contract.bits {
                    return Err(Invalid(format!(
                        "instruction {id:?}: arithmetic width differs from domain"
                    )));
                }
                ScalarValue::Integer {
                    bits: contract.bits,
                    value: integer(&operands[1], contract.bits)?.combine(
                        Affine::constant(imm, state.mask),
                        inst.opcode == M::SubRI,
                        state.mask,
                    ),
                }
            }
            _ => unreachable!("opcode admitted above"),
        };
        state.write(&operands[0], value)?;
    }
    if !returned || seen.iter().any(|live| !live) {
        return Err(Invalid(
            "missing return or unaccounted instruction arena entries".into(),
        ));
    }
    Ok(result)
}

/// Check both complete streams independently and bind the successful claim to
/// the exact immutable pair. Unsupported input is an error, never a fallback.
pub fn check_aarch64_affine_lowering<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
) -> Result<CheckedAarch64AffineLowering<'a>, AffineLoweringError> {
    check_affine_lowering(source, machine, false)
}

/// Source applicability only: the exact LIR lies inside the affine domain.
/// This grants nothing; a binder uses it so that only the source decides
/// whether a machine body is judged at all.
pub(crate) fn check_affine_source_domain(source: &Function) -> Result<(), AffineLoweringError> {
    source_contract(source).map(|_| ())
}

/// Internal final-body check: interpret allocated caller-save registers and
/// exact lowered copies. The raw lowering API retains its narrower contract.
pub(crate) fn check_allocated_aarch64_affine_lowering<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
) -> Result<CheckedAarch64AffineLowering<'a>, AffineLoweringError> {
    check_affine_lowering(source, machine, true)
}

/// Interpret both complete paths and the actual entry branch independently.
/// The caller validates instruction ownership, edges and the common frame.
pub(crate) fn check_allocated_aarch64_diamond(
    source: &Function,
    prefix: &MachFunction,
    branch: &trust_cg_ir::MachInst,
    taken: &MachFunction,
    not_taken: &MachFunction,
) -> Result<(), AffineLoweringError> {
    check_aarch64_diamond_with_allocation(source, prefix, branch, taken, not_taken, true)
}

fn check_aarch64_diamond_with_allocation(
    source: &Function,
    prefix: &MachFunction,
    branch: &trust_cg_ir::MachInst,
    taken: &MachFunction,
    not_taken: &MachFunction,
    allocated: bool,
) -> Result<(), AffineLoweringError> {
    use AffineLoweringError::UnsupportedMachine as Unsupported;
    use trust_cg_ir::{InstId, MachInst};
    let contract = source_contract(source)?;
    if contract.return_type != Some(ScalarType::Integer(contract.bits)) {
        return Err(Unsupported("diamond needs a flat integer return".into()));
    }
    let mut predicate_body = prefix.clone();
    let condition = match branch.opcode {
        M::BCond => match branch.operands.as_slice() {
            [MachOperand::Imm(cc @ 0..=13), _] => *cc,
            _ => return Err(Unsupported("invalid conditional branch operands".into())),
        },
        M::Cbz | M::Cbnz => {
            let [input, _] = branch.operands.as_slice() else {
                return Err(Unsupported("invalid compare branch operands".into()));
            };
            match input {
                MachOperand::PReg(_) => {}
                MachOperand::VReg(_) if !allocated => {}
                _ => return Err(Unsupported("invalid compare branch register".into())),
            }
            predicate_body.insts.push(MachInst::new(
                M::CmpRI,
                vec![input.clone(), MachOperand::Imm(0)],
            ));
            i64::from(branch.opcode == M::Cbnz)
        }
        _ => return Err(Unsupported("unsupported diamond branch".into())),
    };
    predicate_body.insts.push(MachInst::new(
        M::CSet,
        vec![
            MachOperand::PReg(trust_cg_ir::regs::X0),
            MachOperand::Imm(condition),
        ],
    ));
    predicate_body
        .insts
        .push(MachInst::new(M::Ret, vec![MachOperand::PReg(LR)]));
    predicate_body.blocks[0].insts = (0..predicate_body.insts.len())
        .map(|n| InstId(n as u32))
        .collect();
    predicate_body.signature.returns = vec![trust_cg_ir::function::Type::B1];
    let predicate_contract = SourceContract {
        bits: contract.bits,
        param_bits: contract.param_bits.clone(),
        return_type: Some(ScalarType::Bool),
        result: None,
        instruction_count: 0,
    };
    let Some(ScalarValue::Bool(predicate)) =
        machine_result_with_allocation(source, &predicate_body, &predicate_contract, allocated)?
    else {
        return Err(Unsupported("branch predicate is not canonical".into()));
    };
    let arm = |machine| -> Result<Affine, AffineLoweringError> {
        machine_result_with_allocation(source, machine, &contract, allocated)?
            .and_then(|value| value.as_affine(contract.bits))
            .ok_or_else(|| Unsupported("diamond arm is not a flat integer".into()))
    };
    let result = ScalarValue::select(contract.bits, predicate, arm(taken)?, arm(not_taken)?);
    if contract.result != Some(result) {
        return Err(AffineLoweringError::ReturnMismatch);
    }
    Ok(())
}

/// Bind an independently normalized scalar source result to the complete raw
/// ISel stream. The caller retains the original Core/source identity; this
/// Rust correspondence check grants no formal proof or final-byte authority.
/// Actual bounded chain/diamond edges and arena ownership are checked before
/// making scalar path views. The raw register/effect contract is unchanged.
pub(crate) fn check_raw_aarch64_control(
    source_view: &Function,
    original_machine: &MachFunction,
) -> Result<(), AffineLoweringError> {
    use crate::source_bound_frame::{
        ControlRefusal, branch_paths, check_owned_instructions, linear, scalar_body,
    };
    use AffineLoweringError::{InvalidMachine as Invalid, UnsupportedMachine as Unsupported};

    let contract = source_contract(source_view)?;
    match linear::machine_chain(original_machine) {
        Ok(chain) => {
            check_owned_instructions(original_machine, &chain.live, false)
                .ok_or_else(|| Invalid("unaccounted raw instruction arena entries".into()))?;
            let body = scalar_body(original_machine, &chain.instructions);
            let actual = machine_result(source_view, &body, &contract)?;
            return if actual == contract.result {
                Ok(())
            } else {
                Err(AffineLoweringError::ReturnMismatch)
            };
        }
        Err(ControlRefusal::Branch(mismatch)) => return Err(Invalid(mismatch.to_string())),
        Err(ControlRefusal::Shape) => {}
    }
    let paths = branch_paths::machine_paths_raw(original_machine).map_err(|error| match error {
        ControlRefusal::Branch(mismatch) => Invalid(mismatch.to_string()),
        ControlRefusal::Shape => Unsupported("requires a bounded raw chain or diamond".into()),
    })?;
    check_owned_instructions(original_machine, &paths.live, true)
        .ok_or_else(|| Invalid("unaccounted raw instruction arena entries".into()))?;
    let prefix = scalar_body(original_machine, &paths.prefix);
    let complete_path = |path: &[trust_cg_ir::InstId]| {
        let ids: Vec<_> = paths.prefix.iter().chain(path).copied().collect();
        scalar_body(original_machine, &ids)
    };
    let taken = complete_path(&paths.paths[0]);
    let not_taken = complete_path(&paths.paths[1]);
    check_aarch64_diamond_with_allocation(
        source_view,
        &prefix,
        &original_machine.insts[paths.branch.0 as usize],
        &taken,
        &not_taken,
        false,
    )
}

fn check_affine_lowering<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
    allocated: bool,
) -> Result<CheckedAarch64AffineLowering<'a>, AffineLoweringError> {
    let contract = source_contract(source)?;
    let actual = machine_result_with_allocation(source, machine, &contract, allocated)?;
    if contract.result != actual {
        return Err(AffineLoweringError::ReturnMismatch);
    }
    Ok(CheckedAarch64AffineLowering {
        source,
        machine,
        statistics: AffineLoweringStatistics {
            source_instructions: contract.instruction_count,
            machine_instructions: machine.insts.len(),
            parameter_count: source.signature.params.len(),
        },
    })
}
