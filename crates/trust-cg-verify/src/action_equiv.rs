// trust-cg-verify/action_equiv.rs - whole-function translation validation vs the trust-ir interpreter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// FIRST INCREMENT of the whole-action translation-validation lane (the
// trust-cg half of ty's "ty equiv" ask, trust-self-service-cli-2026-06-23.md
// §"ty equiv"): everything else in this crate proves PER-INSTRUCTION
// lowerings and pass chains; nothing checked a whole lowered function against
// the source function's semantics. This module does, with trust-ir's own
// deterministic interpreter as the oracle, over a structured, deterministic
// input sample (boundary values + fixed-seed splitmix64 tuples).
//
// SCOPE (honest, fail-closed): pure scalar-integer functions only —
// arithmetic/bitwise/shift/compare/select over i8..i128 + bool, block
// parameters, branches/switches, asserts, returns. Any construct outside that
// slice (calls, memory beyond parameters, floats, vectors, pointers,
// atomics, EH) yields `Inconclusive` naming the construct — NEVER a silent
// `Verified`. Differential sampling refutes with a concrete witness but
// cannot prove; `Verified` here means "agreed on every sampled input", the
// same evidentiary tier as the crate's Statistical strength, and is labeled
// as such in the verdict docs.

//! Whole-function equivalence checking: a lowered [`trust_cg_lower::Function`]
//! against its source [`trust_ir::Function`] executed by trust-ir's
//! interpreter, over deterministic sampled inputs.

use std::collections::HashMap;

use trust_cg_lower::Function as LirFunction;
use trust_cg_lower::instructions::{Block as LirBlock, IntCC, Opcode, Value};
use trust_cg_lower::types::Type as LirType;
use trust_ir::{
    FuncId, Function as TirFunction, Inst, InterpretErrorCode, InterpretValue, InterpretValueKind,
    Interpreter, Module as TirModule, Ty,
};

/// Fixed seed for the pseudo-random input tuples ("trust_cg" in ASCII):
/// reruns and cross-process invocations sample the identical input set.
const EQUIV_SAMPLE_SEED: u64 = 0x7472_7573_745f_6367;

/// Number of splitmix64-generated input tuples beyond the boundary product.
const RANDOM_TUPLES: usize = 64;

/// Cap on the boundary-value cross product (tuples, not values).
const MAX_BOUNDARY_TUPLES: usize = 1024;

/// Per-input step budget for the lowered-function evaluator.
const LIR_STEP_BUDGET: usize = 200_000;

/// Outcome of one execution, in the shape both sides can agree on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EquivalenceOutcome {
    /// Normal return: raw two's-complement bit patterns of each return value,
    /// masked to the value's declared width.
    Returns(Vec<u128>),
    /// A runtime trap (source `Assert` failure / lowered trap carrier).
    Trap,
}

/// A concrete counterexample: the input on which oracle and lowered function
/// disagree, with both observed outcomes.
#[derive(Debug, Clone)]
pub struct EquivalenceWitness {
    /// Raw bit pattern per parameter (masked to the parameter's width),
    /// in signature order.
    pub inputs: Vec<u128>,
    /// What trust-ir's interpreter (the oracle) did.
    pub oracle: EquivalenceOutcome,
    /// What the lowered function did.
    pub lowered: EquivalenceOutcome,
}

/// Verdict of [`verify_function_equivalence`].
#[derive(Debug, Clone)]
pub enum EquivalenceVerdict {
    /// Oracle and lowered function agreed on every compared input.
    ///
    /// EVIDENTIARY TIER: differential sampling — the Statistical strength,
    /// NOT a formal proof. A symbolic discharge lane can upgrade this later.
    Verified {
        /// Inputs on which both sides were executed and compared.
        inputs_checked: usize,
        /// Inputs skipped because the SOURCE hit undefined behavior there
        /// (e.g. division by zero): nothing is demanded of the lowering on
        /// UB inputs, but they are counted so coverage stays honest.
        inputs_skipped_source_ub: usize,
    },
    /// The lowered function disagreed with the oracle on a concrete input.
    Refuted { witness: Box<EquivalenceWitness> },
    /// The check could not run to a verdict — unsupported construct, missing
    /// function, or an oracle/evaluator incapacity. Fail-closed: never treat
    /// as `Verified`.
    Inconclusive { reason: String },
}

/// Check a lowered function against trust-ir's interpreter as oracle over
/// structured sampled inputs (per-width boundary values + a fixed-seed
/// splitmix64 sample).
///
/// * `module` — the source trust-ir module (context for the oracle).
/// * `fn_id` — the source function inside `module`.
/// * `lowered` — the adapter-lowered LIR function claimed to implement it.
///
/// Returns [`EquivalenceVerdict::Verified`] when every compared input
/// agrees, [`EquivalenceVerdict::Refuted`] with a concrete witness on the
/// first disagreement, and [`EquivalenceVerdict::Inconclusive`] (fail-closed,
/// loudly naming the construct) on anything outside the supported pure
/// scalar-integer slice.
pub fn verify_function_equivalence(
    module: &TirModule,
    fn_id: FuncId,
    lowered: &LirFunction,
) -> EquivalenceVerdict {
    let Some(source) = module.function_by_id(fn_id) else {
        return inconclusive(format!("source function {fn_id} not found in module"));
    };
    if source.name != lowered.name {
        // A mis-zipped (source, lowered) pair must not be judged: the verdict
        // would attach to the wrong function.
        return inconclusive(format!(
            "source/lowered name mismatch: `{}` vs `{}`",
            source.name, lowered.name
        ));
    }
    if let Err(reason) = scan_source_function(source) {
        return inconclusive(reason);
    }
    if let Err(reason) = scan_lowered_function(lowered) {
        return inconclusive(reason);
    }

    // Parameter shapes: the source entry block's params are authoritative for
    // the oracle; the lowered signature must agree in arity.
    let Some(entry) = source.blocks.iter().find(|block| block.id == source.entry) else {
        return inconclusive("source function has no entry block".to_string());
    };
    let mut param_shapes = Vec::with_capacity(entry.params.len());
    for (_vid, ty) in &entry.params {
        match param_shape(ty) {
            Some(shape) => param_shapes.push(shape),
            None => {
                return inconclusive(format!(
                    "unsupported parameter type {ty} (supported: bool + integers up to 64 bits)"
                ));
            }
        }
    }
    if lowered.signature.params.len() != param_shapes.len() {
        return inconclusive(format!(
            "parameter arity mismatch: source {} vs lowered {}",
            param_shapes.len(),
            lowered.signature.params.len()
        ));
    }

    let interpreter = Interpreter::with_module(module);
    let mut inputs_checked = 0usize;
    let mut inputs_skipped_source_ub = 0usize;

    for input in sample_inputs(&param_shapes) {
        let oracle = match run_oracle(&interpreter, source, &param_shapes, &input) {
            OracleResult::Outcome(outcome) => outcome,
            OracleResult::SourceUb => {
                inputs_skipped_source_ub += 1;
                continue;
            }
            OracleResult::Inconclusive(reason) => return inconclusive(reason),
        };
        let lowered_outcome = match run_lowered(lowered, &param_shapes, &input) {
            Ok(outcome) => outcome,
            Err(reason) => return inconclusive(reason),
        };
        if oracle != lowered_outcome {
            return EquivalenceVerdict::Refuted {
                witness: Box::new(EquivalenceWitness {
                    inputs: input,
                    oracle,
                    lowered: lowered_outcome,
                }),
            };
        }
        inputs_checked += 1;
    }

    if inputs_checked == 0 {
        // Zero compared inputs is not evidence of anything.
        return inconclusive(format!(
            "no comparable inputs: every sampled input ({inputs_skipped_source_ub}) hit source UB"
        ));
    }
    EquivalenceVerdict::Verified {
        inputs_checked,
        inputs_skipped_source_ub,
    }
}

fn inconclusive(reason: String) -> EquivalenceVerdict {
    EquivalenceVerdict::Inconclusive { reason }
}

// ---------------------------------------------------------------------------
// Supported-construct scans (fail closed, name the construct)
// ---------------------------------------------------------------------------

fn scan_source_function(func: &TirFunction) -> Result<(), String> {
    if func.blocks.is_empty() {
        return Err(format!("source function `{}` has no body", func.name));
    }
    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::BinOp { ty, .. }
                | Inst::UnOp { ty, .. }
                | Inst::ICmp { ty, .. }
                | Inst::Select { ty, .. }
                | Inst::Copy { ty, .. }
                | Inst::Const { ty, .. } => {
                    if !is_scalar_int_ty(ty) {
                        return Err(format!(
                            "unsupported non-integer type {ty} in `{}`",
                            func.name
                        ));
                    }
                }
                Inst::Cast { src_ty, dst_ty, .. } => {
                    if !is_scalar_int_ty(src_ty) || !is_scalar_int_ty(dst_ty) {
                        return Err(format!(
                            "unsupported cast {src_ty} -> {dst_ty} in `{}`",
                            func.name
                        ));
                    }
                }
                Inst::Br { .. }
                | Inst::CondBr { .. }
                | Inst::Switch { .. }
                | Inst::Return { .. }
                | Inst::Assert { .. } => {}
                // Everything else — calls (side effects), memory, atomics,
                // aggregates, pointers, floats, proof pseudo-ops — is outside
                // the slice. Decline loudly rather than guess.
                other => {
                    return Err(format!(
                        "unsupported source construct {} in `{}` (calls/memory/floats are \
                         outside the equivalence slice)",
                        inst_variant_name(other),
                        func.name
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Stable variant label for decline messages (no Debug payload noise).
fn inst_variant_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Const { .. } => "Const",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        Inst::Assert { .. } => "Assert",
        Inst::Assume { .. } => "Assume",
        Inst::Unreachable => "Unreachable",
        _ => "non-scalar instruction",
    }
}

fn is_scalar_int_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
    )
}

fn scan_lowered_function(func: &LirFunction) -> Result<(), String> {
    for (block_id, block) in &func.blocks {
        for inst in &block.instructions {
            if !lowered_opcode_supported(&inst.opcode) {
                return Err(format!(
                    "unsupported lowered opcode {:?} in `{}` block {}",
                    opcode_label(&inst.opcode),
                    func.name,
                    block_id.0
                ));
            }
        }
    }
    Ok(())
}

/// Compact label for decline messages: the variant name without payloads.
fn opcode_label(opcode: &Opcode) -> String {
    let full = format!("{opcode:?}");
    full.split([' ', '{', '('])
        .next()
        .unwrap_or("?")
        .to_string()
}

fn lowered_opcode_supported(opcode: &Opcode) -> bool {
    matches!(
        opcode,
        Opcode::Iconst { .. }
            | Opcode::Iconst128 { .. }
            | Opcode::Copy
            | Opcode::Iadd
            | Opcode::Isub
            | Opcode::Imul
            | Opcode::Udiv
            | Opcode::Sdiv
            | Opcode::Urem
            | Opcode::Srem
            | Opcode::Ineg
            | Opcode::Bnot
            | Opcode::CtPop
            | Opcode::Ishl
            | Opcode::Ushr
            | Opcode::Sshr
            | Opcode::Band
            | Opcode::Bor
            | Opcode::Bxor
            | Opcode::BandNot
            | Opcode::BorNot
            | Opcode::Sextend { .. }
            | Opcode::Uextend { .. }
            | Opcode::Trunc { .. }
            | Opcode::Icmp { .. }
            | Opcode::Select { .. }
            | Opcode::GuardDivZero { .. }
            | Opcode::GuardShiftRange { .. }
            | Opcode::Assert
            | Opcode::Jump { .. }
            | Opcode::Brif { .. }
            | Opcode::Switch { .. }
            | Opcode::Trap
            | Opcode::Return
    )
}

// ---------------------------------------------------------------------------
// Input sampling
// ---------------------------------------------------------------------------

/// Parameter shape: trust-ir type (oracle side) + width/signedness for raw
/// bit-pattern generation and LIR binding.
#[derive(Debug, Clone)]
struct ParamShape {
    ty: Ty,
    bits: u32,
    signed: bool,
}

fn param_shape(ty: &Ty) -> Option<ParamShape> {
    let (bits, signed) = match ty {
        Ty::Bool => (1, false),
        Ty::I8 => (8, true),
        Ty::U8 => (8, false),
        Ty::I16 => (16, true),
        Ty::U16 => (16, false),
        Ty::I32 => (32, true),
        Ty::U32 => (32, false),
        Ty::I64 => (64, true),
        Ty::U64 => (64, false),
        // 128-bit parameters would need U128-range oracle plumbing; decline
        // for the first increment (they still work as intermediates).
        _ => return None,
    };
    Some(ParamShape {
        ty: ty.clone(),
        bits,
        signed,
    })
}

fn width_mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

fn sign_extend(raw: u128, bits: u32) -> i128 {
    if bits >= 128 {
        raw as i128
    } else {
        let shift = 128 - bits;
        ((raw << shift) as i128) >> shift
    }
}

/// Deterministic per-parameter boundary values (raw bit patterns).
fn boundary_values(shape: &ParamShape) -> Vec<u128> {
    let mask = width_mask(shape.bits);
    let mut values = if shape.bits == 1 {
        vec![0, 1]
    } else if shape.signed {
        let min = 1u128 << (shape.bits - 1); // sign bit only == MIN
        let max = min - 1;
        vec![
            0,
            1,
            mask, /* -1 */
            min,
            max,
            3,
            (0u128.wrapping_sub(3)) & mask,
        ]
    } else {
        vec![0, 1, 2, 3, mask, mask - 1, 1u128 << (shape.bits - 1)]
    };
    values.dedup();
    values
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// The deterministic input set: capped boundary cross product + fixed-seed
/// pseudo-random tuples. Zero-parameter functions get the single empty tuple.
fn sample_inputs(shapes: &[ParamShape]) -> Vec<Vec<u128>> {
    if shapes.is_empty() {
        return vec![Vec::new()];
    }
    let per_param: Vec<Vec<u128>> = shapes.iter().map(boundary_values).collect();
    let product: usize = per_param
        .iter()
        .map(|v| v.len())
        .try_fold(1usize, |acc, n| acc.checked_mul(n))
        .unwrap_or(usize::MAX);
    let take = product.min(MAX_BOUNDARY_TUPLES);

    let mut inputs = Vec::with_capacity(take + RANDOM_TUPLES);
    // First `take` tuples of the cross product in lexicographic order —
    // deterministic and prefix-stable under cap growth.
    for index in 0..take {
        let mut remaining = index;
        let mut tuple = Vec::with_capacity(shapes.len());
        for values in per_param.iter().rev() {
            tuple.push(values[remaining % values.len()]);
            remaining /= values.len();
        }
        tuple.reverse();
        inputs.push(tuple);
    }
    let mut state = EQUIV_SAMPLE_SEED;
    for _ in 0..RANDOM_TUPLES {
        let tuple = shapes
            .iter()
            .map(|shape| {
                let wide =
                    (u128::from(splitmix64(&mut state)) << 64) | u128::from(splitmix64(&mut state));
                wide & width_mask(shape.bits)
            })
            .collect();
        inputs.push(tuple);
    }
    inputs
}

// ---------------------------------------------------------------------------
// Oracle side (trust-ir interpreter)
// ---------------------------------------------------------------------------

enum OracleResult {
    Outcome(EquivalenceOutcome),
    /// The source function's own semantics are undefined on this input
    /// (e.g. division by zero): the lowering owes nothing here.
    SourceUb,
    Inconclusive(String),
}

fn run_oracle(
    interpreter: &Interpreter<'_>,
    source: &TirFunction,
    shapes: &[ParamShape],
    input: &[u128],
) -> OracleResult {
    let mut args = Vec::with_capacity(input.len());
    for (shape, raw) in shapes.iter().zip(input) {
        let value = if matches!(shape.ty, Ty::Bool) {
            InterpretValue::bool(raw & 1 == 1)
        } else {
            let as_int = if shape.signed {
                sign_extend(*raw, shape.bits)
            } else {
                *raw as i128
            };
            match InterpretValue::int(shape.ty.clone(), as_int) {
                Ok(value) => value,
                Err(error) => {
                    return OracleResult::Inconclusive(format!(
                        "oracle argument construction failed: {error:?}"
                    ));
                }
            }
        };
        args.push(value);
    }

    match interpreter.execute_function(source, args) {
        Ok(outcome) => {
            let mut raws = Vec::with_capacity(outcome.returns.len());
            for value in &outcome.returns {
                match &value.kind {
                    InterpretValueKind::Int(int) => raws.push(int.as_unsigned()),
                    InterpretValueKind::Bool(b) => raws.push(u128::from(*b)),
                    other => {
                        return OracleResult::Inconclusive(format!(
                            "oracle returned a non-scalar value: {other:?}"
                        ));
                    }
                }
            }
            OracleResult::Outcome(EquivalenceOutcome::Returns(raws))
        }
        Err(error) => match error.code {
            InterpretErrorCode::Panic => OracleResult::Outcome(EquivalenceOutcome::Trap),
            InterpretErrorCode::UndefinedBehavior => OracleResult::SourceUb,
            // Everything else (unsupported constructs the scan missed, fuel,
            // type errors) is an incapacity, not a verdict.
            _ => OracleResult::Inconclusive(format!("oracle error: {error:?}")),
        },
    }
}

// ---------------------------------------------------------------------------
// Lowered side: a small concrete evaluator for the supported LIR slice
// ---------------------------------------------------------------------------

fn lir_type_bits(ty: &LirType) -> Option<u32> {
    match ty {
        LirType::B1 => Some(1),
        LirType::I8 => Some(8),
        LirType::I16 => Some(16),
        LirType::I32 => Some(32),
        LirType::I64 => Some(64),
        LirType::I128 => Some(128),
        _ => None,
    }
}

/// Evaluate the lowered function on one input tuple.
///
/// The adapter resolves trust-ir block arguments into edge-copy blocks, so
/// only the ENTRY block's params bind from outside; every other block param
/// value is defined by `Copy` instructions on the incoming edge.
fn run_lowered(
    func: &LirFunction,
    shapes: &[ParamShape],
    input: &[u128],
) -> Result<EquivalenceOutcome, String> {
    let entry = func
        .blocks
        .get(&func.entry_block)
        .ok_or_else(|| format!("lowered `{}` has no entry block", func.name))?;
    if entry.params.len() != shapes.len() {
        return Err(format!(
            "lowered `{}` entry block binds {} params for {} source params",
            func.name,
            entry.params.len(),
            shapes.len()
        ));
    }

    let mut values: HashMap<u32, (u128, u32)> = HashMap::new();
    for ((value, ty), raw) in entry.params.iter().zip(input) {
        let bits = lir_type_bits(ty)
            .ok_or_else(|| format!("unsupported lowered param type {ty:?} in `{}`", func.name))?;
        values.insert(value.0, (*raw & width_mask(bits), bits));
    }

    let mut current = func.entry_block;
    let mut steps = 0usize;
    'blocks: loop {
        let block = func.blocks.get(&current).ok_or_else(|| {
            format!(
                "lowered `{}` jumps to missing block {}",
                func.name, current.0
            )
        })?;
        for inst in &block.instructions {
            steps += 1;
            if steps > LIR_STEP_BUDGET {
                return Err(format!(
                    "lowered `{}` exceeded the {LIR_STEP_BUDGET}-step evaluation budget",
                    func.name
                ));
            }
            let read = |values: &HashMap<u32, (u128, u32)>,
                        value: &Value|
             -> Result<(u128, u32), String> {
                values
                    .get(&value.0)
                    .copied()
                    .ok_or_else(|| format!("lowered `{}` reads undefined v{}", func.name, value.0))
            };
            let arg =
                |values: &HashMap<u32, (u128, u32)>, index: usize| -> Result<(u128, u32), String> {
                    let value = inst.args.get(index).ok_or_else(|| {
                        format!("lowered `{}` missing operand {index}", func.name)
                    })?;
                    read(values, value)
                };
            let write = |values: &mut HashMap<u32, (u128, u32)>,
                         results: &[Value],
                         raw: u128,
                         bits: u32|
             -> Result<(), String> {
                let dst = results
                    .first()
                    .ok_or_else(|| format!("lowered `{}` missing result", func.name))?;
                values.insert(dst.0, (raw & width_mask(bits), bits));
                Ok(())
            };

            match &inst.opcode {
                Opcode::Iconst { ty, imm } => {
                    let bits = lir_type_bits(ty)
                        .ok_or_else(|| format!("unsupported Iconst type {ty:?}"))?;
                    write(&mut values, &inst.results, *imm as i128 as u128, bits)?;
                }
                Opcode::Iconst128 { lo, hi } => {
                    let raw = (u128::from(*hi as u64) << 64) | u128::from(*lo as u64);
                    write(&mut values, &inst.results, raw, 128)?;
                }
                Opcode::Copy => {
                    let (raw, bits) = arg(&values, 0)?;
                    write(&mut values, &inst.results, raw, bits)?;
                }
                Opcode::Iadd
                | Opcode::Isub
                | Opcode::Imul
                | Opcode::Band
                | Opcode::Bor
                | Opcode::Bxor
                | Opcode::BandNot
                | Opcode::BorNot => {
                    let (lhs, bits) = arg(&values, 0)?;
                    let (rhs, rbits) = arg(&values, 1)?;
                    if bits != rbits {
                        return Err(format!("width mismatch in `{}` binary op", func.name));
                    }
                    let raw = match &inst.opcode {
                        Opcode::Iadd => lhs.wrapping_add(rhs),
                        Opcode::Isub => lhs.wrapping_sub(rhs),
                        Opcode::Imul => lhs.wrapping_mul(rhs),
                        Opcode::Band => lhs & rhs,
                        Opcode::Bor => lhs | rhs,
                        Opcode::Bxor => lhs ^ rhs,
                        Opcode::BandNot => lhs & !rhs,
                        _ => lhs | !rhs,
                    };
                    write(&mut values, &inst.results, raw, bits)?;
                }
                Opcode::Udiv | Opcode::Urem | Opcode::Sdiv | Opcode::Srem => {
                    let (lhs, bits) = arg(&values, 0)?;
                    let (rhs, rbits) = arg(&values, 1)?;
                    if bits != rbits {
                        return Err(format!("width mismatch in `{}` division", func.name));
                    }
                    if rhs == 0 {
                        return Ok(EquivalenceOutcome::Trap);
                    }
                    let raw = match &inst.opcode {
                        Opcode::Udiv => lhs / rhs,
                        Opcode::Urem => lhs % rhs,
                        signed_op => {
                            let sl = sign_extend(lhs, bits);
                            let sr = sign_extend(rhs, bits);
                            let min = sign_extend(1u128 << (bits - 1), bits);
                            if sl == min && sr == -1 {
                                return Ok(EquivalenceOutcome::Trap);
                            }
                            let value = if matches!(signed_op, Opcode::Sdiv) {
                                sl / sr
                            } else {
                                sl % sr
                            };
                            value as u128
                        }
                    };
                    write(&mut values, &inst.results, raw, bits)?;
                }
                Opcode::Ineg => {
                    let (raw, bits) = arg(&values, 0)?;
                    write(&mut values, &inst.results, 0u128.wrapping_sub(raw), bits)?;
                }
                Opcode::Bnot => {
                    let (raw, bits) = arg(&values, 0)?;
                    write(&mut values, &inst.results, !raw, bits)?;
                }
                Opcode::CtPop => {
                    let (raw, bits) = arg(&values, 0)?;
                    write(
                        &mut values,
                        &inst.results,
                        u128::from(raw.count_ones()),
                        bits,
                    )?;
                }
                Opcode::Ishl | Opcode::Ushr | Opcode::Sshr => {
                    let (raw, bits) = arg(&values, 0)?;
                    let (amount, _) = arg(&values, 1)?;
                    if amount >= u128::from(bits) {
                        // Mirrors the source contract: an out-of-range shift is
                        // UB there, so the oracle skips the input; reaching
                        // this in a compared run means the LOWERING introduced
                        // it — treat as a trap-visible divergence.
                        return Ok(EquivalenceOutcome::Trap);
                    }
                    let raw = match &inst.opcode {
                        Opcode::Ishl => raw << amount,
                        Opcode::Ushr => raw >> amount,
                        _ => (sign_extend(raw, bits) >> amount) as u128,
                    };
                    write(&mut values, &inst.results, raw, bits)?;
                }
                Opcode::Sextend { from_ty, to_ty } => {
                    let (raw, _) = arg(&values, 0)?;
                    let from = lir_type_bits(from_ty)
                        .ok_or_else(|| format!("unsupported Sextend from {from_ty:?}"))?;
                    let to = lir_type_bits(to_ty)
                        .ok_or_else(|| format!("unsupported Sextend to {to_ty:?}"))?;
                    write(
                        &mut values,
                        &inst.results,
                        sign_extend(raw, from) as u128,
                        to,
                    )?;
                }
                Opcode::Uextend { from_ty, to_ty } => {
                    let (raw, _) = arg(&values, 0)?;
                    let from = lir_type_bits(from_ty)
                        .ok_or_else(|| format!("unsupported Uextend from {from_ty:?}"))?;
                    let to = lir_type_bits(to_ty)
                        .ok_or_else(|| format!("unsupported Uextend to {to_ty:?}"))?;
                    write(&mut values, &inst.results, raw & width_mask(from), to)?;
                }
                Opcode::Trunc { to_ty } => {
                    let (raw, _) = arg(&values, 0)?;
                    let to = lir_type_bits(to_ty)
                        .ok_or_else(|| format!("unsupported Trunc to {to_ty:?}"))?;
                    write(&mut values, &inst.results, raw, to)?;
                }
                Opcode::Icmp { cond } => {
                    let (lhs, bits) = arg(&values, 0)?;
                    let (rhs, rbits) = arg(&values, 1)?;
                    if bits != rbits {
                        return Err(format!("width mismatch in `{}` compare", func.name));
                    }
                    let outcome = icmp(*cond, lhs, rhs, bits);
                    write(&mut values, &inst.results, u128::from(outcome), 1)?;
                }
                Opcode::Select {
                    cond: IntCC::NotEqual,
                } => {
                    // Adapter shape: args = [cond, then_val, else_val],
                    // select-then when cond != 0.
                    let (cond, _) = arg(&values, 0)?;
                    let (then_val, bits) = arg(&values, 1)?;
                    let (else_val, _) = arg(&values, 2)?;
                    let raw = if cond != 0 { then_val } else { else_val };
                    write(&mut values, &inst.results, raw, bits)?;
                }
                Opcode::Select { cond } => {
                    return Err(format!(
                        "unsupported Select condition {cond:?} in `{}`",
                        func.name
                    ));
                }
                Opcode::GuardDivZero { .. } => {
                    // Runtime shape of the proof-only carrier: trap when the
                    // divisor is zero (expand_trap_div_zero_if_zero).
                    let (divisor, _) = arg(&values, 0)?;
                    if divisor == 0 {
                        return Ok(EquivalenceOutcome::Trap);
                    }
                }
                Opcode::GuardShiftRange { bitwidth, .. } => {
                    let (amount, _) = arg(&values, 0)?;
                    if amount >= u128::from(*bitwidth) {
                        return Ok(EquivalenceOutcome::Trap);
                    }
                }
                Opcode::Assert => {
                    let (cond, _) = arg(&values, 0)?;
                    if cond == 0 {
                        return Ok(EquivalenceOutcome::Trap);
                    }
                }
                Opcode::Trap => return Ok(EquivalenceOutcome::Trap),
                Opcode::Jump { dest } => {
                    current = *dest;
                    continue 'blocks;
                }
                Opcode::Brif {
                    cond,
                    then_dest,
                    else_dest,
                } => {
                    let (cond, _) = read(&values, cond)?;
                    current = if cond != 0 { *then_dest } else { *else_dest };
                    continue 'blocks;
                }
                Opcode::Switch { cases, default } => {
                    let (selector, bits) = arg(&values, 0)?;
                    let mut next: LirBlock = *default;
                    for (case, dest) in cases {
                        if (*case as i128 as u128) & width_mask(bits) == selector {
                            next = *dest;
                            break;
                        }
                    }
                    current = next;
                    continue 'blocks;
                }
                Opcode::Return => {
                    let mut raws = Vec::with_capacity(inst.args.len());
                    for index in 0..inst.args.len() {
                        raws.push(arg(&values, index)?.0);
                    }
                    return Ok(EquivalenceOutcome::Returns(raws));
                }
                other => {
                    // Unreachable given scan_lowered_function, but fail closed
                    // if the allowlists ever drift apart.
                    return Err(format!(
                        "unsupported lowered opcode {:?} reached evaluation in `{}`",
                        opcode_label(other),
                        func.name
                    ));
                }
            }
        }
        // A block ended without a terminator: malformed for this slice.
        return Err(format!(
            "lowered `{}` block {} falls off the end without a terminator",
            func.name, current.0
        ));
    }
}

fn icmp(cond: IntCC, lhs: u128, rhs: u128, bits: u32) -> bool {
    let sl = sign_extend(lhs, bits);
    let sr = sign_extend(rhs, bits);
    match cond {
        IntCC::Equal => lhs == rhs,
        IntCC::NotEqual => lhs != rhs,
        IntCC::SignedLessThan => sl < sr,
        IntCC::SignedGreaterThanOrEqual => sl >= sr,
        IntCC::SignedGreaterThan => sl > sr,
        IntCC::SignedLessThanOrEqual => sl <= sr,
        IntCC::UnsignedLessThan => lhs < rhs,
        IntCC::UnsignedGreaterThanOrEqual => lhs >= rhs,
        IntCC::UnsignedGreaterThan => lhs > rhs,
        IntCC::UnsignedLessThanOrEqual => lhs <= rhs,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::adapter::translate_module;
    use trust_ir::{BinOp, Block, BlockId, Constant, FuncTy, ICmpOp, InstrNode, Module, ValueId};

    /// `fn branchy(a: i64, b: i64) -> i64`:
    /// ```text
    /// entry(a, b):
    ///   sum  = add i64 a, b
    ///   gt   = icmp sgt i64 a, b
    ///   condbr gt, then(sum), else(sum)
    /// then(x): r = sub i64 x, b ; return r
    /// else(y): r = xor i64 y, a ; return r
    /// ```
    fn branchy_module() -> Module {
        let mut module = Module::new("action_equiv_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = trust_ir::Function::new(FuncId::new(0), "branchy", ft, BlockId::new(0));

        let a = ValueId::new(0);
        let b = ValueId::new(1);
        let sum = ValueId::new(2);
        let gt = ValueId::new(3);
        let x = ValueId::new(4);
        let then_r = ValueId::new(5);
        let y = ValueId::new(6);
        let else_r = ValueId::new(7);

        let mut entry = Block::new(BlockId::new(0))
            .with_param(a, Ty::I64)
            .with_param(b, Ty::I64);
        entry.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: a,
                rhs: b,
            })
            .with_result(sum),
        );
        entry.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I64,
                lhs: a,
                rhs: b,
            })
            .with_result(gt),
        );
        entry.body.push(InstrNode::new(Inst::CondBr {
            cond: gt,
            then_target: BlockId::new(1),
            then_args: vec![sum],
            else_target: BlockId::new(2),
            else_args: vec![sum],
        }));
        func.blocks.push(entry);

        let mut then_block = Block::new(BlockId::new(1)).with_param(x, Ty::I64);
        then_block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: x,
                rhs: b,
            })
            .with_result(then_r),
        );
        then_block.body.push(InstrNode::new(Inst::Return {
            values: vec![then_r],
        }));
        func.blocks.push(then_block);

        let mut else_block = Block::new(BlockId::new(2)).with_param(y, Ty::I64);
        else_block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Xor,
                ty: Ty::I64,
                lhs: y,
                rhs: a,
            })
            .with_result(else_r),
        );
        else_block.body.push(InstrNode::new(Inst::Return {
            values: vec![else_r],
        }));
        func.blocks.push(else_block);

        module.add_function(func);
        module
    }

    fn lower_first(module: &Module) -> LirFunction {
        let lowered = translate_module(module).expect("test module lowers");
        assert_eq!(lowered.len(), 1);
        lowered.into_iter().next().unwrap().0
    }

    #[test]
    fn correct_lowering_verifies() {
        let module = branchy_module();
        let lowered = lower_first(&module);
        match verify_function_equivalence(&module, FuncId::new(0), &lowered) {
            EquivalenceVerdict::Verified {
                inputs_checked,
                inputs_skipped_source_ub,
            } => {
                assert!(
                    inputs_checked > 50,
                    "expected a real sample, got {inputs_checked}"
                );
                assert_eq!(inputs_skipped_source_ub, 0, "branchy has no UB inputs");
            }
            other => panic!("adapter lowering of branchy must verify, got {other:?}"),
        }
    }

    #[test]
    fn divergent_mock_lowering_is_refuted_with_concrete_witness() {
        let module = branchy_module();
        let mut lowered = lower_first(&module);

        // The deliberately divergent mock lowering: the Iadd became an Isub
        // (the classic wrong-opcode isel defect).
        let mut corrupted = false;
        for block in lowered.blocks.values_mut() {
            for inst in &mut block.instructions {
                if matches!(inst.opcode, Opcode::Iadd) {
                    inst.opcode = Opcode::Isub;
                    corrupted = true;
                }
            }
        }
        assert!(corrupted, "test premise: the lowering contains an Iadd");

        match verify_function_equivalence(&module, FuncId::new(0), &lowered) {
            EquivalenceVerdict::Refuted { witness } => {
                // The witness must be a CONCRETE, complete counterexample.
                assert_eq!(witness.inputs.len(), 2);
                assert_ne!(
                    witness.oracle, witness.lowered,
                    "witness must show an actual disagreement"
                );
                // And it must genuinely refute: a+b != a-b requires b != 0.
                assert_ne!(witness.inputs[1], 0, "a divergence needs b != 0");
            }
            other => panic!("sub-for-add corruption must be refuted, got {other:?}"),
        }
    }

    #[test]
    fn unsupported_construct_is_inconclusive_not_verified() {
        // `fn effectful() -> i64 { call helper(); ... }` — a call is outside
        // the slice (side effects), so the check must DECLINE, not verify.
        let mut module = Module::new("action_equiv_unsupported");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut caller = trust_ir::Function::new(FuncId::new(0), "effectful", ft, BlockId::new(0));
        let r = ValueId::new(0);
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![],
            })
            .with_result(r),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![r] }));
        caller.blocks.push(entry);
        module.add_function(caller);

        let mut helper = trust_ir::Function::new(FuncId::new(1), "helper", ft, BlockId::new(1));
        let hv = ValueId::new(1);
        let mut hentry = Block::new(BlockId::new(1));
        hentry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            })
            .with_result(hv),
        );
        hentry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![hv] }));
        helper.blocks.push(hentry);
        module.add_function(helper);

        let lowered = translate_module(&module).expect("call module lowers");
        let (caller_lowered, _) = lowered
            .into_iter()
            .find(|(f, _)| f.name == "effectful")
            .expect("caller lowered");

        match verify_function_equivalence(&module, FuncId::new(0), &caller_lowered) {
            EquivalenceVerdict::Inconclusive { reason } => {
                assert!(
                    reason.contains("Call"),
                    "the decline must name the construct, got: {reason}"
                );
            }
            other => panic!("a call must be Inconclusive (never Verified), got {other:?}"),
        }
    }

    #[test]
    fn sample_inputs_are_deterministic() {
        let shapes = vec![
            param_shape(&Ty::I64).unwrap(),
            param_shape(&Ty::U8).unwrap(),
        ];
        assert_eq!(sample_inputs(&shapes), sample_inputs(&shapes));
        // Boundary product (7 x 7) + 64 random tuples.
        assert_eq!(sample_inputs(&shapes).len(), 49 + 64);
    }
}
