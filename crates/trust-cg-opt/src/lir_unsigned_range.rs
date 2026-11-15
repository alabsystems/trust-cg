// trust-cg-opt/lir_unsigned_range.rs - Conservative LIR unsigned-range simplification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A small, target-independent unsigned interval analysis over LIR.
//!
//! The pass intentionally operates before instruction selection.  It proves a
//! few common checks from facts that are intrinsic to the LIR expression (for
//! example, `x & 63` is in `0..=63`) and rewrites only when the whole unsigned
//! interval establishes the result.  Unknown or malformed input is left
//! untouched.
//!
//! Proof-only `Guard*` opcodes are outside this pass.  They carry obligations
//! consumed by the certified-elimination path; an ordinary dataflow fact must
//! not bypass that authorization boundary.
//!
//! Nothing validates the rewrites this pass makes: it deletes `Assert`s and
//! folds `Brif`, `Select`, compares and checked arithmetic on the strength of
//! its own interval facts, and every proof downstream takes the simplified
//! LIR as its source. So a compile that claims proofs does not run it (ruling
//! OD-225, `trust_cg_codegen::lir_module_prep`, "Proof claims"). The way back
//! is V-range: a theorem whose source is the LIR before this pass and which
//! proves each deleted `Assert` and each folded edge infeasible. The trust-ir
//! port of these rules (`trust-cg-irmid`, `passes/range.rs`) has its own
//! witness checker (`trust-cg-verify`, `trust_ir_mid_tv_range.rs`); this LIR
//! pass has none.

use crate::fast_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use std::borrow::Cow;

use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::{Function, ProofContext, Type};

/// Counts of LIR instructions simplified by [`simplify_function`].
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct LirUnsignedRangeStats {
    pub checked_adds_simplified: usize,
    pub checked_muls_simplified: usize,
    pub comparisons_folded: usize,
    pub selects_folded: usize,
    pub asserts_removed: usize,
    pub branches_folded: usize,
}

impl LirUnsignedRangeStats {
    fn merge(&mut self, other: Self) {
        self.checked_adds_simplified += other.checked_adds_simplified;
        self.checked_muls_simplified += other.checked_muls_simplified;
        self.comparisons_folded += other.comparisons_folded;
        self.selects_folded += other.selects_folded;
        self.asserts_removed += other.asserts_removed;
        self.branches_folded += other.branches_folded;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct UIntRange {
    lo: u128,
    hi: u128,
    width: u32,
}

impl UIntRange {
    fn exact(value: u128, width: u32) -> Self {
        Self {
            lo: value,
            hi: value,
            width,
        }
    }

    fn exact_value(self) -> Option<u128> {
        (self.lo == self.hi).then_some(self.lo)
    }
}

#[derive(Debug, Default)]
struct FunctionRewritePlan {
    stats: LirUnsignedRangeStats,
    blocks: Vec<BlockRewritePlan>,
}

#[derive(Debug)]
struct BlockRewritePlan {
    block_id: Block,
    replacements: Vec<(usize, Vec<Instruction>)>,
}

/// Simplify all functions while leaving their proof contexts byte-for-byte
/// logically untouched.
pub fn simplify_module(functions: &mut [(Function, ProofContext)]) -> LirUnsignedRangeStats {
    let mut total = LirUnsignedRangeStats::default();
    for (function, _) in functions {
        total.merge(simplify_function(function));
    }
    total
}

/// [`simplify_module`] over only the functions at `indices` (an index past
/// the end is ignored). A JIT runs the pass over the functions its module
/// inliner changed — where inlining can expose new masked operands — rather
/// than over the whole module (`trust_cg_codegen::lir_module_prep`).
pub fn simplify_functions_at(
    functions: &mut [(Function, ProofContext)],
    indices: &[usize],
) -> LirUnsignedRangeStats {
    let mut total = LirUnsignedRangeStats::default();
    for &index in indices {
        if let Some((function, _)) = functions.get_mut(index) {
            total.merge(simplify_function(function));
        }
    }
    total
}

/// Return a simplified view of one LIR function, cloning it only when the
/// analysis found at least one authorized rewrite.
///
/// A function with no candidate opcode, a candidate whose range cannot be
/// proved, or malformed metadata that makes the pass fail closed is returned as
/// [`Cow::Borrowed`].  [`Cow::Owned`] therefore means the returned function was
/// actually changed.  The input is never mutated, and an owned result is
/// identical to applying [`simplify_function`] to a clone of the same input.
pub fn simplify_function_clone_on_change(function: &Function) -> Cow<'_, Function> {
    let plan = plan_function_rewrites(function);
    if plan.blocks.is_empty() {
        return Cow::Borrowed(function);
    }

    let mut simplified = function.clone();
    apply_function_rewrite_plan(&mut simplified, plan);
    Cow::Owned(simplified)
}

/// Simplify one LIR function using block-local unsigned interval facts.
///
/// Block-locality is deliberate: it needs no dominance assumptions and cannot
/// accidentally carry a fact across a loop backedge or CFG join.  The source
/// patterns targeted here produce their mask, checked operation/comparison,
/// and runtime assertion in one block.
pub fn simplify_function(function: &mut Function) -> LirUnsignedRangeStats {
    let plan = plan_function_rewrites(function);
    let stats = plan.stats;
    apply_function_rewrite_plan(function, plan);
    stats
}

fn plan_function_rewrites(function: &Function) -> FunctionRewritePlan {
    let mut plan = FunctionRewritePlan::default();
    if !function
        .blocks
        .values()
        .any(|block| block.instructions.iter().any(instruction_may_be_simplified))
    {
        return plan;
    }

    let value_types = infer_value_types(function);

    // Stable traversal is useful for reproducible diagnostics and tests even
    // though facts never cross a block boundary.
    let mut seen_blocks =
        HashSet::with_capacity_and_hasher(function.blocks.len(), Default::default());
    let mut block_ids = Vec::with_capacity(function.blocks.len());
    for block in &function.block_order {
        if function.blocks.contains_key(block) && seen_blocks.insert(*block) {
            block_ids.push(*block);
        }
    }
    let mut unordered: Vec<Block> = function
        .blocks
        .keys()
        .copied()
        .filter(|block| seen_blocks.insert(*block))
        .collect();
    unordered.sort_unstable();
    block_ids.extend(unordered);

    for block_id in block_ids {
        let Some(block) = function.blocks.get(&block_id) else {
            continue;
        };
        if !block.instructions.iter().any(instruction_may_be_simplified) {
            continue;
        }

        let original_origins = function
            .trust_ir_origins
            .get(&block_id)
            .map(Vec::as_slice)
            .unwrap_or_default();

        // A nonempty sidecar is an exact positional binding, not a best-effort
        // hint.  Refuse the whole block if either binding is malformed; padding
        // or truncating it while rewriting could attach a proof/source origin
        // to the wrong instruction.
        if (!block.source_locs.is_empty() && block.source_locs.len() != block.instructions.len())
            || (!original_origins.is_empty() && original_origins.len() != block.instructions.len())
        {
            continue;
        }

        let mut facts = HashMap::<Value, UIntRange>::default();
        let mut replacements = Vec::<(usize, Vec<Instruction>)>::new();

        for (index, instruction) in block.instructions.iter().enumerate() {
            // Be fail-closed even for malformed non-SSA input: a redefinition
            // cannot inherit the prior definition's fact.
            for result in &instruction.results {
                facts.remove(result);
            }

            match rewrite_instruction(instruction, &value_types, &facts, &mut plan.stats) {
                Some(replacement) => {
                    for emitted_instruction in &replacement {
                        learn_facts(emitted_instruction, &value_types, &mut facts);
                    }
                    replacements.push((index, replacement));
                }
                None => learn_facts(instruction, &value_types, &mut facts),
            }
        }

        if replacements.is_empty() {
            continue;
        }

        plan.blocks.push(BlockRewritePlan {
            block_id,
            replacements,
        });
    }

    plan
}

fn apply_function_rewrite_plan(function: &mut Function, plan: FunctionRewritePlan) {
    for BlockRewritePlan {
        block_id,
        replacements,
    } in plan.blocks
    {
        // Mutation is intentionally delayed until a rewrite is known to exist,
        // so an unchanged block keeps its instruction and sidecar buffers and
        // never pays for deep instruction clones or rebuilt sidecars.
        let had_origin_sidecar = function.trust_ir_origins.contains_key(&block_id);
        let Some(block) = function.blocks.get_mut(&block_id) else {
            // A plan authorizes edits only to its analyzed block. If it is
            // absent, do not touch either instructions or orphaned sidecars.
            continue;
        };
        let original_instructions = std::mem::take(&mut block.instructions);
        let original_locs = std::mem::take(&mut block.source_locs);
        let original_origins = function
            .trust_ir_origins
            .remove(&block_id)
            .unwrap_or_default();
        let extra_instructions = replacements
            .iter()
            .map(|(_, replacement)| replacement.len().saturating_sub(1))
            .sum::<usize>();
        let new_len = original_instructions.len() + extra_instructions;
        let mut new_instructions = Vec::with_capacity(new_len);
        let mut new_locs = (!original_locs.is_empty()).then(|| Vec::with_capacity(new_len));
        let mut new_origins = (!original_origins.is_empty()).then(|| Vec::with_capacity(new_len));
        let mut replacements = replacements.into_iter().peekable();

        for (index, instruction) in original_instructions.into_iter().enumerate() {
            let source_loc = original_locs.get(index).copied().flatten();
            let trust_ir_origin = original_origins.get(index).copied().flatten();
            if let Some((_, replacement)) =
                replacements.next_if(|(replacement_index, _)| *replacement_index == index)
            {
                for emitted_instruction in replacement {
                    new_instructions.push(emitted_instruction);
                    // A one-to-many checked-op rewrite keeps the exact source
                    // site and trust-ir origin on every replacement.
                    if let Some(new_locs) = &mut new_locs {
                        new_locs.push(source_loc);
                    }
                    if let Some(new_origins) = &mut new_origins {
                        new_origins.push(trust_ir_origin);
                    }
                }
            } else {
                new_instructions.push(instruction);
                if let Some(new_locs) = &mut new_locs {
                    new_locs.push(source_loc);
                }
                if let Some(new_origins) = &mut new_origins {
                    new_origins.push(trust_ir_origin);
                }
            }
        }

        block.instructions = new_instructions;
        block.source_locs = new_locs.unwrap_or_default();
        if had_origin_sidecar {
            function
                .trust_ir_origins
                .insert(block_id, new_origins.unwrap_or_default());
        }
    }
}

fn instruction_may_be_simplified(instruction: &Instruction) -> bool {
    matches!(
        instruction.opcode,
        Opcode::CheckedUadd
            | Opcode::CheckedUmul
            | Opcode::Icmp {
                cond: IntCC::UnsignedLessThan
            }
            | Opcode::Select {
                cond: IntCC::NotEqual
            }
            | Opcode::Assert
            | Opcode::Brif { .. }
    )
}

/// Reconstruct the small slice of LIR's type relation needed by this pass.
///
/// `Function::value_types` is intentionally a sparse hint map, so treating a
/// missing entry as an unknown would make ordinary adapter-produced scalar LIR
/// invisible here.  Conversely, choosing one of two contradictory hints could
/// authorize a bad rewrite.  Build equality components from the exact opcode
/// contracts we consume, collect all explicit type evidence, and type a
/// component only when every piece of evidence agrees.
fn infer_value_types(function: &Function) -> HashMap<Value, Type> {
    let mut adjacency = HashMap::<Value, Vec<Value>>::default();
    let mut evidence = HashMap::<Value, Vec<Type>>::default();

    // Entry block parameters are the concrete value bindings for the function
    // signature.  Reject an incomplete binding for the whole function, and
    // treat both type declarations as evidence so a mismatch poisons every
    // connected value rather than authorizing a rewrite by guessing.
    let Some(entry_block) = function.blocks.get(&function.entry_block) else {
        return HashMap::default();
    };
    if entry_block.params.len() != function.signature.params.len() {
        return HashMap::default();
    }
    for ((value, _), ty) in entry_block
        .params
        .iter()
        .zip(function.signature.params.iter())
    {
        constrain_type(&mut adjacency, &mut evidence, *value, ty.clone());
    }

    for (value, ty) in &function.value_types {
        constrain_type(&mut adjacency, &mut evidence, *value, ty.clone());
    }
    for block in function.blocks.values() {
        for (value, ty) in &block.params {
            constrain_type(&mut adjacency, &mut evidence, *value, ty.clone());
        }
        for instruction in &block.instructions {
            match &instruction.opcode {
                Opcode::Iconst { ty, .. }
                    if instruction.args.is_empty() && instruction.results.len() == 1 =>
                {
                    constrain_type(
                        &mut adjacency,
                        &mut evidence,
                        instruction.results[0],
                        ty.clone(),
                    );
                }
                Opcode::Copy if instruction.args.len() == 1 && instruction.results.len() == 1 => {
                    constrain_equal(
                        &mut adjacency,
                        &[instruction.args[0], instruction.results[0]],
                    );
                }
                Opcode::Band if instruction.args.len() == 2 && instruction.results.len() == 1 => {
                    constrain_equal(
                        &mut adjacency,
                        &[
                            instruction.args[0],
                            instruction.args[1],
                            instruction.results[0],
                        ],
                    );
                }
                Opcode::Uextend { from_ty, to_ty }
                    if instruction.args.len() == 1 && instruction.results.len() == 1 =>
                {
                    constrain_type(
                        &mut adjacency,
                        &mut evidence,
                        instruction.args[0],
                        from_ty.clone(),
                    );
                    constrain_type(
                        &mut adjacency,
                        &mut evidence,
                        instruction.results[0],
                        to_ty.clone(),
                    );
                }
                Opcode::CheckedUadd | Opcode::CheckedUmul
                    if instruction.args.len() == 2 && instruction.results.len() == 2 =>
                {
                    constrain_equal(
                        &mut adjacency,
                        &[
                            instruction.args[0],
                            instruction.args[1],
                            instruction.results[0],
                        ],
                    );
                    constrain_type(
                        &mut adjacency,
                        &mut evidence,
                        instruction.results[1],
                        Type::B1,
                    );
                }
                Opcode::Icmp { .. }
                    if instruction.args.len() == 2 && instruction.results.len() == 1 =>
                {
                    constrain_equal(&mut adjacency, &[instruction.args[0], instruction.args[1]]);
                    constrain_type(
                        &mut adjacency,
                        &mut evidence,
                        instruction.results[0],
                        Type::B1,
                    );
                }
                Opcode::Select { .. }
                    if instruction.args.len() == 3 && instruction.results.len() == 1 =>
                {
                    constrain_type(&mut adjacency, &mut evidence, instruction.args[0], Type::B1);
                    constrain_equal(
                        &mut adjacency,
                        &[
                            instruction.args[1],
                            instruction.args[2],
                            instruction.results[0],
                        ],
                    );
                }
                Opcode::Assert if instruction.args.len() == 1 && instruction.results.is_empty() => {
                    constrain_type(&mut adjacency, &mut evidence, instruction.args[0], Type::B1);
                }
                Opcode::Brif { cond, .. }
                    if instruction.args.as_slice() == [*cond] && instruction.results.is_empty() =>
                {
                    constrain_type(&mut adjacency, &mut evidence, *cond, Type::B1);
                }
                _ => {}
            }
        }
    }

    let mut types = HashMap::default();
    let mut visited = HashSet::default();
    for start in adjacency.keys().copied().collect::<Vec<_>>() {
        if !visited.insert(start) {
            continue;
        }
        let mut stack = vec![start];
        let mut component = Vec::new();
        let mut component_type: Option<Type> = None;
        let mut conflict = false;
        while let Some(value) = stack.pop() {
            component.push(value);
            if let Some(value_evidence) = evidence.get(&value) {
                for ty in value_evidence {
                    match &component_type {
                        Some(known) if known != ty => conflict = true,
                        Some(_) => {}
                        None => component_type = Some(ty.clone()),
                    }
                }
            }
            if let Some(neighbors) = adjacency.get(&value) {
                for neighbor in neighbors {
                    if visited.insert(*neighbor) {
                        stack.push(*neighbor);
                    }
                }
            }
        }
        if !conflict && let Some(ty) = component_type {
            for value in component {
                types.insert(value, ty.clone());
            }
        }
    }
    types
}

fn constrain_type(
    adjacency: &mut HashMap<Value, Vec<Value>>,
    evidence: &mut HashMap<Value, Vec<Type>>,
    value: Value,
    ty: Type,
) {
    adjacency.entry(value).or_default();
    evidence.entry(value).or_default().push(ty);
}

fn constrain_equal(adjacency: &mut HashMap<Value, Vec<Value>>, values: &[Value]) {
    let Some((&first, rest)) = values.split_first() else {
        return;
    };
    adjacency.entry(first).or_default();
    for value in rest {
        adjacency.entry(first).or_default().push(*value);
        adjacency.entry(*value).or_default().push(first);
    }
}

fn rewrite_instruction(
    instruction: &Instruction,
    value_types: &HashMap<Value, Type>,
    facts: &HashMap<Value, UIntRange>,
    stats: &mut LirUnsignedRangeStats,
) -> Option<Vec<Instruction>> {
    match &instruction.opcode {
        Opcode::CheckedUadd => {
            checked_arithmetic_range(instruction, value_types, facts, false)?;
            stats.checked_adds_simplified += 1;
            Some(checked_replacement(instruction, Opcode::Iadd))
        }
        Opcode::CheckedUmul => {
            checked_arithmetic_range(instruction, value_types, facts, true)?;
            stats.checked_muls_simplified += 1;
            Some(checked_replacement(instruction, Opcode::Imul))
        }
        Opcode::Icmp {
            cond: IntCC::UnsignedLessThan,
        } => {
            let value = fold_unsigned_less_than(instruction, value_types, facts)?;
            stats.comparisons_folded += 1;
            Some(vec![Instruction {
                opcode: Opcode::Iconst {
                    ty: Type::B1,
                    imm: i64::from(value),
                },
                args: vec![],
                results: instruction.results.clone(),
            }])
        }
        Opcode::Select {
            cond: IntCC::NotEqual,
        } => {
            if instruction.args.len() != 3 || instruction.results.len() != 1 {
                return None;
            }
            let condition_value = instruction.args[0];
            if value_types.get(&condition_value) != Some(&Type::B1) {
                return None;
            }
            let condition_fact = facts.get(&condition_value)?;
            if condition_fact.width != 1 {
                return None;
            }
            let condition = condition_fact.exact_value()?;
            let selected = if condition != 0 {
                instruction.args[1]
            } else {
                instruction.args[2]
            };
            if value_types.get(&selected) != value_types.get(&instruction.results[0]) {
                return None;
            }
            stats.selects_folded += 1;
            Some(vec![Instruction {
                opcode: Opcode::Copy,
                args: vec![selected],
                results: instruction.results.clone(),
            }])
        }
        Opcode::Assert => {
            if instruction.args.len() != 1 || !instruction.results.is_empty() {
                return None;
            }
            let condition_value = instruction.args[0];
            if value_types.get(&condition_value) != Some(&Type::B1) {
                return None;
            }
            let condition = facts.get(&condition_value)?;
            if condition.width != 1 {
                return None;
            }
            if condition.lo == 0 {
                return None;
            }
            stats.asserts_removed += 1;
            Some(vec![])
        }
        Opcode::Brif {
            cond,
            then_dest,
            else_dest,
        } => {
            if instruction.args.as_slice() != [*cond] || !instruction.results.is_empty() {
                return None;
            }
            if value_types.get(cond) != Some(&Type::B1) {
                return None;
            }
            let condition_fact = facts.get(cond)?;
            if condition_fact.width != 1 {
                return None;
            }
            let condition = condition_fact.exact_value()?;
            let dest = if condition != 0 {
                *then_dest
            } else {
                *else_dest
            };
            stats.branches_folded += 1;
            Some(vec![Instruction {
                opcode: Opcode::Jump { dest },
                args: vec![],
                results: vec![],
            }])
        }
        _ => None,
    }
}

fn checked_replacement(instruction: &Instruction, arithmetic_opcode: Opcode) -> Vec<Instruction> {
    vec![
        Instruction {
            opcode: arithmetic_opcode,
            args: instruction.args.clone(),
            results: vec![instruction.results[0]],
        },
        Instruction {
            opcode: Opcode::Iconst {
                ty: Type::B1,
                imm: 0,
            },
            args: vec![],
            results: vec![instruction.results[1]],
        },
    ]
}

fn checked_arithmetic_range(
    instruction: &Instruction,
    value_types: &HashMap<Value, Type>,
    facts: &HashMap<Value, UIntRange>,
    multiply: bool,
) -> Option<UIntRange> {
    if instruction.args.len() != 2 || instruction.results.len() != 2 {
        return None;
    }
    let ty = value_types.get(&instruction.args[0])?;
    if value_types.get(&instruction.args[1]) != Some(ty)
        || value_types.get(&instruction.results[0]) != Some(ty)
        || value_types.get(&instruction.results[1]) != Some(&Type::B1)
    {
        return None;
    }
    let width = arithmetic_width(ty)?;
    let lhs = facts.get(&instruction.args[0])?;
    let rhs = facts.get(&instruction.args[1])?;
    if lhs.width != width || rhs.width != width {
        return None;
    }

    let (lo, hi) = if multiply {
        (lhs.lo.checked_mul(rhs.lo)?, lhs.hi.checked_mul(rhs.hi)?)
    } else {
        (lhs.lo.checked_add(rhs.lo)?, lhs.hi.checked_add(rhs.hi)?)
    };
    (hi <= unsigned_max(width)).then_some(UIntRange { lo, hi, width })
}

fn fold_unsigned_less_than(
    instruction: &Instruction,
    value_types: &HashMap<Value, Type>,
    facts: &HashMap<Value, UIntRange>,
) -> Option<bool> {
    if instruction.args.len() != 2
        || instruction.results.len() != 1
        || value_types.get(&instruction.results[0]) != Some(&Type::B1)
    {
        return None;
    }
    let lhs_ty = value_types.get(&instruction.args[0])?;
    if value_types.get(&instruction.args[1]) != Some(lhs_ty) {
        return None;
    }
    let width = integer_width(lhs_ty)?;
    let lhs = facts.get(&instruction.args[0])?;
    let rhs = facts.get(&instruction.args[1])?;
    if lhs.width != width || rhs.width != width {
        return None;
    }
    if lhs.hi < rhs.lo {
        Some(true)
    } else if lhs.lo >= rhs.hi {
        Some(false)
    } else {
        None
    }
}

fn learn_facts(
    instruction: &Instruction,
    value_types: &HashMap<Value, Type>,
    facts: &mut HashMap<Value, UIntRange>,
) {
    let fact = (|| -> Option<(Value, UIntRange)> {
        match &instruction.opcode {
            Opcode::Iconst { ty, imm }
                if instruction.args.is_empty()
                    && instruction.results.len() == 1
                    && value_types.get(&instruction.results[0]) == Some(ty) =>
            {
                let width = integer_width(ty)?;
                let value = immediate_as_unsigned(ty, *imm)?;
                Some((instruction.results[0], UIntRange::exact(value, width)))
            }
            Opcode::Copy if instruction.args.len() == 1 && instruction.results.len() == 1 => {
                let source = instruction.args[0];
                let result = instruction.results[0];
                if value_types.get(&source) != value_types.get(&result) {
                    None
                } else {
                    facts.get(&source).copied().map(|range| (result, range))
                }
            }
            Opcode::Band if instruction.args.len() == 2 && instruction.results.len() == 1 => {
                band_fact(instruction, value_types, facts)
            }
            Opcode::Uextend { from_ty, to_ty }
                if instruction.args.len() == 1 && instruction.results.len() == 1 =>
            {
                let source = instruction.args[0];
                let result = instruction.results[0];
                let from_width = integer_width(from_ty)?;
                let to_width = integer_width(to_ty)?;
                if from_width >= to_width
                    || value_types.get(&source) != Some(from_ty)
                    || value_types.get(&result) != Some(to_ty)
                {
                    None
                } else {
                    facts.get(&source).and_then(|range| {
                        (range.width == from_width).then_some((
                            result,
                            UIntRange {
                                lo: range.lo,
                                hi: range.hi,
                                width: to_width,
                            },
                        ))
                    })
                }
            }
            Opcode::Iadd if instruction.args.len() == 2 && instruction.results.len() == 1 => {
                plain_arithmetic_fact(instruction, value_types, facts, false)
            }
            Opcode::Imul if instruction.args.len() == 2 && instruction.results.len() == 1 => {
                plain_arithmetic_fact(instruction, value_types, facts, true)
            }
            _ => None,
        }
    })();

    if let Some((value, range)) = fact {
        facts.insert(value, range);
    }
}

fn band_fact(
    instruction: &Instruction,
    value_types: &HashMap<Value, Type>,
    facts: &HashMap<Value, UIntRange>,
) -> Option<(Value, UIntRange)> {
    let lhs_ty = value_types.get(&instruction.args[0])?;
    if value_types.get(&instruction.args[1]) != Some(lhs_ty)
        || value_types.get(&instruction.results[0]) != Some(lhs_ty)
    {
        return None;
    }
    let width = integer_width(lhs_ty)?;
    let lhs_hi = facts
        .get(&instruction.args[0])
        .filter(|range| range.width == width)
        .map(|range| range.hi);
    let rhs_hi = facts
        .get(&instruction.args[1])
        .filter(|range| range.width == width)
        .map(|range| range.hi);
    let hi = match (lhs_hi, rhs_hi) {
        (Some(lhs), Some(rhs)) => lhs.min(rhs),
        (Some(bound), None) | (None, Some(bound)) => bound,
        (None, None) => return None,
    };
    Some((instruction.results[0], UIntRange { lo: 0, hi, width }))
}

fn plain_arithmetic_fact(
    instruction: &Instruction,
    value_types: &HashMap<Value, Type>,
    facts: &HashMap<Value, UIntRange>,
    multiply: bool,
) -> Option<(Value, UIntRange)> {
    let ty = value_types.get(&instruction.args[0])?;
    if value_types.get(&instruction.args[1]) != Some(ty)
        || value_types.get(&instruction.results[0]) != Some(ty)
    {
        return None;
    }
    let width = arithmetic_width(ty)?;
    let lhs = facts.get(&instruction.args[0])?;
    let rhs = facts.get(&instruction.args[1])?;
    if lhs.width != width || rhs.width != width {
        return None;
    }
    let (lo, hi) = if multiply {
        (lhs.lo.checked_mul(rhs.lo)?, lhs.hi.checked_mul(rhs.hi)?)
    } else {
        (lhs.lo.checked_add(rhs.lo)?, lhs.hi.checked_add(rhs.hi)?)
    };
    (hi <= unsigned_max(width)).then_some((instruction.results[0], UIntRange { lo, hi, width }))
}

fn immediate_as_unsigned(ty: &Type, imm: i64) -> Option<u128> {
    let width = integer_width(ty)?;
    if width == 1 {
        return match imm {
            0 => Some(0),
            1 => Some(1),
            _ => None,
        };
    }
    Some((imm as u64 as u128) & unsigned_max(width))
}

fn integer_width(ty: &Type) -> Option<u32> {
    match ty {
        Type::B1 => Some(1),
        Type::I8 => Some(8),
        Type::I16 => Some(16),
        Type::I32 => Some(32),
        Type::I64 => Some(64),
        _ => None,
    }
}

fn arithmetic_width(ty: &Type) -> Option<u32> {
    match ty {
        Type::I8 => Some(8),
        Type::I16 => Some(16),
        Type::I32 => Some(32),
        Type::I64 => Some(64),
        _ => None,
    }
}

fn unsigned_max(width: u32) -> u128 {
    (1_u128 << width) - 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{SourceLoc, TrustIrInstId};
    use trust_cg_lower::function::{BasicBlock, Signature};

    fn inst(opcode: Opcode, args: &[u32], results: &[u32]) -> Instruction {
        Instruction {
            opcode,
            args: args.iter().copied().map(Value).collect(),
            results: results.iter().copied().map(Value).collect(),
        }
    }

    fn function(instructions: Vec<Instruction>, value_types: &[(u32, Type)]) -> Function {
        let mut function = Function::new("range_test", Signature::default());
        function.blocks.insert(
            Block(0),
            BasicBlock {
                instructions,
                ..BasicBlock::default()
            },
        );
        function.block_order.push(Block(0));
        for (value, ty) in value_types {
            function.value_types.insert(Value(*value), ty.clone());
        }
        function
    }

    fn opcodes(function: &Function) -> Vec<&Opcode> {
        function.blocks[&Block(0)]
            .instructions
            .iter()
            .map(|instruction| &instruction.opcode)
            .collect()
    }

    #[test]
    fn clone_on_change_borrows_when_there_is_no_candidate_opcode() {
        let function = function(
            vec![inst(
                Opcode::Iconst {
                    ty: Type::I32,
                    imm: 7,
                },
                &[],
                &[0],
            )],
            &[(0, Type::I32)],
        );

        match simplify_function_clone_on_change(&function) {
            Cow::Borrowed(borrowed) => assert!(std::ptr::eq(borrowed, &function)),
            Cow::Owned(_) => panic!("a function with no candidate opcode must not be cloned"),
        }
    }

    #[test]
    fn clone_on_change_borrows_when_candidate_cannot_be_proved() {
        let function = function(
            vec![inst(Opcode::CheckedUadd, &[0, 1], &[2, 3])],
            &[
                (0, Type::I32),
                (1, Type::I32),
                (2, Type::I32),
                (3, Type::B1),
            ],
        );

        match simplify_function_clone_on_change(&function) {
            Cow::Borrowed(borrowed) => assert!(std::ptr::eq(borrowed, &function)),
            Cow::Owned(_) => {
                panic!("an unbounded checked add is a candidate but not an authorized rewrite")
            }
        }
        assert!(matches!(
            function.blocks[&Block(0)].instructions[0].opcode,
            Opcode::CheckedUadd
        ));
    }

    #[test]
    fn clone_on_change_owns_actual_rewrite_and_matches_mutating_api() {
        let original = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I32,
                        imm: 31,
                    },
                    &[],
                    &[1],
                ),
                inst(Opcode::Band, &[0, 1], &[2]),
                inst(Opcode::CheckedUadd, &[2, 2], &[3, 4]),
            ],
            &[
                (0, Type::I32),
                (1, Type::I32),
                (2, Type::I32),
                (3, Type::I32),
                (4, Type::B1),
            ],
        );
        let mut expected = original.clone();
        let stats = simplify_function(&mut expected);
        assert_eq!(stats.checked_adds_simplified, 1);

        let Cow::Owned(owned) = simplify_function_clone_on_change(&original) else {
            panic!("a proven-safe checked add must produce an owned changed function");
        };

        assert_eq!(
            format!("{owned:#?}"),
            format!("{expected:#?}"),
            "the Cow helper must apply exactly the mutating API's rewrite plan"
        );
        assert!(matches!(
            original.blocks[&Block(0)].instructions[2].opcode,
            Opcode::CheckedUadd
        ));
        assert!(matches!(
            owned.blocks[&Block(0)].instructions[2].opcode,
            Opcode::Iadd
        ));
    }

    #[test]
    fn masked_checked_add_select_and_assert_simplify_with_exact_sidecars() {
        let instructions = vec![
            inst(
                Opcode::Iconst {
                    ty: Type::I32,
                    imm: 32_767,
                },
                &[],
                &[2],
            ),
            inst(Opcode::Band, &[0, 2], &[3]),
            inst(Opcode::Band, &[1, 2], &[4]),
            inst(Opcode::CheckedUadd, &[3, 4], &[5, 6]),
            inst(
                Opcode::Iconst {
                    ty: Type::B1,
                    imm: 0,
                },
                &[],
                &[7],
            ),
            inst(
                Opcode::Iconst {
                    ty: Type::B1,
                    imm: 1,
                },
                &[],
                &[8],
            ),
            inst(
                Opcode::Select {
                    cond: IntCC::NotEqual,
                },
                &[6, 7, 8],
                &[9],
            ),
            inst(Opcode::Assert, &[9], &[]),
        ];
        let mut function = function(
            instructions,
            &[
                (0, Type::I32),
                (1, Type::I32),
                (2, Type::I32),
                (3, Type::I32),
                (4, Type::I32),
                (5, Type::I32),
                (6, Type::B1),
                (7, Type::B1),
                (8, Type::B1),
                (9, Type::B1),
            ],
        );
        // Production adapter LIR keeps this map sparse.  The pass must recover
        // ordinary scalar types from block/opcode constraints, not test hints.
        function.value_types.clear();
        let original_locs: Vec<Option<SourceLoc>> = (0..8)
            .map(|index| {
                Some(SourceLoc {
                    file: 1,
                    line: 100 + index,
                    col: index,
                })
            })
            .collect();
        let original_origins: Vec<Option<TrustIrInstId>> =
            (10..18).map(|index| Some(TrustIrInstId(index))).collect();
        function.blocks.get_mut(&Block(0)).unwrap().source_locs = original_locs.clone();
        function
            .trust_ir_origins
            .insert(Block(0), original_origins.clone());

        let stats = simplify_function(&mut function);

        assert_eq!(stats.checked_adds_simplified, 1);
        assert_eq!(stats.selects_folded, 1);
        assert_eq!(stats.asserts_removed, 1);
        let block = &function.blocks[&Block(0)];
        assert!(
            !opcodes(&function)
                .iter()
                .any(|opcode| matches!(opcode, Opcode::CheckedUadd | Opcode::Assert))
        );
        assert!(matches!(block.instructions[3].opcode, Opcode::Iadd));
        assert_eq!(block.instructions[3].results, vec![Value(5)]);
        assert!(matches!(
            block.instructions[4].opcode,
            Opcode::Iconst {
                ty: Type::B1,
                imm: 0
            }
        ));
        assert_eq!(block.instructions[4].results, vec![Value(6)]);
        assert_eq!(block.instructions[7].opcode, Opcode::Copy);
        assert_eq!(block.instructions[7].args, vec![Value(8)]);

        assert_eq!(
            block.source_locs,
            vec![
                original_locs[0],
                original_locs[1],
                original_locs[2],
                original_locs[3],
                original_locs[3],
                original_locs[4],
                original_locs[5],
                original_locs[6],
            ]
        );
        assert_eq!(
            function.trust_ir_origins[&Block(0)],
            vec![
                original_origins[0],
                original_origins[1],
                original_origins[2],
                original_origins[3],
                original_origins[3],
                original_origins[4],
                original_origins[5],
                original_origins[6],
            ]
        );
        assert_eq!(block.instructions.len(), block.source_locs.len());
        assert_eq!(
            block.instructions.len(),
            function.trust_ir_origins[&Block(0)].len()
        );
    }

    #[test]
    fn masked_i64_checked_mul_simplifies() {
        let mut function = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I64,
                        imm: i64::from(u32::MAX),
                    },
                    &[],
                    &[2],
                ),
                inst(Opcode::Band, &[0, 2], &[3]),
                inst(Opcode::Band, &[1, 2], &[4]),
                inst(Opcode::CheckedUmul, &[3, 4], &[5, 6]),
            ],
            &[
                (0, Type::I64),
                (1, Type::I64),
                (2, Type::I64),
                (3, Type::I64),
                (4, Type::I64),
                (5, Type::I64),
                (6, Type::B1),
            ],
        );

        let stats = simplify_function(&mut function);

        assert_eq!(stats.checked_muls_simplified, 1);
        let block = &function.blocks[&Block(0)];
        assert!(matches!(block.instructions[3].opcode, Opcode::Imul));
        assert!(matches!(
            block.instructions[4].opcode,
            Opcode::Iconst {
                ty: Type::B1,
                imm: 0
            }
        ));
    }

    #[test]
    fn masked_shift_comparison_folds_and_removes_runtime_assert() {
        let mut function = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I64,
                        imm: 63,
                    },
                    &[],
                    &[1],
                ),
                inst(Opcode::Band, &[0, 1], &[2]),
                inst(
                    Opcode::Iconst {
                        ty: Type::I64,
                        imm: 64,
                    },
                    &[],
                    &[3],
                ),
                inst(
                    Opcode::Icmp {
                        cond: IntCC::UnsignedLessThan,
                    },
                    &[2, 3],
                    &[4],
                ),
                inst(Opcode::Assert, &[4], &[]),
            ],
            &[
                (0, Type::I64),
                (1, Type::I64),
                (2, Type::I64),
                (3, Type::I64),
                (4, Type::B1),
            ],
        );
        function.value_types.clear();

        let stats = simplify_function(&mut function);

        assert_eq!(stats.comparisons_folded, 1);
        assert_eq!(stats.asserts_removed, 1);
        let block = &function.blocks[&Block(0)];
        assert!(matches!(
            block.instructions[3].opcode,
            Opcode::Iconst {
                ty: Type::B1,
                imm: 1
            }
        ));
        assert!(
            !block
                .instructions
                .iter()
                .any(|instruction| matches!(instruction.opcode, Opcode::Assert))
        );
    }

    #[test]
    fn all_i8_masks_below_max_prove_the_next_bound() {
        for mask in 0_i64..=254 {
            let mut function = function(
                vec![
                    inst(
                        Opcode::Iconst {
                            ty: Type::I8,
                            imm: mask,
                        },
                        &[],
                        &[1],
                    ),
                    inst(Opcode::Band, &[0, 1], &[2]),
                    inst(
                        Opcode::Iconst {
                            ty: Type::I8,
                            imm: mask + 1,
                        },
                        &[],
                        &[3],
                    ),
                    inst(
                        Opcode::Icmp {
                            cond: IntCC::UnsignedLessThan,
                        },
                        &[2, 3],
                        &[4],
                    ),
                ],
                &[
                    (0, Type::I8),
                    (1, Type::I8),
                    (2, Type::I8),
                    (3, Type::I8),
                    (4, Type::B1),
                ],
            );

            let stats = simplify_function(&mut function);
            assert_eq!(stats.comparisons_folded, 1, "mask={mask}");
            assert!(matches!(
                function.blocks[&Block(0)].instructions[3].opcode,
                Opcode::Iconst {
                    ty: Type::B1,
                    imm: 1
                }
            ));
        }
    }

    #[test]
    fn potentially_overflowing_add_and_mul_stay_checked() {
        let mut function = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I32,
                        imm: -1,
                    },
                    &[],
                    &[2],
                ),
                inst(Opcode::Band, &[0, 2], &[3]),
                inst(Opcode::Band, &[1, 2], &[4]),
                inst(Opcode::CheckedUadd, &[3, 4], &[5, 6]),
                inst(
                    Opcode::Iconst {
                        ty: Type::I64,
                        imm: 1_i64 << 32,
                    },
                    &[],
                    &[12],
                ),
                inst(Opcode::Band, &[10, 12], &[13]),
                inst(Opcode::Band, &[11, 12], &[14]),
                inst(Opcode::CheckedUmul, &[13, 14], &[15, 16]),
            ],
            &[
                (0, Type::I32),
                (1, Type::I32),
                (2, Type::I32),
                (3, Type::I32),
                (4, Type::I32),
                (5, Type::I32),
                (6, Type::B1),
                (10, Type::I64),
                (11, Type::I64),
                (12, Type::I64),
                (13, Type::I64),
                (14, Type::I64),
                (15, Type::I64),
                (16, Type::B1),
            ],
        );

        let stats = simplify_function(&mut function);

        assert_eq!(stats, LirUnsignedRangeStats::default());
        assert!(
            opcodes(&function)
                .iter()
                .any(|opcode| matches!(opcode, Opcode::CheckedUadd))
        );
        assert!(
            opcodes(&function)
                .iter()
                .any(|opcode| matches!(opcode, Opcode::CheckedUmul))
        );
    }

    #[test]
    fn boundary_mask_and_signed_comparison_do_not_fold() {
        let mut function = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I64,
                        imm: 64,
                    },
                    &[],
                    &[1],
                ),
                inst(Opcode::Band, &[0, 1], &[2]),
                inst(
                    Opcode::Icmp {
                        cond: IntCC::UnsignedLessThan,
                    },
                    &[2, 1],
                    &[3],
                ),
                inst(
                    Opcode::Icmp {
                        cond: IntCC::SignedLessThan,
                    },
                    &[2, 1],
                    &[4],
                ),
                inst(Opcode::Assert, &[3], &[]),
            ],
            &[
                (0, Type::I64),
                (1, Type::I64),
                (2, Type::I64),
                (3, Type::B1),
                (4, Type::B1),
            ],
        );

        let stats = simplify_function(&mut function);

        assert_eq!(stats, LirUnsignedRangeStats::default());
        assert!(matches!(
            function.blocks[&Block(0)].instructions[2].opcode,
            Opcode::Icmp {
                cond: IntCC::UnsignedLessThan
            }
        ));
        assert!(matches!(
            function.blocks[&Block(0)].instructions[3].opcode,
            Opcode::Icmp {
                cond: IntCC::SignedLessThan
            }
        ));
        assert!(matches!(
            function.blocks[&Block(0)].instructions[4].opcode,
            Opcode::Assert
        ));
    }

    #[test]
    fn malformed_checked_op_and_proof_guard_are_untouched() {
        let mut function = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I64,
                        imm: 63,
                    },
                    &[],
                    &[1],
                ),
                inst(Opcode::Band, &[0, 1], &[2]),
                // Missing overflow result: reject the rewrite rather than panic.
                inst(Opcode::CheckedUadd, &[2, 2], &[3]),
                inst(
                    Opcode::GuardShiftRange {
                        bitwidth: 64,
                        obligation: Some(7),
                    },
                    &[2],
                    &[],
                ),
            ],
            &[
                (0, Type::I64),
                (1, Type::I64),
                (2, Type::I64),
                (3, Type::I64),
            ],
        );

        let stats = simplify_function(&mut function);

        assert_eq!(stats, LirUnsignedRangeStats::default());
        assert!(matches!(
            function.blocks[&Block(0)].instructions[2].opcode,
            Opcode::CheckedUadd
        ));
        assert!(matches!(
            function.blocks[&Block(0)].instructions[3].opcode,
            Opcode::GuardShiftRange {
                bitwidth: 64,
                obligation: Some(7)
            }
        ));
    }

    #[test]
    fn misaligned_nonempty_sidecars_refuse_the_whole_block() {
        let make_candidate = || {
            function(
                vec![
                    inst(
                        Opcode::Iconst {
                            ty: Type::I64,
                            imm: 31,
                        },
                        &[],
                        &[1],
                    ),
                    inst(Opcode::Band, &[0, 1], &[2]),
                    inst(Opcode::CheckedUadd, &[2, 2], &[3, 4]),
                ],
                &[
                    (0, Type::I64),
                    (1, Type::I64),
                    (2, Type::I64),
                    (3, Type::I64),
                    (4, Type::B1),
                ],
            )
        };

        let mut bad_locations = make_candidate();
        let short_locations = vec![Some(SourceLoc {
            file: 7,
            line: 8,
            col: 9,
        })];
        bad_locations.blocks.get_mut(&Block(0)).unwrap().source_locs = short_locations.clone();
        assert_eq!(
            simplify_function(&mut bad_locations),
            LirUnsignedRangeStats::default()
        );
        assert_eq!(bad_locations.blocks[&Block(0)].source_locs, short_locations);
        assert!(matches!(
            bad_locations.blocks[&Block(0)].instructions[2].opcode,
            Opcode::CheckedUadd
        ));

        let mut bad_origins = make_candidate();
        let short_origins = vec![Some(TrustIrInstId(99))];
        bad_origins
            .trust_ir_origins
            .insert(Block(0), short_origins.clone());
        assert_eq!(
            simplify_function(&mut bad_origins),
            LirUnsignedRangeStats::default()
        );
        assert_eq!(bad_origins.trust_ir_origins[&Block(0)], short_origins);
        assert!(matches!(
            bad_origins.blocks[&Block(0)].instructions[2].opcode,
            Opcode::CheckedUadd
        ));
    }

    #[test]
    fn malformed_type_metadata_never_authorizes_rewrites() {
        let mut function = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I64,
                        imm: 1,
                    },
                    &[],
                    &[0],
                ),
                inst(Opcode::Assert, &[0], &[]),
                inst(
                    Opcode::Select {
                        cond: IntCC::NotEqual,
                    },
                    &[0, 1, 2],
                    &[3],
                ),
                inst(
                    Opcode::Brif {
                        cond: Value(0),
                        then_dest: Block(1),
                        else_dest: Block(2),
                    },
                    &[0],
                    &[],
                ),
                inst(
                    Opcode::Iconst {
                        ty: Type::I32,
                        imm: 31,
                    },
                    &[],
                    &[10],
                ),
                inst(Opcode::Band, &[9, 10], &[11]),
                // The second result is not B1 according to the metadata.
                inst(Opcode::CheckedUadd, &[11, 11], &[12, 13]),
                inst(
                    Opcode::Iconst {
                        ty: Type::I32,
                        imm: 32,
                    },
                    &[],
                    &[14],
                ),
                // The comparison result is not B1 according to the metadata.
                inst(
                    Opcode::Icmp {
                        cond: IntCC::UnsignedLessThan,
                    },
                    &[11, 14],
                    &[15],
                ),
            ],
            &[
                (0, Type::I64),
                (1, Type::I64),
                (2, Type::I64),
                (3, Type::I64),
                (9, Type::I32),
                (10, Type::I32),
                (11, Type::I32),
                (12, Type::I32),
                (13, Type::I32),
                (14, Type::I32),
                (15, Type::I32),
            ],
        );

        let stats = simplify_function(&mut function);

        assert_eq!(stats, LirUnsignedRangeStats::default());
        let block = &function.blocks[&Block(0)];
        assert!(matches!(block.instructions[1].opcode, Opcode::Assert));
        assert!(matches!(
            block.instructions[2].opcode,
            Opcode::Select { .. }
        ));
        assert!(matches!(block.instructions[3].opcode, Opcode::Brif { .. }));
        assert!(matches!(block.instructions[6].opcode, Opcode::CheckedUadd));
        assert!(matches!(block.instructions[8].opcode, Opcode::Icmp { .. }));
    }

    #[test]
    fn conflicting_signature_parameter_type_fails_closed() {
        let mut function = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I32,
                        imm: 31,
                    },
                    &[],
                    &[1],
                ),
                inst(Opcode::Band, &[0, 1], &[2]),
                inst(Opcode::CheckedUadd, &[2, 2], &[3, 4]),
            ],
            &[
                (0, Type::I32),
                (1, Type::I32),
                (2, Type::I32),
                (3, Type::I32),
                (4, Type::B1),
            ],
        );
        function.signature.params = vec![Type::I64];
        function.blocks.get_mut(&Block(0)).unwrap().params = vec![(Value(0), Type::I32)];

        let stats = simplify_function(&mut function);

        assert_eq!(stats, LirUnsignedRangeStats::default());
        assert!(matches!(
            function.blocks[&Block(0)].instructions[2].opcode,
            Opcode::CheckedUadd
        ));
    }

    #[test]
    fn stale_block_plan_preserves_unrelated_instructions_and_orphaned_sidecars() {
        let mut function = function(vec![inst(Opcode::Trap, &[], &[])], &[]);
        function
            .trust_ir_origins
            .insert(Block(9), vec![Some(trust_cg_ir::TrustIrInstId(7))]);
        apply_function_rewrite_plan(
            &mut function,
            FunctionRewritePlan {
                stats: LirUnsignedRangeStats::default(),
                blocks: vec![BlockRewritePlan {
                    block_id: Block(9),
                    replacements: vec![(0, vec![inst(Opcode::Return, &[], &[])])],
                }],
            },
        );
        assert!(matches!(
            function.blocks[&Block(0)].instructions[0].opcode,
            Opcode::Trap
        ));
        assert_eq!(
            function.trust_ir_origins[&Block(9)],
            vec![Some(trust_cg_ir::TrustIrInstId(7))]
        );
    }

    #[test]
    fn exact_condition_folds_branch_and_module_keeps_proof_context() {
        let function = function(
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::B1,
                        imm: 1,
                    },
                    &[],
                    &[0],
                ),
                inst(
                    Opcode::Brif {
                        cond: Value(0),
                        then_dest: Block(1),
                        else_dest: Block(2),
                    },
                    &[0],
                    &[],
                ),
            ],
            &[(0, Type::B1)],
        );
        let mut proof_context = ProofContext::default();
        proof_context.noalias_param_indices = vec![2, 4];
        let mut empty_sidecar_function = function.clone();
        empty_sidecar_function
            .trust_ir_origins
            .insert(Block(0), vec![]);
        let mut module = vec![
            (function, proof_context),
            (empty_sidecar_function, ProofContext::default()),
        ];

        let stats = simplify_module(&mut module);

        assert_eq!(stats.branches_folded, 2);
        assert!(matches!(
            module[0].0.blocks[&Block(0)].instructions[1].opcode,
            Opcode::Jump { dest: Block(1) }
        ));
        assert!(module[0].0.blocks[&Block(0)].source_locs.is_empty());
        assert!(!module[0].0.trust_ir_origins.contains_key(&Block(0)));
        assert_eq!(module[1].0.trust_ir_origins[&Block(0)], vec![]);
        assert_eq!(module[0].1.noalias_param_indices, vec![2, 4]);
    }
}
