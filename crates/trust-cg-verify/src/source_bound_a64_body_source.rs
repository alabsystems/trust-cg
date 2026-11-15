// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The LIR side of the AArch64 whole-body theorem: admission (the source alone
//! decides applicability) and the gated encoding of the admitted DAG.
//!
//! Admission checks the complete function before anything is encoded: its
//! metadata, signature, block structure (an acyclic, fully reachable CFG of
//! `Jump`/`Brif`/`Return` terminators), the block-argument copies, SSA
//! definitions and dominance of every use, and the type of every value
//! (inferred, then checked against the `value_types` sidecar).
//!
//! The encoding is linear in the source: each block gets a reach flag, each
//! edge a taken flag, each join parameter the value its taken edge carries
//! (the simultaneous-substitution rule), and each instruction one named
//! definition. Semantics:
//!
//! * `Iconst`, `Copy`; wrapping `Iadd`, `Isub`, `Ineg`; bitwise `Band`, `Bor`,
//!   `Bxor`, `Bnot`, `BandNot`, `BorNot` on `I32`/`I64` and the Boolean
//!   connectives on `B1` (the 0/1 carrier, one bit here);
//! * `I8`/`I16` constants, copies, bitwise values and parameters, and typed
//!   `Uextend` to a wider admitted integer. Narrow ABI results may use the
//!   adapter's explicit I32 carrier; all 32 carrier bits are observed. A
//!   narrow result without that carrier stays outside this owner's domain;
//! * `Ishl`, `Ushr`, `Sshr` with trust-ir's shift-amount rule: the amount is
//!   the unsigned value of the second operand, and executing a shift whose
//!   amount is not below the width is undefined (`ShiftInRange`). The theorem
//!   is stated only for inputs on which no executed shift is out of range;
//! * `Icmp` (all ten conditions) of two integers, a `B1`;
//! * `Select { NotEqual | Equal }` of a `B1` or integer condition (nonzero, or
//!   zero) between two values of one admitted type, nested or not;
//! * `Brif` (taken when its condition is nonzero), `Jump`, `Return`.

use std::collections::{HashMap, HashSet};

use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode as L, Value};
use trust_cg_lower::{Function, Type};

use super::{A64BodyRefusal, A64BodyUnsupported, Defs, Ty, and_bit, bool_bv, is_one, unsupported};
use crate::smt::SmtExpr as E;

/// Most blocks an admitted source may have.
pub(super) const MAX_SOURCE_BLOCKS: usize = 16;
/// Most instructions an admitted source may have.
pub(super) const MAX_SOURCE_INSTRUCTIONS: usize = 256;

#[cfg(test)]
#[path = "source_bound_a64_body_source_resource_tests.rs"]
mod resource_tests;

/// The LIR opcodes this owner admits (terminators included), by name. The
/// census in the tests binds this list to [`admitted_opcode`].
pub const ADMITTED_LIR_OPCODES: &[&str] = &[
    "Iconst", "Uextend", "Copy", "Iadd", "Isub", "Ineg", "Band", "Bor", "Bxor", "Bnot", "BandNot",
    "BorNot", "Ishl", "Ushr", "Sshr", "Icmp", "Select", "Brif", "Jump", "Return",
];

/// Whether this owner admits `opcode` at all (its operand types are checked
/// separately). `Select` is admitted only with an `Equal`/`NotEqual` test.
pub(crate) fn admitted_opcode(opcode: &L) -> bool {
    matches!(
        opcode,
        L::Iconst { .. }
            | L::Uextend { .. }
            | L::Copy
            | L::Iadd
            | L::Isub
            | L::Ineg
            | L::Band
            | L::Bor
            | L::Bxor
            | L::Bnot
            | L::BandNot
            | L::BorNot
            | L::Ishl
            | L::Ushr
            | L::Sshr
            | L::Icmp { .. }
            | L::Jump { .. }
            | L::Brif { .. }
            | L::Return
    ) || matches!(
        opcode,
        L::Select {
            cond: IntCC::Equal | IntCC::NotEqual
        }
    )
}

/// The admitted source: structure and types, before any encoding.
pub(super) struct Admitted<'a> {
    pub(super) source: &'a Function,
    /// Parameter types, in signature order (`Value(i)` is parameter `i`).
    pub(super) params: Vec<Ty>,
    /// The returned type.
    pub(super) returns: Ty,
    /// Blocks in a topological order of the CFG, entry first.
    order: Vec<Block>,
    types: HashMap<Value, Ty>,
    /// The argument copies of each `Jump` edge, keyed by the jumping block:
    /// `(parameter value, argument value)` in parameter order.
    edge_arguments: HashMap<Block, Vec<(Value, Value)>>,
    /// Instruction positions of argument copies, which define no value of
    /// their own block.
    argument_copies: HashSet<(Block, usize)>,
}

fn shape(detail: impl Into<String>) -> A64BodyRefusal {
    unsupported(A64BodyUnsupported::SourceShape(detail.into()))
}

fn domain(detail: impl Into<String>) -> A64BodyRefusal {
    unsupported(A64BodyUnsupported::SourceDomain(detail.into()))
}

fn ty_of(ty: &Type) -> Option<Ty> {
    match ty {
        Type::I8 => Some(Ty::I8),
        Type::I16 => Some(Ty::I16),
        Type::I32 => Some(Ty::I32),
        Type::I64 => Some(Ty::I64),
        Type::B1 => Some(Ty::B1),
        _ => None,
    }
}

fn lir_type(ty: Ty) -> Type {
    match ty {
        Ty::I8 => Type::I8,
        Ty::I16 => Type::I16,
        Ty::I32 => Type::I32,
        Ty::I64 => Type::I64,
        Ty::B1 => Type::B1,
    }
}

fn successors(block: Block, last: &Instruction) -> Result<Vec<Block>, A64BodyRefusal> {
    match &last.opcode {
        L::Jump { dest } if last.args.is_empty() && last.results.is_empty() => Ok(vec![*dest]),
        L::Brif {
            cond,
            then_dest,
            else_dest,
        } if last.args == [*cond] && last.results.is_empty() => {
            if then_dest == else_dest {
                return Err(shape(format!(
                    "block {block:?} branches to {then_dest:?} on both edges"
                )));
            }
            Ok(vec![*then_dest, *else_dest])
        }
        L::Return => Ok(Vec::new()),
        L::Jump { .. } | L::Brif { .. } => Err(domain(format!(
            "block {block:?} ends in a malformed {}",
            opcode_name(&last.opcode)
        ))),
        other => Err(shape(format!(
            "block {block:?} ends in {}, which is not a Jump, Brif or Return",
            opcode_name(other)
        ))),
    }
}

/// The variant name of an opcode, without its fields.
pub(crate) fn opcode_name(opcode: &L) -> String {
    debug_variant_name(opcode)
}

/// Read only the derived enum's variant name. Stopping the formatter before
/// its fields avoids traversing an unsupported opcode's vectors or a type's
/// nested aggregate payload just to report why it was refused.
fn debug_variant_name(value: &impl std::fmt::Debug) -> String {
    struct Name(String);
    impl std::fmt::Write for Name {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            for character in text.chars() {
                if matches!(character, ' ' | '{' | '(') || self.0.len() >= 64 {
                    return Err(std::fmt::Error);
                }
                self.0.push(character);
            }
            Ok(())
        }
    }
    let mut name = Name(String::new());
    let _ = std::fmt::write(&mut name, format_args!("{value:?}"));
    name.0
}

/// Necessary shape conditions of the existing admission, checked before CFG,
/// parameter-owner or operand-type maps are allocated. Each admitted join
/// parameter needs an argument Copy witness, and every inferred non-input
/// value occupies an instruction result slot (including those Copies).
/// Thus these aggregate bounds remove no source the full admission accepts.
fn preflight_shape(source: &Function) -> Result<(), A64BodyRefusal> {
    let mut instructions = 0usize;
    let mut parameters = 0usize;
    for (id, block) in &source.blocks {
        instructions = instructions
            .checked_add(block.instructions.len())
            .ok_or_else(|| shape("instruction count overflow"))?;
        if *id != source.entry_block {
            parameters = parameters
                .checked_add(block.params.len())
                .ok_or_else(|| shape("block parameter count overflow"))?;
        }
    }
    if instructions > MAX_SOURCE_INSTRUCTIONS {
        return Err(shape(format!(
            "{instructions} instructions (the owner admits at most {MAX_SOURCE_INSTRUCTIONS})"
        )));
    }
    if parameters > instructions {
        return Err(shape(format!(
            "{parameters} non-entry parameters exceed {instructions} possible argument Copy witnesses"
        )));
    }
    let value_bound = source.signature.params.len() + instructions;
    if source.value_types.len() > value_bound {
        return Err(domain(format!(
            "{} type hints exceed {value_bound} possible inferred values",
            source.value_types.len()
        )));
    }
    let mut copies = 0usize;
    let mut results = 0usize;
    for (id, block) in &source.blocks {
        for (index, inst) in block.instructions.iter().enumerate() {
            let (args, result_count) = match &inst.opcode {
                L::Iconst { .. } => (0, 1),
                L::Copy | L::Ineg | L::Bnot | L::Uextend { .. } => (1, 1),
                L::Iadd
                | L::Isub
                | L::Band
                | L::Bor
                | L::Bxor
                | L::BandNot
                | L::BorNot
                | L::Ishl
                | L::Ushr
                | L::Sshr
                | L::Icmp { .. } => (2, 1),
                L::Select {
                    cond: IntCC::Equal | IntCC::NotEqual,
                } => (3, 1),
                L::Brif { .. } | L::Return => (1, 0),
                L::Jump { .. } => (0, 0),
                other => {
                    return Err(domain(format!(
                        "block {id:?} instruction {index}: {} is outside the body owner",
                        opcode_name(other)
                    )));
                }
            };
            if inst.args.len() != args || inst.results.len() != result_count {
                return Err(domain(format!(
                    "block {id:?} instruction {index}: {} takes {args} arguments and \
                     {result_count} results, got {} arguments and {} results",
                    opcode_name(&inst.opcode),
                    inst.args.len(),
                    inst.results.len()
                )));
            }
            copies += usize::from(matches!(inst.opcode, L::Copy));
            results += result_count;
        }
    }
    if parameters > copies {
        return Err(shape(format!(
            "{parameters} non-entry parameters exceed {copies} argument Copy witnesses"
        )));
    }
    let value_bound = source.signature.params.len() + results;
    if source.value_types.len() > value_bound {
        return Err(domain(format!(
            "{} type hints exceed {value_bound} possible inferred values",
            source.value_types.len()
        )));
    }
    Ok(())
}

fn is_terminator(opcode: &L) -> bool {
    matches!(
        opcode,
        L::Jump { .. } | L::Brif { .. } | L::Return | L::Trap | L::Switch { .. } | L::Invoke { .. }
    )
}

/// Admit `source`, or say why not. Reads only the LIR function.
pub(super) fn admit(source: &Function) -> Result<Admitted<'_>, A64BodyRefusal> {
    if !source.stack_slots.is_empty()
        || !source.eh_info.is_empty()
        || source.stack_protector != trust_cg_ir::function::StackProtectorMode::None
        || !source.param_pointee_types.is_empty()
        || source.abi_sret_param.is_some()
        || !source.sret_arg_callees.is_empty()
        || !source.sret_arg_indirect_callees.is_empty()
        || source.stack_limit.is_some()
    {
        return Err(domain(
            "the body owner needs a function without stack slots, EH, stack protection, \
             stack-limit checks or aggregate ABI metadata",
        ));
    }
    let signature = &source.signature;
    if signature.params.len() > 8 {
        return Err(domain("more than eight register parameters"));
    }
    let params = signature
        .params
        .iter()
        .map(|ty| {
            ty_of(ty).ok_or_else(|| domain(format!("parameter type {}", debug_variant_name(ty))))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let returns = match signature.returns.as_slice() {
        [ty] => {
            ty_of(ty).ok_or_else(|| domain(format!("return type {}", debug_variant_name(ty))))?
        }
        [] => return Err(unsupported(A64BodyUnsupported::NoObservable)),
        _ => return Err(domain("more than one result")),
    };
    if source.blocks.is_empty() || source.blocks.len() > MAX_SOURCE_BLOCKS {
        return Err(shape(format!(
            "{} blocks (the owner admits 1 to {MAX_SOURCE_BLOCKS})",
            source.blocks.len()
        )));
    }
    if !source.block_order.is_empty()
        && (source.block_order.len() != source.blocks.len()
            || source.block_order.iter().collect::<HashSet<_>>().len() != source.blocks.len()
            || source
                .block_order
                .iter()
                .any(|id| !source.blocks.contains_key(id)))
    {
        return Err(shape(
            "the block order does not name every block exactly once",
        ));
    }
    let entry = source
        .blocks
        .get(&source.entry_block)
        .ok_or_else(|| shape("the entry block has no body"))?;
    // Entry parameters: empty (the `Value(0..n)` convention) or exactly the
    // signature's values.
    if !entry.params.is_empty()
        && (entry.params.len() != params.len()
            || entry
                .params
                .iter()
                .enumerate()
                .any(|(i, (value, ty))| value.0 as usize != i || ty_of(ty) != Some(params[i])))
    {
        return Err(domain(
            "entry parameters disagree with the Value(0..n) signature convention",
        ));
    }
    preflight_shape(source)?;
    // Successors from each block's one terminator.
    let mut succs: HashMap<Block, Vec<Block>> = HashMap::new();
    for (id, block) in &source.blocks {
        let Some((last, body)) = block.instructions.split_last() else {
            return Err(shape(format!("block {id:?} is empty")));
        };
        if body.iter().any(|inst| is_terminator(&inst.opcode)) {
            return Err(shape(format!(
                "block {id:?} transfers control before its last instruction"
            )));
        }
        let targets = successors(*id, last)?;
        if let Some(missing) = targets.iter().find(|t| !source.blocks.contains_key(t)) {
            return Err(shape(format!(
                "block {id:?} branches to {missing:?}, which has no body"
            )));
        }
        succs.insert(*id, targets);
    }
    // Acyclic and reachable: depth-first colouring from the entry. The
    // reverse postorder is a topological order.
    #[derive(Clone, Copy, PartialEq)]
    enum Colour {
        Open,
        Done,
    }
    let mut colour: HashMap<Block, Colour> = HashMap::new();
    let mut postorder = Vec::new();
    let mut stack: Vec<(Block, usize)> = vec![(source.entry_block, 0)];
    colour.insert(source.entry_block, Colour::Open);
    while let Some((block, next)) = stack.pop() {
        let Some(target) = succs[&block].get(next).copied() else {
            colour.insert(block, Colour::Done);
            postorder.push(block);
            continue;
        };
        stack.push((block, next + 1));
        match colour.get(&target) {
            Some(Colour::Open) => {
                return Err(shape(format!(
                    "a loop (block {block:?} branches back to block {target:?}); loops stay \
                     outside the body owner"
                )));
            }
            Some(Colour::Done) => {}
            None => {
                colour.insert(target, Colour::Open);
                stack.push((target, 0));
            }
        }
    }
    if postorder.len() != source.blocks.len() {
        // The x86-64 lane no longer refuses here: a block the walk does not
        // reach lies on no entry-to-end path, so a path-by-path theorem
        // neither constrains it nor needs it, and `x86_source_bound_body`
        // excludes it (`SourceCfg::dead`) while its two machine-side owners
        // account for whatever lowers it. The same widening applies here
        // verbatim, but this lane has no host to measure it on, and an
        // unmeasured verifier widening is not worth shipping: a64 keeps the
        // refusal until it can be exercised. 2026-10-14.
        return Err(shape("a block is unreachable from the entry block"));
    }
    let order: Vec<Block> = postorder.into_iter().rev().collect();
    let mut preds: HashMap<Block, Vec<Block>> = order.iter().map(|b| (*b, Vec::new())).collect();
    for block in &order {
        for target in &succs[block] {
            preds.get_mut(target).expect("reachable").push(*block);
        }
    }
    if !preds[&source.entry_block].is_empty() {
        return Err(shape("the entry block has a predecessor"));
    }
    // Block parameters and their argument copies.
    let mut param_owner: HashMap<Value, Block> = HashMap::new();
    for (id, block) in &source.blocks {
        if *id == source.entry_block {
            continue;
        }
        for (value, ty) in &block.params {
            if ty_of(ty).is_none() {
                return Err(domain(format!(
                    "block {id:?} parameter {value:?} has type {}",
                    debug_variant_name(ty)
                )));
            }
            if param_owner.insert(*value, *id).is_some() {
                return Err(domain(format!("{value:?} is a parameter of two blocks")));
            }
        }
    }
    let mut edge_arguments: HashMap<Block, Vec<(Value, Value)>> = HashMap::new();
    let mut argument_copies = HashSet::new();
    for block_id in &order {
        let block = &source.blocks[block_id];
        let last = block.instructions.last().expect("non-empty");
        let jump_target = match last.opcode {
            L::Jump { dest } => Some(dest),
            _ => None,
        };
        let mut arguments: HashMap<Value, Value> = HashMap::new();
        for (index, inst) in block.instructions.iter().enumerate() {
            let defines_parameter = inst
                .results
                .iter()
                .find_map(|result| param_owner.get(result).map(|owner| (*result, *owner)));
            let Some((parameter, owner)) = defines_parameter else {
                continue;
            };
            if inst.opcode != L::Copy || inst.args.len() != 1 || inst.results.len() != 1 {
                return Err(domain(format!(
                    "block {block_id:?} instruction {index} defines block parameter \
                     {parameter:?} other than by an argument copy"
                )));
            }
            if jump_target != Some(owner) {
                return Err(shape(format!(
                    "block {block_id:?} copies an argument for block {owner:?}, which it does \
                     not jump to"
                )));
            }
            if param_owner.get(&inst.args[0]) == Some(&owner) {
                return Err(domain(format!(
                    "block {block_id:?} passes a parameter of block {owner:?} back to it"
                )));
            }
            if arguments.insert(parameter, inst.args[0]).is_some() {
                return Err(domain(format!(
                    "block {block_id:?} copies argument {parameter:?} twice"
                )));
            }
            argument_copies.insert((*block_id, index));
        }
        if let Some(target) = jump_target {
            let target_params = &source.blocks[&target].params;
            if target != source.entry_block {
                let ordered = target_params
                    .iter()
                    .map(|(value, _)| {
                        arguments
                            .get(value)
                            .map(|argument| (*value, *argument))
                            .ok_or_else(|| {
                                domain(format!(
                                    "block {block_id:?} jumps to {target:?} without an argument \
                                     for {value:?}"
                                ))
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                edge_arguments.insert(*block_id, ordered);
            }
        }
    }
    for (block_id, block) in &source.blocks {
        if *block_id == source.entry_block || block.params.is_empty() {
            continue;
        }
        for pred in &preds[block_id] {
            if !matches!(
                source.blocks[pred].instructions.last().map(|i| &i.opcode),
                Some(L::Jump { .. })
            ) {
                return Err(shape(format!(
                    "block {block_id:?} has parameters but is reached by a conditional branch \
                     from {pred:?}"
                )));
            }
        }
    }
    // Dominators of the DAG, in topological order.
    let mut dominators: HashMap<Block, HashSet<Block>> = HashMap::new();
    for block in &order {
        let mut set: Option<HashSet<Block>> = None;
        for pred in &preds[block] {
            let pred_set = &dominators[pred];
            set = Some(match set {
                None => pred_set.clone(),
                Some(current) => current.intersection(pred_set).copied().collect(),
            });
        }
        let mut set = set.unwrap_or_default();
        set.insert(*block);
        dominators.insert(*block, set);
    }
    // Types, single definitions and dominance of every use.
    let mut types: HashMap<Value, Ty> = HashMap::new();
    let mut defined_in: HashMap<Value, Block> = HashMap::new();
    for (i, ty) in params.iter().enumerate() {
        types.insert(Value(i as u32), *ty);
        defined_in.insert(Value(i as u32), source.entry_block);
    }
    for block_id in &order {
        let block = &source.blocks[block_id];
        if *block_id != source.entry_block {
            for (value, ty) in &block.params {
                let ty = ty_of(ty).expect("checked above");
                if types.insert(*value, ty).is_some() {
                    return Err(domain(format!("{value:?} is defined twice")));
                }
                defined_in.insert(*value, *block_id);
            }
        }
        for (index, inst) in block.instructions.iter().enumerate() {
            if !admitted_opcode(&inst.opcode) {
                return Err(domain(format!(
                    "block {block_id:?} instruction {index}: {} is outside the body owner",
                    opcode_name(&inst.opcode)
                )));
            }
            let mut operand_types = Vec::with_capacity(inst.args.len());
            for arg in &inst.args {
                let Some(owner) = defined_in.get(arg) else {
                    return Err(domain(format!(
                        "block {block_id:?} instruction {index} reads {arg:?} before any \
                         definition reaches it"
                    )));
                };
                if !dominators[block_id].contains(owner) {
                    return Err(domain(format!(
                        "block {block_id:?} instruction {index} reads {arg:?}, whose \
                         definition in {owner:?} does not dominate it"
                    )));
                }
                operand_types.push(types[arg]);
            }
            if argument_copies.contains(&(*block_id, index)) {
                let parameter = inst.results[0];
                if types.get(&parameter) == Some(&operand_types[0]) {
                    continue;
                }
                // The parameter's own type is assigned at its block; check it
                // against the block's declaration here.
                let declared = param_owner
                    .get(&parameter)
                    .and_then(|owner| {
                        source.blocks[owner]
                            .params
                            .iter()
                            .find(|(value, _)| *value == parameter)
                    })
                    .and_then(|(_, ty)| ty_of(ty));
                if declared != Some(operand_types[0]) {
                    return Err(domain(format!(
                        "block {block_id:?} instruction {index} passes a {:?} for a {:?} \
                         parameter",
                        operand_types[0], declared
                    )));
                }
                continue;
            }
            if matches!(inst.opcode, L::Return)
                && matches!(returns, Ty::I8 | Ty::I16)
                && !unsigned_return_carrier(source, inst.args[0], returns)
            {
                return Err(domain(
                    "a narrow result needs an explicit matching Uextend-to-I32 carrier",
                ));
            }
            let result = infer(&inst.opcode, &operand_types, &inst.args, returns)
                .map_err(|why| domain(format!("block {block_id:?} instruction {index}: {why}")))?;
            match (result, inst.results.as_slice()) {
                (None, []) => {}
                (Some(ty), [value]) => {
                    if types.insert(*value, ty).is_some() {
                        return Err(domain(format!(
                            "block {block_id:?} instruction {index} redefines {value:?}"
                        )));
                    }
                    defined_in.insert(*value, *block_id);
                }
                _ => {
                    return Err(domain(format!(
                        "block {block_id:?} instruction {index} has the wrong number of results"
                    )));
                }
            }
        }
    }
    for (value, hint) in &source.value_types {
        if types.get(value).map(|ty| lir_type(*ty)).as_ref() != Some(hint) {
            return Err(domain(format!("inconsistent type hint for {value:?}")));
        }
    }
    Ok(Admitted {
        source,
        params,
        returns,
        order,
        types,
        edge_arguments,
        argument_copies,
    })
}

/// A signless narrow signature cannot supply a signedness premise. Require
/// the actual source's matching zero-extension, optionally through SSA copies.
/// Block parameters are excluded: a single predecessor's argument copy is
/// not evidence for every incoming carrier. Shapes and total size were checked
/// before this walk; repeated values still refuse rather than loop.
fn unsigned_return_carrier(source: &Function, mut value: Value, returns: Ty) -> bool {
    let mut seen = HashSet::new();
    while seen.insert(value) {
        if source
            .blocks
            .values()
            .any(|block| block.params.iter().any(|(v, _)| *v == value))
        {
            return false;
        }
        let Some(inst) = source
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .find(|inst| inst.results.as_slice() == [value])
        else {
            return false;
        };
        match &inst.opcode {
            L::Uextend { from_ty, to_ty } => {
                return ty_of(from_ty) == Some(returns) && *to_ty == Type::I32;
            }
            L::Copy => value = inst.args[0],
            _ => return false,
        }
    }
    false
}

/// The result type of one admitted instruction, from its operand types.
fn infer(opcode: &L, operands: &[Ty], args: &[Value], returns: Ty) -> Result<Option<Ty>, String> {
    let integer = |ty: Ty| matches!(ty, Ty::I32 | Ty::I64);
    match (opcode, operands) {
        (L::Iconst { ty, imm }, []) => match ty_of(ty) {
            Some(Ty::B1) if !matches!(*imm, 0 | 1) => Err("a noncanonical Boolean literal".into()),
            Some(ty) => Ok(Some(ty)),
            None => Err(format!("constant of type {}", debug_variant_name(ty))),
        },
        (L::Uextend { from_ty, to_ty }, [a])
            if ty_of(from_ty) == Some(*a)
                && *a != Ty::B1
                && ty_of(to_ty).is_some_and(|to| to != Ty::B1 && to.width() > a.width()) =>
        {
            Ok(ty_of(to_ty))
        }
        (L::Copy, [a]) => Ok(Some(*a)),
        (L::Iadd | L::Isub | L::Ishl | L::Ushr | L::Sshr, [a, b]) if a == b && integer(*a) => {
            Ok(Some(*a))
        }
        (L::Ineg, [a]) if integer(*a) => Ok(Some(*a)),
        (L::Band | L::Bor | L::Bxor | L::BandNot | L::BorNot, [a, b]) if a == b => Ok(Some(*a)),
        (L::Bnot, [a]) => Ok(Some(*a)),
        (L::Icmp { .. }, [a, b]) if a == b && integer(*a) => Ok(Some(Ty::B1)),
        (L::Select { .. }, [_, t, e]) if t == e => Ok(Some(*t)),
        (L::Brif { .. }, [_]) => Ok(None),
        (L::Jump { .. }, []) => Ok(None),
        (L::Return, [ty])
            if (matches!(returns, Ty::I8 | Ty::I16) && *ty == Ty::I32)
                || (!matches!(returns, Ty::I8 | Ty::I16) && *ty == returns) =>
        {
            Ok(None)
        }
        (L::Return, _) => Err(format!(
            "returns {operands:?} where the signature returns {returns:?} ({args:?})"
        )),
        _ => Err(format!(
            "{} with operand types {operands:?} is outside the body owner",
            opcode_name(opcode)
        )),
    }
}

/// The source side of the theorem: the returned value, the definedness flag
/// (one bit: no executed shift had an out-of-range amount) and the same
/// condition as a Boolean domain premise (`None` when it always holds).
pub(super) struct SourceTheorem {
    pub(super) result: E,
    pub(super) defined: E,
    pub(super) domain: Option<E>,
}

/// `cond != 0` of a `B1` or integer condition value.
fn nonzero(term: &E, ty: Ty) -> E {
    match ty {
        Ty::B1 => is_one(term.clone()),
        _ => term.clone().eq_expr(E::bv_const(0, ty.width())).not_expr(),
    }
}

fn all_ones(width: u32) -> E {
    E::bv_const(crate::smt::mask(u64::MAX, width), width)
}

impl Admitted<'_> {
    /// Encode the source over the parameter inputs (`entry` gives the entry
    /// register input of each parameter, 64 bits).
    pub(super) fn encode(&self, defs: &mut Defs, entry: &[E]) -> SourceTheorem {
        let source = self.source;
        let mut env: HashMap<Value, E> = HashMap::new();
        for (i, ty) in self.params.iter().enumerate() {
            let input = entry[i].clone();
            // The 64-bit entry register carries the parameter in its low bits;
            // a `B1` is bit 0 (AAPCS64: an 8-bit 0/1 whose bits 1..7 are zero).
            let term = match ty {
                Ty::I64 => input,
                Ty::I8 => input.extract(7, 0),
                Ty::I16 => input.extract(15, 0),
                Ty::I32 => input.extract(31, 0),
                Ty::B1 => input.extract(0, 0),
            };
            env.insert(Value(i as u32), defs.source(term));
        }
        let mut reach: HashMap<Block, E> = HashMap::new();
        // Taken flag and argument terms of every edge into a block.
        let mut incoming: HashMap<Block, Vec<(E, Vec<E>)>> = HashMap::new();
        let mut returns: Vec<(E, E)> = Vec::new();
        let mut defined_terms: Vec<E> = Vec::new();
        let mut domain_terms: Vec<E> = Vec::new();
        for block_id in &self.order {
            let block = &source.blocks[block_id];
            let reached = if *block_id == source.entry_block {
                E::bv_const(1, 1)
            } else {
                let edges = incoming.get(block_id).map(Vec::as_slice).unwrap_or(&[]);
                let mut flag = edges[0].0.clone();
                for (taken, _) in &edges[1..] {
                    flag = flag.bvor(taken.clone());
                }
                if edges.len() > 1 {
                    flag = defs.source(flag);
                }
                // Simultaneous substitution: every parameter takes the
                // argument its (one) taken edge carries.
                for (position, (value, _)) in block.params.iter().enumerate() {
                    let mut term = edges[edges.len() - 1].1[position].clone();
                    for (taken, arguments) in edges[..edges.len() - 1].iter().rev() {
                        term = E::ite(is_one(taken.clone()), arguments[position].clone(), term);
                    }
                    let term = if edges.len() > 1 {
                        defs.source(term)
                    } else {
                        term
                    };
                    env.insert(*value, term);
                }
                flag
            };
            reach.insert(*block_id, reached.clone());
            for (index, inst) in block.instructions.iter().enumerate() {
                if self.argument_copies.contains(&(*block_id, index)) {
                    continue;
                }
                let operand = |position: usize| env[&inst.args[position]].clone();
                let operand_ty = |position: usize| self.types[&inst.args[position]];
                let value = match &inst.opcode {
                    L::Iconst { ty, imm } => {
                        let width = ty_of(ty).expect("admitted").width();
                        Some(E::bv_const(*imm as u64, width))
                    }
                    L::Uextend { to_ty, .. } => Some(defs.source(operand(0).zero_ext(
                        ty_of(to_ty).expect("admitted").width() - operand_ty(0).width(),
                    ))),
                    L::Copy => Some(operand(0)),
                    L::Iadd => Some(defs.source(operand(0).bvadd(operand(1)))),
                    L::Isub => Some(defs.source(operand(0).bvsub(operand(1)))),
                    L::Ineg => Some(defs.source(operand(0).bvneg())),
                    L::Band => Some(defs.source(operand(0).bvand(operand(1)))),
                    L::Bor => Some(defs.source(operand(0).bvor(operand(1)))),
                    L::Bxor => Some(defs.source(operand(0).bvxor(operand(1)))),
                    L::Bnot => {
                        let width = operand_ty(0).width();
                        Some(defs.source(operand(0).bvxor(all_ones(width))))
                    }
                    L::BandNot => {
                        let width = operand_ty(1).width();
                        Some(defs.source(operand(0).bvand(operand(1).bvxor(all_ones(width)))))
                    }
                    L::BorNot => {
                        let width = operand_ty(1).width();
                        Some(defs.source(operand(0).bvor(operand(1).bvxor(all_ones(width)))))
                    }
                    L::Ishl | L::Ushr | L::Sshr => {
                        let width = operand_ty(0).width();
                        let amount = operand(1);
                        // ShiftInRange: executing this shift is defined only
                        // when the unsigned amount is below the width.
                        // An amount that is provably in range (a constant
                        // below the width, or masked by one: Rust's
                        // `x << (y & (w - 1))`) needs no definedness condition.
                        if !defs.provably_below(&amount, u64::from(width)) {
                            let in_range =
                                amount.clone().bvult(E::bv_const(u64::from(width), width));
                            if reached == E::bv_const(1, 1) {
                                defined_terms.push(bool_bv(in_range.clone()));
                                domain_terms.push(in_range);
                            } else {
                                defined_terms.push(
                                    reached
                                        .clone()
                                        .bvxor(E::bv_const(1, 1))
                                        .bvor(bool_bv(in_range.clone())),
                                );
                                domain_terms
                                    .push(is_one(reached.clone()).not_expr().or_expr(in_range));
                            }
                        }
                        let shifted = match inst.opcode {
                            L::Ishl => operand(0).bvshl(amount),
                            L::Ushr => operand(0).bvlshr(amount),
                            _ => operand(0).bvashr(amount),
                        };
                        Some(defs.source(shifted))
                    }
                    L::Icmp { cond } => {
                        let (a, b) = (operand(0), operand(1));
                        let holds = match cond {
                            IntCC::Equal => a.eq_expr(b),
                            IntCC::NotEqual => a.eq_expr(b).not_expr(),
                            IntCC::SignedLessThan => a.bvslt(b),
                            IntCC::SignedGreaterThanOrEqual => a.bvslt(b).not_expr(),
                            IntCC::SignedGreaterThan => b.bvslt(a),
                            IntCC::SignedLessThanOrEqual => b.bvslt(a).not_expr(),
                            IntCC::UnsignedLessThan => a.bvult(b),
                            IntCC::UnsignedGreaterThanOrEqual => a.bvult(b).not_expr(),
                            IntCC::UnsignedGreaterThan => b.bvult(a),
                            IntCC::UnsignedLessThanOrEqual => b.bvult(a).not_expr(),
                        };
                        Some(defs.source(bool_bv(holds)))
                    }
                    L::Select { cond } => {
                        let test = nonzero(&operand(0), operand_ty(0));
                        let test = if *cond == IntCC::Equal {
                            test.not_expr()
                        } else {
                            test
                        };
                        Some(defs.source(E::ite(test, operand(1), operand(2))))
                    }
                    L::Brif {
                        then_dest,
                        else_dest,
                        ..
                    } => {
                        let test = nonzero(&operand(0), operand_ty(0));
                        let then_taken =
                            defs.source(and_bit(reached.clone(), bool_bv(test.clone())));
                        let else_taken =
                            defs.source(and_bit(reached.clone(), bool_bv(test.not_expr())));
                        incoming
                            .entry(*then_dest)
                            .or_default()
                            .push((then_taken, Vec::new()));
                        incoming
                            .entry(*else_dest)
                            .or_default()
                            .push((else_taken, Vec::new()));
                        None
                    }
                    L::Jump { dest } => {
                        let arguments = self
                            .edge_arguments
                            .get(block_id)
                            .map(|pairs| pairs.iter().map(|(_, arg)| env[arg].clone()).collect())
                            .unwrap_or_default();
                        incoming
                            .entry(*dest)
                            .or_default()
                            .push((reached.clone(), arguments));
                        None
                    }
                    L::Return => {
                        // Narrow signatures require the adapter's explicit I32
                        // carrier. The ABI caller can observe all of W0.
                        returns.push((reached.clone(), operand(0)));
                        None
                    }
                    other => unreachable!("{other:?} was admitted"),
                };
                if let (Some(value), [result]) = (value, inst.results.as_slice()) {
                    env.insert(*result, value);
                }
            }
        }
        let (_, last) = returns.last().cloned().expect("an admitted DAG returns");
        let mut result = last;
        for (reached, value) in returns[..returns.len() - 1].iter().rev() {
            result = E::ite(is_one(reached.clone()), value.clone(), result);
        }
        let result = defs.source(result);
        let defined = match defined_terms.split_first() {
            None => E::bv_const(1, 1),
            Some((first, rest)) => {
                let mut all = first.clone();
                for term in rest {
                    all = all.bvand(term.clone());
                }
                defs.source(all)
            }
        };
        let domain = domain_terms
            .into_iter()
            .reduce(|all, term| all.and_expr(term));
        SourceTheorem {
            result,
            defined,
            domain,
        }
    }
}
