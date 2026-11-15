// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact retained-LIR admission for the shared observation graph driver.
//! Pointer types have already been erased to word carriers here. Type hints
//! must agree with producing operations; they never choose their semantics.
//! The read-only wrapper retains its original opcode/width floor. Wider
//! integer and store observations require the distinct scalar-memory profile.

use super::*;
use std::collections::HashMap;
use trust_cg_ir::function::StackProtectorMode;
use trust_cg_lower::instructions::{Instruction, IntCC, Opcode};
use trust_cg_lower::{Function, Type};

type Result<T> = std::result::Result<T, ReadOnlySourceError>;

fn refuse(reason: &'static str) -> ReadOnlySourceError {
    ReadOnlySourceError::Lowering(reason)
}

fn kind(ty: &Type, profile: Profile) -> Result<Kind> {
    match ty {
        Type::I64 => Ok(Kind::Word),
        Type::B1 => Ok(Kind::Boolean),
        Type::I32 if profile.writable() => Ok(Kind::Word32),
        _ => Err(refuse("requires exact I64 or B1 LIR carriers")),
    }
}

fn memory_width(ty: &Type, profile: Profile) -> Option<u32> {
    match ty {
        Type::I64 => Some(8),
        Type::I32 if profile.writable() => Some(4),
        _ => None,
    }
}

fn memory_shape(ty: &Type, align: Option<u32>, profile: Profile) -> bool {
    memory_width(ty, profile)
        .is_some_and(|width| align.is_none_or(|a| a != 0 && a <= width && a.is_power_of_two()))
}

/// Check all resource bounds and constructor arities before allocating maps,
/// graph vectors, or cloning any opcode or operand list.
fn preflight(lir: &Function, profile: Profile) -> Result<()> {
    if lir.blocks.len() > 16
        || lir.block_order.len() > 16
        || lir.value_types.len() > 384
        || lir.signature.params.len() > 8
    {
        return Err(ReadOnlySourceError::Budget("read-only LIR shape limit"));
    }
    if lir.blocks.is_empty()
        || lir.signature.params.is_empty()
        || lir.signature.params.iter().any(|ty| *ty != Type::I64)
        || if profile.vector_returns() {
            !(1..=8).contains(&lir.signature.returns.len())
                || lir
                    .signature
                    .returns
                    .iter()
                    .any(|ty| kind(ty, profile).is_err())
        } else {
            lir.signature.returns != [Type::I64]
        }
        || !lir.stack_slots.is_empty()
        || !lir.eh_info.is_empty()
        || !lir.eh_type_table.is_empty()
        || lir.stack_protector != StackProtectorMode::None
        || lir.stack_limit.is_some()
        || lir.abi_sret_param.is_some()
        || !lir.param_pointee_types.is_empty()
        || !lir.sret_arg_callees.is_empty()
        || !lir.sret_arg_indirect_callees.is_empty()
        || !lir.pure_callees.is_empty()
        || !lir.libm_pure_callees.is_empty()
        || !lir.target_features.is_empty()
    {
        return Err(refuse(
            "requires an ordinary word-returning read-only LIR body",
        ));
    }
    let entry = lir
        .blocks
        .get(&lir.entry_block)
        .ok_or_else(|| refuse("LIR entry block does not exist"))?;
    if entry.params.len() != lir.signature.params.len()
        || entry
            .params
            .iter()
            .zip(&lir.signature.params)
            .any(|((_, actual), expected)| actual != expected)
    {
        return Err(refuse("LIR entry parameters disagree with its signature"));
    }
    if !lir.block_order.is_empty()
        && (lir.block_order.len() != lir.blocks.len()
            || lir.block_order.iter().enumerate().any(|(index, id)| {
                !lir.blocks.contains_key(id) || lir.block_order[..index].contains(id)
            }))
    {
        return Err(refuse("LIR block order omits or repeats a block"));
    }
    let mut count = 0usize;
    for block in lir.blocks.values() {
        if block.params.len() > 8 || block.instructions.len() > 256 - count {
            return Err(ReadOnlySourceError::Budget(
                "read-only LIR instruction limit",
            ));
        }
        count += block.instructions.len();
        if block.instructions.is_empty() {
            return Err(refuse("empty read-only LIR block"));
        }
        for (_, ty) in &block.params {
            kind(ty, profile)?;
        }
        for instruction in &block.instructions {
            if profile.vector_returns()
                && matches!(instruction.opcode, Opcode::Return)
                && instruction.args.len() != lir.signature.returns.len()
            {
                return Err(refuse(
                    "scalar return arity differs from retained signature",
                ));
            }
            shape(instruction, profile)?;
        }
    }
    for ty in lir.value_types.values() {
        kind(ty, profile)?;
    }
    Ok(())
}

fn shape(instruction: &Instruction, profile: Profile) -> Result<()> {
    let arguments = instruction.args.len();
    let results = instruction.results.len();
    if results > 1
        || arguments
            > if matches!(instruction.opcode, Opcode::Jump { .. })
                || profile.vector_returns() && matches!(instruction.opcode, Opcode::Return)
            {
                8
            } else {
                3
            }
    {
        return Err(ReadOnlySourceError::Budget("read-only LIR operand limit"));
    }
    let (expected_arguments, expected_results) = match &instruction.opcode {
        Opcode::Iconst { ty: Type::I64, .. } => (0, 1),
        Opcode::Iconst { ty: Type::I32, imm }
            if profile.writable()
                && (i32::try_from(*imm).is_ok() || u32::try_from(*imm).is_ok()) =>
        {
            (0, 1)
        }
        Opcode::Iconst {
            ty: Type::B1,
            imm: 0 | 1,
        } => (0, 1),
        Opcode::Copy | Opcode::Bitcast { to_ty: Type::I64 } => (1, 1),
        Opcode::Uextend {
            from_ty: Type::I32,
            to_ty: Type::I64,
        } if profile.writable() => (1, 1),
        Opcode::Imul if profile.writable() => (2, 1),
        Opcode::Iadd
        | Opcode::Isub
        | Opcode::Band
        | Opcode::Bor
        | Opcode::Bxor
        | Opcode::Ishl
        | Opcode::Ushr
        | Opcode::Sshr
        | Opcode::Icmp { .. }
        | Opcode::ArrayGep { elem_ty: Type::I8 } => (2, 1),
        Opcode::Select {
            cond: IntCC::Equal | IntCC::NotEqual,
        } => (3, 1),
        Opcode::Load { ty, align } if memory_shape(ty, *align, profile) => (1, 1),
        Opcode::Store { ty, align } if profile.writable() && memory_shape(ty, *align, profile) => {
            (2, 0)
        }
        Opcode::Return if profile.vector_returns() && (1..=8).contains(&arguments) => {
            (arguments, 0)
        }
        Opcode::Call { .. } if profile.vector_returns() => {
            return Err(refuse(
                "scalar-return calls require a checked callee/aggregate ABI owner",
            ));
        }
        Opcode::Return => (1, 0),
        Opcode::Jump { .. } => (arguments, 0),
        Opcode::Brif { cond, .. } if instruction.args.as_slice() == [*cond] => (1, 0),
        _ => return Err(refuse("unsupported retained LIR instruction or metadata")),
    };
    if (arguments, results) != (expected_arguments, expected_results) {
        return Err(refuse(
            "LIR operand or result arity disagrees with its operation",
        ));
    }
    Ok(())
}

fn fixed_kind(instruction: &Instruction, profile: Profile) -> Option<Kind> {
    match &instruction.opcode {
        Opcode::Iconst { ty: Type::B1, .. } | Opcode::Icmp { .. } => Some(Kind::Boolean),
        Opcode::Iconst { ty: Type::I32, .. } | Opcode::Load { ty: Type::I32, .. }
            if profile.writable() =>
        {
            Some(Kind::Word32)
        }
        Opcode::Iconst { ty: Type::I64, .. }
        | Opcode::Bitcast { to_ty: Type::I64 }
        | Opcode::ArrayGep { elem_ty: Type::I8 }
        | Opcode::Load { ty: Type::I64, .. } => Some(Kind::Word),
        Opcode::Uextend {
            from_ty: Type::I32,
            to_ty: Type::I64,
        } if profile.writable() => Some(Kind::Word),
        Opcode::Iadd
        | Opcode::Isub
        | Opcode::Band
        | Opcode::Bor
        | Opcode::Bxor
        | Opcode::Ishl
        | Opcode::Ushr
        | Opcode::Sshr
            if profile == Profile::ReadOnly =>
        {
            Some(Kind::Word)
        }
        _ => None,
    }
}

/// Infer copy/select and writable-profile arithmetic results from real
/// definitions, not the optional hint table. This bounded type fixed point is
/// independent of execution order; the parent checks dominance, paths, edges
/// and their simultaneous arguments. The legacy read-only word floor remains
/// fixed, and every hint still has to equal its actual producing codec.
fn definitions(
    lir: &Function,
    profile: Profile,
    projection: Option<&scalar_edge_projection::CheckedScalarBlockArguments<'_>>,
) -> Result<HashMap<u32, Kind>> {
    let mut defined = HashMap::with_capacity(384);
    let mut inferred = HashMap::with_capacity(384);
    let mut pending = Vec::new();
    for (block_id, block) in &lir.blocks {
        for (id, ty) in &block.params {
            if defined.insert(id.0, ()).is_some() {
                return Err(refuse("duplicate retained LIR SSA definition"));
            }
            inferred.insert(id.0, kind(ty, profile)?);
        }
        for (index, instruction) in block.instructions.iter().enumerate() {
            if projection.is_some_and(|p| p.omitted(block_id.0, index)) {
                continue;
            }
            if let Some(result) = instruction.results.first() {
                if defined.insert(result.0, ()).is_some() {
                    return Err(refuse("duplicate retained LIR SSA definition"));
                }
                if let Some(kind) = fixed_kind(instruction, profile) {
                    inferred.insert(result.0, kind);
                } else {
                    pending.push(instruction);
                }
            }
        }
    }
    while !pending.is_empty() {
        let before = pending.len();
        let mut error = None;
        pending.retain(|instruction| {
            let result = match &instruction.opcode {
                Opcode::Copy => inferred.get(&instruction.args[0].0).copied(),
                Opcode::Iadd
                | Opcode::Isub
                | Opcode::Imul
                | Opcode::Band
                | Opcode::Bor
                | Opcode::Bxor
                | Opcode::Ishl
                | Opcode::Ushr
                | Opcode::Sshr
                    if profile.writable() =>
                {
                    match (
                        inferred.get(&instruction.args[0].0),
                        inferred.get(&instruction.args[1].0),
                    ) {
                        (Some(left), Some(right))
                            if left == right
                                && (matches!(left, Kind::Word | Kind::Word32)
                                    || *left == Kind::Boolean
                                        && matches!(
                                            instruction.opcode,
                                            Opcode::Band | Opcode::Bor | Opcode::Bxor
                                        )) =>
                        {
                            Some(*left)
                        }
                        (Some(_), Some(_)) => {
                            error = Some(refuse(
                                "LIR arithmetic operand kinds disagree or are unsupported",
                            ));
                            None
                        }
                        _ => None,
                    }
                }
                Opcode::Select { .. } => {
                    match (
                        inferred.get(&instruction.args[1].0),
                        inferred.get(&instruction.args[2].0),
                    ) {
                        (Some(left), Some(right)) if left == right => Some(*left),
                        (Some(_), Some(_)) => {
                            error = Some(refuse("LIR select arm kinds disagree"));
                            None
                        }
                        _ => None,
                    }
                }
                _ => {
                    error = Some(refuse("unsupported LIR result-kind inference"));
                    None
                }
            };
            if let Some(kind) = result {
                inferred.insert(instruction.results[0].0, kind);
                false
            } else {
                true
            }
        });
        if let Some(error) = error {
            return Err(error);
        }
        if before == pending.len() {
            return Err(refuse(
                "undefined or cyclic retained LIR copy/select definition",
            ));
        }
    }
    for (id, ty) in &lir.value_types {
        if inferred.get(&id.0) != Some(&kind(ty, profile)?) {
            return Err(refuse(
                "LIR value hint disagrees with its producing definition",
            ));
        }
    }
    if profile.writable() {
        for instruction in lir.blocks.values().flat_map(|block| &block.instructions) {
            match &instruction.opcode {
                Opcode::Uextend { from_ty, .. } => {
                    if inferred.get(&instruction.args[0].0) != Some(&kind(from_ty, profile)?) {
                        return Err(refuse(
                            "LIR extension source disagrees with its producing definition",
                        ));
                    }
                }
                Opcode::Store { ty, .. } => {
                    if inferred.get(&instruction.args[0].0) != Some(&kind(ty, profile)?)
                        || inferred.get(&instruction.args[1].0) != Some(&Kind::Word)
                    {
                        return Err(refuse(
                            "LIR store value/address kinds disagree with real definitions",
                        ));
                    }
                }
                Opcode::Load { .. }
                    if inferred.get(&instruction.args[0].0) != Some(&Kind::Word) =>
                {
                    return Err(refuse("LIR load address is not an actual word definition"));
                }
                _ => {}
            }
        }
    }
    Ok(inferred)
}

pub(super) fn graph(lir: &Function) -> Result<Graph> {
    graph_profile(lir, Profile::ReadOnly)
}

pub(super) fn graph_bound(
    module: &Module,
    ordinal: usize,
    lir: &Function,
    profile: Profile,
) -> Result<Graph> {
    preflight(lir, profile)?;
    let parameters: HashSet<_> = lir
        .blocks
        .iter()
        .filter(|(id, _)| **id != lir.entry_block)
        .flat_map(|(_, b)| b.params.iter().map(|(v, _)| *v))
        .collect();
    let has_transport = lir
        .blocks
        .values()
        .flat_map(|b| &b.instructions)
        .any(|n| n.results.iter().any(|v| parameters.contains(v)));
    if !has_transport {
        return if profile == Profile::ReadOnly {
            graph(lir)
        } else {
            graph_profile(lir, profile)
        };
    }
    let projection = scalar_edge_projection::check_scalar_block_arguments(module, ordinal, lir)?;
    graph_projected(module, ordinal, lir, profile, &projection)
}

pub(super) fn graph_projected(
    module: &Module,
    ordinal: usize,
    lir: &Function,
    profile: Profile,
    projection: &scalar_edge_projection::CheckedScalarBlockArguments<'_>,
) -> Result<Graph> {
    if !projection.matches(module, ordinal, lir) {
        return Err(refuse("stale/foreign scalar edge projection"));
    }
    graph_with_projection(lir, profile, Some(projection))
}

pub(super) fn graph_profile(lir: &Function, profile: Profile) -> Result<Graph> {
    graph_with_projection(lir, profile, None)
}
fn graph_with_projection(
    lir: &Function,
    profile: Profile,
    projection: Option<&scalar_edge_projection::CheckedScalarBlockArguments<'_>>,
) -> Result<Graph> {
    preflight(lir, profile)?;
    let kinds = definitions(lir, profile, projection)?;
    let entry = &lir.blocks[&lir.entry_block];
    let parameters = entry
        .params
        .iter()
        .map(|(id, _)| (id.0, Kind::Word))
        .collect();
    let mut block_ids: Vec<_> = lir.blocks.keys().copied().collect();
    block_ids.sort_unstable();
    let mut blocks = Vec::with_capacity(block_ids.len());
    for id in block_ids {
        let block = &lir.blocks[&id];
        let parameters = block
            .params
            .iter()
            .map(|(id, ty)| Ok((id.0, kind(ty, profile)?)))
            .collect::<Result<_>>()?;
        let mut nodes = Vec::with_capacity(block.instructions.len());
        for (instruction, node) in block.instructions.iter().enumerate() {
            if projection.is_some_and(|p| p.omitted(id.0, instruction)) {
                continue;
            }
            let operation = match &node.opcode {
                Opcode::Iconst { ty: Type::I32, imm } if profile.writable() => {
                    // Preflight admits signed I32 and unsigned U32 carrier
                    // spellings only. Both denote this exact 32-bit pattern.
                    Operation::Constant(u64::from(*imm as u32))
                }
                Opcode::Iconst { imm, .. } => Operation::Constant(*imm as u64),
                Opcode::Copy | Opcode::Bitcast { to_ty: Type::I64 } => {
                    Operation::Copy(node.args[0].0)
                }
                Opcode::Uextend {
                    from_ty: Type::I32,
                    to_ty: Type::I64,
                } if profile.writable() => Operation::ZeroExtend(node.args[0].0),
                Opcode::Iadd
                | Opcode::Isub
                | Opcode::Imul
                | Opcode::Band
                | Opcode::Bor
                | Opcode::Bxor
                | Opcode::Ishl
                | Opcode::Ushr
                | Opcode::Sshr => Operation::Binary {
                    opcode: node.opcode.clone(),
                    left: node.args[0].0,
                    right: node.args[1].0,
                },
                Opcode::Icmp { cond } => Operation::Compare {
                    condition: *cond,
                    left: node.args[0].0,
                    right: node.args[1].0,
                },
                Opcode::Select { cond } => Operation::Select {
                    condition: node.args[0].0,
                    then_value: node.args[1].0,
                    else_value: node.args[2].0,
                    invert: *cond == IntCC::Equal,
                },
                Opcode::ArrayGep { elem_ty: Type::I8 } if profile.writable() => {
                    Operation::ScaledOffset {
                        base: node.args[0].0,
                        index: node.args[1].0,
                        scale: 1,
                        signed: false,
                    }
                }
                Opcode::ArrayGep { elem_ty: Type::I8 } => Operation::Offset {
                    base: node.args[0].0,
                    index: node.args[1].0,
                    scale: 1,
                },
                Opcode::Load { ty, align } if profile.writable() => Operation::MemoryLoad {
                    address: node.args[0].0,
                    alignment: u64::from(align.unwrap_or(ty.align())),
                    byte_width: memory_width(ty, profile).expect("preflight scalar load width"),
                },
                Opcode::Load {
                    ty: Type::I64,
                    align,
                } => Operation::Load {
                    address: node.args[0].0,
                    alignment: u64::from(align.unwrap_or(8)),
                },
                Opcode::Store { ty, align } if profile.writable() => Operation::Store {
                    address: node.args[1].0,
                    value: node.args[0].0,
                    alignment: u64::from(align.unwrap_or(ty.align())),
                    byte_width: memory_width(ty, profile).expect("preflight scalar store width"),
                },
                Opcode::Return if profile.vector_returns() => Operation::VectorReturn(
                    node.args
                        .iter()
                        .zip(&lir.signature.returns)
                        .map(|(id, ty)| Ok((id.0, kind(ty, profile)?)))
                        .collect::<Result<_>>()?,
                ),
                Opcode::Return => Operation::Return(node.args[0].0),
                Opcode::Jump { dest } => Operation::Jump {
                    target: dest.0,
                    args: projection
                        .and_then(|p| p.jump_arguments(id.0))
                        .map(|args| args.to_vec())
                        .unwrap_or_else(|| node.args.iter().map(|value| value.0).collect()),
                },
                Opcode::Brif {
                    cond,
                    then_dest,
                    else_dest,
                } => Operation::Branch {
                    condition: cond.0,
                    then_target: then_dest.0,
                    then_args: Vec::new(),
                    else_target: else_dest.0,
                    else_args: Vec::new(),
                },
                _ => return Err(refuse("unsupported retained LIR operation after preflight")),
            };
            let result = node.results.first().map(|value| (value.0, kinds[&value.0]));
            nodes.push(Node {
                site: ReadOnlySite {
                    block: id.0,
                    instruction,
                },
                result,
                operation,
            });
        }
        blocks.push(Block {
            id: id.0,
            parameters,
            nodes,
        });
    }
    Ok(Graph {
        entry: lir.entry_block.0,
        parameters,
        blocks,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::{BasicBlock, Signature};
    use trust_cg_lower::instructions::{Block as LirBlock, Value};

    fn instruction(opcode: Opcode, args: &[u32], result: Option<u32>) -> Instruction {
        Instruction {
            opcode,
            args: args.iter().copied().map(Value).collect(),
            results: result.into_iter().map(Value).collect(),
        }
    }

    fn function(instructions: Vec<Instruction>) -> Function {
        let mut lir = Function::new(
            "readonly_lir",
            Signature {
                params: vec![Type::I64],
                returns: vec![Type::I64],
            },
        );
        lir.blocks.insert(
            LirBlock(0),
            BasicBlock {
                params: vec![(Value(0), Type::I64)],
                instructions,
                ..Default::default()
            },
        );
        lir
    }

    fn ordinary() -> Function {
        function(vec![
            instruction(
                Opcode::Iconst {
                    ty: Type::I64,
                    imm: 7,
                },
                &[],
                Some(1),
            ),
            instruction(Opcode::Return, &[1], None),
        ])
    }

    fn scalar_profile() -> Profile {
        Profile::ScalarMemory(scalar_memory::Endpoint::Lir)
    }

    #[test]
    fn scalar_lir_retains_real_i32_arithmetic_store_order_load_width_and_extension() {
        let mut lir = function(vec![
            instruction(
                Opcode::Iconst {
                    ty: Type::I32,
                    imm: -1,
                },
                &[],
                Some(1),
            ),
            instruction(
                Opcode::Iconst {
                    ty: Type::I32,
                    imm: 2,
                },
                &[],
                Some(2),
            ),
            instruction(Opcode::Copy, &[1], Some(3)),
            instruction(Opcode::Iadd, &[3, 2], Some(4)),
            instruction(Opcode::Imul, &[4, 2], Some(5)),
            instruction(
                Opcode::Store {
                    ty: Type::I32,
                    align: Some(2),
                },
                &[5, 0],
                None,
            ),
            instruction(
                Opcode::Load {
                    ty: Type::I32,
                    align: Some(2),
                },
                &[0],
                Some(6),
            ),
            instruction(
                Opcode::Uextend {
                    from_ty: Type::I32,
                    to_ty: Type::I64,
                },
                &[6],
                Some(7),
            ),
            instruction(Opcode::Return, &[7], None),
        ]);
        for id in 1..=6 {
            lir.value_types.insert(Value(id), Type::I32);
        }
        lir.value_types.insert(Value(7), Type::I64);
        assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Lowering(_))));
        let checked = graph_profile(&lir, scalar_profile()).unwrap();
        let nodes = &checked.blocks[0].nodes;
        assert!(matches!(
            nodes[0].operation,
            Operation::Constant(0xffff_ffff)
        ));
        assert_eq!(nodes[3].result, Some((4, Kind::Word32)));
        assert_eq!(nodes[4].result, Some((5, Kind::Word32)));
        assert!(matches!(
            nodes[5].operation,
            Operation::Store {
                address: 0,
                value: 5,
                alignment: 2,
                byte_width: 4
            }
        ));
        assert!(nodes[5].result.is_none());
        assert!(matches!(
            nodes[6].operation,
            Operation::MemoryLoad {
                address: 0,
                alignment: 2,
                byte_width: 4
            }
        ));
        assert_eq!(nodes[6].result, Some((6, Kind::Word32)));
        assert!(matches!(nodes[7].operation, Operation::ZeroExtend(6)));
        assert_eq!(nodes[7].result, Some((7, Kind::Word)));
    }

    #[test]
    fn scalar_lir_hints_cannot_hide_mixed_binary_width_or_wrong_extension_store_producers() {
        let narrow = || {
            instruction(
                Opcode::Iconst {
                    ty: Type::I32,
                    imm: 1,
                },
                &[],
                Some(1),
            )
        };
        for opcode in [
            Opcode::Iadd,
            Opcode::Isub,
            Opcode::Imul,
            Opcode::Band,
            Opcode::Bor,
            Opcode::Bxor,
            Opcode::Ishl,
            Opcode::Ushr,
            Opcode::Sshr,
        ] {
            for hint in [Type::I32, Type::I64] {
                let mut lir = function(vec![
                    narrow(),
                    instruction(opcode.clone(), &[1, 0], Some(2)),
                    instruction(Opcode::Return, &[0], None),
                ]);
                lir.value_types.insert(Value(2), hint);
                assert!(matches!(
                    graph_profile(&lir, scalar_profile()),
                    Err(ReadOnlySourceError::Lowering(_))
                ));
            }
        }
        for ty in [Type::I64, Type::B1] {
            let lir = function(vec![
                instruction(Opcode::Iconst { ty, imm: 1 }, &[], Some(1)),
                instruction(
                    Opcode::Uextend {
                        from_ty: Type::I32,
                        to_ty: Type::I64,
                    },
                    &[1],
                    Some(2),
                ),
                instruction(Opcode::Return, &[2], None),
            ]);
            assert!(matches!(
                graph_profile(&lir, scalar_profile()),
                Err(ReadOnlySourceError::Lowering(_))
            ));
        }
        for (ty, args) in [(Type::I64, [1, 0]), (Type::I32, [0, 1]), (Type::B1, [1, 0])] {
            let lir = function(vec![
                narrow(),
                instruction(Opcode::Store { ty, align: None }, &args, None),
                instruction(Opcode::Return, &[0], None),
            ]);
            assert!(matches!(
                graph_profile(&lir, scalar_profile()),
                Err(ReadOnlySourceError::Lowering(_))
            ));
        }
        let lir = function(vec![
            narrow(),
            instruction(
                Opcode::Uextend {
                    from_ty: Type::B1,
                    to_ty: Type::I64,
                },
                &[1],
                Some(2),
            ),
            instruction(Opcode::Return, &[2], None),
        ]);
        assert!(matches!(
            graph_profile(&lir, scalar_profile()),
            Err(ReadOnlySourceError::Lowering(_))
        ));
        for imm in [i64::from(i32::MIN) - 1, i64::from(u32::MAX) + 1] {
            let lir = function(vec![
                instruction(Opcode::Iconst { ty: Type::I32, imm }, &[], Some(1)),
                instruction(Opcode::Return, &[0], None),
            ]);
            assert!(matches!(
                graph_profile(&lir, scalar_profile()),
                Err(ReadOnlySourceError::Lowering(_))
            ));
        }
    }

    #[test]
    fn scalar_lir_preserves_readonly_floor_and_boolean_bitwise_only_inference() {
        let lir = function(vec![
            instruction(
                Opcode::Iconst {
                    ty: Type::B1,
                    imm: 1,
                },
                &[],
                Some(1),
            ),
            instruction(
                Opcode::Iconst {
                    ty: Type::B1,
                    imm: 0,
                },
                &[],
                Some(2),
            ),
            instruction(Opcode::Band, &[1, 2], Some(3)),
            instruction(Opcode::Return, &[0], None),
        ]);
        let checked = graph_profile(&lir, scalar_profile()).unwrap();
        assert_eq!(checked.blocks[0].nodes[2].result, Some((3, Kind::Boolean)));
        for opcode in [
            Opcode::Iadd,
            Opcode::Isub,
            Opcode::Imul,
            Opcode::Ishl,
            Opcode::Ushr,
            Opcode::Sshr,
        ] {
            let mut malformed = lir.clone();
            malformed.blocks.get_mut(&LirBlock(0)).unwrap().instructions[2].opcode = opcode;
            assert!(matches!(
                graph_profile(&malformed, scalar_profile()),
                Err(ReadOnlySourceError::Lowering(_))
            ));
        }
        for (opcode, args, result) in [
            (
                Opcode::Iconst {
                    ty: Type::I32,
                    imm: 1,
                },
                vec![],
                Some(1),
            ),
            (
                Opcode::Load {
                    ty: Type::I32,
                    align: None,
                },
                vec![0],
                Some(1),
            ),
            (
                Opcode::Store {
                    ty: Type::I64,
                    align: None,
                },
                vec![0, 0],
                None,
            ),
            (Opcode::Imul, vec![0, 0], Some(1)),
            (
                Opcode::Uextend {
                    from_ty: Type::I32,
                    to_ty: Type::I64,
                },
                vec![0],
                Some(1),
            ),
        ] {
            let lir = function(vec![
                instruction(opcode, &args, result),
                instruction(Opcode::Return, &[0], None),
            ]);
            assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Lowering(_))));
        }
    }

    #[test]
    fn readonly_lir_definitions_determine_copy_select_and_bitcast_kinds() {
        let mut lir = function(vec![
            instruction(
                Opcode::Iconst {
                    ty: Type::B1,
                    imm: 1,
                },
                &[],
                Some(1),
            ),
            instruction(
                Opcode::Iconst {
                    ty: Type::B1,
                    imm: 0,
                },
                &[],
                Some(2),
            ),
            instruction(Opcode::Copy, &[1], Some(3)),
            instruction(Opcode::Select { cond: IntCC::Equal }, &[3, 1, 2], Some(4)),
            instruction(Opcode::Bitcast { to_ty: Type::I64 }, &[4], Some(5)),
            instruction(Opcode::Return, &[5], None),
        ]);
        lir.value_types.insert(Value(3), Type::B1);
        lir.value_types.insert(Value(4), Type::B1);
        lir.value_types.insert(Value(5), Type::I64);
        let checked = graph(&lir).unwrap();
        assert_eq!(checked.parameters, [(0, Kind::Word)]);
        let nodes = &checked.blocks[0].nodes;
        assert_eq!(nodes[2].result, Some((3, Kind::Boolean)));
        assert_eq!(nodes[3].result, Some((4, Kind::Boolean)));
        assert!(matches!(
            nodes[3].operation,
            Operation::Select { invert: true, .. }
        ));
        assert_eq!(nodes[4].result, Some((5, Kind::Word)));
        assert_eq!(nodes[4].site.block, 0);
        assert_eq!(nodes[4].site.instruction, 4);
    }

    #[test]
    fn readonly_lir_value_hints_cannot_choose_semantics_or_invent_values() {
        for (value, ty) in [(1, Type::B1), (99, Type::I64), (1, Type::I32)] {
            let mut lir = ordinary();
            lir.value_types.insert(Value(value), ty);
            assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Lowering(_))));
        }
        let mut lir = ordinary();
        lir.value_types.insert(Value(1), Type::I64);
        assert!(graph(&lir).is_ok());
    }

    #[test]
    fn readonly_lir_branches_bind_both_condition_spellings() {
        let mut lir = function(vec![
            instruction(
                Opcode::Iconst {
                    ty: Type::B1,
                    imm: 1,
                },
                &[],
                Some(1),
            ),
            instruction(
                Opcode::Brif {
                    cond: Value(1),
                    then_dest: LirBlock(1),
                    else_dest: LirBlock(2),
                },
                &[1],
                None,
            ),
        ]);
        for id in [1, 2] {
            lir.blocks.insert(
                LirBlock(id),
                BasicBlock {
                    instructions: vec![
                        instruction(
                            Opcode::Iconst {
                                ty: Type::I64,
                                imm: i64::from(id),
                            },
                            &[],
                            Some(id + 1),
                        ),
                        instruction(Opcode::Return, &[id + 1], None),
                    ],
                    ..Default::default()
                },
            );
        }
        let checked = graph(&lir).unwrap();
        assert!(matches!(
            &checked.blocks[0].nodes[1].operation,
            Operation::Branch { condition: 1, then_target: 1, then_args, else_target: 2, else_args }
                if then_args.is_empty() && else_args.is_empty()
        ));
        lir.blocks.get_mut(&LirBlock(0)).unwrap().instructions[1].args[0] = Value(0);
        assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Lowering(_))));
    }

    #[test]
    fn readonly_lir_load_and_gep_keep_exact_operands_and_alignment() {
        let lir = function(vec![
            instruction(
                Opcode::Iconst {
                    ty: Type::I64,
                    imm: 8,
                },
                &[],
                Some(1),
            ),
            instruction(Opcode::ArrayGep { elem_ty: Type::I8 }, &[0, 1], Some(2)),
            instruction(
                Opcode::Load {
                    ty: Type::I64,
                    align: Some(4),
                },
                &[2],
                Some(3),
            ),
            instruction(Opcode::Return, &[3], None),
        ]);
        let checked = graph(&lir).unwrap();
        assert!(matches!(
            checked.blocks[0].nodes[1].operation,
            Operation::Offset {
                base: 0,
                index: 1,
                scale: 1
            }
        ));
        assert!(matches!(
            checked.blocks[0].nodes[2].operation,
            Operation::Load {
                address: 2,
                alignment: 4
            }
        ));
    }

    #[test]
    fn readonly_lir_refuses_malformed_effectful_and_noncanonical_operations() {
        for opcode in [
            Opcode::Iconst {
                ty: Type::B1,
                imm: 2,
            },
            Opcode::Load {
                ty: Type::I64,
                align: Some(0),
            },
            Opcode::Load {
                ty: Type::I64,
                align: Some(3),
            },
            Opcode::Load {
                ty: Type::I64,
                align: Some(16),
            },
            Opcode::VolatileLoad {
                ty: Type::I64,
                align: None,
            },
            Opcode::ArrayGep { elem_ty: Type::I64 },
            Opcode::Select {
                cond: IntCC::SignedLessThan,
            },
        ] {
            let lir = function(vec![
                instruction(opcode, &[0], Some(1)),
                instruction(Opcode::Return, &[1], None),
            ]);
            assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Lowering(_))));
        }
        let mut lir = ordinary();
        lir.blocks.get_mut(&LirBlock(0)).unwrap().instructions[0]
            .args
            .push(Value(0));
        assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Lowering(_))));
    }

    #[test]
    fn readonly_lir_refuses_duplicate_and_uninferrable_definitions() {
        for instructions in [
            vec![
                instruction(Opcode::Copy, &[0], Some(0)),
                instruction(Opcode::Return, &[0], None),
            ],
            vec![
                instruction(Opcode::Copy, &[2], Some(1)),
                instruction(Opcode::Copy, &[1], Some(2)),
                instruction(Opcode::Return, &[1], None),
            ],
            vec![
                instruction(Opcode::Copy, &[99], Some(1)),
                instruction(Opcode::Return, &[1], None),
            ],
            vec![
                instruction(
                    Opcode::Iconst {
                        ty: Type::B1,
                        imm: 1,
                    },
                    &[],
                    Some(1),
                ),
                instruction(
                    Opcode::Select {
                        cond: IntCC::NotEqual,
                    },
                    &[1, 0, 1],
                    Some(2),
                ),
                instruction(Opcode::Return, &[2], None),
            ],
        ] {
            assert!(matches!(
                graph(&function(instructions)),
                Err(ReadOnlySourceError::Lowering(_))
            ));
        }
    }

    #[test]
    fn readonly_lir_preflight_bounds_shapes_before_graph_construction() {
        let mut lir = ordinary();
        lir.value_types
            .extend((1000..1385).map(|id| (Value(id), Type::I64)));
        assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Budget(_))));
        let mut lir = ordinary();
        lir.blocks.get_mut(&LirBlock(0)).unwrap().instructions =
            vec![instruction(Opcode::Copy, &[0], Some(1)); 257];
        assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Budget(_))));
        let mut lir = ordinary();
        lir.blocks.get_mut(&LirBlock(0)).unwrap().instructions[0].args = vec![Value(0); 4];
        assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Budget(_))));
        let mut lir = ordinary();
        lir.block_order = vec![LirBlock(0), LirBlock(0)];
        assert!(matches!(graph(&lir), Err(ReadOnlySourceError::Lowering(_))));
    }
}
