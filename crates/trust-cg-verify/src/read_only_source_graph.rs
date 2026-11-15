// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Shared bounded CFG/SSA driver for independently adapted source endpoints.
//! It never prunes an untaken constant branch before validating that branch.

use super::*;

#[path = "read_only_source_liveness.rs"]
mod liveness;

#[cfg(test)]
#[path = "scalar_memory_arithmetic_tests.rs"]
mod arithmetic_tests;

struct Validated<'a> {
    blocks: HashMap<u32, &'a Block>,
    order: Vec<u32>,
}

fn destinations(operation: &Operation) -> Vec<u32> {
    match operation {
        Operation::Jump { target, .. } => vec![*target],
        Operation::Branch {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        _ => vec![],
    }
}

fn validate(graph: &Graph, boundary: Boundary) -> Result<Validated<'_>, ReadOnlySourceError> {
    if graph.blocks.is_empty() || graph.blocks.len() > MAX_BLOCKS || graph.parameters.len() > 8 {
        return Err(ReadOnlySourceError::Budget("graph size"));
    }
    let mut blocks = HashMap::new();
    let mut definitions = HashSet::new();
    let mut instructions = 0usize;
    for block in &graph.blocks {
        instructions += block.nodes.len();
        if instructions > MAX_INSTRUCTIONS || block.parameters.len() > 8 {
            return Err(ReadOnlySourceError::Budget("source nodes/parameters"));
        }
        if block.nodes.is_empty() || blocks.insert(block.id, block).is_some() {
            return Err(boundary.error("empty or duplicate block"));
        }
        for id in block
            .parameters
            .iter()
            .map(|(id, _)| *id)
            .chain(block.nodes.iter().flat_map(Node::definition_ids))
        {
            if !definitions.insert(id) {
                return Err(boundary.error("duplicate SSA definition"));
            }
        }
        for (i, node) in block.nodes.iter().enumerate() {
            if matches!(&node.operation, Operation::VectorReturn(values) if values.is_empty() || values.len() > 8)
            {
                return Err(boundary.error("scalar return vector arity"));
            }
            let terminal = matches!(
                node.operation,
                Operation::Return(_)
                    | Operation::VectorReturn(_)
                    | Operation::VoidReturn
                    | Operation::NativeTargetFrontier
                    | Operation::Jump { .. }
                    | Operation::Branch { .. }
            );
            if terminal != (i + 1 == block.nodes.len()) || terminal && node.result.is_some() {
                return Err(boundary.error("terminator position/result"));
            }
        }
    }
    if definitions.len() > MAX_VALUES {
        return Err(ReadOnlySourceError::Budget("SSA values"));
    }
    let entry = blocks
        .get(&graph.entry)
        .ok_or(boundary.error("missing entry"))?;
    if entry.parameters != graph.parameters {
        return Err(boundary.error("entry parameter identity/type"));
    }
    let mut reached = HashSet::new();
    let mut pending = vec![graph.entry];
    let mut indegrees: HashMap<_, usize> = blocks.keys().map(|&id| (id, 0)).collect();
    for block in blocks.values() {
        for target in destinations(&block.nodes.last().unwrap().operation) {
            *indegrees
                .get_mut(&target)
                .ok_or(boundary.error("missing branch target"))? += 1;
        }
    }
    while let Some(id) = pending.pop() {
        if reached.insert(id) {
            pending.extend(destinations(&blocks[&id].nodes.last().unwrap().operation));
        }
    }
    if reached.len() != blocks.len() {
        return Err(boundary.error("unreachable/uninspected block"));
    }
    let mut ready: Vec<_> = indegrees
        .iter()
        .filter_map(|(&id, &n)| (n == 0).then_some(id))
        .collect();
    let mut order = Vec::with_capacity(blocks.len());
    while let Some(id) = ready.pop() {
        order.push(id);
        for target in destinations(&blocks[&id].nodes.last().unwrap().operation) {
            let degree = indegrees.get_mut(&target).unwrap();
            *degree -= 1;
            if *degree == 0 {
                ready.push(target);
            }
        }
    }
    if order.len() != blocks.len() {
        return Err(boundary.error("cyclic graph"));
    }
    Ok(Validated { blocks, order })
}

#[derive(Clone)]
struct State {
    block: u32,
    values: HashMap<u32, Value>,
    records: HashMap<u32, native_aggregates::RecordState>,
    guard: Term,
    memory: Option<Term>,
}

fn read(state: &State, id: u32, boundary: Boundary) -> Result<&Value, ReadOnlySourceError> {
    state
        .values
        .get(&id)
        .ok_or(boundary.error("undefined or nondominating SSA operand"))
}
fn bounded(term: Option<Term>) -> Result<Term, ReadOnlySourceError> {
    term.ok_or(ReadOnlySourceError::Budget("raw expression tree"))
}
fn word(value: &Value, boundary: Boundary) -> Result<&Term, ReadOnlySourceError> {
    if value.kind == Kind::Boolean {
        Err(boundary.error("word operation has Boolean operand"))
    } else {
        Ok(&value.term)
    }
}
fn condition(value: &Value, boundary: Boundary) -> Result<Term, ReadOnlySourceError> {
    if value.kind != Kind::Boolean {
        return Err(boundary.error("noncanonical branch/select condition"));
    }
    bounded(
        value
            .term
            .unary(3, |e| e.eq_expr(E::bv_const(0, 1)).not_expr()),
    )
}
fn fork_fits(state: &State) -> Result<(), ReadOnlySourceError> {
    let total = state
        .values
        .values()
        .try_fold(
            state.guard.nodes
                + state.memory.as_ref().map_or(0, |m| m.nodes)
                + state
                    .records
                    .values()
                    .map(|r| r.fields.iter().map(|f| f.nodes).sum::<usize>())
                    .sum::<usize>(),
            |n, v| n.checked_add(v.term.nodes),
        )
        .ok_or(ReadOnlySourceError::Budget("fork overflow"))?;
    if total.checked_mul(2).is_none_or(|n| n > MAX_ENV_NODES) {
        return Err(ReadOnlySourceError::Budget("fork environments"));
    }
    Ok(())
}

// A control guard composes several independently bounded scalar values. Keep
// the existing raw body's per-value 4096 limit intact; bound this new complete
// read-only graph's guarded/query composition separately, before cloning.
fn guarded(before: &Term, condition: &Term, invert: bool) -> Result<Term, ReadOnlySourceError> {
    let nodes = before
        .nodes
        .checked_add(condition.nodes)
        .and_then(|n| n.checked_add(if invert { 2 } else { 1 }))
        .ok_or(ReadOnlySourceError::Budget("path guard overflow"))?;
    if nodes > MAX_QUERY_NODES {
        return Err(ReadOnlySourceError::Budget("path guard expression"));
    }
    Ok(Term {
        nodes,
        expr: before.expr.clone().and_expr(if invert {
            condition.expr.clone().not_expr()
        } else {
            condition.expr.clone()
        }),
    })
}

fn geometry_fits(used: &mut usize, nodes: usize) -> Result<(), ReadOnlySourceError> {
    let total = used
        .checked_add(nodes)
        .filter(|n| *n <= MAX_GEOMETRY_NODES)
        .ok_or(ReadOnlySourceError::Budget(
            "aggregate geometry expressions",
        ))?;
    *used = total;
    Ok(())
}

fn access_geometry(
    geometry: &mut Vec<E>,
    used: &mut usize,
    guard: &Term,
    address: &Term,
    width: u32,
    alignment: u64,
) -> Result<(), ReadOnlySourceError> {
    geometry_fits(used, guard.nodes + address.nodes * 2 + 9)?;
    let valid = address
        .expr
        .clone()
        .bvule(E::bv_const(u64::MAX - u64::from(width - 1), 64))
        .and_expr(
            address
                .expr
                .clone()
                .bvand(E::bv_const(alignment - 1, 64))
                .eq_expr(E::bv_const(0, 64)),
        );
    geometry.push(guard.expr.clone().not_expr().or_expr(valid));
    Ok(())
}
fn edge(
    state: &State,
    target: &Block,
    args: &[u32],
    guard: Term,
    boundary: Boundary,
    liveness: &liveness::Liveness,
) -> Result<State, ReadOnlySourceError> {
    if args.len() != target.parameters.len() {
        return Err(boundary.error("edge argument arity"));
    }
    // Read ALL arguments before binding any destination (parallel SSA copies).
    let arguments: Vec<_> = args
        .iter()
        .map(|&id| read(state, id, boundary).cloned())
        .collect::<Result<_, _>>()?;
    // Copy only dominating values demanded by this successor. ALL edge
    // arguments above were read simultaneously, even unused parameters.
    let mut values = state
        .values
        .iter()
        .filter(|(id, _)| liveness.needed(target.id, 0, **id))
        .map(|(&id, value)| (id, value.clone()))
        .collect::<HashMap<_, _>>();
    for ((id, kind), value) in target.parameters.iter().zip(arguments) {
        if *kind != value.kind {
            return Err(boundary.error("edge argument type"));
        }
        if state.values.contains_key(id) {
            return Err(boundary.error("edge overwrites prior SSA value"));
        }
        if liveness.needed(target.id, 0, *id) {
            values.insert(*id, value);
        }
    }
    Ok(State {
        block: target.id,
        values,
        records: state
            .records
            .iter()
            .filter(|(id, _)| liveness.needed(target.id, 0, **id))
            .map(|(id, record)| (*id, record.clone()))
            .collect(),
        guard,
        memory: state.memory.clone(),
    })
}

pub(super) fn observe(
    graph: &Graph,
    inputs: &[(String, u32)],
    memory: &E,
    boundary: Boundary,
) -> Result<Observations, ReadOnlySourceError> {
    observe_profile(graph, inputs, memory, boundary, Profile::ReadOnly)
}

pub(super) fn observe_profile(
    graph: &Graph,
    inputs: &[(String, u32)],
    memory: &E,
    boundary: Boundary,
    profile: Profile,
) -> Result<Observations, ReadOnlySourceError> {
    let Validated { blocks, order } = validate(graph, boundary)?;
    let liveness = liveness::compute(graph, &blocks, &order, boundary)?;
    let mut values = graph
        .parameters
        .iter()
        .zip(inputs)
        .map(|((id, kind), (name, _))| {
            (
                *id,
                Value {
                    kind: *kind,
                    term: Term::leaf(E::var(name, 64)),
                    literal: None,
                },
            )
        })
        .collect();
    liveness.retain_before(graph.entry, 0, &mut values);
    let mut pending = vec![State {
        block: graph.entry,
        values,
        records: HashMap::new(),
        guard: Term::leaf(E::BoolConst(true)),
        memory: profile.writable().then(|| Term::leaf(memory.clone())),
    }];
    let mut memory_observations = match profile {
        Profile::ReadOnly => None,
        Profile::ScalarMemory(endpoint) | Profile::ScalarReturns(endpoint) => {
            Some(scalar_memory::MemoryObservations::new(endpoint))
        }
        Profile::ConditionalWrapper(endpoint) | Profile::NativeAggregates(endpoint) => {
            Some(scalar_memory::MemoryObservations::conditional(endpoint))
        }
        Profile::NativeTarget => Some(scalar_memory::MemoryObservations::conditional(
            scalar_memory::Endpoint::Machine,
        )),
    };
    if profile.native_target() {
        let initial = native_aggregate_target::input(
            &mut memory_observations.as_mut().unwrap().definitions,
            memory_sort(),
        )?;
        pending[0].memory = Some(Term::leaf(initial));
    }
    let mut target = native_aggregate_target::Effects::default();
    let mut conditional = profile
        .conditional_calls()
        .then(conditional_wrapper::ObservedEffects::default);
    let mut void_returns = 0usize;
    let mut native_events = Vec::new();
    let mut native_nodes = 0usize;
    let mut reads = Vec::new();
    let mut geometry = Vec::new();
    let mut geometry_nodes = 0usize;
    let mut returns = Vec::new();
    let mut vector_returns: Vec<(Term, Vec<Value>)> = Vec::new();
    let mut vector_return_nodes = 0usize;
    let mut forks = 0usize;
    while let Some(mut state) = pending.pop() {
        for (instruction, node) in blocks[&state.block].nodes.iter().enumerate() {
            let result = |term, literal| -> Result<Value, ReadOnlySourceError> {
                let (_, kind) = node
                    .result
                    .ok_or(boundary.error("value node has no result"))?;
                Ok(Value {
                    kind,
                    term,
                    literal,
                })
            };
            let value = match &node.operation {
                Operation::NativeTarget(op) => {
                    if !profile.native_target() {
                        return Err(
                            boundary.error("native target operation outside target profile")
                        );
                    }
                    let value = op.execute(
                        node.site,
                        &mut state.values,
                        &mut state.memory,
                        &mut state.guard,
                        &mut memory_observations
                            .as_mut()
                            .ok_or(boundary.error("missing native target memory"))?
                            .definitions,
                        &mut target,
                    )?;
                    if let Some(value) = value {
                        value
                    } else {
                        liveness.retain_before(state.block, instruction + 1, &mut state.values);
                        continue;
                    }
                }
                Operation::NativeTargetFrontier => {
                    if !profile.native_target() || node.result.is_some() {
                        return Err(boundary.error("native target frontier outside profile"));
                    }
                    void_returns += 1;
                    memory_observations.as_mut().unwrap().returns.push((
                        state.guard.clone(),
                        state
                            .memory
                            .clone()
                            .ok_or(boundary.error("missing target frontier world"))?,
                    ));
                    break;
                }
                Operation::NativeAggregateCall {
                    intent,
                    binding,
                    record,
                    args,
                } => {
                    if !profile.native_events()
                        || node.result.is_some()
                        || args.len() != intent.argument_codecs().len()
                    {
                        return Err(
                            boundary.error("native aggregate event shape or occurrence limit")
                        );
                    }
                    if native_events.len() >= MAX_READS {
                        return Err(ReadOnlySourceError::Budget(
                            "native aggregate execution occurrences",
                        ));
                    }
                    // Reserve the complete event before cloning its retained
                    // terms/names or allocating fresh outcome declarations.
                    let mut additional = state
                        .guard
                        .nodes
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(intent.callee_name().len()))
                        .and_then(|n| n.checked_add(state.memory.as_ref().map_or(0, |m| m.nodes)))
                        .and_then(|n| n.checked_add(6))
                        .ok_or(ReadOnlySourceError::Budget(
                            "native aggregate event inventory",
                        ))?;
                    for id in args {
                        additional = additional
                            .checked_add(read(&state, *id, boundary)?.term.nodes)
                            .ok_or(ReadOnlySourceError::Budget(
                                "native aggregate event inventory",
                            ))?;
                    }
                    native_nodes = native_nodes
                        .checked_add(additional)
                        .filter(|n| *n <= MAX_TOTAL_QUERY_NODES)
                        .ok_or(ReadOnlySourceError::Budget(
                            "native aggregate event inventory",
                        ))?;
                    let arguments = args
                        .iter()
                        .zip(intent.argument_codecs())
                        .map(|(id, codec)| {
                            let value = read(&state, *id, boundary)?;
                            if value.kind != native_aggregates::codec_kind(*codec) {
                                return Err(boundary.error("native aggregate argument kind"));
                            }
                            Ok(value.term.expr.clone())
                        })
                        .collect::<Result<Vec<_>, ReadOnlySourceError>>()?;
                    let observed = memory_observations
                        .as_mut()
                        .ok_or(boundary.error("missing native event memory"))?;
                    let (fields, after, normal) = observed.definitions.record_outcome()?;
                    let before = state
                        .memory
                        .clone()
                        .ok_or(boundary.error("missing native prior world"))?;
                    let continuation = guarded(&state.guard, &normal, false)?;
                    native_events.push(native_aggregates::PendingNativeAggregateEvent {
                        intent: intent.clone(),
                        binding: *binding,
                        site: node.site,
                        guard: state.guard.expr.clone(),
                        arguments,
                        before: before.expr,
                        record: native_aggregates::PendingNativeAggregateEvent::product(
                            intent.layout().clone(),
                            &fields,
                        ),
                        after: after.expr.clone(),
                        normal: normal.expr,
                        continuation: continuation.expr.clone(),
                    });
                    if state
                        .records
                        .insert(
                            *record,
                            native_aggregates::RecordState {
                                layout: intent.layout().clone(),
                                fields,
                            },
                        )
                        .is_some()
                        || state.values.contains_key(record)
                    {
                        return Err(boundary.error("repeated native aggregate record definition"));
                    }
                    state.memory = Some(after);
                    state.guard = continuation;
                    state
                        .records
                        .retain(|id, _| liveness.needed(state.block, instruction + 1, *id));
                    liveness.retain_before(state.block, instruction + 1, &mut state.values);
                    continue;
                }
                Operation::AggregateField {
                    record,
                    layout,
                    field,
                } => {
                    if !profile.native_events() {
                        return Err(boundary.error("aggregate field outside native event profile"));
                    }
                    let value = state
                        .records
                        .get(record)
                        .ok_or(boundary.error("undefined or nondominating aggregate record"))?;
                    if &value.layout != layout
                        || *field >= 2
                        || node.result.map(|(_, k)| k)
                            != Some(native_aggregates::codec_kind(layout.fields()[*field]))
                    {
                        return Err(boundary.error("aggregate field type/index/layout"));
                    }
                    let term = value.fields[*field].clone();
                    if !liveness.needed(state.block, instruction + 1, *record) {
                        state.records.remove(record);
                    }
                    result(term, None)?
                }
                Operation::ExactModuleCall {
                    callee,
                    args,
                    results,
                } => {
                    if !profile.conditional_calls()
                        || node.result.is_some()
                        || args.len() > 8
                        || results.is_empty()
                        || results.len() > 8
                    {
                        return Err(boundary.error("conditional exact-call shape"));
                    }
                    let effects = conditional
                        .as_mut()
                        .ok_or(boundary.error("missing conditional effect inventory"))?;
                    if effects.calls.len() >= MAX_READS {
                        return Err(ReadOnlySourceError::Budget("conditional call events"));
                    }
                    let arguments = args
                        .iter()
                        .map(|id| {
                            read(&state, *id, boundary).and_then(|v| word(v, boundary).cloned())
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let before = state
                        .memory
                        .clone()
                        .ok_or(boundary.error("missing pre-call memory"))?;
                    let observed = memory_observations
                        .as_mut()
                        .ok_or(boundary.error("missing call memory inventory"))?;
                    let widths: Vec<_> = results.iter().map(|(_, kind)| kind.bits()).collect();
                    let (values, after, normal) = observed.definitions.call_outcomes(&widths)?;
                    effects.push_call(
                        node.site,
                        *callee,
                        state.guard.clone(),
                        arguments,
                        before,
                        values.clone(),
                        after.clone(),
                        normal,
                    )?;
                    state.memory = Some(after);
                    for ((id, kind), term) in results.iter().zip(values) {
                        if state
                            .values
                            .insert(
                                *id,
                                Value {
                                    kind: *kind,
                                    term,
                                    literal: None,
                                },
                            )
                            .is_some()
                        {
                            return Err(boundary.error("repeated conditional call result"));
                        }
                    }
                    liveness.retain_before(state.block, instruction + 1, &mut state.values);
                    continue;
                }
                Operation::VoidReturn => {
                    if !(profile.conditional_calls() || profile.native_events())
                        || node.result.is_some()
                    {
                        return Err(
                            boundary.error("void terminal outside conditional wrapper profile")
                        );
                    }
                    void_returns += 1;
                    memory_observations
                        .as_mut()
                        .ok_or(boundary.error("missing void memory inventory"))?
                        .returns
                        .push((
                            state.guard.clone(),
                            state
                                .memory
                                .clone()
                                .ok_or(boundary.error("missing returned memory"))?,
                        ));
                    break;
                }
                Operation::NullPointer => {
                    if !profile.conditional_calls()
                        || node.result.map(|(_, kind)| kind) != Some(Kind::Pointer)
                    {
                        return Err(
                            boundary.error("null pointer outside conditional wrapper profile")
                        );
                    }
                    result(Term::leaf(E::bv_const(0, 64)), Some(0))?
                }
                Operation::Constant(literal) => {
                    let (_, kind) = node
                        .result
                        .ok_or(boundary.error("constant has no result"))?;
                    let bits = kind.bits();
                    if kind == Kind::Pointer || bits < 64 && *literal >= (1u64 << bits) {
                        return Err(boundary.error("invalid scalar constant"));
                    }
                    result(Term::leaf(E::bv_const(*literal, bits)), Some(*literal))?
                }
                Operation::Copy(id) => read(&state, *id, boundary)?.clone(),
                Operation::Binary {
                    opcode,
                    left,
                    right,
                } => {
                    let a = read(&state, *left, boundary)?;
                    let b = read(&state, *right, boundary)?;
                    if a.kind != b.kind || a.kind == Kind::Pointer {
                        return Err(boundary.error("binary operand type"));
                    }
                    let bits = a.kind.bits();
                    let ty = if bits == 32 {
                        LirType::I32
                    } else {
                        LirType::I64
                    };
                    let term = match opcode {
                        Opcode::Iadd | Opcode::Isub
                            if bits == 64 || profile.writable() && bits == 32 =>
                        {
                            if profile.writable() {
                                // Exact scalar-memory values wrap at their
                                // actual width; no flags or overflow result
                                // are observed. Reuse the shared source codec
                                // without widening erased pointer-carrier adds.
                                // The legacy read-only transcription stays fixed.
                                a.term.binary(&b.term, 1, |a, b| {
                                    crate::trust_ir_semantics::encode_trust_ir_binop(
                                        opcode, ty, a, b,
                                    )
                                })
                            } else {
                                raw_arithmetic(opcode, bits, &a.term, &b.term)
                            }
                        }
                        Opcode::Imul if profile.writable() && matches!(bits, 32 | 64) => {
                            a.term.binary(&b.term, 1, E::bvmul)
                        }
                        Opcode::Band | Opcode::Bor | Opcode::Bxor => {
                            a.term.binary(&b.term, 1, |a, b| {
                                crate::trust_ir_semantics::encode_trust_ir_bitwise_binop(
                                    opcode, ty, a, b,
                                )
                            })
                        }
                        Opcode::Ishl | Opcode::Ushr | Opcode::Sshr
                            if (bits == 64 || profile.writable() && bits == 32)
                                && b.literal.is_some_and(|n| n < u64::from(bits)) =>
                        {
                            a.term.binary(&b.term, 1, |a, b| {
                                crate::trust_ir_semantics::encode_trust_ir_shift(opcode, ty, a, b)
                            })
                        }
                        _ => return Err(boundary.error("binary/shift outside raw profile")),
                    };
                    result(bounded(term)?, None)?
                }
                Operation::Compare {
                    condition,
                    left,
                    right,
                } => {
                    let a = read(&state, *left, boundary)?;
                    let b = read(&state, *right, boundary)?;
                    if a.kind != b.kind || a.kind == Kind::Pointer {
                        return Err(boundary.error("comparison operand type"));
                    }
                    result(bounded(raw_compare(condition, &a.term, &b.term))?, None)?
                }
                Operation::Select {
                    condition: cond,
                    then_value,
                    else_value,
                    invert,
                } => {
                    let c = read(&state, *cond, boundary)?;
                    condition(c, boundary)?;
                    let a = read(&state, *then_value, boundary)?;
                    let b = read(&state, *else_value, boundary)?;
                    if a.kind != b.kind {
                        return Err(boundary.error("select arm type"));
                    }
                    result(
                        bounded(raw_select(&c.term, &a.term, &b.term, *invert))?,
                        None,
                    )?
                }
                Operation::Offset { base, index, scale } => {
                    let base = word(read(&state, *base, boundary)?, boundary)?;
                    let index = read(&state, *index, boundary)?;
                    let offset = index
                        .literal
                        .filter(|_| index.kind == Kind::Word)
                        .and_then(|n| n.checked_mul(*scale))
                        .filter(|n| *n <= 4095)
                        .ok_or(boundary.error("nonconstant/unbounded byte offset"))?;
                    let term =
                        bounded(base.binary(&Term::leaf(E::bv_const(offset, 64)), 1, E::bvadd))?;
                    geometry_fits(&mut geometry_nodes, state.guard.nodes + base.nodes + 4)?;
                    geometry.push(
                        state
                            .guard
                            .expr
                            .clone()
                            .not_expr()
                            .or_expr(base.expr.clone().bvule(E::bv_const(u64::MAX - offset, 64))),
                    );
                    result(term, None)?
                }
                Operation::ScaledOffset {
                    base,
                    index,
                    scale,
                    signed,
                } => {
                    if !profile.writable() || !matches!(scale, 1 | 4 | 8) {
                        return Err(boundary.error("scaled offset outside scalar-memory profile"));
                    }
                    let base = read(&state, *base, boundary)?;
                    let index = read(&state, *index, boundary)?;
                    if !matches!(base.kind, Kind::Word | Kind::Pointer)
                        || index.kind != Kind::Word
                        || *signed && !index.literal.is_some_and(|n| n <= i64::MAX as u64)
                    {
                        return Err(boundary.error("scaled offset carrier or signed dynamic index"));
                    }
                    let offset = bounded(index.term.binary(
                        &Term::leaf(E::bv_const(*scale, 64)),
                        1,
                        E::bvmul,
                    ))?;
                    let term = bounded(base.term.binary(&offset, 1, E::bvadd))?;
                    geometry_fits(
                        &mut geometry_nodes,
                        state.guard.nodes + index.term.nodes + base.term.nodes + offset.nodes + 8,
                    )?;
                    let nonwrapping = index
                        .term
                        .expr
                        .clone()
                        .bvule(E::bv_const(u64::MAX / scale, 64))
                        .and_expr(
                            base.term
                                .expr
                                .clone()
                                .bvule(E::bv_const(u64::MAX, 64).bvsub(offset.expr)),
                        );
                    geometry.push(state.guard.expr.clone().not_expr().or_expr(nonwrapping));
                    result(term, None)?
                }
                Operation::ZeroExtend(id) => {
                    let value = read(&state, *id, boundary)?;
                    if !profile.writable()
                        || value.kind != Kind::Word32
                        || node.result.map(|(_, kind)| kind) != Some(Kind::Word)
                    {
                        return Err(
                            boundary.error("zero extension requires exact 32-to-64 carriers")
                        );
                    }
                    result(
                        bounded(value.term.unary(1, |e| {
                            crate::trust_ir_semantics::encode_trust_ir_uextend(32, 64, e)
                        }))?,
                        value.literal,
                    )?
                }
                Operation::Load { address, alignment } => {
                    if reads.len() >= MAX_READS {
                        return Err(ReadOnlySourceError::Budget("guarded reads"));
                    }
                    let address = word(read(&state, *address, boundary)?, boundary)?;
                    let nodes = address
                        .nodes
                        .checked_mul(8)
                        .and_then(|n| n.checked_add(72))
                        .ok_or(ReadOnlySourceError::Budget("load expression overflow"))?;
                    if nodes > super::super::MAX_NODES {
                        return Err(ReadOnlySourceError::Budget("load expression tree"));
                    }
                    let loaded = result(
                        Term {
                            expr: encode_load_le(memory, &address.expr, 8),
                            nodes,
                        },
                        None,
                    )?;
                    if loaded.kind == Kind::Boolean
                        || !alignment.is_power_of_two()
                        || *alignment > 8
                    {
                        return Err(boundary.error("load codec/alignment"));
                    }
                    geometry_fits(
                        &mut geometry_nodes,
                        state.guard.nodes + address.nodes * 2 + 9,
                    )?;
                    let valid = address
                        .expr
                        .clone()
                        .bvule(E::bv_const(u64::MAX - 7, 64))
                        .and_expr(
                            address
                                .expr
                                .clone()
                                .bvand(E::bv_const(*alignment - 1, 64))
                                .eq_expr(E::bv_const(0, 64)),
                        );
                    geometry.push(state.guard.expr.clone().not_expr().or_expr(valid));
                    reads.push(Read {
                        site: node.site,
                        guard: state.guard.clone(),
                        address: address.clone(),
                        alignment: *alignment,
                        kind: loaded.kind,
                        byte_width: 8,
                    });
                    loaded
                }
                Operation::MemoryLoad {
                    address,
                    alignment,
                    byte_width,
                } => {
                    if !profile.writable()
                        || !matches!(byte_width, 4 | 8)
                        || !alignment.is_power_of_two()
                        || *alignment > 8
                    {
                        return Err(boundary.error("scalar-memory load codec/alignment"));
                    }
                    if reads.len() >= MAX_READS {
                        return Err(ReadOnlySourceError::Budget("guarded reads"));
                    }
                    let address = read(&state, *address, boundary)?;
                    if !matches!(address.kind, Kind::Word | Kind::Pointer) {
                        return Err(boundary.error("scalar-memory load address carrier"));
                    }
                    let current = state
                        .memory
                        .as_ref()
                        .ok_or(boundary.error("missing current memory"))?;
                    let n = *byte_width as usize;
                    // Exact LE load tree: n copies of memory/address, byte
                    // extensions, adds, shifts and ORs. Preflight before cloning.
                    let nodes = current
                        .nodes
                        .checked_add(address.term.nodes)
                        .and_then(|v| v.checked_mul(n))
                        .and_then(|v| v.checked_add(7 * n - 5))
                        .filter(|v| *v <= super::super::MAX_NODES)
                        .ok_or(ReadOnlySourceError::Budget(
                            "current-memory load expression",
                        ))?;
                    let loaded = result(
                        Term {
                            expr: encode_load_le(&current.expr, &address.term.expr, *byte_width),
                            nodes,
                        },
                        None,
                    )?;
                    if loaded.kind.bits() != byte_width * 8 || loaded.kind == Kind::Boolean {
                        return Err(boundary.error("scalar-memory load result width"));
                    }
                    if profile.native_target() {
                        target.access(
                            node.site,
                            &state.guard,
                            &address.term,
                            &loaded.term,
                            current,
                            current,
                            true,
                            *byte_width,
                            *alignment,
                        )?;
                    }
                    access_geometry(
                        &mut geometry,
                        &mut geometry_nodes,
                        &state.guard,
                        &address.term,
                        *byte_width,
                        *alignment,
                    )?;
                    reads.push(Read {
                        site: node.site,
                        guard: state.guard.clone(),
                        address: address.term.clone(),
                        alignment: *alignment,
                        kind: loaded.kind,
                        byte_width: *byte_width,
                    });
                    loaded
                }
                Operation::Store {
                    address,
                    value,
                    alignment,
                    byte_width,
                } => {
                    if !profile.writable()
                        || node.result.is_some()
                        || !matches!(byte_width, 4 | 8)
                        || !alignment.is_power_of_two()
                        || *alignment > 8
                    {
                        return Err(boundary.error("scalar-memory store shape/alignment"));
                    }
                    let address = read(&state, *address, boundary)?;
                    let value = read(&state, *value, boundary)?;
                    if !matches!(address.kind, Kind::Word | Kind::Pointer)
                        || !(matches!(value.kind, Kind::Word | Kind::Word32)
                            || profile.conditional_calls() && value.kind == Kind::Pointer)
                        || value.kind.bits() != byte_width * 8
                    {
                        return Err(boundary.error("scalar-memory store address/value codec"));
                    }
                    let current = state
                        .memory
                        .as_ref()
                        .ok_or(boundary.error("missing current memory"))?;
                    let n = *byte_width as usize;
                    let nodes = address
                        .term
                        .nodes
                        .checked_add(value.term.nodes)
                        .and_then(|v| v.checked_mul(n))
                        .and_then(|v| v.checked_add(current.nodes))
                        .and_then(|v| v.checked_add(4 * n - 2))
                        .filter(|v| *v <= super::super::MAX_NODES)
                        .ok_or(ReadOnlySourceError::Budget(
                            "current-memory store expression",
                        ))?;
                    let observed = memory_observations
                        .as_mut()
                        .ok_or(boundary.error("missing memory inventory"))?;
                    if observed.writes.len() >= MAX_READS {
                        return Err(ReadOnlySourceError::Budget("guarded writes"));
                    }
                    access_geometry(
                        &mut geometry,
                        &mut geometry_nodes,
                        &state.guard,
                        &address.term,
                        *byte_width,
                        *alignment,
                    )?;
                    observed.writes.push(scalar_memory::Write {
                        site: node.site,
                        guard: state.guard.clone(),
                        address: address.term.clone(),
                        byte_width: *byte_width,
                        alignment: *alignment,
                    });
                    if let Some(effects) = &mut conditional {
                        effects.push_store(
                            node.site,
                            state.guard.clone(),
                            address.term.clone(),
                            value.term.clone(),
                            *byte_width,
                            *alignment,
                            value.kind,
                        )?;
                    }
                    let next_memory = observed.definitions.bind(
                        Term {
                            expr: encode_store_le(
                                &current.expr,
                                &address.term.expr,
                                &value.term.expr,
                                *byte_width,
                            ),
                            nodes,
                        },
                        memory_sort(),
                    )?;
                    if profile.native_target() {
                        target.access(
                            node.site,
                            &state.guard,
                            &address.term,
                            &value.term,
                            current,
                            &next_memory,
                            false,
                            *byte_width,
                            *alignment,
                        )?;
                    }
                    state.memory = Some(next_memory);
                    liveness.release_after(state.block, instruction, None, &mut state.values);
                    continue;
                }
                Operation::VectorReturn(ids) => {
                    if !profile.vector_returns()
                        || node.result.is_some()
                        || !(1..=8).contains(&ids.len())
                    {
                        return Err(
                            boundary.error("typed vector terminal outside scalar-return profile")
                        );
                    }
                    if vector_returns.len() >= MAX_PATHS {
                        return Err(ReadOnlySourceError::Budget("return paths"));
                    }
                    // Admit the entire retained path/lane inventory BEFORE
                    // cloning expressions. No lane or cold return is dropped.
                    let mut nodes = state.guard.nodes;
                    for (id, kind) in ids {
                        let value = read(&state, *id, boundary)?;
                        if value.kind != *kind
                            || value.term.expr.try_bv_width().ok() != Some(kind.bits())
                        {
                            return Err(boundary.error("vector return operand codec differs"));
                        }
                        nodes = nodes
                            .checked_add(value.term.nodes)
                            .ok_or(ReadOnlySourceError::Budget("vector return inventory"))?;
                    }
                    vector_return_nodes = vector_return_nodes
                        .checked_add(nodes)
                        .filter(|n| *n <= MAX_TOTAL_QUERY_NODES)
                        .ok_or(ReadOnlySourceError::Budget("vector return inventory"))?;
                    if let Some((_, first)) = vector_returns.first()
                        && (first.len() != ids.len()
                            || first
                                .iter()
                                .zip(ids)
                                .any(|(value, (_, kind))| value.kind != *kind))
                    {
                        return Err(boundary.error("vector return paths disagree on arity/codec"));
                    }
                    let values = ids
                        .iter()
                        .map(|(id, _)| read(&state, *id, boundary).cloned())
                        .collect::<Result<Vec<_>, _>>()?;
                    vector_returns.push((state.guard.clone(), values));
                    memory_observations
                        .as_mut()
                        .ok_or(boundary.error("missing vector memory inventory"))?
                        .returns
                        .push((
                            state.guard.clone(),
                            state
                                .memory
                                .clone()
                                .ok_or(boundary.error("missing returned memory"))?,
                        ));
                    break;
                }
                Operation::Return(id) => {
                    let value = read(&state, *id, boundary)?;
                    if value.kind != Kind::Word {
                        return Err(boundary.error("return is not a full 64-bit word"));
                    }
                    if returns.len() >= MAX_PATHS {
                        return Err(ReadOnlySourceError::Budget("return paths"));
                    }
                    returns.push((state.guard.clone(), value.term.clone()));
                    if let Some(observed) = &mut memory_observations {
                        observed.returns.push((
                            state.guard.clone(),
                            state
                                .memory
                                .clone()
                                .ok_or(boundary.error("missing returned memory"))?,
                        ));
                    }
                    break;
                }
                Operation::Jump { target, args } => {
                    fork_fits(&state)?;
                    pending.push(edge(
                        &state,
                        blocks[target],
                        args,
                        state.guard.clone(),
                        boundary,
                        &liveness,
                    )?);
                    break;
                }
                Operation::Branch {
                    condition: id,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => {
                    forks += 1;
                    if forks >= MAX_PATHS {
                        return Err(ReadOnlySourceError::Budget("control forks"));
                    }
                    fork_fits(&state)?;
                    let condition = condition(read(&state, *id, boundary)?, boundary)?;
                    let yes = guarded(&state.guard, &condition, false)?;
                    let no = guarded(&state.guard, &condition, true)?;
                    pending.push(edge(
                        &state,
                        blocks[then_target],
                        then_args,
                        yes,
                        boundary,
                        &liveness,
                    )?);
                    pending.push(edge(
                        &state,
                        blocks[else_target],
                        else_args,
                        no,
                        boundary,
                        &liveness,
                    )?);
                    break;
                }
            };
            let (id, kind) = node
                .result
                .ok_or(boundary.error("value node has no result"))?;
            // Pointers lower to word carriers, but each endpoint must preserve
            // its own exact result kind. No Bool-width metadata laundering.
            let width = kind.bits();
            if value.kind != kind || value.term.expr.try_bv_width().ok() != Some(width) {
                return Err(boundary.error("result type or repeated SSA definition"));
            }
            let mut value = value;
            if let Some(observed) = &mut memory_observations
                && value.literal.is_none()
            {
                value.term = observed
                    .definitions
                    .bind(value.term, crate::smt::SmtSort::BitVec(width))?;
            }
            if value.kind != kind
                || value.term.expr.try_bv_width().ok() != Some(width)
                || state.values.insert(id, value).is_some()
            {
                return Err(boundary.error("result type or repeated SSA definition"));
            }
            // Evaluate and validate even dead instructions before releasing
            // their value. Guards, geometry and read demands live separately.
            // Full-graph validation guarantees a following terminator here.
            liveness.release_after(state.block, instruction, Some(id), &mut state.values);
        }
    }
    if returns.is_empty() && vector_returns.is_empty() && void_returns == 0 {
        return Err(boundary.error("no return paths"));
    }
    if usize::from(void_returns > 0)
        + usize::from(!returns.is_empty())
        + usize::from(!vector_returns.is_empty())
        > 1
    {
        return Err(boundary.error("mixed scalar and void terminal"));
    }
    let has_scalar_result = !returns.is_empty();
    let mut result = Term::leaf(E::bv_const(0, 64));
    for (guard, value) in returns {
        let nodes = result
            .nodes
            .checked_add(guard.nodes)
            .and_then(|n| n.checked_add(value.nodes))
            .and_then(|n| n.checked_add(1))
            .ok_or(ReadOnlySourceError::Budget("return expression overflow"))?;
        if nodes > MAX_QUERY_NODES {
            return Err(ReadOnlySourceError::Budget("complete return expression"));
        }
        result = Term {
            expr: E::ite(guard.expr, value.expr, result.expr),
            nodes,
        };
    }
    let vector = if let Some((_, first)) = vector_returns.first() {
        let mut lanes = first
            .iter()
            .map(|value| Term::leaf(E::bv_const(0, value.kind.bits())))
            .collect::<Vec<_>>();
        let mut total = lanes.len();
        for (guard, values) in vector_returns {
            for (lane, value) in lanes.iter_mut().zip(values) {
                let nodes = lane
                    .nodes
                    .checked_add(guard.nodes)
                    .and_then(|n| n.checked_add(value.term.nodes))
                    .and_then(|n| n.checked_add(1))
                    .filter(|n| *n <= MAX_QUERY_NODES)
                    .ok_or(ReadOnlySourceError::Budget(
                        "complete vector return expression",
                    ))?;
                total = total
                    .checked_add(guard.nodes)
                    .and_then(|n| n.checked_add(value.term.nodes))
                    .and_then(|n| n.checked_add(1))
                    .filter(|n| *n <= MAX_TOTAL_QUERY_NODES)
                    .ok_or(ReadOnlySourceError::Budget(
                        "complete vector return inventory",
                    ))?;
                *lane = Term {
                    expr: E::ite(guard.expr.clone(), value.term.expr, lane.expr.clone()),
                    nodes,
                };
            }
        }
        Some(lanes)
    } else {
        None
    };
    Ok(Observations {
        target,
        native: native_events,
        result: has_scalar_result.then_some(result),
        vector,
        conditional,
        reads,
        geometry,
        geometry_nodes,
        memory: memory_observations,
    })
}
