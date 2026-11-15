// Copyright 2026 Andrew Yates | Apache-2.0

//! Complete ordered internal scalar results and byte memory at actual target
//! endpoints. This is not a C aggregate ABI claim: ONE Struct return remains
//! outside this profile. Provider calls, private frames and their permissions
//! keep their existing refusals. Every lane and every path is retained.

use super::*;
use crate::source_bound_frame::ScalarReturnSourceQueries;
use trust_cg_lower::abi::{AppleAArch64ABI, ArgLocation};

pub struct ScalarReturnTargetQueries<'a> {
    source: &'a ScalarReturnSourceQueries<'a>,
    endpoint: ScalarMemoryTargetEndpoint<'a>,
    returns: Vec<ProofObligation>,
    memory: Vec<ProofObligation>,
    reads: Vec<ScalarMemoryTargetAccess>,
    writes: Vec<ScalarMemoryTargetAccess>,
    read_demands: Vec<ProofObligation>,
    write_demands: Vec<ProofObligation>,
    definitions: Vec<E>,
}

impl<'a> ScalarReturnTargetQueries<'a> {
    pub fn source(&self) -> &'a ScalarReturnSourceQueries<'a> {
        self.source
    }
    pub fn endpoint(&self) -> ScalarMemoryTargetEndpoint<'a> {
        self.endpoint
    }
    /// Path-major, then original source result order. No result is a status-only
    /// proxy for the remaining values.
    pub fn return_obligations(&self) -> &[ProofObligation] {
        &self.returns
    }
    pub fn memory_obligations(&self) -> &[ProofObligation] {
        &self.memory
    }
    pub fn reads(&self) -> &[ScalarMemoryTargetAccess] {
        &self.reads
    }
    pub fn writes(&self) -> &[ScalarMemoryTargetAccess] {
        &self.writes
    }
    pub fn read_obligations(&self) -> &[ProofObligation] {
        &self.read_demands
    }
    pub fn write_obligations(&self) -> &[ProofObligation] {
        &self.write_demands
    }
    pub fn encoding_definitions(&self) -> &[E] {
        &self.definitions
    }
}

fn registers(source: &ScalarReturnSourceQueries<'_>) -> Result<Vec<usize>, ReadOnlyTargetError> {
    if source
        .module()
        .target_info
        .as_ref()
        .map(|target| target.triple.as_str())
        != Some("aarch64-apple-darwin")
        || !matches!(
            source.source().calling_conv,
            trust_ir::CallingConv::C | trust_ir::CallingConv::Fast
        )
    {
        return Err(ReadOnlyTargetError::Machine(
            "requires declared AArch64/Darwin C or internal Fast source ABI",
        ));
    }
    let returns = &source.lir().signature.returns;
    if !(1..=8).contains(&returns.len())
        || returns.iter().any(|ty| *ty != trust_cg_lower::Type::I64)
        || source.return_codecs().len() != returns.len()
    {
        return Err(ReadOnlyTargetError::Machine(
            "requires complete 64-bit scalar return sequence",
        ));
    }
    let locations = AppleAArch64ABI::classify_returns(returns);
    locations
        .iter()
        .enumerate()
        .map(|(index, location)| match location {
            ArgLocation::Reg(register) if usize::from(register.encoding()) == index => Ok(index),
            _ => Err(ReadOnlyTargetError::Machine(
                "non-scalar or indirect result ABI",
            )),
        })
        .collect()
}

fn bind<'a>(
    source: &'a ScalarReturnSourceQueries<'a>,
    endpoint: ScalarMemoryTargetEndpoint<'a>,
    steps: Vec<Step>,
    stage: Stage,
    registers: &[usize],
) -> Result<ScalarReturnTargetQueries<'a>, ReadOnlyTargetError> {
    let source_returns = source.return_obligations();
    if source_returns.len() != registers.len() || source_returns.is_empty() {
        return Err(ReadOnlyTargetError::Control(
            "source return inventory differs",
        ));
    }
    let mut current = 0;
    let observed = observe_returning_at(
        &steps,
        &source_returns[0].inputs,
        source.lir().signature.params.len(),
        Some(stage),
        Some(registers),
        &mut current,
    )
    .map_err(|error| match error {
        ReadOnlyTargetError::Budget(reason) => ReadOnlyTargetError::BudgetAt {
            step: current,
            reason,
        },
        other => other,
    })?;
    if observed.vector_returns.len() != observed.memories.len()
        || observed.vector_returns.is_empty()
    {
        return Err(ReadOnlyTargetError::Control(
            "target vector return/memory inventory differs",
        ));
    }
    let source_byte = &source.memory_obligation().trust_ir_expr;
    let source_byte_nodes = expression_nodes(source_byte, None, MAX_QUERY_NODES)?;
    let lane_nodes = source_returns
        .iter()
        .map(|q| expression_nodes(&q.trust_ir_expr, None, MAX_QUERY_NODES))
        .collect::<Result<Vec<_>, _>>()?;
    let premises = source
        .geometry()
        .iter()
        .chain(&source.definitions()[..source.source_definition_count()])
        .chain(&observed.definitions)
        .cloned()
        .collect::<Vec<_>>();
    let premise_nodes = bounded_sum(
        premises
            .iter()
            .map(|p| expression_nodes(p, None, MAX_QUERY_NODES))
            .collect::<Result<Vec<_>, _>>()?,
        MAX_TOTAL_QUERY_NODES,
    )?;
    let premise_work = bounded_sum([premise_nodes, premises.len(), 1], MAX_TOTAL_QUERY_NODES)?;
    let mut total = 0;
    let mut reserve = |nodes: usize| -> Result<(), ReadOnlyTargetError> {
        let work = bounded_sum([nodes, premise_work, 2], MAX_QUERY_NODES)?;
        total = bounded_sum([total, work], MAX_TOTAL_QUERY_NODES)?;
        Ok(())
    };
    let mut returns = Vec::new();
    let mut memories = Vec::new();
    for ((guard, values), memory) in observed.vector_returns.iter().zip(&observed.memories) {
        if values.len() != source_returns.len() {
            return Err(ReadOnlyTargetError::Control("target result arity differs"));
        }
        for ((value, original), nodes) in values.iter().zip(source_returns).zip(&lane_nodes) {
            reserve(bounded_sum(
                [guard.nodes, *nodes, value.nodes, 4],
                MAX_QUERY_NODES,
            )?)?;
            returns.push(
                guard
                    .expr
                    .clone()
                    .not_expr()
                    .or_expr(original.trust_ir_expr.clone().eq_expr(value.expr.clone())),
            );
        }
        reserve(bounded_sum(
            [guard.nodes, source_byte_nodes, memory.nodes, 7],
            MAX_QUERY_NODES,
        )?)?;
        memories.push(
            guard.expr.clone().not_expr().or_expr(
                source_byte
                    .clone()
                    .eq_expr(E::select(memory.expr.clone(), E::var("observe", 64))),
            ),
        );
    }
    let original_reads = originals(source.source_reads())?;
    let original_writes = originals(source.source_writes())?;
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    for (accesses, originals, out) in [
        (&observed.reads, &original_reads, &mut reads),
        (&observed.writes, &original_writes, &mut writes),
    ] {
        for access in accesses {
            let conclusion = demand(access, originals)?;
            reserve(conclusion.nodes)?;
            out.push(conclusion.expr);
        }
    }
    let mut inputs = source_returns[0].inputs.clone();
    inputs.extend((source.lir().signature.params.len()..31).map(|i| (format!("entry_x{i}"), 64)));
    inputs.extend(["entry_n", "entry_z", "entry_c", "entry_v"].map(|n| (n.into(), 1)));
    let label = match endpoint {
        ScalarMemoryTargetEndpoint::Machine(_) => "actual MachIR",
        ScalarMemoryTargetEndpoint::FinalBytes(_) => "independent final words",
    };
    let pending = |kind: &str, index: usize, expression| ProofObligation {
        name: format!("Original scalar-return Core -> {label} {kind} {index}"),
        trust_ir_expr: E::BoolConst(true),
        aarch64_expr: expression,
        inputs: inputs.clone(),
        preconditions: premises.clone(),
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    let obligations = |kind, values: Vec<E>| {
        values
            .into_iter()
            .enumerate()
            .map(|(index, value)| pending(kind, index, value))
            .collect()
    };
    Ok(ScalarReturnTargetQueries {
        source,
        endpoint,
        returns: obligations("ordered result", returns),
        memory: obligations("all final bytes", memories),
        read_demands: obligations("read demand", reads),
        write_demands: obligations("write demand", writes),
        reads: observed.reads.into_iter().map(access).collect(),
        writes: observed.writes.into_iter().map(access).collect(),
        definitions: observed.definitions,
    })
}

pub fn bind_scalar_return_machine<'a>(
    source: &'a ScalarReturnSourceQueries<'a>,
    machine: &'a MachFunction,
) -> Result<ScalarReturnTargetQueries<'a>, ReadOnlyTargetError> {
    let registers = registers(source)?;
    let signature: trust_cg_ir::function::Signature = (&source.lir().signature).into();
    if machine.name != source.source().name || machine.signature != signature {
        return Err(ReadOnlyTargetError::Machine(
            "function identity/signature differs from original Core",
        ));
    }
    let steps = machine::adapt_returns(machine, &registers)?;
    bind(
        source,
        ScalarMemoryTargetEndpoint::Machine(machine),
        steps,
        Stage::Machine,
        &registers,
    )
}

pub fn bind_scalar_return_bytes<'a>(
    source: &'a ScalarReturnSourceQueries<'a>,
    code: &'a [u8],
) -> Result<ScalarReturnTargetQueries<'a>, ReadOnlyTargetError> {
    let registers = registers(source)?;
    let steps = bytes::adapt_profile(code, Profile::ScalarMemory)?;
    bind(
        source,
        ScalarMemoryTargetEndpoint::FinalBytes(code),
        steps,
        Stage::Words,
        &registers,
    )
}
