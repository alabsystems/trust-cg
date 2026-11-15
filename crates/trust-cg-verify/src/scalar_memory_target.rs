// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Pending ORIGINAL Core → allocated machine/final-word scalar-memory
//! relations. Every return compares full X0 and every final byte; each actual
//! read/write remains a separate demand. Exact acyclic definitions and ORIGINAL
//! geometry are the only premises. No target geometry, region-disjointness,
//! temporal initialization, caller permission or native seal follows.

use super::*;
use crate::source_bound_frame::{ScalarMemoryAccess, ScalarMemorySourceQueries};

#[path = "scalar_return_target.rs"]
mod return_vectors;
pub use return_vectors::{
    ScalarReturnTargetQueries, bind_scalar_return_bytes, bind_scalar_return_machine,
};

#[derive(Debug, Clone, Copy)]
pub enum ScalarMemoryTargetEndpoint<'a> {
    Machine(&'a MachFunction),
    FinalBytes(&'a [u8]),
}

#[derive(Debug, Clone)]
pub struct ScalarMemoryTargetAccess {
    pub step: usize,
    pub lane: usize,
    pub guard: E,
    pub address: E,
    pub byte_width: u32,
    pub alignment: u64,
}

pub struct ScalarMemoryTargetQueries<'a> {
    source: &'a ScalarMemorySourceQueries<'a>,
    endpoint: ScalarMemoryTargetEndpoint<'a>,
    returns: Vec<ProofObligation>,
    memory: Vec<ProofObligation>,
    read_demands: Vec<ProofObligation>,
    write_demands: Vec<ProofObligation>,
    reads: Vec<ScalarMemoryTargetAccess>,
    writes: Vec<ScalarMemoryTargetAccess>,
    definitions: Vec<E>,
}

impl<'a> ScalarMemoryTargetQueries<'a> {
    pub fn source(&self) -> &'a ScalarMemorySourceQueries<'a> {
        self.source
    }
    pub fn endpoint(&self) -> ScalarMemoryTargetEndpoint<'a> {
        self.endpoint
    }
    pub fn return_obligations(&self) -> &[ProofObligation] {
        &self.returns
    }
    pub fn memory_obligations(&self) -> &[ProofObligation] {
        &self.memory
    }
    pub fn read_obligations(&self) -> &[ProofObligation] {
        &self.read_demands
    }
    pub fn write_obligations(&self) -> &[ProofObligation] {
        &self.write_demands
    }
    pub fn reads(&self) -> &[ScalarMemoryTargetAccess] {
        &self.reads
    }
    pub fn writes(&self) -> &[ScalarMemoryTargetAccess] {
        &self.writes
    }
    /// Complete endpoint-local equations. Original Core equations are obtained
    /// separately from source(); every obligation includes BOTH inventories.
    pub fn encoding_definitions(&self) -> &[E] {
        &self.definitions
    }
}

fn access(read: Read) -> ScalarMemoryTargetAccess {
    ScalarMemoryTargetAccess {
        step: read.step,
        lane: read.lane,
        guard: read.guard.expr,
        address: read.address.expr,
        byte_width: read.byte_width,
        alignment: read.alignment,
    }
}

struct Original<'a> {
    access: &'a ScalarMemoryAccess,
    guard_nodes: usize,
    address_nodes: usize,
}

fn originals(accesses: &[ScalarMemoryAccess]) -> Result<Vec<Original<'_>>, ReadOnlyTargetError> {
    accesses
        .iter()
        .map(|access| {
            Ok(Original {
                access,
                guard_nodes: expression_nodes(&access.guard, None, MAX_QUERY_NODES)?,
                address_nodes: expression_nodes(&access.address, None, MAX_QUERY_NODES)?,
            })
        })
        .collect()
}

fn demand(read: &Read, originals: &[Original<'_>]) -> Result<Term, ReadOnlyTargetError> {
    let (expr, nodes) = crate::scalar_memory_relations::demand(
        (&read.guard.expr, read.guard.nodes),
        (&read.address.expr, read.address.nodes),
        read.byte_width,
        read.alignment,
        originals.iter().map(|original| {
            (
                original.access.guard.clone(),
                original.guard_nodes,
                original.access.address.clone(),
                original.address_nodes,
                original.access.byte_width,
                original.access.alignment,
            )
        }),
        MAX_QUERY_NODES,
    )
    .map_err(ReadOnlyTargetError::Budget)?;
    Ok(Term { expr, nodes })
}

fn bind<'a>(
    source: &'a ScalarMemorySourceQueries<'a>,
    endpoint: ScalarMemoryTargetEndpoint<'a>,
    steps: Vec<Step>,
    stage: Stage,
) -> Result<ScalarMemoryTargetQueries<'a>, ReadOnlyTargetError> {
    let abi_arity = source.lir().signature.params.len();
    let mut current = 0;
    let observed = observe_profile_at(
        &steps,
        &source.status_obligation().inputs,
        abi_arity,
        Some(stage),
        &mut current,
    )
    .map_err(|error| match error {
        ReadOnlyTargetError::Budget(reason) => ReadOnlyTargetError::BudgetAt {
            step: current,
            reason,
        },
        other => other,
    })?;
    if observed.memories.len() != observed.returns.len() {
        return Err(ReadOnlyTargetError::Control(
            "target return/memory snapshot mismatch",
        ));
    }
    let source_status = &source.status_obligation().trust_ir_expr;
    let source_byte = &source.memory_obligation().trust_ir_expr;
    let source_status_nodes = expression_nodes(source_status, None, MAX_QUERY_NODES)?;
    let source_byte_nodes = expression_nodes(source_byte, None, MAX_QUERY_NODES)?;
    let premises = source
        .source_geometry()
        .iter()
        .chain(source.original_encoding_definitions())
        .chain(&observed.definitions)
        .cloned()
        .collect::<Vec<_>>();
    // Count every premise AND plus the negated-equivalence Eq/Not envelope.
    // Reserve each entire query BEFORE retaining another conclusion/premise
    // clone; no aggregate budget is checked only after building the collection.
    let premise_nodes = bounded_sum(
        premises
            .iter()
            .map(|p| expression_nodes(p, None, MAX_QUERY_NODES))
            .collect::<Result<Vec<_>, _>>()?,
        MAX_TOTAL_QUERY_NODES,
    )?;
    let premise_work = bounded_sum([premise_nodes, premises.len(), 1], MAX_TOTAL_QUERY_NODES)?;
    let mut total = 0usize;
    let mut reserve = |nodes: usize| -> Result<(), ReadOnlyTargetError> {
        let work = bounded_sum([nodes, premise_work, 2], MAX_QUERY_NODES)?;
        total = bounded_sum([total, work], MAX_TOTAL_QUERY_NODES)?;
        Ok(())
    };
    let mut returns = Vec::new();
    let mut memories = Vec::new();
    for ((guard, value), memory) in observed.returns.iter().zip(&observed.memories) {
        let nodes = bounded_sum(
            [guard.nodes, source_status_nodes, value.nodes, 4],
            MAX_QUERY_NODES,
        )?;
        reserve(nodes)?;
        returns.push(
            guard
                .expr
                .clone()
                .not_expr()
                .or_expr(source_status.clone().eq_expr(value.expr.clone())),
        );
        let nodes = bounded_sum(
            [guard.nodes, source_byte_nodes, memory.nodes, 7],
            MAX_QUERY_NODES,
        )?;
        reserve(nodes)?;
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
    for read in &observed.reads {
        let conclusion = demand(read, &original_reads)?;
        reserve(conclusion.nodes)?;
        reads.push(conclusion.expr);
    }
    let mut writes = Vec::new();
    for write in &observed.writes {
        let conclusion = demand(write, &original_writes)?;
        reserve(conclusion.nodes)?;
        writes.push(conclusion.expr);
    }
    let mut inputs = source.status_obligation().inputs.clone();
    // `observe` stays free and does NOT initialize X4 in the four-arg action.
    inputs.extend((abi_arity..31).map(|i| (format!("entry_x{i}"), 64)));
    inputs.extend(["entry_n", "entry_z", "entry_c", "entry_v"].map(|n| (n.into(), 1)));
    let label = match endpoint {
        ScalarMemoryTargetEndpoint::Machine(_) => "actual MachIR",
        ScalarMemoryTargetEndpoint::FinalBytes(_) => "independent final words",
    };
    let pending = |kind: &str, index: usize, expression: E| ProofObligation {
        name: format!("Original scalar-memory Core -> {label} {kind} {index}"),
        trust_ir_expr: E::BoolConst(true),
        aarch64_expr: expression,
        inputs: inputs.clone(),
        preconditions: premises.clone(),
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    let obligations = |kind: &str, conclusions: Vec<E>| {
        conclusions
            .into_iter()
            .enumerate()
            .map(|(i, e)| pending(kind, i, e))
            .collect()
    };
    Ok(ScalarMemoryTargetQueries {
        source,
        endpoint,
        returns: obligations("full status", returns),
        memory: obligations("all final bytes", memories),
        read_demands: obligations("read demand", reads),
        write_demands: obligations("write demand", writes),
        reads: observed.reads.into_iter().map(access).collect(),
        writes: observed.writes.into_iter().map(access).collect(),
        definitions: observed.definitions,
    })
}

/// Pending relations for the complete allocated endpoint. No query is solved
/// and source applicability never becomes a skipped unsupported target row.
pub fn bind_scalar_memory_machine<'a>(
    source: &'a ScalarMemorySourceQueries<'a>,
    target: &'a MachFunction,
) -> Result<ScalarMemoryTargetQueries<'a>, ReadOnlyTargetError> {
    let signature: trust_cg_ir::function::Signature = (&source.lir().signature).into();
    if target.name != source.source().name || target.signature != signature {
        return Err(ReadOnlyTargetError::Machine(
            "function identity/signature differs from original Core",
        ));
    }
    bind(
        source,
        ScalarMemoryTargetEndpoint::Machine(target),
        machine::adapt_profile(target, Profile::ScalarMemory)?,
        Stage::Machine,
    )
}

/// `code` is the complete FINAL word stream. This neither authorizes nor
/// applies relocations. No encoder/source/MachIR hint supplies decoded fields.
pub fn bind_scalar_memory_bytes<'a>(
    source: &'a ScalarMemorySourceQueries<'a>,
    code: &'a [u8],
) -> Result<ScalarMemoryTargetQueries<'a>, ReadOnlyTargetError> {
    bind(
        source,
        ScalarMemoryTargetEndpoint::FinalBytes(code),
        bytes::adapt_profile(code, Profile::ScalarMemory)?,
        Stage::Words,
    )
}
