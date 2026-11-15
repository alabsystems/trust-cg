// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Pending scalar status/byte-memory relations, not native/caller authority.
//!
//! Uses the same original Core/LIR graph and execution driver as the immutable
//! read-only owner, under a distinct writable profile. Exact acyclic equations
//! share observed values/memory without assuming aliases away. Every equation
//! participates in every query; they are semantic definitions, not caller
//! geometry. Rust transcription, initialization/provenance, live permission,
//! external Normal-memory noninterference and actual native/frame/publication
//! remain separate required gates. Byte equality is not shadow-state equality.

use super::*;
use crate::scalar_memory_definitions::{
    Definitions as SharedDefinitions, Error as DefinitionError, Limits as DefinitionLimits, Stage,
};
use crate::smt::SmtSort;

#[cfg(test)]
#[path = "scalar_memory_source_ty_tests.rs"]
mod ty_tests;

#[cfg(test)]
#[path = "scalar_memory_source_tests.rs"]
pub(super) mod tests;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Endpoint {
    Core,
    Lir,
    Machine,
}

/// Distinct codecs retain the public read-only surface unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarMemoryCodec {
    Word32,
    Word64,
    Pointer,
}

/// A conditional access DEMAND at its actual point, not a permission receipt.
/// Read bytes must be initialized/live/readable then; writes need live writable
/// storage. A modeled store does not establish provenance or caller authority.
#[derive(Debug, Clone)]
pub struct ScalarMemoryAccess {
    pub site: ReadOnlySite,
    pub guard: E,
    pub address: E,
    pub byte_width: u32,
    pub alignment: u64,
    pub codec: ScalarMemoryCodec,
}

pub(super) struct Write {
    pub(super) site: ReadOnlySite,
    pub(super) guard: Term,
    pub(super) address: Term,
    pub(super) byte_width: u32,
    pub(super) alignment: u64,
}

/// Closed namespaces cannot collide with abi_xN/entry_memory/observe inputs or
/// each other. An execution occurrence, not SSA/site identity, chooses a name.
/// RHS references are checked against only already defined same-stage symbols.
pub(super) struct Definitions {
    shared: SharedDefinitions,
}

impl std::ops::Deref for Definitions {
    type Target = SharedDefinitions;

    fn deref(&self) -> &Self::Target {
        &self.shared
    }
}

impl Definitions {
    pub(super) fn native_target_input(&mut self, sort: SmtSort) -> Result<E, DefinitionError> {
        self.shared.native_target_input(sort)
    }
    pub(super) fn record_outcome(
        &mut self,
    ) -> Result<([Term; 2], Term, Term), ReadOnlySourceError> {
        self.shared
            .conditional_record_outcome()
            .map(|(fields, memory, normal)| {
                (
                    fields.map(Term::leaf),
                    Term::leaf(memory),
                    Term::leaf(normal),
                )
            })
            .map_err(|error| match error {
                DefinitionError::Invalid(reason) => ReadOnlySourceError::Source(reason),
                DefinitionError::Budget(reason) => ReadOnlySourceError::Budget(reason),
            })
    }
    pub(super) fn conditional(endpoint: Endpoint) -> Self {
        let mut value = Self::new(endpoint);
        value.shared.enable_conditional_call_inputs();
        value
    }

    pub(super) fn call_outcomes(
        &mut self,
        widths: &[u32],
    ) -> Result<(Vec<Term>, Term, Term), ReadOnlySourceError> {
        self.shared
            .conditional_call_outcomes(widths)
            .map(|(values, memory, normal)| {
                (
                    values.into_iter().map(Term::leaf).collect(),
                    Term::leaf(memory),
                    Term::leaf(normal),
                )
            })
            .map_err(|error| match error {
                DefinitionError::Invalid(reason) => ReadOnlySourceError::Source(reason),
                DefinitionError::Budget(reason) => ReadOnlySourceError::Budget(reason),
            })
    }

    pub(super) fn new(endpoint: Endpoint) -> Self {
        Self {
            shared: SharedDefinitions::new(
                match endpoint {
                    Endpoint::Core => Stage::Core,
                    Endpoint::Lir => Stage::Lir,
                    Endpoint::Machine => Stage::Machine,
                },
                // Preserve the original source namespace and all its limits.
                8,
                DefinitionLimits {
                    rhs_nodes: super::super::MAX_NODES,
                    collection_nodes: MAX_GEOMETRY_NODES,
                    occurrences: MAX_INSTRUCTIONS * MAX_PATHS,
                },
            ),
        }
    }

    pub(super) fn bind(&mut self, value: Term, sort: SmtSort) -> Result<Term, ReadOnlySourceError> {
        self.shared
            .bind(value.expr, value.nodes, sort)
            .map(Term::leaf)
            .map_err(|error| match error {
                DefinitionError::Invalid(reason) => ReadOnlySourceError::Source(reason),
                DefinitionError::Budget(reason) => ReadOnlySourceError::Budget(reason),
            })
    }
}

pub(super) struct MemoryObservations {
    pub(super) definitions: Definitions,
    pub(super) writes: Vec<Write>,
    pub(super) returns: Vec<(Term, Term)>,
}

impl MemoryObservations {
    pub(super) fn conditional(endpoint: Endpoint) -> Self {
        Self {
            definitions: Definitions::conditional(endpoint),
            writes: Vec::new(),
            returns: Vec::new(),
        }
    }

    pub(super) fn new(endpoint: Endpoint) -> Self {
        Self {
            definitions: Definitions::new(endpoint),
            writes: Vec::new(),
            returns: Vec::new(),
        }
    }
}

/// Source and retained LIR share one privately assembled pending inventory.
/// There is no completion certificate or Checked/native/publication capability.
pub struct ScalarMemorySourceQueries<'a> {
    module: &'a Module,
    ordinal: usize,
    lir: &'a Function,
    source_reads: Vec<ScalarMemoryAccess>,
    source_writes: Vec<ScalarMemoryAccess>,
    lowering_reads: Vec<ScalarMemoryAccess>,
    lowering_writes: Vec<ScalarMemoryAccess>,
    status: ProofObligation,
    memory: ProofObligation,
    read_demands: Vec<ProofObligation>,
    write_demands: Vec<ProofObligation>,
    definitions: Vec<E>,
    source_definition_count: usize,
    geometry: Vec<E>,
}

impl<'a> ScalarMemorySourceQueries<'a> {
    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        &self.module.functions[self.ordinal]
    }
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    pub fn source_reads(&self) -> &[ScalarMemoryAccess] {
        &self.source_reads
    }
    pub fn source_writes(&self) -> &[ScalarMemoryAccess] {
        &self.source_writes
    }
    pub fn lowering_reads(&self) -> &[ScalarMemoryAccess] {
        &self.lowering_reads
    }
    pub fn lowering_writes(&self) -> &[ScalarMemoryAccess] {
        &self.lowering_writes
    }
    pub fn status_obligation(&self) -> &ProofObligation {
        &self.status
    }
    pub fn memory_obligation(&self) -> &ProofObligation {
        &self.memory
    }
    pub fn read_obligations(&self) -> &[ProofObligation] {
        &self.read_demands
    }
    pub fn write_obligations(&self) -> &[ProofObligation] {
        &self.write_demands
    }
    /// Exact semantic equations, distinguished from external source geometry.
    pub fn encoding_definitions(&self) -> &[E] {
        &self.definitions
    }
    /// Complete ORIGINAL Core-stage equations, with an explicit construction
    /// boundary. Target relations need no unrelated LIR definitions or name
    /// filtering. Existing Core/LIR obligations still retain both inventories.
    pub fn original_encoding_definitions(&self) -> &[E] {
        &self.definitions[..self.source_definition_count]
    }
    pub fn source_geometry(&self) -> &[E] {
        &self.geometry
    }
}

fn codec(kind: Kind) -> Result<ScalarMemoryCodec, ReadOnlySourceError> {
    match kind {
        Kind::Word => Ok(ScalarMemoryCodec::Word64),
        Kind::Word32 => Ok(ScalarMemoryCodec::Word32),
        Kind::Pointer => Ok(ScalarMemoryCodec::Pointer),
        Kind::Boolean => Err(ReadOnlySourceError::Source(
            "Boolean memory is outside scalar profile",
        )),
    }
}

pub(super) fn access(read: &Read) -> Result<ScalarMemoryAccess, ReadOnlySourceError> {
    Ok(ScalarMemoryAccess {
        site: read.site,
        guard: read.guard.expr.clone(),
        address: read.address.expr.clone(),
        byte_width: read.byte_width,
        alignment: read.alignment,
        codec: codec(read.kind)?,
    })
}

pub(super) fn write_access(write: &Write) -> ScalarMemoryAccess {
    ScalarMemoryAccess {
        site: write.site,
        guard: write.guard.expr.clone(),
        address: write.address.expr.clone(),
        byte_width: write.byte_width,
        alignment: write.alignment,
        codec: if write.byte_width == 4 {
            ScalarMemoryCodec::Word32
        } else {
            ScalarMemoryCodec::Word64
        },
    }
}

pub(super) fn final_byte(
    observed: &MemoryObservations,
    entry: &E,
) -> Result<Term, ReadOnlySourceError> {
    let observe = E::var("observe", 64);
    let mut result = Term {
        expr: E::select(entry.clone(), observe.clone()),
        nodes: 3,
    };
    for (guard, memory) in &observed.returns {
        let nodes = result
            .nodes
            .checked_add(guard.nodes)
            .and_then(|n| n.checked_add(memory.nodes + 3))
            .filter(|n| *n <= MAX_QUERY_NODES)
            .ok_or(ReadOnlySourceError::Budget(
                "scalar-memory final-byte observation",
            ))?;
        result = Term {
            expr: E::ite(
                guard.expr.clone(),
                E::select(memory.expr.clone(), observe.clone()),
                result.expr,
            ),
            nodes,
        };
    }
    Ok(result)
}

// A free byte observer covers unions of original intervals, allowing legitimate
// store splitting/coalescing. Matching final bytes never replaces this demand.
pub(super) fn demand(
    target_guard: &Term,
    target_address: &Term,
    width: u32,
    alignment: u64,
    originals: impl Iterator<Item = (Term, Term, u32, u64)>,
) -> Result<Term, ReadOnlySourceError> {
    let (expr, nodes) = crate::scalar_memory_relations::demand(
        (&target_guard.expr, target_guard.nodes),
        (&target_address.expr, target_address.nodes),
        width,
        alignment,
        originals.map(|(g, a, w, align)| (g.expr, g.nodes, a.expr, a.nodes, w, align)),
        MAX_QUERY_NODES,
    )
    .map_err(ReadOnlySourceError::Budget)?;
    Ok(Term { expr, nodes })
}

/// Bind original scalar Core and independently adapted retained LIR. Source
/// applicability precedes target admission. Does not discharge any obligation.
pub fn bind_scalar_memory_source<'a>(
    module: &'a Module,
    ordinal: usize,
    lowering: &'a Function,
) -> Result<ScalarMemorySourceQueries<'a>, ReadOnlySourceError> {
    let target = module
        .target_info
        .as_ref()
        .ok_or(ReadOnlySourceError::Source("missing target layout"))?;
    if target.pointer_size != 8 || target.endianness != Endianness::Little {
        return Err(ReadOnlySourceError::Source(
            "requires 64-bit little-endian pointers",
        ));
    }
    let source_graph = core::graph_profile(module, ordinal, Profile::ScalarMemory(Endpoint::Core))?;
    let lower_graph = lir::graph_bound(
        module,
        ordinal,
        lowering,
        Profile::ScalarMemory(Endpoint::Lir),
    )?;
    if source_graph.parameters.len() != lower_graph.parameters.len()
        || module.functions[ordinal].name != lowering.name
    {
        return Err(ReadOnlySourceError::Lowering(
            "scalar-memory signature or function identity differs",
        ));
    }
    let mut inputs: Vec<_> = (0..source_graph.parameters.len())
        .map(|i| (format!("abi_x{i}"), 64))
        .collect();
    inputs.push(("observe".into(), 64));
    let entry = E::uf("entry_memory", Vec::new(), memory_sort());
    let mut source = graph::observe_profile(
        &source_graph,
        &inputs,
        &entry,
        Boundary::Source,
        Profile::ScalarMemory(Endpoint::Core),
    )?;
    let mut lower = graph::observe_profile(
        &lower_graph,
        &inputs,
        &entry,
        Boundary::Lowering,
        Profile::ScalarMemory(Endpoint::Lir),
    )?;
    let source_memory = source.memory.take().ok_or(ReadOnlySourceError::Source(
        "missing original memory observation",
    ))?;
    let lower_memory = lower.memory.take().ok_or(ReadOnlySourceError::Lowering(
        "missing lowered memory observation",
    ))?;
    let source_byte = final_byte(&source_memory, &entry)?;
    let lower_byte = final_byte(&lower_memory, &entry)?;
    let mut definitions = source_memory.definitions.equations.clone();
    definitions.extend(lower_memory.definitions.equations.iter().cloned());
    // Include every connective inserted by negated_equivalence, not only
    // the premise trees. The old read-only request spelling is untouched.
    let premise_nodes = source.geometry_nodes
        + source_memory.definitions.nodes
        + lower_memory.definitions.nodes
        + source.geometry.len()
        + definitions.len()
        + 1;
    let source_result = source
        .result
        .take()
        .ok_or(ReadOnlySourceError::Source("missing scalar status"))?;
    let lower_result = lower
        .result
        .take()
        .ok_or(ReadOnlySourceError::Lowering("missing scalar status"))?;
    let mut total = 0usize;
    let mut relations = Vec::new();
    reserve_query(
        &mut total,
        source_result.nodes + lower_result.nodes + premise_nodes + 1,
    )?;
    relations.push(("full status".to_owned(), source_result, lower_result));
    reserve_query(
        &mut total,
        source_byte.nodes + lower_byte.nodes + premise_nodes + 1,
    )?;
    relations.push(("all final bytes".to_owned(), source_byte, lower_byte));
    for (index, read) in lower.reads.iter().enumerate() {
        let conclusion = demand(
            &read.guard,
            &read.address,
            read.byte_width,
            read.alignment,
            source.reads.iter().map(|r| {
                (
                    r.guard.clone(),
                    r.address.clone(),
                    r.byte_width,
                    r.alignment,
                )
            }),
        )?;
        reserve_query(&mut total, conclusion.nodes + premise_nodes + 2)?;
        relations.push((
            format!("read demand {index}"),
            Term::leaf(E::BoolConst(true)),
            conclusion,
        ));
    }
    for (index, write) in lower_memory.writes.iter().enumerate() {
        let conclusion = demand(
            &write.guard,
            &write.address,
            write.byte_width,
            write.alignment,
            source_memory.writes.iter().map(|w| {
                (
                    w.guard.clone(),
                    w.address.clone(),
                    w.byte_width,
                    w.alignment,
                )
            }),
        )?;
        reserve_query(&mut total, conclusion.nodes + premise_nodes + 2)?;
        relations.push((
            format!("write demand {index}"),
            Term::leaf(E::BoolConst(true)),
            conclusion,
        ));
    }
    // Reserve each complete query before retaining another demand or cloning
    // its premises; local bounds must not hide aggregate expression growth.
    let mut premises = source.geometry.clone();
    premises.extend(definitions.iter().cloned());
    let mut obligations = relations.into_iter().map(|(name, source, lower)| {
        pending(
            format!("Original scalar-memory Core -> LIR {name}"),
            source.expr,
            lower.expr,
            &inputs,
            &premises,
        )
    });
    let status = obligations.next().unwrap();
    let memory = obligations.next().unwrap();
    let read_demands = obligations.by_ref().take(lower.reads.len()).collect();
    let write_demands = obligations.collect();
    Ok(ScalarMemorySourceQueries {
        module,
        ordinal,
        lir: lowering,
        source_reads: source.reads.iter().map(access).collect::<Result<_, _>>()?,
        source_writes: source_memory.writes.iter().map(write_access).collect(),
        lowering_reads: lower.reads.iter().map(access).collect::<Result<_, _>>()?,
        lowering_writes: lower_memory.writes.iter().map(write_access).collect(),
        status,
        memory,
        read_demands,
        write_demands,
        definitions,
        source_definition_count: source_memory.definitions.equations.len(),
        geometry: source.geometry,
    })
}
