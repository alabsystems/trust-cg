// Copyright 2026 Andrew Yates | Apache-2.0

//! Pending ordered scalar-return and byte-memory observations. No machine
//! return registers, call ABI, source-body theorem, caller permission or native
//! authority follows. Calls/aggregates require their separate checked owner.
//! Uses the existing graph/adapters/driver, definitions, memory and demand
//! contracts; the original word-status and conditional void profiles stay strict.

use super::*;
pub use scalar_edge_projection::ScalarEdgeCodec as ScalarReturnCodec;
use scalar_memory::{Endpoint, ScalarMemoryAccess};

#[cfg(test)]
#[path = "scalar_return_source_tests.rs"]
pub(crate) mod tests;

/// Borrowed exact endpoints and unresolved per-lane/byte/access obligations.
/// Pointer is only an original scalar codec with an erased I64 LIR carrier;
/// it never establishes storage, native ABI or physical return placement.
pub struct ScalarReturnSourceQueries<'a> {
    module: &'a Module,
    ordinal: usize,
    lir: &'a Function,
    codecs: Vec<ScalarReturnCodec>,
    returns: Vec<ProofObligation>,
    memory: ProofObligation,
    source_reads: Vec<ScalarMemoryAccess>,
    source_writes: Vec<ScalarMemoryAccess>,
    lowering_reads: Vec<ScalarMemoryAccess>,
    lowering_writes: Vec<ScalarMemoryAccess>,
    read_demands: Vec<ProofObligation>,
    write_demands: Vec<ProofObligation>,
    definitions: Vec<E>,
    source_definition_count: usize,
    geometry: Vec<E>,
}
impl<'a> ScalarReturnSourceQueries<'a> {
    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        &self.module.functions[self.ordinal]
    }
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    pub fn return_codecs(&self) -> &[ScalarReturnCodec] {
        &self.codecs
    }
    pub fn return_obligations(&self) -> &[ProofObligation] {
        &self.returns
    }
    pub fn memory_obligation(&self) -> &ProofObligation {
        &self.memory
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
    pub fn read_obligations(&self) -> &[ProofObligation] {
        &self.read_demands
    }
    pub fn write_obligations(&self) -> &[ProofObligation] {
        &self.write_demands
    }
    /// Complete semantic equations from both endpoints, never caller facts.
    pub fn definitions(&self) -> &[E] {
        &self.definitions
    }
    pub fn source_definition_count(&self) -> usize {
        self.source_definition_count
    }
    pub fn geometry(&self) -> &[E] {
        &self.geometry
    }
}

/// Construct all ordered scalar-return lanes, final byte equality and complete
/// read/write demands for original Core and retained LIR. Every path is checked;
/// each query retains every semantic definition and original geometry demand.
/// C/Fast describe source conventions only; no native placement is inferred.
pub fn bind_scalar_return_source<'a>(
    module: &'a Module,
    ordinal: usize,
    lowering: &'a Function,
) -> Result<ScalarReturnSourceQueries<'a>, ReadOnlySourceError> {
    if module.functions.len() > MAX_VALUES || module.func_types.len() > MAX_VALUES {
        return Err(ReadOnlySourceError::Budget(
            "scalar-return module inventory",
        ));
    }
    // The selected-body profile never hides uncharged unused payload hashing.
    conditional_wrapper::module_digest(module)?;
    conditional_wrapper::lowering_digest(std::slice::from_ref(lowering))?;
    let target = module
        .target_info
        .as_ref()
        .ok_or(ReadOnlySourceError::Source("missing target layout"))?;
    if target.pointer_size != 8 || target.endianness != Endianness::Little {
        return Err(ReadOnlySourceError::Source(
            "requires 64-bit little-endian pointers",
        ));
    }
    let source_graph =
        core::graph_profile(module, ordinal, Profile::ScalarReturns(Endpoint::Core))?;
    let original = &module.functions[ordinal];
    let signature = &module.func_types[original.ty.index() as usize];
    let codecs = signature
        .returns
        .iter()
        .map(|ty| {
            ScalarReturnCodec::source(ty).ok_or(ReadOnlySourceError::Source(
                "non-scalar original return codec",
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if original.name != lowering.name
        || signature.params.len() != lowering.signature.params.len()
        || codecs
            .iter()
            .map(|c| c.carrier())
            .ne(lowering.signature.returns.iter().cloned())
    {
        return Err(ReadOnlySourceError::Lowering(
            "scalar-return identity/arity/carrier differs",
        ));
    }
    let lower_graph = lir::graph_bound(
        module,
        ordinal,
        lowering,
        Profile::ScalarReturns(Endpoint::Lir),
    )?;
    if source_graph.parameters.len() != lower_graph.parameters.len() {
        return Err(ReadOnlySourceError::Lowering(
            "scalar-return input arity differs",
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
        Profile::ScalarReturns(Endpoint::Core),
    )?;
    let mut lower = graph::observe_profile(
        &lower_graph,
        &inputs,
        &entry,
        Boundary::Lowering,
        Profile::ScalarReturns(Endpoint::Lir),
    )?;
    let source_memory = source
        .memory
        .take()
        .ok_or(ReadOnlySourceError::Source("missing vector-return memory"))?;
    let lower_memory = lower.memory.take().ok_or(ReadOnlySourceError::Lowering(
        "missing vector-return memory",
    ))?;
    let source_lanes = source
        .vector
        .take()
        .ok_or(ReadOnlySourceError::Source("missing original return lanes"))?;
    let lower_lanes = lower.vector.take().ok_or(ReadOnlySourceError::Lowering(
        "missing retained return lanes",
    ))?;
    if source_lanes.len() != codecs.len() || lower_lanes.len() != codecs.len() {
        return Err(ReadOnlySourceError::Lowering(
            "observed scalar return arity differs",
        ));
    }
    let source_byte = scalar_memory::final_byte(&source_memory, &entry)?;
    let lower_byte = scalar_memory::final_byte(&lower_memory, &entry)?;
    let mut definitions = source_memory.definitions.equations.clone();
    definitions.extend(lower_memory.definitions.equations.iter().cloned());
    let premise_nodes = source.geometry_nodes
        + source_memory.definitions.nodes
        + lower_memory.definitions.nodes
        + source.geometry.len()
        + definitions.len()
        + 1;
    let mut total = 0usize;
    let mut relations = Vec::new();
    for (index, (source, lower)) in source_lanes.into_iter().zip(lower_lanes).enumerate() {
        let width = match codecs[index].carrier() {
            trust_cg_lower::Type::I64 => 64,
            trust_cg_lower::Type::I32 => 32,
            trust_cg_lower::Type::B1 => 1,
            _ => unreachable!(),
        };
        if source.expr.try_bv_width().ok() != Some(width)
            || lower.expr.try_bv_width().ok() != Some(width)
        {
            return Err(ReadOnlySourceError::Lowering(
                "observed scalar return width differs",
            ));
        }
        reserve_query(&mut total, source.nodes + lower.nodes + premise_nodes + 1)?;
        relations.push((
            format!("return lane {index} {:?}", codecs[index]),
            source,
            lower,
        ));
    }
    reserve_query(
        &mut total,
        source_byte.nodes + lower_byte.nodes + premise_nodes + 1,
    )?;
    relations.push(("all final bytes".into(), source_byte, lower_byte));
    for (index, read) in lower.reads.iter().enumerate() {
        let conclusion = scalar_memory::demand(
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
        let conclusion = scalar_memory::demand(
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
    // Admit all queries before cloning their complete shared premise inventory.
    let mut premises = source.geometry.clone();
    premises.extend(definitions.iter().cloned());
    let mut obligations = relations.into_iter().map(|(name, source, lower)| {
        pending(
            format!("Original scalar-return Core -> LIR {name}"),
            source.expr,
            lower.expr,
            &inputs,
            &premises,
        )
    });
    let returns = obligations.by_ref().take(codecs.len()).collect();
    let memory = obligations.next().unwrap();
    let read_demands = obligations.by_ref().take(lower.reads.len()).collect();
    let write_demands = obligations.collect();
    Ok(ScalarReturnSourceQueries {
        module,
        ordinal,
        lir: lowering,
        codecs,
        returns,
        memory,
        source_reads: source
            .reads
            .iter()
            .map(scalar_memory::access)
            .collect::<Result<_, _>>()?,
        source_writes: source_memory
            .writes
            .iter()
            .map(scalar_memory::write_access)
            .collect(),
        lowering_reads: lower
            .reads
            .iter()
            .map(scalar_memory::access)
            .collect::<Result<_, _>>()?,
        lowering_writes: lower_memory
            .writes
            .iter()
            .map(scalar_memory::write_access)
            .collect(),
        read_demands,
        write_demands,
        definitions,
        source_definition_count: source_memory.definitions.equations.len(),
        geometry: source.geometry,
    })
}
