// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Original Core/LIR queries for bounded read-only integer computations.
//!
//! This is an untrusted query constructor, NOT checked equivalence, a memory
//! capability, frame owner or publication receipt. Callers still owe live,
//! initialized readable storage and the original pointer/provenance contract.
//! Actual machine/byte correspondence, private-frame separation and independent
//! replay remain separate gates. Reads require ordinary Normal memory whose
//! relevant bytes are stable throughout execution: read-only code alone does
//! not exclude concurrent, signal-handler or device writes. One arbitrary
//! entry array preserves read-read aliases, not temporal mutation.

use super::{E, Term, raw_arithmetic, raw_compare, raw_select};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
use std::collections::{HashMap, HashSet};
use trust_cg_lower::instructions::{IntCC, Opcode};
use trust_cg_lower::{Function, Type as LirType};
use trust_ir::{Endianness, Module};

#[path = "read_only_source_core.rs"]
mod core;
#[path = "read_only_source_graph.rs"]
mod graph;
#[path = "read_only_source_lir.rs"]
mod lir;

#[path = "scalar_memory_source.rs"]
pub mod scalar_memory;

#[path = "conditional_wrapper_source.rs"]
pub mod conditional_wrapper;

#[path = "scalar_edge_projection.rs"]
pub mod scalar_edge_projection;

#[path = "scalar_return_source.rs"]
pub mod scalar_returns;

#[path = "native_aggregate_target.rs"]
pub mod native_aggregate_target;
#[path = "native_aggregate_source.rs"]
pub mod native_aggregates;

#[cfg(all(test, feature = "source-defined-call"))]
#[path = "read_only_source_licensed_tests.rs"]
mod licensed_tests;

#[cfg(test)]
#[path = "read_only_source_ty_tests.rs"]
mod ty_tests;

#[cfg(test)]
#[path = "read_only_source_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "read_only_source_budget_tests.rs"]
mod budget_tests;

#[cfg(test)]
#[path = "read_only_source_liveness_tests.rs"]
mod liveness_tests;

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "read_only_source_native_tests.rs"]
mod native_tests;

const MAX_BLOCKS: usize = 16;
const MAX_INSTRUCTIONS: usize = 256;
const MAX_VALUES: usize = 384;
const MAX_PATHS: usize = 64;
const MAX_READS: usize = 64;
const MAX_ENV_NODES: usize = 65_536;
const MAX_QUERY_NODES: usize = 32_768;
const MAX_GEOMETRY_NODES: usize = 32_768;
const MAX_TOTAL_QUERY_NODES: usize = 262_144;

/// Original location within one retained endpoint; never an instruction license.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadOnlySite {
    pub block: u32,
    pub instruction: usize,
}

/// Scalar codec retained by the original source. Lowering erases pointer types
/// to I64, but that erasure never establishes pointee ownership or readability.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReadOnlyType {
    Word,
    Boolean,
    Pointer,
}
// Private wider observation codecs do not expand the public read-only owner.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Word,
    Word32,
    Boolean,
    Pointer,
}

impl Kind {
    fn bits(self) -> u32 {
        match self {
            Self::Word | Self::Pointer => 64,
            Self::Word32 => 32,
            Self::Boolean => 1,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Profile {
    ReadOnly,
    ScalarMemory(scalar_memory::Endpoint),
    ScalarReturns(scalar_memory::Endpoint),
    ConditionalWrapper(scalar_memory::Endpoint),
    NativeAggregates(scalar_memory::Endpoint),
    NativeTarget,
}

impl Profile {
    fn native_events(self) -> bool {
        matches!(self, Self::NativeAggregates(_))
    }
    fn native_target(self) -> bool {
        self == Self::NativeTarget
    }
    fn conditional_calls(self) -> bool {
        matches!(self, Self::ConditionalWrapper(_))
    }

    fn vector_returns(self) -> bool {
        matches!(self, Self::ScalarReturns(_) | Self::NativeAggregates(_))
    }

    fn writable(self) -> bool {
        matches!(
            self,
            Self::ScalarMemory(_)
                | Self::ScalarReturns(_)
                | Self::ConditionalWrapper(_)
                | Self::NativeAggregates(_)
                | Self::NativeTarget
        )
    }
}

/// Conditional caller demand at this exact source/lowering load.
///
/// Whenever `guard` holds, the entire nonwrapping `byte_width` interval at
/// `address` must be live, readable, initialized and effectively aligned.
/// These terms refer to the SAME arbitrary entry memory and ABI words as the
/// return query. They are requirements, not proofs that any caller supplies it.
/// The relevant ordinary Normal-memory bytes must remain stable for the call;
/// no concurrent/signal/MMIO-writer exclusion follows from the body's loads.
#[derive(Debug, Clone)]
pub struct ReadOnlyLoad {
    pub site: ReadOnlySite,
    pub guard: E,
    pub address: E,
    pub byte_width: u32,
    pub alignment: u64,
    pub value_type: ReadOnlyType,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ReadOnlySourceError {
    #[error("unsupported native target instruction at {site:?}: {opcode:?}")]
    TargetInstruction {
        site: ReadOnlySite,
        opcode: trust_cg_ir::AArch64Opcode,
    },
    #[error("invalid or unsupported original read-only Core: {0}")]
    Source(&'static str),
    #[error("read-only lowering rejected: {0}")]
    Lowering(&'static str),
    #[error("read-only query resource limit: {0}")]
    Budget(&'static str),
}

/// Privately constructed, borrowed inputs and UNRESOLVED semantic queries.
/// It supplies no Checked metric, proof strength, or instruction/native credit.
pub struct ReadOnlySourceQueries<'a> {
    module: &'a Module,
    ordinal: usize,
    lir: &'a Function,
    source_reads: Vec<ReadOnlyLoad>,
    lowering_reads: Vec<ReadOnlyLoad>,
    return_obligation: ProofObligation,
    load_obligations: Vec<ProofObligation>,
    original_result: std::sync::Arc<E>,
    original_parameter_count: usize,
}

impl<'a> ReadOnlySourceQueries<'a> {
    pub(crate) fn original_result(&self) -> &std::sync::Arc<E> {
        &self.original_result
    }
    pub(crate) fn original_parameter_count(&self) -> usize {
        self.original_parameter_count
    }

    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        &self.module.functions[self.ordinal]
    }
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    pub fn read_requirements(&self) -> &[ReadOnlyLoad] {
        &self.source_reads
    }
    pub fn lowering_reads(&self) -> &[ReadOnlyLoad] {
        &self.lowering_reads
    }
    pub fn return_obligation(&self) -> &ProofObligation {
        &self.return_obligation
    }
    /// Each target read must be covered by a simultaneously live source read
    /// of this exact address/width with sufficient alignment. Return equality
    /// alone would miss extra dead or hoisted potentially faulting loads.
    pub fn load_obligations(&self) -> &[ProofObligation] {
        &self.load_obligations
    }
}

// Borrowed endpoint adapters produce only a bounded observation graph for the
// shared query driver; this is not a compiler IR or executable normalization.
struct Graph {
    entry: u32,
    parameters: Vec<(u32, Kind)>,
    blocks: Vec<Block>,
}
struct Block {
    id: u32,
    parameters: Vec<(u32, Kind)>,
    nodes: Vec<Node>,
}
struct Node {
    site: ReadOnlySite,
    result: Option<(u32, Kind)>,
    operation: Operation,
}
impl Node {
    fn definition_ids(&self) -> impl Iterator<Item = u32> + '_ {
        self.results()
            .map(|(id, _)| id)
            .chain(match &self.operation {
                Operation::NativeAggregateCall { record, .. } => Some(*record),
                _ => None,
            })
    }
    fn results(&self) -> impl Iterator<Item = (u32, Kind)> + '_ {
        self.result.into_iter().chain(
            match &self.operation {
                Operation::ExactModuleCall { results, .. } => results.as_slice(),
                Operation::NativeTarget(native_aggregate_target::Operation::Call {
                    results,
                    ..
                }) => results.as_slice(),
                _ => &[],
            }
            .iter()
            .copied(),
        )
    }
}

enum Operation {
    NativeTarget(native_aggregate_target::Operation),
    NativeTargetFrontier,
    NativeAggregateCall {
        intent: trust_cg_lower::aggregate_call_transport::AggregateCallIntent,
        binding: trust_cg_lower::instructions::DirectCallBinding,
        record: u32,
        args: Vec<u32>,
    },
    AggregateField {
        record: u32,
        layout: trust_cg_lower::aggregate_call_transport::FlatAggregateLayout,
        field: usize,
    },
    ExactModuleCall {
        callee: u32,
        args: Vec<u32>,
        results: Vec<(u32, Kind)>,
    },
    VoidReturn,
    NullPointer,
    Constant(u64),
    Copy(u32),
    Binary {
        opcode: Opcode,
        left: u32,
        right: u32,
    },
    Compare {
        condition: IntCC,
        left: u32,
        right: u32,
    },
    Select {
        condition: u32,
        then_value: u32,
        else_value: u32,
        invert: bool,
    },
    Offset {
        base: u32,
        index: u32,
        scale: u64,
    },
    Load {
        address: u32,
        alignment: u64,
    },
    MemoryLoad {
        address: u32,
        alignment: u64,
        byte_width: u32,
    },
    Store {
        address: u32,
        value: u32,
        alignment: u64,
        byte_width: u32,
    },
    ZeroExtend(u32),
    ScaledOffset {
        base: u32,
        index: u32,
        scale: u64,
        signed: bool,
    },
    Return(u32),
    VectorReturn(Vec<(u32, Kind)>),
    Jump {
        target: u32,
        args: Vec<u32>,
    },
    Branch {
        condition: u32,
        then_target: u32,
        then_args: Vec<u32>,
        else_target: u32,
        else_args: Vec<u32>,
    },
}

#[derive(Clone)]
struct Value {
    kind: Kind,
    term: Term,
    literal: Option<u64>,
}
struct Read {
    site: ReadOnlySite,
    guard: Term,
    address: Term,
    alignment: u64,
    kind: Kind,
    byte_width: u32,
}
struct Observations {
    target: native_aggregate_target::Effects,
    native: Vec<native_aggregates::PendingNativeAggregateEvent>,
    result: Option<Term>,
    vector: Option<Vec<Term>>,
    conditional: Option<conditional_wrapper::ObservedEffects>,
    reads: Vec<Read>,
    geometry: Vec<E>,
    geometry_nodes: usize,
    memory: Option<scalar_memory::MemoryObservations>,
}

#[derive(Clone, Copy)]
enum Boundary {
    Source,
    Lowering,
}
impl Boundary {
    fn error(self, detail: &'static str) -> ReadOnlySourceError {
        match self {
            Self::Source => ReadOnlySourceError::Source(detail),
            Self::Lowering => ReadOnlySourceError::Lowering(detail),
        }
    }
}

fn pending(
    name: String,
    source: E,
    lowering: E,
    inputs: &[(String, u32)],
    geometry: &[E],
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr: source,
        aarch64_expr: lowering,
        inputs: inputs.to_vec(),
        preconditions: geometry.to_vec(),
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

fn public_read(read: &Read) -> Result<ReadOnlyLoad, ReadOnlySourceError> {
    let value_type = match read.kind {
        Kind::Word => ReadOnlyType::Word,
        Kind::Boolean => ReadOnlyType::Boolean,
        Kind::Pointer => ReadOnlyType::Pointer,
        Kind::Word32 => {
            return Err(ReadOnlySourceError::Source(
                "narrow memory cannot acquire a read-only owner",
            ));
        }
    };
    if read.byte_width != 8 {
        return Err(ReadOnlySourceError::Source(
            "non-eight-byte memory cannot acquire a read-only owner",
        ));
    }
    Ok(ReadOnlyLoad {
        site: read.site,
        guard: read.guard.expr.clone(),
        address: read.address.expr.clone(),
        byte_width: 8,
        alignment: read.alignment,
        value_type,
    })
}

// Count logical serialization/traversal work, not distinct Arc allocations or
// measured RSS. Preconditions recur in every query even when AST nodes share.
fn reserve_query(used: &mut usize, nodes: usize) -> Result<(), ReadOnlySourceError> {
    let total = used
        .checked_add(nodes)
        .filter(|n| *n <= MAX_TOTAL_QUERY_NODES)
        .ok_or(ReadOnlySourceError::Budget(
            "aggregate obligation expressions",
        ))?;
    *used = total;
    Ok(())
}

fn load_query_nodes(guard: usize, coverage: usize) -> Result<usize, ReadOnlySourceError> {
    guard
        .checked_add(coverage)
        .and_then(|n| n.checked_add(2))
        .filter(|n| *n <= MAX_QUERY_NODES)
        .ok_or(ReadOnlySourceError::Budget("load-demand expression"))
}

/// Construct the original-source/LIR relation and guarded load-demand queries.
/// Source applicability is decided FIRST; unsupported target shapes cannot
/// downgrade a supported source into a coverage skip. Construction never
/// solves the queries or authenticates storage, a pointer claim or native code.
pub fn bind_read_only_source<'a>(
    module: &'a Module,
    ordinal: usize,
    lowering: &'a Function,
) -> Result<ReadOnlySourceQueries<'a>, ReadOnlySourceError> {
    require_readonly_target(module)?;
    let source = core::graph(module, ordinal)?;
    bind_read_only_source_graph(module, ordinal, lowering, source)
}

fn require_readonly_target(module: &Module) -> Result<(), ReadOnlySourceError> {
    let target = module
        .target_info
        .as_ref()
        .ok_or(ReadOnlySourceError::Source("missing target layout"))?;
    if target.pointer_size != 8 || target.endianness != Endianness::Little {
        return Err(ReadOnlySourceError::Source(
            "requires 64-bit little-endian pointers",
        ));
    }
    Ok(())
}

fn bind_read_only_source_graph<'a>(
    module: &'a Module,
    ordinal: usize,
    lowering: &'a Function,
    source: Graph,
) -> Result<ReadOnlySourceQueries<'a>, ReadOnlySourceError> {
    require_readonly_target(module)?;
    let lower = lir::graph_bound(module, ordinal, lowering, Profile::ReadOnly)?;
    if source.parameters.len() != lower.parameters.len() {
        return Err(ReadOnlySourceError::Lowering(
            "signature arity differs from original Core",
        ));
    }
    let original = &module.functions[ordinal];
    if original.name != lowering.name {
        return Err(ReadOnlySourceError::Lowering(
            "function identity differs from original Core",
        ));
    }
    let inputs: Vec<_> = (0..source.parameters.len())
        .map(|i| (format!("abi_x{i}"), 64))
        .collect();
    // A free array, NOT memory_proofs::symbolic_memory's uniform-byte array.
    let memory = E::uf("entry_memory", vec![], memory_sort());
    let source = graph::observe(&source, &inputs, &memory, Boundary::Source)?;
    let lower = graph::observe(&lower, &inputs, &memory, Boundary::Lowering)?;
    let source_result = source
        .result
        .as_ref()
        .ok_or(ReadOnlySourceError::Source("missing scalar return"))?;
    let lower_result = lower
        .result
        .as_ref()
        .ok_or(ReadOnlySourceError::Lowering("missing scalar return"))?;
    let mut total_nodes = 0;
    reserve_query(
        &mut total_nodes,
        source_result.nodes + lower_result.nodes + source.geometry_nodes + 1,
    )?;
    let mut load_queries = Vec::with_capacity(lower.reads.len());
    for target in &lower.reads {
        let mut coverage = E::BoolConst(false);
        let mut nodes = 1usize;
        for original in &source.reads {
            if original.alignment < target.alignment {
                continue;
            }
            nodes = nodes
                .checked_add(original.guard.nodes)
                .and_then(|n| n.checked_add(original.address.nodes))
                .and_then(|n| n.checked_add(target.address.nodes))
                .and_then(|n| n.checked_add(3))
                .ok_or(ReadOnlySourceError::Budget(
                    "load-demand expression overflow",
                ))?;
            if nodes > MAX_QUERY_NODES {
                return Err(ReadOnlySourceError::Budget("load-demand expression"));
            }
            coverage = coverage.or_expr(
                original.guard.expr.clone().and_expr(
                    original
                        .address
                        .expr
                        .clone()
                        .eq_expr(target.address.expr.clone()),
                ),
            );
        }
        let query_nodes = load_query_nodes(target.guard.nodes, nodes)?;
        reserve_query(&mut total_nodes, query_nodes + source.geometry_nodes + 2)?;
        load_queries.push(target.guard.expr.clone().not_expr().or_expr(coverage));
    }
    // Preflight ALL queries before cloning the source precondition inventory.
    let return_obligation = pending(
        "Original read-only Core -> LIR full status/return".into(),
        source_result.expr.clone(),
        lower_result.expr.clone(),
        &inputs,
        &source.geometry,
    );
    let load_obligations = load_queries
        .into_iter()
        .enumerate()
        .map(|(index, target_valid)| {
            pending(
                format!("Original read-only Core -> LIR load demand {index}"),
                E::BoolConst(true),
                target_valid,
                &inputs,
                &source.geometry,
            )
        })
        .collect();
    Ok(ReadOnlySourceQueries {
        original_result: std::sync::Arc::new(source_result.expr.clone()),
        original_parameter_count: inputs.len(),
        module,
        ordinal,
        lir: lowering,
        source_reads: source
            .reads
            .iter()
            .map(public_read)
            .collect::<Result<_, _>>()?,
        lowering_reads: lower
            .reads
            .iter()
            .map(public_read)
            .collect::<Result<_, _>>()?,
        return_obligation,
        load_obligations,
    })
}

/// Distinct source-defined-call query owner retaining the actual checked
/// source/Core entry. Queries remain unresolved and grant no native entry,
/// pointer access, frame or machine correspondence by themselves.
#[cfg(feature = "source-defined-call")]
pub struct LicensedReadOnlySourceQueries<'a, 'entry, 'module> {
    entry: &'a trust_ir_build::core_execution::CheckedReadonlyEightLicensedEntry<'entry, 'module>,
    queries: ReadOnlySourceQueries<'a>,
}
#[cfg(feature = "source-defined-call")]
impl<'a, 'entry, 'module> LicensedReadOnlySourceQueries<'a, 'entry, 'module> {
    pub fn core_entry(
        &self,
    ) -> &'a trust_ir_build::core_execution::CheckedReadonlyEightLicensedEntry<'entry, 'module>
    {
        self.entry
    }
    pub fn queries(&self) -> &ReadOnlySourceQueries<'a> {
        &self.queries
    }
}

/// Retain the ordinary diagnostic metadata refusal. This separate constructor
/// consumes the original checked whole-entry/source-family owner and enforces
/// the DEFAULT codegen license, without exposing a permissive policy knob.
#[cfg(feature = "source-defined-call")]
pub fn bind_licensed_read_only_source<'a, 'entry, 'module>(
    entry: &'a trust_ir_build::core_execution::CheckedReadonlyEightLicensedEntry<'entry, 'module>,
    lowering: &'a Function,
) -> Result<LicensedReadOnlySourceQueries<'a, 'entry, 'module>, String> {
    let family = entry.source_family();
    let module = family.module();
    let (_, callee) = entry.core_entry().functions_in(module)?;
    trust_cg_lower::CodegenLicensePolicy::default()
        .enforce_module(module)
        .map_err(|error| format!("licensed readonly default codegen license: {error}"))?;
    let ordinal = module
        .functions
        .iter()
        .position(|function| function.id == callee)
        .ok_or("licensed readonly actual callee absent")?;
    let graph = core::graph_licensed_readonly(module, ordinal, family)
        .map_err(|error| error.to_string())?;
    let queries = bind_read_only_source_graph(module, ordinal, lowering, graph)
        .map_err(|error| error.to_string())?;
    Ok(LicensedReadOnlySourceQueries { entry, queries })
}
