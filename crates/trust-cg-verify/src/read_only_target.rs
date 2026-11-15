// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Pending original-source relations for bounded, frameless A64 code.
//!
//! MachIR and final words have independent adapters. This driver composes their
//! own architectural register/flag effects, visits BOTH arms of every branch,
//! and requires every instruction to be reachable in an acyclic graph. Each
//! return has a guarded full-X0 query; each load has a guarded source-demand
//! query, including discarded/dead loads. No target constraint is added to the
//! original source's premises. These are unresolved queries, NOT Checked
//! execution, memory permission, frame ownership, relocation or replay proof.
//!
//! The initial profile writes only X0–X17, does not use SP, and has no stores,
//! calls, atomics or system effects. This is checked from the actual endpoint,
//! not inferred from a zero frame-layout metric or the source's read-only tag.
//! Stable ordinary Normal-memory, caller liveness/provenance/readability and
//! independent proof/publication gates remain external requirements.
//! Addresses use the untagged byte-array model; RET additionally assumes GCS
//! is disabled. Neither a pointer type nor this constructor establishes those
//! machine/host conditions. An enabled GCS return has additional memory and
//! architectural-state effects outside this pending profile.
//!
//! The distinct scalar-memory constructors reuse this observer with current
//! byte memory, exact stage-local definitions, 32/64-bit loads/stores and
//! paired-load lanes. They compare original Core status/final bytes and retain
//! every read/write demand; the original read-only API/admission is unchanged.
//! Neither profile establishes initialization at the time of an access.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
use crate::nzcv::NzcvFlags;
use crate::scalar_memory_definitions::{Definitions, Error as DefinitionError, Limits, Stage};
use crate::smt::{SmtExpr as E, SmtSort};
use crate::source_bound_frame::ReadOnlySourceQueries;
use std::collections::HashMap;
use std::sync::Arc;
use trust_cg_ir::MachFunction;

#[path = "read_only_target_bytes.rs"]
mod bytes;
#[path = "read_only_target_liveness.rs"]
mod liveness;
#[path = "read_only_target_machine.rs"]
mod machine;

#[path = "scalar_memory_target.rs"]
mod scalar_memory;

#[path = "read_only_target_memory.rs"]
mod memory;

pub use scalar_memory::{
    ScalarMemoryTargetAccess, ScalarMemoryTargetEndpoint, ScalarMemoryTargetQueries,
    ScalarReturnTargetQueries, bind_scalar_memory_bytes, bind_scalar_memory_machine,
    bind_scalar_return_bytes, bind_scalar_return_machine,
};

#[cfg(test)]
#[path = "read_only_target_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "read_only_target_scalar_memory_tests.rs"]
pub(crate) mod scalar_memory_tests;

#[cfg(test)]
#[path = "scalar_memory_target_tests.rs"]
mod scalar_memory_target_tests;

const MAX_STEPS: usize = 256;
const MAX_PATHS: usize = 64;
const MAX_READS: usize = 64;
// Logical tree work, not an RSS claim. DAG substitution and path forks retain
// shared expression children; later serializers may visit shared trees again.
const MAX_TERM_NODES: usize = 32_768;
const MAX_STATE_NODES: usize = 262_144;
const MAX_QUERY_NODES: usize = 65_536;
const MAX_TOTAL_QUERY_NODES: usize = 1_048_576;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ReadOnlyTargetError {
    #[error("unsupported read-only allocated machine: {0}")]
    Machine(&'static str),
    #[error("unsupported read-only final A64 bytes: {0}")]
    Bytes(&'static str),
    #[error("invalid read-only target control/effect: {0}")]
    Control(&'static str),
    #[error("read-only target resource limit: {0}")]
    Budget(&'static str),
    #[error("read-only target resource limit at step {step}: {reason}")]
    BudgetAt { step: usize, reason: &'static str },
}

/// The immutable endpoint whose OWN effects these queries describe.
#[derive(Debug, Clone, Copy)]
pub enum ReadOnlyTargetEndpoint<'a> {
    Machine(&'a MachFunction),
    FinalBytes(&'a [u8]),
}

/// One actual target load's conditional demand. The index names an endpoint
/// step, not a source instruction or a proof-authorized machine row.
#[derive(Debug, Clone)]
pub struct ReadOnlyTargetLoad {
    pub step: usize,
    pub guard: E,
    pub address: E,
    pub byte_width: u32,
    pub alignment: u64,
}

/// Borrowed endpoints and pending queries. No public constructor can substitute
/// a source hint for an observed target or mint a verification receipt.
pub struct ReadOnlyTargetQueries<'a> {
    source: &'a ReadOnlySourceQueries<'a>,
    endpoint: ReadOnlyTargetEndpoint<'a>,
    returns: Vec<ProofObligation>,
    loads: Vec<ProofObligation>,
    reads: Vec<ReadOnlyTargetLoad>,
}

impl<'a> ReadOnlyTargetQueries<'a> {
    pub fn source(&self) -> &'a ReadOnlySourceQueries<'a> {
        self.source
    }
    pub fn endpoint(&self) -> ReadOnlyTargetEndpoint<'a> {
        self.endpoint
    }
    pub fn return_obligations(&self) -> &[ProofObligation] {
        &self.returns
    }
    pub fn load_obligations(&self) -> &[ProofObligation] {
        &self.loads
    }
    pub fn reads(&self) -> &[ReadOnlyTargetLoad] {
        &self.reads
    }
}

// Tiny observation records, not executable IR or a second compiler. The
// adapters independently use existing architectural semantic encoders.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Profile {
    ReadOnly,
    ScalarMemory,
}

enum Step {
    Scalar {
        destination: Option<usize>,
        value: E,
        flags: Option<Box<NzcvFlags>>,
    },
    Load {
        destination: usize,
        address: E,
        alignment: u64,
    },
    MemoryLoad {
        destination: usize,
        address: E,
        byte_width: u32,
        alignment: u64,
    },
    MemoryStore {
        address: E,
        value: Box<E>,
        byte_width: u32,
        alignment: u64,
    },
    LoadPair {
        destinations: [usize; 2],
        address: Box<E>,
        byte_width: u32,
        alignment: u64,
    },
    Branch {
        condition: E,
        taken: usize,
    },
    Jump(usize),
    Return,
    Inert,
}

fn register(index: usize) -> E {
    E::var(format!("x{index}"), 64)
}

fn flags() -> NzcvFlags {
    let flag = |name| E::uf(name, vec![], SmtSort::Bool);
    NzcvFlags {
        n: flag("flag_n"),
        z: flag("flag_z"),
        c: flag("flag_c"),
        v: flag("flag_v"),
    }
}

#[derive(Clone)]
struct Term {
    expr: E,
    nodes: usize,
}

impl Term {
    fn leaf(expr: E) -> Self {
        Self { expr, nodes: 1 }
    }
}

#[derive(Clone)]
struct State {
    pc: usize,
    x: [Option<Term>; 31],
    flags: [Option<Term>; 4],
    guard: Term,
    // Present only in the scalar-memory profile. This is architectural state,
    // not an SSA slot: lexical register retirement must never drop it.
    // Immutable memory versions fork/snapshot by handle, not a cloned UF
    // descriptor. The unchanged read-only profile pays only an empty pointer.
    memory: Option<Arc<Term>>,
}

struct Read {
    step: usize,
    guard: Term,
    address: Term,
    alignment: u64,
    byte_width: u32,
    lane: usize,
}

struct Observations {
    returns: Vec<(Term, Term)>,
    vector_returns: Vec<(Term, Vec<Term>)>,
    reads: Vec<Read>,
    writes: Vec<Read>,
    memories: Vec<Arc<Term>>,
    definitions: Vec<E>,
}

fn bounded_sum(
    values: impl IntoIterator<Item = usize>,
    limit: usize,
) -> Result<usize, ReadOnlyTargetError> {
    values.into_iter().try_fold(0usize, |total, n| {
        total
            .checked_add(n)
            .filter(|n| *n <= limit)
            .ok_or(ReadOnlyTargetError::Budget("logical expression work"))
    })
}

fn replacement<'a>(expr: &E, state: &'a State) -> Result<Option<&'a Term>, ReadOnlyTargetError> {
    match expr {
        E::Var { name, width: 64 } => {
            let index = name.strip_prefix('x').and_then(|n| n.parse::<usize>().ok());
            let index = index
                .filter(|i| *i < 31 && name == &format!("x{i}"))
                .ok_or(ReadOnlyTargetError::Control(
                    "unknown architectural template input",
                ))?;
            Ok(Some(state.x[index].as_ref().ok_or(
                ReadOnlyTargetError::Control("read of retired architectural slot"),
            )?))
        }
        E::Var { .. } => Err(ReadOnlyTargetError::Control(
            "wrong-sort architectural template input",
        )),
        E::UF {
            name,
            args,
            ret_sort,
        } => {
            let index = ["flag_n", "flag_z", "flag_c", "flag_v"]
                .iter()
                .position(|n| *n == name);
            let index = index
                .filter(|_| args.is_empty() && *ret_sort == SmtSort::Bool)
                .ok_or(ReadOnlyTargetError::Control(
                    "unknown architectural template UF",
                ))?;
            Ok(Some(state.flags[index].as_ref().ok_or(
                ReadOnlyTargetError::Control("read of retired architectural slot"),
            )?))
        }
        _ => Ok(None),
    }
}

// Postorder accounting memoizes input DAG nodes but SUMS child weights, so it
// bounds expanded serialization work too. Every replacement is counted before
// the existing iterative DAG rewriter clones anything into the output.
fn expression_nodes(
    expr: &E,
    state: Option<&State>,
    limit: usize,
) -> Result<usize, ReadOnlyTargetError> {
    let mut pending = vec![(expr, false)];
    let mut sizes = HashMap::<*const E, usize>::new();
    while let Some((node, ready)) = pending.pop() {
        let key = node as *const E;
        if sizes.contains_key(&key) {
            continue;
        }
        if let Some(value) = state.map(|s| replacement(node, s)).transpose()?.flatten() {
            if value.nodes > limit {
                return Err(ReadOnlyTargetError::Budget("substituted expression"));
            }
            sizes.insert(key, value.nodes);
            continue;
        }
        if !ready {
            pending.push((node, true));
            node.for_each_child(&mut |child| pending.push((child, false)));
        } else {
            let mut children = vec![1];
            node.for_each_child(&mut |child| children.push(sizes[&(child as *const E)]));
            sizes.insert(key, bounded_sum(children, limit)?);
        }
    }
    Ok(sizes[&(expr as *const E)])
}

fn compose(expr: &E, state: &State) -> Result<Term, ReadOnlyTargetError> {
    let nodes = expression_nodes(expr, Some(state), MAX_TERM_NODES)?;
    let expr = expr
        .try_rewrite_dag(&mut |node| {
            replacement(node, state).map(|term| term.map(|t| t.expr.clone()))
        })?
        .unwrap_or_else(|| expr.clone());
    Ok(Term { expr, nodes })
}

fn state_nodes(state: &State) -> Result<usize, ReadOnlyTargetError> {
    bounded_sum(
        state
            .x
            .iter()
            .chain(&state.flags)
            .filter_map(Option::as_ref)
            .chain([&state.guard])
            .chain(state.memory.iter().map(Arc::as_ref))
            .map(|t| t.nodes),
        MAX_STATE_NODES,
    )
}

fn projected_nodes(state: &State, live: u64) -> Result<usize, ReadOnlyTargetError> {
    bounded_sum(
        state
            .x
            .iter()
            .chain(&state.flags)
            .enumerate()
            .filter(|(i, _)| live & (1 << i) != 0)
            .filter_map(|(_, t)| t.as_ref())
            .map(|t| t.nodes)
            .chain([state.guard.nodes])
            .chain(state.memory.iter().map(|term| term.nodes)),
        MAX_STATE_NODES,
    )
}

fn prune(state: &mut State, live: u64) {
    for (i, slot) in state.x.iter_mut().chain(&mut state.flags).enumerate() {
        if live & (1 << i) == 0 {
            *slot = None;
        }
    }
}

fn live_states(pending: &[State], next_nodes: usize) -> Result<(), ReadOnlyTargetError> {
    let nodes = pending
        .iter()
        .map(state_nodes)
        .collect::<Result<Vec<_>, _>>()?;
    bounded_sum(nodes.into_iter().chain([next_nodes]), MAX_STATE_NODES)?;
    Ok(())
}

fn live_states_with_definitions(
    pending: &[State],
    next_nodes: usize,
    definition_nodes: usize,
) -> Result<(), ReadOnlyTargetError> {
    let held = pending
        .iter()
        .map(state_nodes)
        .collect::<Result<Vec<_>, _>>()?;
    bounded_sum(
        held.into_iter().chain([next_nodes, definition_nodes]),
        MAX_STATE_NODES,
    )?;
    Ok(())
}

fn validate(steps: &[Step]) -> Result<(), ReadOnlyTargetError> {
    if steps.is_empty() || steps.len() > MAX_STEPS {
        return Err(ReadOnlyTargetError::Budget("endpoint steps"));
    }
    let mut edges = Vec::with_capacity(steps.len());
    let mut indegrees = vec![0usize; steps.len()];
    for (pc, step) in steps.iter().enumerate() {
        let destinations = match step {
            Step::Return => vec![],
            Step::Jump(target) => vec![*target],
            Step::Branch { condition, taken } => {
                if condition.sort() != SmtSort::Bool {
                    return Err(ReadOnlyTargetError::Control(
                        "branch condition is not Boolean",
                    ));
                }
                vec![*taken, pc + 1]
            }
            Step::Scalar {
                destination,
                value,
                flags,
            } => {
                if destination.is_some_and(|d| d >= 18)
                    || value.sort() != SmtSort::BitVec(64)
                    || flags.as_ref().is_some_and(|f| {
                        [&f.n, &f.z, &f.c, &f.v]
                            .iter()
                            .any(|e| e.sort() != SmtSort::Bool)
                    })
                {
                    return Err(ReadOnlyTargetError::Control(
                        "unsupported destination or effect sort",
                    ));
                }
                vec![pc + 1]
            }
            Step::Load {
                destination,
                address,
                alignment,
            } => {
                if (*destination >= 18 && *destination != 31)
                    || address.sort() != SmtSort::BitVec(64)
                    || !alignment.is_power_of_two()
                    || *alignment > 8
                {
                    return Err(ReadOnlyTargetError::Control("unsupported load effect"));
                }
                vec![pc + 1]
            }
            Step::MemoryLoad { .. } | Step::MemoryStore { .. } | Step::LoadPair { .. } => {
                memory::validate(step)?;
                vec![pc + 1]
            }
            Step::Inert => vec![pc + 1],
        };
        for &target in &destinations {
            let degree = indegrees
                .get_mut(target)
                .ok_or(ReadOnlyTargetError::Control("edge leaves endpoint"))?;
            *degree += 1;
        }
        edges.push(destinations);
    }
    let mut reached = vec![false; steps.len()];
    let mut pending = vec![0];
    while let Some(pc) = pending.pop() {
        if !std::mem::replace(&mut reached[pc], true) {
            pending.extend(&edges[pc]);
        }
    }
    if reached.contains(&false) {
        return Err(ReadOnlyTargetError::Control(
            "unreachable/uninspected instruction",
        ));
    }
    let mut ready: Vec<_> = indegrees
        .iter()
        .enumerate()
        .filter_map(|(i, &n)| (n == 0).then_some(i))
        .collect();
    let mut visited = 0;
    while let Some(pc) = ready.pop() {
        visited += 1;
        for &target in &edges[pc] {
            indegrees[target] -= 1;
            if indegrees[target] == 0 {
                ready.push(target);
            }
        }
    }
    if visited != steps.len() {
        return Err(ReadOnlyTargetError::Control("cyclic target control"));
    }
    Ok(())
}

#[cfg(test)]
fn observe(steps: &[Step], inputs: &[(String, u32)]) -> Result<Observations, ReadOnlyTargetError> {
    observe_at(steps, inputs, &mut 0)
}

fn observe_at(
    steps: &[Step],
    inputs: &[(String, u32)],
    current: &mut usize,
) -> Result<Observations, ReadOnlyTargetError> {
    observe_profile_at(steps, inputs, inputs.len(), None, current)
}

fn definition_error(error: DefinitionError) -> ReadOnlyTargetError {
    match error {
        DefinitionError::Invalid(reason) => ReadOnlyTargetError::Control(reason),
        DefinitionError::Budget(reason) => ReadOnlyTargetError::Budget(reason),
    }
}

fn bind_value(
    definitions: &mut Option<Definitions>,
    value: Term,
    sort: SmtSort,
) -> Result<Term, ReadOnlyTargetError> {
    match definitions {
        None => Ok(value),
        Some(definitions) => definitions
            .bind(value.expr, value.nodes, sort)
            .map(Term::leaf)
            .map_err(definition_error),
    }
}

fn observe_profile_at(
    steps: &[Step],
    inputs: &[(String, u32)],
    abi_arity: usize,
    stage: Option<Stage>,
    current: &mut usize,
) -> Result<Observations, ReadOnlyTargetError> {
    observe_returning_at(steps, inputs, abi_arity, stage, None, current)
}

fn observe_returning_at(
    steps: &[Step],
    inputs: &[(String, u32)],
    abi_arity: usize,
    stage: Option<Stage>,
    returned: Option<&[usize]>,
    current: &mut usize,
) -> Result<Observations, ReadOnlyTargetError> {
    if stage.is_some()
        && (abi_arity > 8
            || (0..abi_arity).any(|i| inputs.get(i) != Some(&(format!("abi_x{i}"), 64))))
    {
        return Err(ReadOnlyTargetError::Control("scalar-memory ABI inputs"));
    }
    let live = match returned {
        None => liveness::compute(steps)?,
        Some(registers) => liveness::compute_returning(steps, registers)?,
    };
    let entry_memory = E::uf("entry_memory", vec![], memory_sort());
    let mut definitions = stage.map(|stage| {
        Definitions::new(
            stage,
            abi_arity,
            Limits {
                rhs_nodes: MAX_TERM_NODES,
                collection_nodes: MAX_STATE_NODES,
                occurrences: MAX_STEPS * MAX_PATHS,
            },
        )
    });
    let initial_flags = ["entry_n", "entry_z", "entry_c", "entry_v"].map(|name| Term {
        expr: E::var(name, 1).eq_expr(E::bv_const(1, 1)),
        nodes: 3,
    });
    let mut pending = vec![State {
        pc: 0,
        x: std::array::from_fn(|i| {
            Some(Term::leaf(E::var(
                inputs
                    .get(i)
                    .filter(|_| i < abi_arity)
                    .map(|(n, _)| n.clone())
                    .unwrap_or_else(|| format!("entry_x{i}")),
                64,
            )))
        }),
        flags: initial_flags.map(Some),
        guard: Term::leaf(E::BoolConst(true)),
        memory: stage.map(|_| Arc::new(Term::leaf(entry_memory.clone()))),
    }];
    prune(&mut pending[0], live[0]);
    let memory = entry_memory;
    let mut result = Observations {
        returns: vec![],
        vector_returns: vec![],
        reads: vec![],
        writes: vec![],
        memories: vec![],
        definitions: vec![],
    };
    let mut returned_nodes = 0usize;
    while let Some(mut state) = pending.pop() {
        loop {
            *current = state.pc;
            match &steps[state.pc] {
                Step::Scalar {
                    destination,
                    value,
                    flags,
                } => {
                    if let Some(definitions) = &definitions {
                        definitions
                            .preflight_occurrences(
                                usize::from(destination.is_some())
                                    + if flags.is_some() { 4 } else { 0 },
                            )
                            .map_err(definition_error)?;
                    }
                    // Every input is read from the BEFORE state; destination
                    // aliases cannot accidentally feed newly written values.
                    // Preflight the enlarged ACTIVE state together with held
                    // siblings before substituting any effect expressions.
                    let value_nodes = expression_nodes(value, Some(&state), MAX_TERM_NODES)?;
                    let mut next_nodes = state_nodes(&state)?;
                    if let Some(index) = destination {
                        next_nodes = bounded_sum(
                            [
                                next_nodes - state.x[*index].as_ref().map_or(0, |t| t.nodes),
                                value_nodes,
                            ],
                            MAX_STATE_NODES,
                        )?;
                    }
                    if let Some(flags) = flags {
                        let new_flags = [&flags.n, &flags.z, &flags.c, &flags.v]
                            .map(|e| expression_nodes(e, Some(&state), MAX_TERM_NODES));
                        let new_flags = new_flags.into_iter().collect::<Result<Vec<_>, _>>()?;
                        let old_flags =
                            state.flags.iter().flatten().map(|f| f.nodes).sum::<usize>();
                        next_nodes = bounded_sum(
                            [
                                next_nodes - old_flags,
                                bounded_sum(new_flags, MAX_STATE_NODES)?,
                            ],
                            MAX_STATE_NODES,
                        )?;
                    }
                    let extra = if definitions.is_some() {
                        let value = if destination.is_some() {
                            value_nodes + 2
                        } else {
                            0
                        };
                        let flags = flags
                            .as_ref()
                            .map(|f| {
                                [&f.n, &f.z, &f.c, &f.v]
                                    .into_iter()
                                    .map(|e| {
                                        expression_nodes(e, Some(&state), MAX_TERM_NODES)
                                            .map(|n| n + 2)
                                    })
                                    .collect::<Result<Vec<_>, _>>()
                            })
                            .transpose()?
                            .unwrap_or_default();
                        bounded_sum(flags.into_iter().chain([value]), MAX_STATE_NODES)?
                    } else {
                        0
                    };
                    let definition_nodes = bounded_sum(
                        [definitions.as_ref().map_or(0, |d| d.nodes), extra],
                        MAX_STATE_NODES,
                    )?;
                    live_states_with_definitions(&pending, next_nodes, definition_nodes)?;
                    let value = compose(value, &state)?;
                    let flags = flags
                        .as_ref()
                        .map(|f| [&f.n, &f.z, &f.c, &f.v].map(|e| compose(e, &state)))
                        .map(|f| f.into_iter().collect::<Result<Vec<_>, _>>())
                        .transpose()?;
                    if let Some(index) = destination {
                        state.x[*index] =
                            Some(bind_value(&mut definitions, value, SmtSort::BitVec(64))?);
                    }
                    if let Some(flags) = flags {
                        state.flags = flags
                            .into_iter()
                            .map(|flag| bind_value(&mut definitions, flag, SmtSort::Bool).map(Some))
                            .collect::<Result<Vec<_>, _>>()?
                            .try_into()
                            .ok()
                            .unwrap();
                    }
                    state.pc += 1;
                }
                Step::Load {
                    destination,
                    address,
                    alignment,
                } => {
                    if definitions.is_some() {
                        return Err(ReadOnlyTargetError::Control(
                            "legacy load under scalar-memory profile",
                        ));
                    }
                    if result.reads.len() >= MAX_READS {
                        return Err(ReadOnlyTargetError::Budget("target read demands"));
                    }
                    let address = compose(address, &state)?;
                    // encode_load_le repeats the address once for each byte.
                    let nodes = bounded_sum(
                        [
                            address
                                .nodes
                                .checked_mul(8)
                                .ok_or(ReadOnlyTargetError::Budget("load expansion"))?,
                            64,
                        ],
                        MAX_TERM_NODES,
                    )?;
                    let next_nodes = if *destination == 31 {
                        state_nodes(&state)?
                    } else {
                        bounded_sum(
                            [
                                state_nodes(&state)?
                                    - state.x[*destination].as_ref().map_or(0, |t| t.nodes),
                                nodes,
                            ],
                            MAX_STATE_NODES,
                        )?
                    };
                    live_states(&pending, next_nodes)?;
                    let value = (*destination != 31).then(|| Term {
                        expr: encode_load_le(&memory, &address.expr, 8),
                        nodes,
                    });
                    result.reads.push(Read {
                        step: state.pc,
                        guard: state.guard.clone(),
                        address,
                        alignment: *alignment,
                        byte_width: 8,
                        lane: 0,
                    });
                    if let Some(value) = value {
                        state.x[*destination] = Some(value);
                    }
                    state.pc += 1;
                }
                Step::MemoryLoad { .. } | Step::MemoryStore { .. } | Step::LoadPair { .. } => {
                    memory::observe(
                        &steps[state.pc],
                        &mut state,
                        &pending,
                        &mut result,
                        definitions.as_mut().ok_or(ReadOnlyTargetError::Control(
                            "scalar-memory effect under read-only profile",
                        ))?,
                    )?;
                    state.pc += 1;
                }
                Step::Branch { condition, taken } => {
                    if let Some(definitions) = &definitions {
                        definitions
                            .preflight_occurrences(2)
                            .map_err(definition_error)?;
                    }
                    if pending.len() + result.returns.len() + 2 > MAX_PATHS {
                        return Err(ReadOnlyTargetError::Budget("target execution paths"));
                    }
                    let condition = compose(condition, &state)?;
                    let nodes =
                        bounded_sum([state.guard.nodes, condition.nodes, 2], MAX_TERM_NODES)?;
                    // Preflight BOTH environments before a state fork. No
                    // constant pruning: invalid code on an untaken arm refuses.
                    let taken_nodes = bounded_sum(
                        [
                            projected_nodes(&state, live[*taken])? - state.guard.nodes,
                            nodes,
                        ],
                        MAX_STATE_NODES,
                    )?;
                    let other_nodes = bounded_sum(
                        [
                            projected_nodes(&state, live[state.pc + 1])? - state.guard.nodes,
                            nodes,
                        ],
                        MAX_STATE_NODES,
                    )?;
                    let held_nodes = pending
                        .iter()
                        .map(state_nodes)
                        .collect::<Result<Vec<_>, _>>()?;
                    bounded_sum(
                        held_nodes.into_iter().chain([taken_nodes, other_nodes]),
                        MAX_STATE_NODES,
                    )?;
                    let definitions_next = if definitions.is_some() {
                        bounded_sum(
                            [definitions.as_ref().map_or(0, |d| d.nodes), 2 * (nodes + 2)],
                            MAX_STATE_NODES,
                        )?
                    } else {
                        0
                    };
                    let held = pending
                        .iter()
                        .map(state_nodes)
                        .collect::<Result<Vec<_>, _>>()?;
                    bounded_sum(
                        held.into_iter()
                            .chain([taken_nodes, other_nodes, definitions_next]),
                        MAX_STATE_NODES,
                    )?;
                    let mut branch = state.clone();
                    branch.pc = *taken;
                    branch.guard = bind_value(
                        &mut definitions,
                        Term {
                            expr: state.guard.expr.clone().and_expr(condition.expr.clone()),
                            nodes,
                        },
                        SmtSort::Bool,
                    )?;
                    prune(&mut branch, live[*taken]);
                    pending.push(branch);
                    state.guard = bind_value(
                        &mut definitions,
                        Term {
                            expr: state.guard.expr.and_expr(condition.expr.not_expr()),
                            nodes,
                        },
                        SmtSort::Bool,
                    )?;
                    state.pc += 1;
                }
                Step::Jump(target) => state.pc = *target,
                Step::Return => {
                    if result.returns.len().max(result.vector_returns.len()) >= MAX_PATHS {
                        return Err(ReadOnlyTargetError::Budget("target returns"));
                    }
                    if let Some(memory) = &state.memory {
                        result.memories.push(memory.clone());
                    }
                    if let Some(registers) = returned {
                        // Reserve all lanes on every path before cloning any
                        // expression. A dead/unused source result is not dropped.
                        returned_nodes = bounded_sum(
                            std::iter::once(returned_nodes)
                                .chain(std::iter::once(state.guard.nodes))
                                .chain(registers.iter().map(|&register| {
                                    state.x[register].as_ref().map_or(0, |value| value.nodes)
                                })),
                            MAX_STATE_NODES,
                        )?;
                        let values = registers
                            .iter()
                            .map(|&register| {
                                state.x[register]
                                    .clone()
                                    .ok_or(ReadOnlyTargetError::Control(
                                        "read of retired returned architectural slot",
                                    ))
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        result.vector_returns.push((state.guard, values));
                    } else {
                        result.returns.push((
                            state.guard,
                            state.x[0].clone().ok_or(ReadOnlyTargetError::Control(
                                "read of retired architectural slot",
                            ))?,
                        ));
                    }
                    break;
                }
                Step::Inert => state.pc += 1,
            }
            let successor_live = live[state.pc];
            prune(&mut state, successor_live);
            live_states_with_definitions(
                &pending,
                state_nodes(&state)?,
                definitions.as_ref().map_or(0, |d| d.nodes),
            )?;
        }
    }
    result.definitions = definitions.map_or_else(Vec::new, |d| d.equations);
    Ok(result)
}

fn bind<'a>(
    source: &'a ReadOnlySourceQueries<'a>,
    endpoint: ReadOnlyTargetEndpoint<'a>,
    steps: Vec<Step>,
) -> Result<ReadOnlyTargetQueries<'a>, ReadOnlyTargetError> {
    let at = |error, stage| match error {
        ReadOnlyTargetError::Budget(_) => ReadOnlyTargetError::Budget(stage),
        other => other,
    };
    let mut current = 0;
    let observation = observe_at(&steps, &source.return_obligation().inputs, &mut current)
        .map_err(|error| match error {
            ReadOnlyTargetError::Budget(reason) => ReadOnlyTargetError::BudgetAt {
                step: current,
                reason,
            },
            other => other,
        })?;
    let source_return = &source.return_obligation().trust_ir_expr;
    let premises = &source.return_obligation().preconditions;
    let source_nodes = expression_nodes(source_return, None, MAX_QUERY_NODES)?;
    let premise_nodes = premises
        .iter()
        .map(|e| expression_nodes(e, None, MAX_QUERY_NODES))
        .collect::<Result<Vec<_>, _>>()?;
    let premise_nodes = bounded_sum(premise_nodes, MAX_TOTAL_QUERY_NODES)?;
    let mut total = 0usize;
    let mut reserve = |nodes| -> Result<(), ReadOnlyTargetError> {
        total = bounded_sum([total, nodes, premise_nodes], MAX_TOTAL_QUERY_NODES)?;
        Ok(())
    };
    let mut returns = vec![];
    for (guard, value) in observation.returns {
        let nodes = bounded_sum([source_nodes, guard.nodes, value.nodes, 4], MAX_QUERY_NODES)
            .map_err(|e| at(e, "guarded target return"))?;
        reserve(nodes).map_err(|e| at(e, "aggregate target returns and source premises"))?;
        returns.push(
            guard
                .expr
                .not_expr()
                .or_expr(source_return.clone().eq_expr(value.expr)),
        );
    }
    let mut loads = vec![];
    for read in &observation.reads {
        let mut coverage = E::BoolConst(false);
        let mut nodes = 1;
        for original in source.read_requirements() {
            if original.byte_width != 8 || original.alignment < read.alignment {
                continue;
            }
            nodes = bounded_sum(
                [
                    nodes,
                    expression_nodes(&original.guard, None, MAX_QUERY_NODES)?,
                    expression_nodes(&original.address, None, MAX_QUERY_NODES)?,
                    read.address.nodes,
                    3,
                ],
                MAX_QUERY_NODES,
            )?;
            coverage = coverage.or_expr(
                original
                    .guard
                    .clone()
                    .and_expr(original.address.clone().eq_expr(read.address.expr.clone())),
            );
        }
        let nodes = bounded_sum([nodes, read.guard.nodes, 3], MAX_QUERY_NODES)?;
        reserve(nodes).map_err(|e| at(e, "aggregate target reads and source premises"))?;
        loads.push(read.guard.expr.clone().not_expr().or_expr(coverage));
    }
    // All aggregate work is checked BEFORE duplicating the source-premise
    // inventory into the individual obligation records.
    let mut inputs = source.return_obligation().inputs.clone();
    inputs.extend((inputs.len()..31).map(|i| (format!("entry_x{i}"), 64)));
    inputs.extend(["entry_n", "entry_z", "entry_c", "entry_v"].map(|n| (n.into(), 1)));
    let pending = |kind, index, expression| ProofObligation {
        name: format!("Original read-only Core -> {kind} guarded {index}"),
        trust_ir_expr: E::BoolConst(true),
        aarch64_expr: expression,
        inputs: inputs.clone(),
        preconditions: premises.clone(),
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    let label = match endpoint {
        ReadOnlyTargetEndpoint::Machine(_) => "actual MachIR",
        ReadOnlyTargetEndpoint::FinalBytes(_) => "independent final words",
    };
    Ok(ReadOnlyTargetQueries {
        source,
        endpoint,
        returns: returns
            .into_iter()
            .enumerate()
            .map(|(i, e)| pending(format!("{label} return"), i, e))
            .collect(),
        loads: loads
            .into_iter()
            .enumerate()
            .map(|(i, e)| pending(format!("{label} load"), i, e))
            .collect(),
        reads: observation
            .reads
            .into_iter()
            .map(|r| ReadOnlyTargetLoad {
                step: r.step,
                guard: r.guard.expr,
                address: r.address.expr,
                byte_width: 8,
                alignment: r.alignment,
            })
            .collect(),
    })
}

/// The source binding must already have admitted the original Core and LIR.
/// An unsupported target returns an error; it cannot turn source applicability
/// into a skipped row. This constructor does not solve any query.
pub fn bind_read_only_machine<'a>(
    source: &'a ReadOnlySourceQueries<'a>,
    target: &'a MachFunction,
) -> Result<ReadOnlyTargetQueries<'a>, ReadOnlyTargetError> {
    let signature: trust_cg_ir::function::Signature = (&source.lir().signature).into();
    if target.name != source.source().name || target.signature != signature {
        return Err(ReadOnlyTargetError::Machine(
            "function identity/signature differs from original Core",
        ));
    }
    bind(
        source,
        ReadOnlyTargetEndpoint::Machine(target),
        machine::adapt(target)?,
    )
}

/// `code` must be the FINAL complete word stream after all patches/relocations.
/// This API neither applies nor authorizes fixups. Independent decoding never
/// uses the compiler's encoder, MachIR layout, source hints or field sidecars.
pub fn bind_read_only_bytes<'a>(
    source: &'a ReadOnlySourceQueries<'a>,
    code: &'a [u8],
) -> Result<ReadOnlyTargetQueries<'a>, ReadOnlyTargetError> {
    bind(
        source,
        ReadOnlyTargetEndpoint::FinalBytes(code),
        bytes::adapt(code)?,
    )
}
