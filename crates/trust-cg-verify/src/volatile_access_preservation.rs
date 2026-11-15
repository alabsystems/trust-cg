// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Volatile access preservation (X-OPCODES-P6): every control-flow path of
//! the final machine stream performs the same volatile accesses, in the same
//! order and the same number of times, as the corresponding source path.
//!
//! Each side is projected onto its volatile accesses: a [`VolatileTraceGraph`]
//! keeps the control-flow graph and, per block, the ordered accesses it
//! performs, labeled by direction (load or store) and access size. Every path
//! from the entry spells a word over those labels. The obligation is that the
//! two sides spell the same words:
//!
//! * the same COMPLETE words — paths that leave the function (return, tail
//!   call, trap) — and
//! * the same PREFIXES — every finite path prefix, which covers paths that
//!   never leave (a loop that runs forever) and paths cut short.
//!
//! [`check_volatile_trace_preservation`] decides both language equalities
//! exactly (subset construction and a product search, bounded) and returns
//! the shortest distinguishing word on failure. Deleting, duplicating,
//! merging (two accesses become one wider access) or reordering accesses of
//! different labels on some path changes a word and is refuted.
//!
//! What it does NOT establish:
//!
//! * addresses, stored values or loaded-value uses: two accesses with the
//!   same label are interchangeable here, so swapping two same-size loads
//!   from different addresses is not detected;
//! * path feasibility: the source graph is the source CFG, every edge
//!   assumed takeable. A transformation that removes a path because it can
//!   never execute (a constant-folded branch, a loop with a known trip count
//!   unrolled completely) changes the words and is REFUSED — fail-closed, not
//!   unsound;
//! * the dereference/value semantics of each access (the memory model of the
//!   plain load/store rows), ordering against non-volatile memory or calls,
//!   or the hardware memory model.
//!
//! The decision is an in-process procedure over the extracted graphs, not an
//! independently checked certificate.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{RegClass, SpecialReg};
use trust_cg_ir::types::BlockId;

/// Direction of a volatile access.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VolatileAccessKind {
    Load,
    Store,
}

/// One volatile access as the trace sees it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VolatileAccess {
    pub kind: VolatileAccessKind,
    /// Access size in bytes.
    pub bytes: u32,
}

impl std::fmt::Display for VolatileAccess {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = match self.kind {
            VolatileAccessKind::Load => "load",
            VolatileAccessKind::Store => "store",
        };
        write!(f, "{kind}{}", self.bytes * 8)
    }
}

/// One block of a [`VolatileTraceGraph`].
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct VolatileTraceBlock {
    /// The block's volatile accesses in program order.
    pub accesses: Vec<VolatileAccess>,
    /// Blocks control may continue to (indices into the graph).
    pub successors: Vec<usize>,
    /// Control may leave the function at the end of this block.
    pub exits: bool,
}

/// A control-flow graph projected onto its volatile accesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VolatileTraceGraph {
    pub entry: usize,
    pub blocks: Vec<VolatileTraceBlock>,
}

impl VolatileTraceGraph {
    /// Number of volatile accesses in blocks reachable from the entry.
    pub fn reachable_access_count(&self) -> usize {
        self.reachable()
            .iter()
            .map(|&b| self.blocks[b].accesses.len())
            .sum()
    }

    fn reachable(&self) -> Vec<usize> {
        let mut seen = vec![false; self.blocks.len()];
        let mut stack = vec![self.entry];
        let mut order = Vec::new();
        while let Some(block) = stack.pop() {
            if block >= self.blocks.len() || seen[block] {
                continue;
            }
            seen[block] = true;
            order.push(block);
            stack.extend(self.blocks[block].successors.iter().copied());
        }
        order
    }

    fn validate(&self, side: &'static str) -> Result<(), VolatileTraceError> {
        if self.entry >= self.blocks.len() {
            return Err(VolatileTraceError::Malformed(format!(
                "{side} entry {} outside {} blocks",
                self.entry,
                self.blocks.len()
            )));
        }
        for (index, block) in self.blocks.iter().enumerate() {
            if let Some(&bad) = block.successors.iter().find(|&&s| s >= self.blocks.len()) {
                return Err(VolatileTraceError::Malformed(format!(
                    "{side} block {index} names successor {bad} outside {} blocks",
                    self.blocks.len()
                )));
            }
        }
        Ok(())
    }
}

/// Why a volatile trace could not be extracted or decided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VolatileTraceError {
    /// A graph is internally inconsistent.
    Malformed(String),
    /// A volatile access whose size or direction cannot be read.
    UnsizedAccess(String),
    /// The trace automata exceed the decision bound.
    TooLarge { states: usize },
}

impl std::fmt::Display for VolatileTraceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed(why) => write!(f, "malformed volatile trace graph: {why}"),
            Self::UnsizedAccess(why) => write!(f, "volatile access without a size: {why}"),
            Self::TooLarge { states } => write!(
                f,
                "volatile trace automata exceed the decision bound ({states} product states)"
            ),
        }
    }
}

/// Which side admits the distinguishing word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VolatileTraceSide {
    /// A source path performs it; no machine path does.
    SourceOnly,
    /// A machine path performs it; no source path does.
    MachineOnly,
}

/// Whether the distinguishing word is a complete path or a prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VolatileTraceScope {
    /// A path from the entry that leaves the function.
    CompletePath,
    /// A path prefix from the entry.
    PathPrefix,
}

/// A refutation: the shortest word one side spells and the other does not.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VolatileTraceViolation {
    pub witness: Vec<VolatileAccess>,
    pub side: VolatileTraceSide,
    pub scope: VolatileTraceScope,
}

impl std::fmt::Display for VolatileTraceViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let word: Vec<String> = self.witness.iter().map(ToString::to_string).collect();
        let (has, lacks) = match self.side {
            VolatileTraceSide::SourceOnly => ("source", "final machine stream"),
            VolatileTraceSide::MachineOnly => ("final machine stream", "source"),
        };
        let what = match self.scope {
            VolatileTraceScope::CompletePath => "a complete path",
            VolatileTraceScope::PathPrefix => "a path prefix",
        };
        write!(
            f,
            "the {has} has {what} performing volatile accesses [{}] that the {lacks} does not",
            word.join(", ")
        )
    }
}

/// What a successful check established.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct VolatileTraceCertificate {
    /// Volatile accesses reachable in the source.
    pub source_accesses: usize,
    /// Volatile accesses reachable in the final machine stream.
    pub machine_accesses: usize,
    /// Product states explored (0 when neither side has a volatile access).
    pub product_states: usize,
}

/// Outcome of [`check_volatile_trace_preservation`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VolatileTraceOutcome {
    Preserved(VolatileTraceCertificate),
    Violated(VolatileTraceViolation),
}

/// Bound on explored product states; beyond it the check refuses.
pub const VOLATILE_TRACE_STATE_BOUND: usize = 200_000;

/// NFA over labels: per state, labeled edges and epsilon edges.
struct Nfa {
    labeled: Vec<Vec<(VolatileAccess, usize)>>,
    epsilon: Vec<Vec<usize>>,
    accepting: Vec<bool>,
    start: usize,
}

/// State `2b` is the start of block `b`; the chain of its accesses runs
/// through fresh states to its end, which reaches each successor's start by
/// epsilon and accepts (complete language) when the block exits.
fn nfa(graph: &VolatileTraceGraph) -> Nfa {
    let mut labeled: Vec<Vec<(VolatileAccess, usize)>> = Vec::new();
    let mut epsilon: Vec<Vec<usize>> = Vec::new();
    let mut accepting = Vec::new();
    let fresh = |labeled: &mut Vec<Vec<(VolatileAccess, usize)>>,
                 epsilon: &mut Vec<Vec<usize>>,
                 accepting: &mut Vec<bool>| {
        labeled.push(Vec::new());
        epsilon.push(Vec::new());
        accepting.push(false);
        labeled.len() - 1
    };
    let starts: Vec<usize> = graph
        .blocks
        .iter()
        .map(|_| fresh(&mut labeled, &mut epsilon, &mut accepting))
        .collect();
    let mut ends = Vec::with_capacity(graph.blocks.len());
    for (index, block) in graph.blocks.iter().enumerate() {
        let mut at = starts[index];
        for &access in &block.accesses {
            let next = fresh(&mut labeled, &mut epsilon, &mut accepting);
            labeled[at].push((access, next));
            at = next;
        }
        accepting[at] = block.exits;
        ends.push(at);
    }
    for (index, block) in graph.blocks.iter().enumerate() {
        for &succ in &block.successors {
            epsilon[ends[index]].push(starts[succ]);
        }
    }
    Nfa {
        labeled,
        epsilon,
        accepting,
        start: starts[graph.entry],
    }
}

impl Nfa {
    fn closure(&self, states: impl IntoIterator<Item = usize>) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        let mut stack: Vec<usize> = states.into_iter().collect();
        while let Some(state) = stack.pop() {
            if out.insert(state) {
                stack.extend(self.epsilon[state].iter().copied());
            }
        }
        out
    }

    fn step(&self, set: &BTreeSet<usize>, label: VolatileAccess) -> BTreeSet<usize> {
        self.closure(set.iter().flat_map(|&state| {
            self.labeled[state]
                .iter()
                .filter(move |(l, _)| *l == label)
                .map(|&(_, next)| next)
        }))
    }

    fn accepts(&self, set: &BTreeSet<usize>) -> bool {
        set.iter().any(|&state| self.accepting[state])
    }

    fn labels(&self) -> BTreeSet<VolatileAccess> {
        self.labeled
            .iter()
            .flat_map(|edges| edges.iter().map(|&(l, _)| l))
            .collect()
    }
}

/// Decide whether the final machine stream preserves the source's volatile
/// accesses on every path (see the module documentation for the exact
/// claim and its limits).
pub fn check_volatile_trace_preservation(
    source: &VolatileTraceGraph,
    machine: &VolatileTraceGraph,
) -> Result<VolatileTraceOutcome, VolatileTraceError> {
    source.validate("source")?;
    machine.validate("machine")?;
    let source_accesses = source.reachable_access_count();
    let machine_accesses = machine.reachable_access_count();
    if source_accesses == 0 && machine_accesses == 0 {
        // Both languages are {empty word}, as complete paths when either side
        // can exit and as prefixes always. Exit reachability is not a
        // volatile-trace property, so no further comparison is made.
        return Ok(VolatileTraceOutcome::Preserved(VolatileTraceCertificate {
            source_accesses,
            machine_accesses,
            product_states: 0,
        }));
    }
    let (s, m) = (nfa(source), nfa(machine));
    let labels: Vec<VolatileAccess> = s.labels().union(&m.labels()).copied().collect();
    let start = (s.closure([s.start]), m.closure([m.start]));
    let mut index: HashMap<(BTreeSet<usize>, BTreeSet<usize>), usize> = HashMap::new();
    let mut parent: Vec<Option<(usize, VolatileAccess)>> = vec![None];
    let mut states = vec![start.clone()];
    index.insert(start, 0);
    let mut queue = VecDeque::from([0usize]);
    let witness = |parent: &[Option<(usize, VolatileAccess)>], mut at: usize| {
        let mut word = Vec::new();
        while let Some((prev, label)) = parent[at] {
            word.push(label);
            at = prev;
        }
        word.reverse();
        word
    };
    while let Some(at) = queue.pop_front() {
        let (ss, ms) = states[at].clone();
        let (s_alive, m_alive) = (!ss.is_empty(), !ms.is_empty());
        if s_alive != m_alive {
            return Ok(VolatileTraceOutcome::Violated(VolatileTraceViolation {
                witness: witness(&parent, at),
                side: if s_alive {
                    VolatileTraceSide::SourceOnly
                } else {
                    VolatileTraceSide::MachineOnly
                },
                scope: VolatileTraceScope::PathPrefix,
            }));
        }
        let (s_accepts, m_accepts) = (s.accepts(&ss), m.accepts(&ms));
        if s_accepts != m_accepts {
            return Ok(VolatileTraceOutcome::Violated(VolatileTraceViolation {
                witness: witness(&parent, at),
                side: if s_accepts {
                    VolatileTraceSide::SourceOnly
                } else {
                    VolatileTraceSide::MachineOnly
                },
                scope: VolatileTraceScope::CompletePath,
            }));
        }
        if !s_alive {
            continue;
        }
        for &label in &labels {
            let next = (s.step(&ss, label), m.step(&ms, label));
            if next.0.is_empty() && next.1.is_empty() {
                continue;
            }
            if index.contains_key(&next) {
                continue;
            }
            if states.len() >= VOLATILE_TRACE_STATE_BOUND {
                return Err(VolatileTraceError::TooLarge {
                    states: states.len(),
                });
            }
            index.insert(next.clone(), states.len());
            parent.push(Some((at, label)));
            states.push(next);
            queue.push_back(states.len() - 1);
        }
    }
    Ok(VolatileTraceOutcome::Preserved(VolatileTraceCertificate {
        source_accesses,
        machine_accesses,
        product_states: states.len(),
    }))
}

// ===========================================================================
// Extraction
// ===========================================================================

/// The source side: a lowered (LIR) function's volatile loads and stores
/// over its CFG. Blocks with no successor (return, trap, tail call) exit.
pub fn lir_volatile_trace(
    function: &trust_cg_lower::Function,
) -> Result<VolatileTraceGraph, VolatileTraceError> {
    use trust_cg_lower::instructions::Opcode;
    // Deterministic numbering: layout order first, then any other block.
    let mut order: Vec<trust_cg_lower::instructions::Block> = function.block_order.clone();
    let mut rest: Vec<_> = function
        .blocks
        .keys()
        .filter(|block| !order.contains(block))
        .copied()
        .collect();
    rest.sort_by_key(|block| block.0);
    order.extend(rest);
    let number: BTreeMap<u32, usize> = order
        .iter()
        .enumerate()
        .map(|(index, block)| (block.0, index))
        .collect();
    let entry = *number.get(&function.entry_block.0).ok_or_else(|| {
        VolatileTraceError::Malformed(format!(
            "source entry block {:?} is not a block",
            function.entry_block
        ))
    })?;
    let mut blocks = Vec::with_capacity(order.len());
    for block in &order {
        let basic = function.blocks.get(block).ok_or_else(|| {
            VolatileTraceError::Malformed(format!(
                "source block_order names missing block {block:?}"
            ))
        })?;
        let mut accesses = Vec::new();
        for inst in &basic.instructions {
            let (kind, ty) = match &inst.opcode {
                Opcode::VolatileLoad { ty, .. } => (VolatileAccessKind::Load, ty),
                Opcode::VolatileStore { ty, .. } => (VolatileAccessKind::Store, ty),
                _ => continue,
            };
            accesses.push(VolatileAccess {
                kind,
                bytes: ty.bytes(),
            });
        }
        let mut successors = Vec::new();
        for succ in basic.successors() {
            let index = *number.get(&succ.0).ok_or_else(|| {
                VolatileTraceError::Malformed(format!(
                    "source block {block:?} branches to missing block {succ:?}"
                ))
            })?;
            if !successors.contains(&index) {
                successors.push(index);
            }
        }
        blocks.push(VolatileTraceBlock {
            exits: successors.is_empty(),
            accesses,
            successors,
        });
    }
    Ok(VolatileTraceGraph { entry, blocks })
}

/// The volatile access an AArch64 instruction performs, if any.
pub fn aarch64_volatile_access(
    opcode: AArch64Opcode,
    operands: &[MachOperand],
) -> Result<Option<VolatileAccess>, VolatileTraceError> {
    use AArch64Opcode as O;
    let (kind, fixed) = match opcode {
        O::VolatileLdrbRI => (VolatileAccessKind::Load, Some(1)),
        O::VolatileLdrhRI => (VolatileAccessKind::Load, Some(2)),
        O::VolatileLdrRI => (VolatileAccessKind::Load, None),
        O::VolatileStrbRI => (VolatileAccessKind::Store, Some(1)),
        O::VolatileStrhRI => (VolatileAccessKind::Store, Some(2)),
        O::VolatileStrRI => (VolatileAccessKind::Store, None),
        _ => return Ok(None),
    };
    let bytes = match fixed {
        Some(bytes) => bytes,
        None => {
            let data = operands.first().ok_or_else(|| {
                VolatileTraceError::UnsizedAccess(format!("{opcode:?} without a data operand"))
            })?;
            let class = match data {
                MachOperand::VReg(v) => Some(v.class),
                MachOperand::PReg(p) => Some(trust_cg_ir::regs::preg_class(*p)),
                MachOperand::Special(SpecialReg::WZR) => Some(RegClass::Gpr32),
                MachOperand::Special(SpecialReg::XZR) => Some(RegClass::Gpr64),
                _ => None,
            };
            match class {
                Some(RegClass::Gpr32 | RegClass::Fpr32) => 4,
                Some(RegClass::Gpr64 | RegClass::Fpr64) => 8,
                Some(RegClass::Fpr16) => 2,
                Some(RegClass::Fpr8) => 1,
                Some(RegClass::Fpr128) => 16,
                other => {
                    return Err(VolatileTraceError::UnsizedAccess(format!(
                        "{opcode:?} data operand {data:?} of class {other:?}"
                    )));
                }
            }
        }
    };
    Ok(Some(VolatileAccess { kind, bytes }))
}

/// The machine side: an AArch64 machine function's volatile accesses over
/// its successor metadata plus the exception edges from each call site to its
/// landing pad. Blocks with no successor exit. Only blocks in `block_order`
/// (the emitted stream) participate.
pub fn aarch64_volatile_trace(
    function: &MachFunction,
) -> Result<VolatileTraceGraph, VolatileTraceError> {
    let number: BTreeMap<u32, usize> = function
        .block_order
        .iter()
        .enumerate()
        .map(|(index, block)| (block.0, index))
        .collect();
    let lookup = |block: BlockId, what: &str| {
        number.get(&block.0).copied().ok_or_else(|| {
            VolatileTraceError::Malformed(format!("machine {what} {block:?} is not emitted"))
        })
    };
    let entry = lookup(function.entry, "entry")?;
    let mut blocks = Vec::with_capacity(function.block_order.len());
    for &block_id in &function.block_order {
        let block = function.blocks.get(block_id.0 as usize).ok_or_else(|| {
            VolatileTraceError::Malformed(format!("machine block {block_id:?} is out of range"))
        })?;
        let mut accesses = Vec::new();
        for inst_id in &block.insts {
            let inst = function.insts.get(inst_id.0 as usize).ok_or_else(|| {
                VolatileTraceError::Malformed(format!(
                    "machine block {block_id:?} names missing instruction {inst_id:?}"
                ))
            })?;
            if let Some(access) = aarch64_volatile_access(inst.opcode, &inst.operands)? {
                accesses.push(access);
            }
        }
        let mut successors = Vec::new();
        for &succ in &block.succs {
            let index = lookup(succ, "successor")?;
            if !successors.contains(&index) {
                successors.push(index);
            }
        }
        blocks.push(VolatileTraceBlock {
            exits: successors.is_empty(),
            accesses,
            successors,
        });
    }
    for site in &function.eh_metadata.call_sites {
        if let Some(pad) = site.landing_pad_block {
            let (from, to) = (
                lookup(site.call_block, "call site")?,
                lookup(pad, "landing pad")?,
            );
            if !blocks[from].successors.contains(&to) {
                blocks[from].successors.push(to);
                // A call block's exit status comes from its normal successors.
            }
        }
    }
    Ok(VolatileTraceGraph { entry, blocks })
}

// ===========================================================================
// Negative controls and the coverage-gate credit hook
// ===========================================================================

/// The corruption a negative control applies, or `None` for a positive
/// control that must be preserved.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VolatileCorruption {
    /// An access removed from a path.
    Delete,
    /// An access performed twice where the source performs it once.
    Duplicate,
    /// Two accesses replaced by one wider access.
    Merge,
    /// Two accesses of different labels exchanged.
    Reorder,
    /// An access performed at another size, in the same position.
    Resize,
    /// An access moved out of a loop (performed once, not per iteration).
    Hoist,
    /// A path removed (a resolved branch).
    RemovePath,
    /// A volatile access replaced by its plain twin.
    Demote,
    /// A volatile access where the source has none.
    Fabricate,
}

/// One control of the credit battery.
#[derive(Debug, Clone)]
pub struct VolatileTraceControl {
    pub label: &'static str,
    pub source: VolatileTraceGraph,
    pub machine: VolatileTraceGraph,
    /// `None`: must be preserved; `Some(kind)`: must be refuted.
    pub corruption: Option<VolatileCorruption>,
}

fn control_graph(blocks: &[(&[VolatileAccess], &[usize])]) -> VolatileTraceGraph {
    VolatileTraceGraph {
        entry: 0,
        blocks: blocks
            .iter()
            .map(|(accesses, successors)| VolatileTraceBlock {
                accesses: accesses.to_vec(),
                successors: successors.to_vec(),
                exits: successors.is_empty(),
            })
            .collect(),
    }
}

/// A lowered source and a machine function built by hand, so the battery
/// also exercises both extractors: `VolatileLoad i32; VolatileStore i8`
/// against `LDR Wt; STRB Wt` with the volatile opcodes, or with `demote`
/// the plain `LDR`.
fn extracted_pair(
    demote: bool,
) -> Result<(VolatileTraceGraph, VolatileTraceGraph), VolatileTraceError> {
    use trust_cg_ir::function::Signature as MachSignature;
    use trust_cg_ir::inst::MachInst;
    use trust_cg_ir::regs::{VReg, X0};
    use trust_cg_lower::function::{BasicBlock, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
    use trust_cg_lower::types::Type;

    let mut source = trust_cg_lower::Function::new("volatile_control", Signature::default());
    source.block_order = vec![Block(0)];
    source.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![(Value(0), Type::I64)],
            source_locs: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::VolatileLoad {
                        ty: Type::I32,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(1)],
                },
                Instruction {
                    opcode: Opcode::VolatileStore {
                        ty: Type::I8,
                        align: None,
                    },
                    args: vec![Value(1), Value(0)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
        },
    );
    let mut machine = MachFunction::new(
        "volatile_control".into(),
        MachSignature::new(vec![], vec![]),
    );
    let w = MachOperand::VReg(VReg::new(0, RegClass::Gpr32));
    let base = MachOperand::PReg(X0);
    let load = if demote {
        AArch64Opcode::LdrRI
    } else {
        AArch64Opcode::VolatileLdrRI
    };
    for inst in [
        MachInst::new(load, vec![w.clone(), base.clone(), MachOperand::Imm(0)]),
        MachInst::new(
            AArch64Opcode::VolatileStrbRI,
            vec![w, base, MachOperand::Imm(0)],
        ),
        MachInst::new(AArch64Opcode::Ret, vec![]),
    ] {
        let id = machine.push_inst(inst);
        machine.append_inst(machine.entry, id);
    }
    Ok((
        lir_volatile_trace(&source)?,
        aarch64_volatile_trace(&machine)?,
    ))
}

/// The credit battery: positives that restructure control flow without
/// changing any path's accesses, and one negative per corruption kind.
pub fn volatile_trace_controls() -> Result<Vec<VolatileTraceControl>, VolatileTraceError> {
    use VolatileAccessKind::{Load, Store};
    const L4: VolatileAccess = VolatileAccess {
        kind: Load,
        bytes: 4,
    };
    const L8: VolatileAccess = VolatileAccess {
        kind: Load,
        bytes: 8,
    };
    const S4: VolatileAccess = VolatileAccess {
        kind: Store,
        bytes: 4,
    };
    const S1: VolatileAccess = VolatileAccess {
        kind: Store,
        bytes: 1,
    };
    // entry: L4, loop { S4 }, exit: L4.
    let reference = || control_graph(&[(&[L4], &[1, 2]), (&[S4], &[1, 2]), (&[L4], &[])]);
    let c = |label, source, machine, corruption| VolatileTraceControl {
        label,
        source,
        machine,
        corruption,
    };
    let (extracted_source, extracted_machine) = extracted_pair(false)?;
    let (_, demoted_machine) = extracted_pair(true)?;
    use VolatileCorruption as K;
    Ok(vec![
        c("identical stream", reference(), reference(), None),
        c(
            "split blocks, an empty block and a rotated loop",
            reference(),
            control_graph(&[
                (&[], &[1]),
                (&[L4], &[2, 4]),
                (&[S4], &[3]),
                (&[], &[2, 4]),
                (&[L4], &[]),
            ]),
            None,
        ),
        c(
            "loop unrolled by two with a remainder",
            reference(),
            control_graph(&[
                (&[L4], &[1, 2, 3]),
                (&[S4, S4], &[1, 2, 3]),
                (&[L4], &[]),
                (&[S4], &[2]),
            ]),
            None,
        ),
        c(
            "extracted LIR and machine functions",
            extracted_source.clone(),
            extracted_machine,
            None,
        ),
        c(
            "the entry load deleted",
            reference(),
            control_graph(&[(&[], &[1, 2]), (&[S4], &[1, 2]), (&[L4], &[])]),
            Some(K::Delete),
        ),
        c(
            "the loop store duplicated",
            reference(),
            control_graph(&[(&[L4], &[1, 2]), (&[S4, S4], &[1, 2]), (&[L4], &[])]),
            Some(K::Duplicate),
        ),
        c(
            "two 32-bit loads merged into one 64-bit load",
            control_graph(&[(&[L4, L4], &[])]),
            control_graph(&[(&[L8], &[])]),
            Some(K::Merge),
        ),
        c(
            "a load reordered past a store",
            control_graph(&[(&[L4, S4], &[])]),
            control_graph(&[(&[S4, L4], &[])]),
            Some(K::Reorder),
        ),
        c(
            "the exit load widened to 64 bits, same count and order",
            reference(),
            control_graph(&[(&[L4], &[1, 2]), (&[S4], &[1, 2]), (&[L8], &[])]),
            Some(K::Resize),
        ),
        c(
            "the loop store hoisted out of the loop",
            reference(),
            control_graph(&[(&[L4, S4], &[1, 2]), (&[], &[1, 2]), (&[L4], &[])]),
            Some(K::Hoist),
        ),
        c(
            "the loop body's path removed",
            reference(),
            control_graph(&[(&[L4], &[2]), (&[S4], &[1, 2]), (&[L4], &[])]),
            Some(K::RemovePath),
        ),
        c(
            "the volatile load demoted to a plain LDR (extracted)",
            extracted_source,
            demoted_machine,
            Some(K::Demote),
        ),
        c(
            "a volatile store fabricated after the loop",
            reference(),
            control_graph(&[(&[L4], &[1, 2]), (&[S4], &[1, 2]), (&[L4, S1], &[])]),
            Some(K::Fabricate),
        ),
    ])
}

/// What the credit hook established.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VolatilePreservationCredit {
    /// Positive controls preserved.
    pub positives: usize,
    /// Negative controls refuted.
    pub controls_refuted: usize,
}

/// The coverage-gate credit hook for the volatile preservation facet.
pub fn volatile_preservation_credit() -> Result<VolatilePreservationCredit, String> {
    let controls =
        volatile_trace_controls().map_err(|error| format!("control battery: {error}"))?;
    volatile_preservation_credit_with(&controls)
}

/// [`volatile_preservation_credit`] over an injected battery. Refuses unless
/// every positive is preserved, every negative is refuted, and the battery
/// has a negative for each of deletion, duplication, merging, reordering
/// and resizing.
pub fn volatile_preservation_credit_with(
    controls: &[VolatileTraceControl],
) -> Result<VolatilePreservationCredit, String> {
    let mut positives = 0;
    let mut controls_refuted = 0;
    let mut kinds = BTreeSet::new();
    for control in controls {
        let outcome = check_volatile_trace_preservation(&control.source, &control.machine)
            .map_err(|error| format!("control `{}`: {error}", control.label))?;
        match (control.corruption, outcome) {
            (None, VolatileTraceOutcome::Preserved(_)) => positives += 1,
            (Some(kind), VolatileTraceOutcome::Violated(_)) => {
                controls_refuted += 1;
                kinds.insert(kind);
            }
            (None, VolatileTraceOutcome::Violated(violation)) => {
                return Err(format!(
                    "positive control `{}` was refuted: {violation}",
                    control.label
                ));
            }
            (Some(_), VolatileTraceOutcome::Preserved(_)) => {
                return Err(format!(
                    "negative control `{}` survived: the check accepted a corrupted stream",
                    control.label
                ));
            }
        }
    }
    for required in [
        VolatileCorruption::Delete,
        VolatileCorruption::Duplicate,
        VolatileCorruption::Merge,
        VolatileCorruption::Reorder,
        VolatileCorruption::Resize,
    ] {
        if !kinds.contains(&required) {
            return Err(format!("the battery has no refuted {required:?} control"));
        }
    }
    if positives == 0 {
        return Err("the battery has no positive control".into());
    }
    Ok(VolatilePreservationCredit {
        positives,
        controls_refuted,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn credit_hook_accepts_the_battery_and_refuses_a_surviving_control() {
        let credit = volatile_preservation_credit().unwrap();
        assert_eq!(credit.positives, 4);
        assert_eq!(credit.controls_refuted, 9);
        let mut battery = volatile_trace_controls().unwrap();
        let identity = battery[0].clone();
        battery.push(VolatileTraceControl {
            label: "identity mutation must survive",
            corruption: Some(VolatileCorruption::Delete),
            ..identity
        });
        assert!(
            volatile_preservation_credit_with(&battery)
                .is_err_and(|error| error.contains("identity mutation must survive"))
        );
        for required in [VolatileCorruption::Merge, VolatileCorruption::Resize] {
            let without: Vec<_> = volatile_trace_controls()
                .unwrap()
                .into_iter()
                .filter(|control| control.corruption != Some(required))
                .collect();
            assert!(
                volatile_preservation_credit_with(&without)
                    .is_err_and(|error| error.contains(&format!("{required:?}"))),
                "{required:?}"
            );
        }
    }

    /// A size change alone — the same accesses, in the same order and number,
    /// one of them at another width — is refuted in both directions. Nothing
    /// else distinguishes these words, so a check that compared labels by
    /// direction only would accept every one of them.
    #[test]
    fn a_size_change_alone_is_refuted() {
        const S8: VolatileAccess = VolatileAccess {
            kind: VolatileAccessKind::Store,
            bytes: 8,
        };
        let source = reference();
        for (machine, side) in [
            // The exit load widened.
            (
                graph(vec![
                    block(&[L4], &[1, 2]),
                    block(&[S4], &[1, 2]),
                    block(&[L8], &[]),
                ]),
                VolatileTraceSide::SourceOnly,
            ),
            // The loop store widened: only paths through the loop differ.
            (
                graph(vec![
                    block(&[L4], &[1, 2]),
                    block(&[S8], &[1, 2]),
                    block(&[L4], &[]),
                ]),
                VolatileTraceSide::SourceOnly,
            ),
        ] {
            match check(&source, &machine) {
                VolatileTraceOutcome::Violated(violation) => {
                    assert_eq!(violation.side, side, "{violation}");
                }
                other => panic!("{other:?}"),
            }
        }
        // Narrowing in the other direction: the machine performs an 8-byte
        // load where the source performs a 4-byte one, in a single block.
        let wide = graph(vec![block(&[L8, S4], &[])]);
        let narrow = graph(vec![block(&[L4, S4], &[])]);
        assert!(matches!(
            check(&wide, &narrow),
            VolatileTraceOutcome::Violated(_)
        ));
    }

    const L4: VolatileAccess = VolatileAccess {
        kind: VolatileAccessKind::Load,
        bytes: 4,
    };
    const L8: VolatileAccess = VolatileAccess {
        kind: VolatileAccessKind::Load,
        bytes: 8,
    };
    const S4: VolatileAccess = VolatileAccess {
        kind: VolatileAccessKind::Store,
        bytes: 4,
    };

    fn block(accesses: &[VolatileAccess], successors: &[usize]) -> VolatileTraceBlock {
        VolatileTraceBlock {
            accesses: accesses.to_vec(),
            successors: successors.to_vec(),
            exits: successors.is_empty(),
        }
    }

    fn graph(blocks: Vec<VolatileTraceBlock>) -> VolatileTraceGraph {
        VolatileTraceGraph { entry: 0, blocks }
    }

    fn check(source: &VolatileTraceGraph, machine: &VolatileTraceGraph) -> VolatileTraceOutcome {
        check_volatile_trace_preservation(source, machine).unwrap()
    }

    /// entry: L4; loop { S4 } ; exit: L4 — a straight-line prefix, a loop and
    /// a branch around it.
    fn reference() -> VolatileTraceGraph {
        graph(vec![
            block(&[L4], &[1, 2]),
            block(&[S4], &[1, 2]),
            block(&[L4], &[]),
        ])
    }

    #[test]
    fn identical_and_restructured_graphs_are_preserved() {
        let source = reference();
        assert!(matches!(
            check(&source, &source),
            VolatileTraceOutcome::Preserved(_)
        ));
        // Block splitting, empty-block insertion and a rotated loop spell the
        // same words.
        let restructured = graph(vec![
            block(&[], &[1]),
            block(&[L4], &[2, 4]),
            block(&[S4], &[3]),
            block(&[], &[2, 4]),
            block(&[L4], &[]),
        ]);
        assert!(matches!(
            check(&source, &restructured),
            VolatileTraceOutcome::Preserved(_)
        ));
        // Partial loop unrolling by two with a remainder keeps S4*.
        let unrolled = graph(vec![
            block(&[L4], &[1, 2, 3]),
            block(&[S4, S4], &[1, 2, 3]),
            block(&[L4], &[]),
            block(&[S4], &[2]),
        ]);
        assert!(matches!(
            check(&source, &unrolled),
            VolatileTraceOutcome::Preserved(_)
        ));
    }

    #[test]
    fn deletion_duplication_merge_and_reorder_are_refuted() {
        let source = reference();
        let refuted = |machine: VolatileTraceGraph, side| match check(&source, &machine) {
            VolatileTraceOutcome::Violated(violation) => {
                assert_eq!(violation.side, side, "{violation}");
                violation
            }
            other => panic!("{other:?}"),
        };
        // Delete the entry load: the machine now completes a path after a
        // single load.
        let deleted = refuted(
            graph(vec![
                block(&[], &[1, 2]),
                block(&[S4], &[1, 2]),
                block(&[L4], &[]),
            ]),
            VolatileTraceSide::MachineOnly,
        );
        assert_eq!(deleted.witness, vec![L4]);
        assert_eq!(deleted.scope, VolatileTraceScope::CompletePath);
        // Duplicate the loop store: the loop now performs pairs only.
        let duplicated = refuted(
            graph(vec![
                block(&[L4], &[1, 2]),
                block(&[S4, S4], &[1, 2]),
                block(&[L4], &[]),
            ]),
            VolatileTraceSide::SourceOnly,
        );
        assert_eq!(duplicated.witness, vec![L4, S4, L4]);
        // Duplicate the exit load.
        refuted(
            graph(vec![
                block(&[L4], &[1, 2]),
                block(&[S4], &[1, 2]),
                block(&[L4, L4], &[]),
            ]),
            VolatileTraceSide::SourceOnly,
        );
        // Merge two 4-byte loads into one 8-byte load.
        let two_loads = graph(vec![block(&[L4, L4], &[])]);
        assert!(matches!(
            check(&two_loads, &graph(vec![block(&[L8], &[])])),
            VolatileTraceOutcome::Violated(_)
        ));
        // Reorder a load past a store.
        let load_store = graph(vec![block(&[L4, S4], &[])]);
        let reordered = check(&load_store, &graph(vec![block(&[S4, L4], &[])]));
        assert!(matches!(reordered, VolatileTraceOutcome::Violated(_)));
        // Hoist the loop store out of the loop (executed once, not per trip).
        refuted(
            graph(vec![
                block(&[L4, S4], &[1, 2]),
                block(&[], &[1, 2]),
                block(&[L4], &[]),
            ]),
            VolatileTraceSide::SourceOnly,
        );
        // Delete the whole loop body.
        refuted(
            graph(vec![
                block(&[L4], &[2]),
                block(&[S4], &[1, 2]),
                block(&[L4], &[]),
            ]),
            VolatileTraceSide::SourceOnly,
        );
    }

    /// Two same-label accesses are interchangeable: a swap of two 4-byte
    /// loads is NOT refuted. This pins the stated limit of the claim.
    #[test]
    fn same_label_swap_is_outside_the_claim() {
        let a = graph(vec![block(&[L4, L4], &[])]);
        assert!(matches!(
            check(&a, &a.clone()),
            VolatileTraceOutcome::Preserved(_)
        ));
    }

    /// Removing an infeasible path is refused (fail-closed), not accepted.
    #[test]
    fn path_removal_is_refused_even_when_it_would_be_legal() {
        let optional = graph(vec![
            block(&[], &[1, 2]),
            block(&[S4], &[2]),
            block(&[], &[]),
        ]);
        let folded = graph(vec![block(&[], &[1]), block(&[], &[])]);
        assert!(matches!(
            check(&optional, &folded),
            VolatileTraceOutcome::Violated(VolatileTraceViolation {
                side: VolatileTraceSide::SourceOnly,
                ..
            })
        ));
    }

    #[test]
    fn graphs_without_volatile_accesses_are_trivially_preserved() {
        let empty = graph(vec![block(&[], &[1]), block(&[], &[])]);
        assert!(matches!(
            check(&empty, &graph(vec![block(&[], &[])])),
            VolatileTraceOutcome::Preserved(VolatileTraceCertificate {
                product_states: 0,
                ..
            })
        ));
        let malformed = VolatileTraceGraph {
            entry: 3,
            blocks: vec![block(&[], &[])],
        };
        assert!(check_volatile_trace_preservation(&malformed, &empty).is_err());
    }

    /// A lowered function whose layout names a block it does not define is
    /// refused as malformed, never a panic inside the per-compile check.
    #[test]
    fn source_layout_naming_a_missing_block_is_malformed() {
        use trust_cg_lower::function::Signature;
        use trust_cg_lower::instructions::Block;
        let mut source = trust_cg_lower::Function::new("stale_layout", Signature::default());
        source.block_order = vec![Block(7)];
        source.entry_block = Block(7);
        assert!(matches!(
            lir_volatile_trace(&source),
            Err(VolatileTraceError::Malformed(_))
        ));
    }
}
