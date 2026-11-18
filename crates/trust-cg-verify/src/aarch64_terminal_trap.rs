// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Check the values and edges of an unsigned counted loop ending in a call
//! followed by a trap. The recurrence relates corresponding visits to the
//! two headers. If the work includes a recognized Euclidean loop, check
//! the remaining normal CFG after contracting its finite remainder phase.

use std::collections::VecDeque;

use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};
use trust_cg_ir::{InstId, MachFunction};
use trust_cg_lower::{Function, instructions::Block};

use crate::aarch64_omitted_trap::EuclideanSource;

#[path = "../../../formal/lean/Trust/A64/ConditionalTrap.lean"]
clean mod conditional_trap;

#[path = "aarch64_terminal_trap_machine.rs"]
mod machine;
#[path = "aarch64_terminal_trap_source.rs"]
mod source;

const MAX_NODES: usize = 1024;
const MAX_VARIABLES: usize = 256;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Recurrence {
    initial: u64,
    limit: u64,
    increment: u64,
}

#[derive(Clone, Copy)]
enum Operand {
    Variable(usize),
    Immediate(u64),
}

#[derive(Clone, Copy)]
enum Effect {
    Unknown(usize),
    Constant {
        dst: usize,
        value: u64,
    },
    Copy {
        dst: usize,
        src: usize,
    },
    Add {
        dst: usize,
        lhs: Operand,
        rhs: Operand,
    },
    ReplaceBits {
        dst: usize,
        mask: u64,
        value: u64,
    },
}

struct Node {
    effects: Vec<Effect>,
    next: Vec<usize>,
}

struct Graph {
    nodes: Vec<Node>,
    variables: usize,
}

struct EuclideanExit {
    backedge: (usize, usize),
    zero: usize,
    impossible: Option<(usize, usize)>,
}

/// A constant or one header value plus a wrapping constant. Unknown includes
/// any value for which paths disagree or whose defining operation is outside
/// this projection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    Unknown,
    Constant(u64),
    Counter(u64),
    Limit(u64),
}

impl Value {
    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Constant(a), Self::Constant(b)) => {
                Self::Constant(trust_cg_a64_trap_counter_step(a, b))
            }
            (Self::Counter(a), Self::Constant(b)) | (Self::Constant(b), Self::Counter(a)) => {
                Self::Counter(trust_cg_a64_trap_counter_step(a, b))
            }
            (Self::Limit(a), Self::Constant(b)) | (Self::Constant(b), Self::Limit(a)) => {
                Self::Limit(trust_cg_a64_trap_counter_step(a, b))
            }
            _ => Self::Unknown,
        }
    }
}

impl Operand {
    fn read(self, values: &[Value]) -> Option<Value> {
        Some(match self {
            Self::Variable(index) => *values.get(index)?,
            Self::Immediate(bits) => Value::Constant(bits),
        })
    }
}

impl Node {
    fn apply(&self, values: &mut [Value]) -> Option<()> {
        for effect in &self.effects {
            let (dst, replacement) = match *effect {
                Effect::Unknown(dst) => (dst, Value::Unknown),
                Effect::Constant { dst, value } => (dst, Value::Constant(value)),
                Effect::Copy { dst, src } => (dst, *values.get(src)?),
                Effect::Add { dst, lhs, rhs } => (dst, lhs.read(values)?.add(rhs.read(values)?)),
                Effect::ReplaceBits { dst, mask, value } => {
                    let previous = *values.get(dst)?;
                    let updated = match previous {
                        Value::Constant(bits) => Value::Constant((bits & !mask) | (value & mask)),
                        _ => Value::Unknown,
                    };
                    (dst, updated)
                }
            };
            *values.get_mut(dst)? = replacement;
        }
        Some(())
    }
}

impl Graph {
    fn recurrence(
        &self,
        entry: usize,
        header: usize,
        work: usize,
        [counter, limit]: [usize; 2],
    ) -> Option<Recurrence> {
        if self.nodes.len() > MAX_NODES
            || self.variables > MAX_VARIABLES
            || counter == limit
            || entry == header
            || !self.nodes.get(header)?.next.contains(&work)
            || counter >= self.variables
            || limit >= self.variables
        {
            return None;
        }

        // Initialization must run straight through to the first header
        // visit. Parameters and registers start without assumed values.
        let mut initial = vec![Value::Unknown; self.variables];
        let mut seen = vec![false; self.nodes.len()];
        let mut at = entry;
        while at != header {
            if std::mem::replace(seen.get_mut(at)?, true) {
                return None;
            }
            let node = self.nodes.get(at)?;
            node.apply(&mut initial)?;
            let [next] = node.next.as_slice() else {
                return None;
            };
            at = *next;
        }
        let (Value::Constant(initial_counter), Value::Constant(initial_limit)) =
            (initial[counter], initial[limit])
        else {
            return None;
        };

        // Start the work edge with arbitrary header values. The child
        // binders check that evaluating the guard preserves both operands.
        // Stop before the next header visit and join all possible paths,
        // including complete trips around any inner cycles.
        let mut body_entry = vec![Value::Unknown; self.variables];
        body_entry[counter] = Value::Counter(0);
        body_entry[limit] = Value::Limit(0);
        let latch = self.paths_to_header(work, header, body_entry)?;
        let (Value::Counter(increment), Value::Limit(0)) = (latch[counter], latch[limit]) else {
            return None;
        };
        Some(Recurrence {
            initial: initial_counter,
            limit: initial_limit,
            increment,
        })
    }

    /// Once a local remainder loop is bound, its backedge is finite and
    /// eventual execution continues at its zero successor. The remaining
    /// work graph must be acyclic and all its leaves must reach the header.
    fn finite_work(
        &self,
        work: usize,
        header: usize,
        phase: EuclideanExit,
        allowed: impl Fn(usize) -> bool,
    ) -> Option<()> {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Visit {
            New,
            Active,
            Done,
        }
        let mut state = vec![Visit::New; self.nodes.len()];
        let mut todo = vec![(work, false)];
        let mut seen_backedge = false;
        let mut seen_impossible = phase.impossible.is_none();
        while let Some((at, done)) = todo.pop() {
            if at == header {
                continue;
            }
            let previous = state.get_mut(at)?;
            if done {
                *previous = Visit::Done;
                continue;
            }
            match *previous {
                Visit::Done => continue,
                Visit::Active => return None,
                Visit::New => *previous = Visit::Active,
            }
            if !allowed(at) {
                return None;
            }
            todo.push((at, true));
            let mut has_next = false;
            for &next in &self.nodes.get(at)?.next {
                let edge = (at, next);
                if phase.impossible == Some(edge) {
                    seen_impossible = true;
                    continue;
                }
                let next = if edge == phase.backedge {
                    seen_backedge = true;
                    phase.zero
                } else {
                    next
                };
                has_next = true;
                todo.push((next, false));
            }
            if !has_next {
                return None;
            }
        }
        (seen_backedge && seen_impossible).then_some(())
    }

    fn paths_to_header(&self, work: usize, header: usize, seed: Vec<Value>) -> Option<Vec<Value>> {
        let mut incoming = vec![None; self.nodes.len()];
        *incoming.get_mut(work)? = Some(seed);
        let mut queue = VecDeque::from([work]);
        while let Some(at) = queue.pop_front() {
            if at == header {
                continue;
            }
            let mut outgoing = incoming[at].as_ref()?.clone();
            let node = &self.nodes[at];
            node.apply(&mut outgoing)?;
            for &next in &node.next {
                let slot = incoming.get_mut(next)?;
                if join_state(slot, &outgoing) && next != header {
                    queue.push_back(next);
                }
            }
        }
        incoming.get_mut(header)?.take()
    }
}

fn join_state(slot: &mut Option<Vec<Value>>, incoming: &[Value]) -> bool {
    let Some(current) = slot else {
        *slot = Some(incoming.to_vec());
        return true;
    };
    let mut changed = false;
    for (old, new) in current.iter_mut().zip(incoming) {
        if *old != Value::Unknown && old != new {
            *old = Value::Unknown;
            changed = true;
        }
    }
    changed
}

fn stamp_matches(
    lir: &Function,
    machine: &MachFunction,
    word: InstId,
    source: SourceInstId,
) -> Option<()> {
    let block = Block(source.block);
    let source_row = lir
        .blocks
        .get(&block)?
        .instructions
        .get(source.index as usize)?;
    let origin = lir
        .trust_ir_origins
        .get(&block)
        .and_then(|origins| origins.get(source.index as usize))
        .copied()
        .flatten();
    let LoweringProvenance::SourceInst {
        id,
        digest,
        trust_ir_inst,
    } = machine.inst_lowering_provenance(word)
    else {
        return None;
    };
    (id == source && digest == source_row.lowering_digest() && trust_ir_inst == origin)
        .then_some(())
}

/// A checked local correspondence within the same header occurrence.
/// This evidence is diagnostic until the surrounding event and call
/// correspondence can be replayed on the original request.
pub(crate) fn describe(
    lir: &Function,
    machine: &MachFunction,
    word: InstId,
    trap: SourceInstId,
) -> Option<String> {
    if lir.name != machine.name {
        return None;
    }
    let src = source::bind(lir, trap)?;
    let dst = machine::bind(machine, word, src.euclidean.as_ref())?;
    if src.recurrence != dst.recurrence || src.symbol != dst.symbol {
        return None;
    }
    for (machine_word, source_id) in [
        (dst.compare, src.compare),
        (dst.branch, src.branch),
        (dst.call, src.call),
        (word, trap),
    ] {
        stamp_matches(lir, machine, machine_word, source_id)?;
    }
    let Recurrence {
        initial,
        limit,
        increment,
    } = src.recurrence;
    // The two binders identify the same loop-exit predicate and a following
    // normal call continuation. Compute which events can reach the trap.
    let trap_outcomes =
        [false, true].map(|returned| trust_cg_a64_trap_after_return(true, returned));
    let work = match (src.euclidean, dst.euclidean_rows) {
        (
            Some(EuclideanSource {
                switch, remainder, ..
            }),
            Some([guard, divide, msub]),
        ) if [
            (guard, switch.0),
            (divide, remainder.0),
            (msub, remainder.0),
        ]
        .into_iter()
        .all(|(row, origin)| stamp_matches(lir, machine, row, origin).is_some()) =>
        {
            ". Both normal work paths reach their next headers by finite Euclidean remainder progress"
        }
        _ => "",
    };
    (trap_outcomes == [false, true]).then(|| format!(
        "BRK has a matched ULT/HS loop counter projection (initial {initial}, limit {limit}, step {increment}) and a matched symbolic call continuation{work}. Header execution effects, call effects and return outcomes still need source-bound proof"
    ))
}

#[cfg(test)]
#[path = "aarch64_terminal_trap_tests.rs"]
mod tests;
