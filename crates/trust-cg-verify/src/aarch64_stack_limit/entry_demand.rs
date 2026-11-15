// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Root-selected fixed-frame demand over the existing final-stream facts.
//!
//! Unlike U10's reserve between checks, a check does not end an entry's
//! demand. This is a structural diagnostic, not a stack-limit certificate,
//! proof, provider-binding fact, runtime headroom check or execution permission.

use std::collections::{BTreeMap, BTreeSet};

use super::{FunctionStackFacts, StackRole};

/// A conservative total fixed-frame demand below one emitted entry's SP.
///
/// The input must be facts from the actual final emitted functions. The
/// diagnostic does not authenticate supplied facts or external assumptions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryStackDemand {
    /// Every reachable own frame and callee demand could be composed.
    Fixed {
        /// Own frame plus the maximum simultaneously active callee demand.
        bytes: u64,
        /// Exact named external assumptions actually used, never inferred.
        /// Their bytes include each external callee's complete call path.
        external_assumptions: BTreeMap<String, u64>,
    },
    /// No total demand is reported; unknown is never a zero-byte demand.
    Unknown(EntryStackDemandUnknown),
}

/// Why a root-selected entry's fixed-frame demand cannot be reported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryStackDemandUnknown {
    /// No emitted function has the requested entry symbol.
    MissingRoot {
        /// Requested entry symbol.
        root: String,
    },
    /// The emitted symbol roster is ambiguous, including unreachable names.
    DuplicateSymbol {
        /// Lexicographically first ambiguous symbol.
        symbol: String,
    },
    /// A reachable own frame could not be modeled by the final-stream net.
    UnknownFrame {
        /// Function whose frame is unknown.
        function: String,
    },
    /// A reachable indirect call has no exact target-set evidence here.
    IndirectCall {
        /// Function containing the indirect call.
        function: String,
    },
    /// A reachable call cycle has no separately established iteration bound.
    ReachableCycle {
        /// Deterministic cycle path, with its first symbol repeated at the end.
        cycle: Vec<String>,
    },
    /// A direct external call has no exact named demand assumption.
    UnboundExternalCall {
        /// Function containing the call.
        caller: String,
        /// External callee symbol.
        callee: String,
    },
    /// A checked function's external overflow handler has no named assumption.
    UnboundOverflowHandler {
        /// Function declaring the handler.
        function: String,
        /// External handler symbol.
        handler: String,
    },
    /// Composing a reachable frame and its callee would overflow `u64`.
    AdditionOverflow {
        /// Function whose demand cannot be represented.
        function: String,
        /// Its own conservative fixed frame.
        frame: u32,
        /// Maximum callee demand to add to that frame.
        callee_demand: u64,
    },
}

/// Compose the total fixed-frame demand of an actual emitted entry.
///
/// External callees and overflow handlers are unknown by default. Checks do
/// not reset total demand, and recursive/indirect/dynamic paths remain unknown.
/// Unrelated unreachable cycles, unknown frames and imports do not affect the
/// selected entry. Duplicate symbols anywhere refuse the ambiguous roster.
pub fn entry_stack_demand(functions: &[FunctionStackFacts], root: &str) -> EntryStackDemand {
    entry_stack_demand_with_assumptions(functions, root, &BTreeMap::new())
}

/// Compose entry demand with explicit assumptions for exact external names.
///
/// An assumption applies only to a callee absent from the emitted roster; it
/// cannot override an emitted body, create a missing root, or resolve an
/// indirect call. It states the external callee's complete demand below its
/// entry SP, including its callees, not merely its local frame. Only actually
/// used assumptions appear in a successful report. No name or byte count
/// authenticates an ABI, provider address, lifetime, proof or runtime owner.
///
/// Every reachable function contributes its full observed frame, including
/// checked functions. A checked function also contributes its overflow handler
/// as a callee. Adding the full frame even for tail calls/overflow paths is a
/// deliberate conservative overestimate. Signal-stack, caller and runtime
/// headroom costs are outside this diagnostic's root-entry boundary.
pub fn entry_stack_demand_with_assumptions(
    functions: &[FunctionStackFacts],
    root: &str,
    external_assumptions: &BTreeMap<String, u64>,
) -> EntryStackDemand {
    match solve(functions, root, external_assumptions) {
        Ok((bytes, external_assumptions)) => EntryStackDemand::Fixed {
            bytes,
            external_assumptions,
        },
        Err(reason) => EntryStackDemand::Unknown(reason),
    }
}

#[derive(Clone, Copy)]
enum CallKind {
    Direct,
    OverflowHandler,
}

#[derive(Clone, Copy)]
struct CallEdge<'a> {
    symbol: &'a str,
    kind: CallKind,
}

struct PendingFunction<'a> {
    index: usize,
    frame: u32,
    callees: Vec<CallEdge<'a>>,
    next_callee: usize,
    maximum_callee: u64,
}

impl<'a> PendingFunction<'a> {
    fn new(
        index: usize,
        function: &'a FunctionStackFacts,
    ) -> Result<Self, EntryStackDemandUnknown> {
        let mut frame = function
            .frame
            .ok_or_else(|| EntryStackDemandUnknown::UnknownFrame {
                function: function.name.clone(),
            })?;
        if function.indirect_call {
            return Err(EntryStackDemandUnknown::IndirectCall {
                function: function.name.clone(),
            });
        }
        let mut callees: Vec<_> = function
            .direct_callees
            .iter()
            .map(|symbol| CallEdge {
                symbol: symbol.as_str(),
                kind: CallKind::Direct,
            })
            .collect();
        if let StackRole::Checked { csa, handler } = &function.role {
            // Actual collected frame depth includes CSA. Keep even supplied
            // contradictory facts conservative; a check never truncates it.
            frame = frame.max(*csa);
            if let Some(handler) = handler {
                // The actual collector already sees the overflow tail call.
                // Preserve that edge but retain its more specific diagnostic.
                if let Some(edge) = callees.iter_mut().find(|edge| edge.symbol == handler) {
                    edge.kind = CallKind::OverflowHandler;
                } else {
                    callees.push(CallEdge {
                        symbol: handler,
                        kind: CallKind::OverflowHandler,
                    });
                    callees.sort_unstable_by_key(|edge| edge.symbol);
                }
            }
        }
        Ok(Self {
            index,
            frame,
            callees,
            next_callee: 0,
            maximum_callee: 0,
        })
    }
}

fn solve(
    functions: &[FunctionStackFacts],
    root: &str,
    external_assumptions: &BTreeMap<String, u64>,
) -> Result<(u64, BTreeMap<String, u64>), EntryStackDemandUnknown> {
    let mut index = BTreeMap::new();
    let mut duplicates = BTreeSet::new();
    for (position, function) in functions.iter().enumerate() {
        if index.insert(function.name.as_str(), position).is_some() {
            duplicates.insert(function.name.as_str());
        }
    }
    if let Some(symbol) = duplicates.first() {
        return Err(EntryStackDemandUnknown::DuplicateSymbol {
            symbol: (*symbol).to_string(),
        });
    }
    let root_index = *index
        .get(root)
        .ok_or_else(|| EntryStackDemandUnknown::MissingRoot {
            root: root.to_string(),
        })?;

    // Iterative DFS distinguishes active nodes from completed shared callees.
    // The compiler's own Rust stack never grows with a model's call depth.
    let mut active = vec![false; functions.len()];
    let mut completed = vec![None; functions.len()];
    let mut stack = vec![PendingFunction::new(root_index, &functions[root_index])?];
    let mut used_assumptions = BTreeMap::new();
    active[root_index] = true;
    while let Some(current) = stack.last_mut() {
        if let Some(&edge) = current.callees.get(current.next_callee) {
            current.next_callee += 1;
            if let Some(&callee) = index.get(edge.symbol) {
                if let Some(demand) = completed[callee] {
                    current.maximum_callee = current.maximum_callee.max(demand);
                } else if active[callee] {
                    let cycle_start = stack
                        .iter()
                        .position(|pending| pending.index == callee)
                        .expect("an active function is on the traversal stack");
                    let mut cycle: Vec<_> = stack[cycle_start..]
                        .iter()
                        .map(|pending| functions[pending.index].name.clone())
                        .collect();
                    cycle.push(functions[callee].name.clone());
                    return Err(EntryStackDemandUnknown::ReachableCycle { cycle });
                } else {
                    stack.push(PendingFunction::new(callee, &functions[callee])?);
                    active[callee] = true;
                }
            } else if let Some(&demand) = external_assumptions.get(edge.symbol) {
                used_assumptions.insert(edge.symbol.to_string(), demand);
                current.maximum_callee = current.maximum_callee.max(demand);
            } else {
                let function = functions[current.index].name.clone();
                return Err(match edge.kind {
                    CallKind::Direct => EntryStackDemandUnknown::UnboundExternalCall {
                        caller: function,
                        callee: edge.symbol.to_string(),
                    },
                    CallKind::OverflowHandler => EntryStackDemandUnknown::UnboundOverflowHandler {
                        function,
                        handler: edge.symbol.to_string(),
                    },
                });
            }
        } else {
            let finished = stack.pop().expect("the traversal stack is nonempty");
            let demand = u64::from(finished.frame)
                .checked_add(finished.maximum_callee)
                .ok_or_else(|| EntryStackDemandUnknown::AdditionOverflow {
                    function: functions[finished.index].name.clone(),
                    frame: finished.frame,
                    callee_demand: finished.maximum_callee,
                })?;
            active[finished.index] = false;
            completed[finished.index] = Some(demand);
            if let Some(parent) = stack.last_mut() {
                parent.maximum_callee = parent.maximum_callee.max(demand);
            } else {
                return Ok((demand, used_assumptions));
            }
        }
    }
    unreachable!("the root traversal returns when its final function completes")
}

#[cfg(test)]
mod tests;
