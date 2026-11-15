// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Closed, acyclic semantic equations shared by original-source and target
//! observations. Fresh occurrence names are not a certificate, caller premise
//! or execution capability. Only past definitions from the SAME stage may be
//! referenced; the byte observer is never an architectural input.

use crate::memory_proofs::memory_sort;
use crate::smt::{SmtExpr as E, SmtSort};
use std::collections::{HashMap, HashSet};

#[cfg(test)]
#[path = "scalar_memory_definitions_tests.rs"]
mod tests;

#[derive(Clone, Copy)]
pub(crate) enum Stage {
    Core,
    Lir,
    Machine,
    Words,
}

impl Stage {
    fn prefix(self) -> &'static str {
        match self {
            Self::Core => "scalar_memory_core_d",
            Self::Lir => "scalar_memory_lir_d",
            Self::Machine => "scalar_memory_machine_d",
            Self::Words => "scalar_memory_words_d",
        }
    }

    fn target(self) -> bool {
        matches!(self, Self::Machine | Self::Words)
    }
}

pub(crate) struct Limits {
    pub(crate) rhs_nodes: usize,
    pub(crate) collection_nodes: usize,
    pub(crate) occurrences: usize,
}

pub(crate) enum Error {
    Invalid(&'static str),
    Budget(&'static str),
}

pub(crate) struct Definitions {
    stage: Stage,
    abi_arity: usize,
    limits: Limits,
    pub(crate) sorts: HashMap<String, SmtSort>,
    pub(crate) equations: Vec<E>,
    pub(crate) nodes: usize,
    conditional_inputs: Option<HashMap<String, SmtSort>>,
    conditional_occurrences: usize,
}

impl Definitions {
    // Closed target-only nondeterministic inputs. No source namespace or
    // physical preservation is shared by allocating these symbols.
    pub(crate) fn native_target_input(&mut self, sort: SmtSort) -> Result<E, Error> {
        if !self.stage.target() {
            return Err(Error::Invalid("native target input stage"));
        }
        let inputs = self
            .conditional_inputs
            .as_mut()
            .ok_or(Error::Invalid("native target inputs disabled"))?;
        if inputs.len() >= self.limits.occurrences {
            return Err(Error::Budget("native target input occurrences"));
        }
        let name = format!(
            "{}_native{}",
            self.stage.prefix(),
            self.conditional_occurrences
        );
        self.conditional_occurrences += 1;
        inputs.insert(name.clone(), sort.clone());
        Ok(E::uf(name, vec![], sort))
    }
    pub(crate) fn new(stage: Stage, abi_arity: usize, limits: Limits) -> Self {
        Self {
            stage,
            abi_arity,
            limits,
            sorts: HashMap::new(),
            equations: Vec::new(),
            nodes: 0,
            conditional_inputs: None,
            conditional_occurrences: 0,
        }
    }

    // The old constructor keeps this closed. Only the separate conditional
    // wrapper profile enables independent, stage-local nondeterministic outcomes.
    pub(crate) fn enable_conditional_call_inputs(&mut self) {
        self.conditional_inputs = Some(HashMap::new());
    }

    pub(crate) fn conditional_call_outcomes(
        &mut self,
        widths: &[u32],
    ) -> Result<(Vec<E>, E, E), Error> {
        if widths.is_empty() || widths.len() > 8 || widths.iter().any(|w| *w != 64) {
            return Err(Error::Invalid("conditional call result codecs"));
        }
        let inputs = self
            .conditional_inputs
            .as_mut()
            .ok_or(Error::Invalid("conditional call inputs disabled"))?;
        if inputs
            .len()
            .checked_add(widths.len() + 2)
            .is_none_or(|n| n > self.limits.occurrences)
        {
            return Err(Error::Budget("conditional call input occurrences"));
        }
        let prefix = format!(
            "{}_call{}_",
            self.stage.prefix(),
            self.conditional_occurrences
        );
        self.conditional_occurrences += 1;
        let mut declare = |suffix: String, sort: SmtSort| {
            let name = format!("{prefix}{suffix}");
            inputs.insert(name.clone(), sort.clone());
            E::uf(name, vec![], sort)
        };
        let values = widths
            .iter()
            .enumerate()
            .map(|(i, w)| declare(format!("result{i}"), SmtSort::BitVec(*w)))
            .collect();
        let memory = declare("memory".into(), memory_sort());
        let normal = declare("returned_normally".into(), SmtSort::Bool);
        Ok((values, memory, normal))
    }

    /// ONE logical flat record, not a scalar-vector return signature. Only
    /// the separate native-event profile calls this closed allocator.
    pub(crate) fn conditional_record_outcome(&mut self) -> Result<([E; 2], E, E), Error> {
        let inputs = self
            .conditional_inputs
            .as_mut()
            .ok_or(Error::Invalid("conditional record inputs disabled"))?;
        if inputs
            .len()
            .checked_add(4)
            .is_none_or(|n| n > self.limits.occurrences)
        {
            return Err(Error::Budget("conditional record input occurrences"));
        }
        let prefix = format!(
            "{}_record{}_",
            self.stage.prefix(),
            self.conditional_occurrences
        );
        self.conditional_occurrences += 1;
        let mut declare = |suffix: &str, sort: SmtSort| {
            let name = format!("{prefix}{suffix}");
            inputs.insert(name.clone(), sort.clone());
            E::uf(name, vec![], sort)
        };
        let fields = [
            declare("field0", SmtSort::BitVec(64)),
            declare("field1", SmtSort::BitVec(64)),
        ];
        let memory = declare("memory", memory_sort());
        let normal = declare("returned_normally", SmtSort::Bool);
        Ok((fields, memory, normal))
    }

    fn input(&self, name: &str, width: u32) -> bool {
        if width == 64 {
            if numbered_input(name, "abi_x", 0, self.abi_arity.min(8)) {
                return true;
            }
            if self.stage.target() && numbered_input(name, "entry_x", self.abi_arity, 31) {
                return true;
            }
        }
        self.stage.target()
            && width == 1
            && ["entry_n", "entry_z", "entry_c", "entry_v"].contains(&name)
    }

    /// Reserve a whole effect's fresh occurrences before any equation is
    /// installed. Node preflight remains the observer's separate obligation.
    pub(crate) fn preflight_occurrences(&self, additional: usize) -> Result<(), Error> {
        self.equations
            .len()
            .checked_add(additional)
            .filter(|n| *n <= self.limits.occurrences)
            .map(|_| ())
            .ok_or(Error::Budget("scalar-memory definition occurrences"))
    }

    /// Reserve and inspect the entire RHS before installing either the fresh
    /// declaration or its equation. Refusal leaves the collection unchanged.
    pub(crate) fn bind(&mut self, value: E, value_nodes: usize, sort: SmtSort) -> Result<E, Error> {
        if self.abi_arity > 8 {
            return Err(Error::Invalid("scalar-memory ABI arity"));
        }
        if value_nodes > self.limits.rhs_nodes {
            return Err(Error::Budget("scalar-memory definition expression"));
        }
        let next = self
            .nodes
            .checked_add(value_nodes)
            .and_then(|n| n.checked_add(2))
            .filter(|n| *n <= self.limits.collection_nodes)
            .ok_or(Error::Budget("scalar-memory definition collection"))?;
        self.preflight_occurrences(1)?;
        match &sort {
            SmtSort::BitVec(bits @ (1 | 32 | 64)) if value.try_bv_width().ok() == Some(*bits) => {}
            SmtSort::Bool if self.stage.target() && value.sort() == SmtSort::Bool => {}
            SmtSort::Array(_, _) if sort == memory_sort() && matches!(value, E::Store { .. }) => {}
            _ => return Err(Error::Invalid("scalar-memory definition sort")),
        }
        let mut pending = vec![&value];
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node as *const E) {
                continue;
            }
            if seen.len() > self.limits.rhs_nodes {
                return Err(Error::Budget("scalar-memory definition graph"));
            }
            match node {
                E::Var { name, width } if self.input(name, *width) => {}
                E::Var { .. } => {
                    return Err(Error::Invalid("unknown scalar-memory free input"));
                }
                E::UF {
                    name,
                    args,
                    ret_sort,
                } if args.is_empty() => {
                    let initial = name == "entry_memory" && *ret_sort == memory_sort();
                    if !initial
                        && self.sorts.get(name) != Some(ret_sort)
                        && self
                            .conditional_inputs
                            .as_ref()
                            .and_then(|inputs| inputs.get(name))
                            != Some(ret_sort)
                    {
                        return Err(Error::Invalid(
                            "undefined or cross-stage scalar-memory symbol",
                        ));
                    }
                }
                E::UF { .. }
                | E::UFDecl { .. }
                | E::ForAll { .. }
                | E::Exists { .. }
                | E::TrapIfZero { .. }
                | E::MemLoad { .. } => {
                    return Err(Error::Invalid("nonclosed scalar-memory definition"));
                }
                _ => {}
            }
            node.for_each_child(&mut |child| pending.push(child));
        }
        let name = format!("{}{}", self.stage.prefix(), self.equations.len());
        let symbol = E::uf(&name, vec![], sort.clone());
        let equation = symbol.clone().eq_expr(value);
        self.sorts.insert(name, sort);
        self.equations.push(equation);
        self.nodes = next;
        Ok(symbol)
    }
}

// Canonical ABI names are recognized without generating every possible input
// name for every RHS leaf. Reject leading zeros/signs and retain exact bounds.
fn numbered_input(name: &str, prefix: &str, first: usize, end: usize) -> bool {
    let Some(digits) = name.strip_prefix(prefix) else {
        return false;
    };
    !digits.is_empty()
        && (digits.len() == 1 || !digits.starts_with('0'))
        && digits.bytes().all(|b| b.is_ascii_digit())
        && digits.parse::<usize>().is_ok_and(|i| first <= i && i < end)
}
