// trust-cg-jit-matrix/src/bcp_baseline.rs - Native Rust watched-literal BCP baseline.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

pub type ClauseIdx = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value {
    Unassigned,
    True,
    False,
}

pub struct BcpState {
    num_vars: usize,
    clauses: Vec<Vec<i32>>,
    watches: Vec<Vec<ClauseIdx>>,
    values: Vec<Value>,
    trail: Vec<i32>,
    /// Parallel to `trail`: the 0-based JIT clause index that forced
    /// each literal. For decision literals (input from `assign(...)`
    /// outside of `propagate(...)`), the entry is `usize::MAX`. Used
    /// by `BcpKernelProvider` to emit the per-implied-literal reason
    /// stream when the host installs a reasons buffer.
    reasons: Vec<usize>,
    qhead: usize,
}

impl BcpState {
    pub fn new(num_vars: usize, mut clauses: Vec<Vec<i32>>) -> Self {
        let mut watches: Vec<Vec<ClauseIdx>> = vec![Vec::new(); 2 * num_vars + 2];
        let values = vec![Value::Unassigned; num_vars + 1];

        for (ci, clause) in clauses.iter_mut().enumerate() {
            if clause.len() >= 2 {
                // watched literal invariant: positions 0 and 1 of each clause
                let w0 = clause[0];
                let w1 = clause[1];
                watches[lit_index(w0)].push(ci);
                watches[lit_index(w1)].push(ci);
            }
        }

        Self {
            num_vars,
            clauses,
            watches,
            values,
            trail: Vec::new(),
            reasons: Vec::new(),
            qhead: 0,
        }
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    pub fn value_of_lit(&self, lit: i32) -> Value {
        let v = lit.unsigned_abs() as usize;
        match self.values[v] {
            Value::Unassigned => Value::Unassigned,
            Value::True => {
                if lit > 0 {
                    Value::True
                } else {
                    Value::False
                }
            }
            Value::False => {
                if lit > 0 {
                    Value::False
                } else {
                    Value::True
                }
            }
        }
    }

    pub fn assign(&mut self, lit: i32) {
        // Decision-level assignment: reason is "no clause" (usize::MAX).
        self.assign_with_reason(lit, usize::MAX);
    }

    /// Like `assign`, but also records the JIT clause index that forced
    /// the literal. Used internally by `propagate(...)` to keep the
    /// `reasons` array in lockstep with `trail`.
    pub fn assign_with_reason(&mut self, lit: i32, reason_ci: usize) {
        let v = lit.unsigned_abs() as usize;
        if self.values[v] != Value::Unassigned {
            return;
        }
        self.values[v] = if lit > 0 { Value::True } else { Value::False };
        self.trail.push(lit);
        self.reasons.push(reason_ci);
    }

    pub fn propagate(&mut self) -> Option<ClauseIdx> {
        // Handle unit clauses on first propagation.
        if self.qhead == 0 {
            for ci in 0..self.clauses.len() {
                if self.clauses[ci].len() == 1 {
                    let unit = self.clauses[ci][0];
                    match self.value_of_lit(unit) {
                        Value::False => return Some(ci),
                        Value::Unassigned => self.assign_with_reason(unit, ci),
                        Value::True => {}
                    }
                }
            }
        }

        while self.qhead < self.trail.len() {
            let assigned = self.trail[self.qhead];
            self.qhead += 1;
            let falsified = -assigned;
            let watch_idx = lit_index(falsified);

            let mut i = 0usize;
            let mut new_watches: Vec<ClauseIdx> = Vec::with_capacity(self.watches[watch_idx].len());
            let watch_list = std::mem::take(&mut self.watches[watch_idx]);

            while i < watch_list.len() {
                let ci = watch_list[i];
                i += 1;

                let clause_len = self.clauses[ci].len();
                if clause_len < 2 {
                    new_watches.push(ci);
                    continue;
                }

                // Ensure clause[1] is the falsified watched literal.
                if self.clauses[ci][0] == falsified {
                    self.clauses[ci].swap(0, 1);
                }

                let other = self.clauses[ci][0];
                if self.value_of_lit(other) == Value::True {
                    new_watches.push(ci);
                    continue;
                }

                let mut found_replacement = false;
                for k in 2..clause_len {
                    let cand = self.clauses[ci][k];
                    if self.value_of_lit(cand) != Value::False {
                        self.clauses[ci].swap(1, k);
                        self.watches[lit_index(cand)].push(ci);
                        found_replacement = true;
                        break;
                    }
                }

                if found_replacement {
                    continue;
                }

                new_watches.push(ci);

                match self.value_of_lit(other) {
                    Value::False => {
                        self.watches[watch_idx] = new_watches;
                        // Append the remaining unprocessed entries.
                        for &rest in &watch_list[i..] {
                            self.watches[watch_idx].push(rest);
                        }
                        return Some(ci);
                    }
                    Value::Unassigned => {
                        self.assign_with_reason(other, ci);
                    }
                    Value::True => {}
                }
            }

            self.watches[watch_idx] = new_watches;
        }

        None
    }

    pub fn trail_len(&self) -> usize {
        self.trail.len()
    }

    /// Return the literal at trail index `idx`. Panics if `idx >=
    /// trail_len()`. Used by the kernel ABI bridge to snapshot newly
    /// propagated literals into the caller-supplied output buffer.
    pub fn trail_at(&self, idx: usize) -> i32 {
        self.trail[idx]
    }

    /// Return the JIT clause index that forced the literal at trail
    /// position `idx`, or `usize::MAX` if the literal was assigned as
    /// a decision (i.e. via `assign(...)` outside of `propagate(...)`).
    pub fn reason_at(&self, idx: usize) -> usize {
        self.reasons[idx]
    }

    pub fn reset(&mut self) {
        for v in 1..=self.num_vars {
            self.values[v] = Value::Unassigned;
        }
        self.trail.clear();
        self.reasons.clear();
        self.qhead = 0;
    }

    /// Seed `values[]` from a host-provided per-variable assignment
    /// slice (`+1` true, `-1` false, `0` unassigned), without pushing
    /// anything onto the trail or advancing `qhead`. Mirrors the
    /// `KernelCtx::initial_values` contract: the caller communicates
    /// the **already-settled** trail state through this method, then
    /// passes only the unprocessed suffix as decisions.
    ///
    /// `slice` is indexed by DIMACS variable number; entry `0` is
    /// ignored. Entries beyond `num_vars` are ignored. Already-assigned
    /// variables (`values[v] != Unassigned`) are overwritten without
    /// regard to the previous value — the caller is expected to call
    /// `reset()` first when reusing the state across solves.
    pub fn seed_initial_values(&mut self, slice: &[i8]) {
        let limit = slice.len().min(self.num_vars + 1);
        for (v, &value) in slice.iter().enumerate().take(limit).skip(1) {
            self.values[v] = match value {
                1 => Value::True,
                -1 => Value::False,
                _ => Value::Unassigned,
            };
        }
    }
}

fn lit_index(lit: i32) -> usize {
    let v = lit.unsigned_abs() as usize;
    if lit > 0 { 2 * v } else { 2 * v + 1 }
}

pub fn random_3sat(num_vars: usize, num_clauses: usize, seed: u64) -> Vec<Vec<i32>> {
    let mut state = if seed == 0 {
        0x9E37_79B9_7F4A_7C15
    } else {
        seed
    };
    let mut clauses = Vec::with_capacity(num_clauses);

    for _ in 0..num_clauses {
        let mut clause = Vec::with_capacity(3);
        while clause.len() < 3 {
            let r = xorshift64(&mut state);
            let var = (r % num_vars as u64) as i32 + 1;
            if clause.iter().any(|&l: &i32| l.unsigned_abs() == var as u32) {
                continue;
            }
            let polarity_bit = xorshift64(&mut state) & 1;
            let lit = if polarity_bit == 0 { var } else { -var };
            clause.push(lit);
        }
        clauses.push(clause);
    }

    clauses
}

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_formula_propagates_trivially() {
        let mut state = BcpState::new(0, Vec::new());
        assert!(state.propagate().is_none());
        assert_eq!(state.trail_len(), 0);
    }

    #[test]
    fn unit_clause_propagates_one_literal() {
        let clauses = vec![vec![3]];
        let mut state = BcpState::new(3, clauses);
        assert!(state.propagate().is_none());
        assert_eq!(state.trail_len(), 1);
        assert_eq!(state.value_of_lit(3), Value::True);
    }

    #[test]
    fn binary_conflict_detection() {
        let clauses = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
        let mut state = BcpState::new(2, clauses);
        state.assign(1);
        state.assign(2);
        let conflict = state.propagate();
        assert!(conflict.is_some());
    }

    #[test]
    fn three_variable_unsat_reaches_conflict() {
        // (x1 v x2 v x3) ^ (-x1) ^ (-x2) ^ (-x3) is UNSAT;
        // BCP from the unit clauses must derive a conflict on the first clause.
        let clauses = vec![vec![1, 2, 3], vec![-1], vec![-2], vec![-3]];
        let mut state = BcpState::new(3, clauses);
        let conflict = state.propagate();
        assert!(conflict.is_some());
    }

    #[test]
    fn chain_propagation_assigns_all() {
        // x1 -> x2 -> x3 implication chain via binary clauses.
        let clauses = vec![vec![-1, 2], vec![-2, 3], vec![-3, 4]];
        let mut state = BcpState::new(4, clauses);
        state.assign(1);
        assert!(state.propagate().is_none());
        assert_eq!(state.value_of_lit(2), Value::True);
        assert_eq!(state.value_of_lit(3), Value::True);
        assert_eq!(state.value_of_lit(4), Value::True);
    }

    #[test]
    fn random_3sat_shape() {
        let clauses = random_3sat(50, 200, 0xCAFE_F00D);
        assert_eq!(clauses.len(), 200);
        for c in &clauses {
            assert_eq!(c.len(), 3);
            for &lit in c {
                let v = lit.unsigned_abs();
                assert!((1..=50).contains(&v));
            }
        }
    }
}
