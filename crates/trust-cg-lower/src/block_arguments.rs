// Copyright 2026 Andrew Yates | Apache-2.0

//! The ordinary adapter's existing parallel-copy schedule. This helper carries
//! no proof or source authority; consumers must independently check semantics
//! and the exact source/retained instruction binding. Cycle temporaries still
//! come from the owning adapter's allocator.
use crate::instructions::{Instruction, Opcode, Value};

pub fn schedule_parallel_copies(
    pairs: Vec<(Value, Value)>,
    mut fresh_value: impl FnMut() -> Value,
) -> Vec<Instruction> {
    // Step 1: drop self-copies.
    let mut pending: Vec<(Value, Value)> = pairs.into_iter().filter(|(s, d)| s != d).collect();

    let mut out: Vec<Instruction> = Vec::new();

    // Iterate until all pending copies have been scheduled.
    while !pending.is_empty() {
        // Compute the set of destinations that are ALSO sources of
        // some other pending copy. A copy whose dst is NOT in this set
        // is "ready" to emit.
        let mut src_set: std::collections::HashSet<Value> = std::collections::HashSet::new();
        for &(s, _) in &pending {
            src_set.insert(s);
        }

        // Drain all ready copies in this pass.
        let mut made_progress = false;
        let mut i = 0;
        while i < pending.len() {
            let (s, d) = pending[i];
            if !src_set.contains(&d) {
                // `d` is not read by any other pending copy -> safe to emit.
                out.push(Instruction {
                    opcode: Opcode::Copy,
                    args: vec![s],
                    results: vec![d],
                });
                pending.swap_remove(i);
                made_progress = true;
                // Recompute src_set on next outer loop iteration.
            } else {
                i += 1;
            }
        }

        if made_progress {
            continue;
        }

        // No ready copies but pending is non-empty -> there is a cycle.
        // Break the first cycle by saving the first dst to a temp and
        // rewriting any pending copy that read that dst as its source.
        //
        // Example (swap a<->b):
        //   pending = [(a, b), (b, a)]
        //   src_set = {a, b}; no ready copy.
        //   Take first copy (a, b): save `tmp = b` (the dst we're about
        //   to overwrite). Then rewrite any other pending copy whose
        //   src == b to src = tmp. Now (b, a) becomes (tmp, a).
        //   Emit (a, b), and (tmp, a) becomes ready next iteration.
        let (s0, d0) = pending[0];
        let tmp = fresh_value();
        out.push(Instruction {
            opcode: Opcode::Copy, // tmp = d0
            args: vec![d0],
            results: vec![tmp],
        });
        // Rewrite any pending copy that reads d0 to read tmp.
        for p in pending.iter_mut() {
            if p.0 == d0 {
                p.0 = tmp;
            }
        }
        // Emit the chosen copy now: d0 = s0.
        out.push(Instruction {
            opcode: Opcode::Copy,
            args: vec![s0],
            results: vec![d0],
        });
        pending.swap_remove(0);
    }

    out
}
