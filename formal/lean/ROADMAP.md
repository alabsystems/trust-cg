# Lean proof-closure roadmap

The v0.1.0 development builds, but it remains conditional and incomplete. Work
should reduce assumptions monotonically in roughly this order.

1. Discharge the classified byte-memory, event, and bitvector helper gaps.
   Lower the pinned `sorry` count only in the same change that removes a real
   site and keeps `lake build` green.
2. Strengthen memory/load survivor interfaces so pair, vector, and spill cases
   can be framed without assumed side conditions.
3. Close or formally reject uncovered jump-table control flow.
4. Prove that callee contracts arise from a well-founded call-graph or explicit
   recursion model instead of entering as assumptions.
5. Extend the Lean/Rust correspondence beyond the current encoder-golden
   matrix, including object layout and relocation behavior.
6. Prove the reverse behavioral inclusion if a no-extra-machine-behavior claim
   is desired.
7. Treat the concurrent/atomic development as a separate proof track and close
   its interleaving argument before presenting it as supported.

For every step, inspect `#print axioms` on the affected load-bearing theorem,
add a negative or mutation control where practical, and keep unsupported
production paths fail-closed. Merely moving a `sorry` behind a new axiom or
strengthening a premise without wiring it to the production gate is not proof
closure.
