# Lean soundness boundary

The Lean development provides conditional, model-level evidence. v0.1.0 does
not claim that it proves the complete Rust compiler, all accepted trust-ir, all
emitted bytes, or real hardware execution end to end.

## Trusted boundary

The current development trusts or assumes at least:

- the Lean kernel and standard logical principles used by the imports;
- four explicit top-level axioms: `srcStep_spec`, `decode_encode`,
  `step_emitted`, and `x86Step_decode`;
- every transitive use of Lean's `sorryAx` from the 17 classified `sorry`
  sites;
- the faithfulness of the modeled source semantics, x86 semantics, encoder,
  loader/layout, and observables;
- the external correspondence between those models and the Rust backend,
  linker/runtime, and hardware.

`bv_decide` produces kernel-checked proof terms for the goals it closes, but
that fact does not discharge the assumptions listed above.

## Classified incomplete areas

The 17 tree-wide `sorry` sites currently fall into these areas:

- byte-level memory and framing lemmas;
- call-graph/callee-contract composition;
- jump-table control flow;
- source-event and bitvector helper facts;
- a reverse-refinement theorem that is outside the forward capstone;
- the separate concurrent/atomic extension.

Some gaps are mechanical and some require stronger interfaces or new semantic
arguments. The release gate pins the aggregate count rather than claiming all
sites are equivalent or off the capstone path.

## How to interpret `compile_refines`

`compile_refines` proves forward inclusion inside the Lean model when supplied
with `Certified_compile P`. It does not construct that premise from an
arbitrary production compilation. In particular:

- call correctness enters through a conditional callee contract;
- unsupported state/operand/control-flow shapes do not gain coverage merely
  because the theorem exists;
- the reverse direction (excluding extra machine behavior) remains open;
- the production Rust emitter is only connected to a named encoder-golden
  matrix, not formally refined in full.

Before relying on a narrower claim, inspect the exact theorem and its
`#print axioms` output. Do not infer a repository-wide verified-compiler claim
from the existence of the capstone declaration.

The authoritative automated checks are the `lake build`, sorry/axiom ratchets,
and encoder-golden binding in the repository soundness gate.
