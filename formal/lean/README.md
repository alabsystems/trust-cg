# trust-cg Lean development

This directory contains a Lean 4 model and a conditional forward-refinement
development for selected trust-cg paths. It is supporting research evidence for
v0.1.0, not an end-to-end proof of the Rust compiler or every emitted binary.

## What the capstone says

`Trust/MetaTheorem/CompileRefines.lean` defines:

```lean
theorem compile_refines (P : Program) (hcert : Certified_compile P) :
    Refines (x86Sem P) (srcSem P)
```

In the Lean model, the theorem maps a source run covered by
`Certified_compile` to a matching modeled x86 run with the same filtered
observable trace. This is a conditional theorem: the development does not yet
prove that the production Rust compiler and runtime gate establish
`Certified_compile` for arbitrary inputs, nor that the Lean encoder and machine
semantics exactly model all bytes and hardware behavior.

The modeled surface is intentionally limited. Cross-function composition,
jump-table control flow, survivor framing, parts of byte-level memory reasoning,
and the concurrent extension remain incomplete.

## Current proof boundary

The release gate pins the current tree-wide baseline at:

- 17 classified `sorry` sites under `Trust/`;
- 4 explicit top-level axioms;
- a green `lake build`;
- a shared Lean/Rust encoder-golden test for its named instruction matrix.

The count ratchets prevent silent growth. They do not turn the remaining
`sorry` sites or axioms into proved facts. Likewise, the golden test binds only
the enumerated encodings; it is not a proof of the full Rust emitter.

Important trusted or incomplete boundaries include:

- `srcStep_spec`, `decode_encode`, `step_emitted`, and `x86Step_decode`;
- the correspondence between modeled instructions and the production emitter;
- the conditional `CalleeContract` used at call boundaries;
- open jump-table and concurrency cases;
- classified memory, event, and bitvector proof gaps.

See [`SOUNDNESS.md`](SOUNDNESS.md) for the inventory and
[`ROADMAP.md`](ROADMAP.md) for the closure order.

## Build and inspect

The package pins Lean in `lean-toolchain` and is built by `lakefile.lean`:

```sh
cd formal/lean
lake build
```

Count the classified gaps and explicit axioms exactly as the release gate does:

```sh
grep -R -h -E '^[[:space:]]*sorry([[:space:]]|$)' --include='*.lean' Trust | wc -l
grep -R -h -E '^axiom ' --include='*.lean' Trust | wc -l
```

When reviewing a load-bearing declaration, use `#print axioms` in a small Lean
query to inspect its actual transitive assumptions. A successful `lake build`
alone is not evidence that a declaration is free of `sorryAx`.

The cross-repository orchestration and exact ratchet implementation live in
[`scripts/soundness_check.sh`](../../scripts/soundness_check.sh) and
[`SOUNDNESS_CHECK.md`](../../SOUNDNESS_CHECK.md).
