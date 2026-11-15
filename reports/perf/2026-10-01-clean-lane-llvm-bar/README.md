# The Clean lane DOES have an LLVM bar — and the same panic refusal blocks it

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · Reference: rustc's in-tree LLVM 22.1.2

## Correcting a claim I made earlier today

I reported that "performance at least matching LLVM and clang" has no referent for the
Lean-through-Clean lane, because its fixtures are `.tir` modules and clang has no Lean
frontend. That is true of the committed `.tir` files and FALSE of the lane as a whole.

`crates/trust-cg-codegen/tests/slices/` holds **149 Rust slices** — the Clean (Lean)
kernel code transcribed at its production positions, which is what the committed `.tir`
fixtures were produced FROM (each fixture's header names its slice:
`file 0 "clean_ctx_whnf_slice.rs"`). **56 of them carry `fn main`**, so they are runnable
programs, and the same program can be built by rustc+LLVM and by rustc+trust-cg. That is
exactly the beat-llvm methodology, applied to the Clean lane's own code.

## Result on the first twelve runnable slices

| slice | llvm | trust-cg | ratio | floor |
|---|---:|---:|---:|---:|
| expr_construction | 0.399 ms | 0.404 ms | **1.0125** | 0.0150 |

and **eleven of twelve fail closed**: binding_defeq, ctor_return, ctx_whnf,
decl_universe_realnames, elim_zero, eta_ext, expr_quot, fvar_opening,
inductive_soundness, lazy_delta, minor_premise.

The one measured row is at **1.0125x with a 0.0150 floor** — inside its own noise, so at
parity, though a 0.4 ms program is too short for the figure to carry much weight.

## The refusals are the SAME blocker, counted

Across those slices' stderr: **39 `[TCG-ASSERT-PANIC]`**, 11 `[TCG-COLLECTION-IMAGE]`,
2 `[TCG-FMT-DECLINED]`. The dominant reason is the bounds-check refusal under
`panic=abort` from upstream's v52 panic cohort — the same one that blocks 10 of 18
beat-llvm programs and 119 `library/core` roots
(`../2026-10-01-panic-cohort-blocks-the-loop-passes/`).

So the blocker is **broader than the Rust benchmark corpus**: it blocks every LLVM
comparison that routes through the bridge, including the Clean lane's own source slices.
That is worth stating plainly, because it means the cohort's completion unblocks the
Clean performance clause too, not just the Rust one.

## What is NOT blocked

Clean's **native** path is unaffected and verified green today: the committed `.tir`
fixtures go through `Compiler::compile` directly — lowering, regalloc, encoding, object
emission — with no bridge and no MIR, and
`trust-cg-codegen --test clean_fixture_host_lowering` passes 5/0 including the O0 and O1
floors. The refusal lives in the bridge's MIR `Assert` admission, which that path never
touches.

## Status of the goal's Clean clause, precisely

* **Compilation via trust-ir: MET** on the native path (the lowering floor).
* **Performance vs LLVM: MEASURABLE, and now partly measured** — 1 slice at parity, 11
  blocked by the panic cohort. Not "structurally unmeasurable", which is what I said
  before checking whether the slices existed.
