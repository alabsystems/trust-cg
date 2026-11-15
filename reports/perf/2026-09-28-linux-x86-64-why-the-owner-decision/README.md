# Whole-program compilation in the default lane requires the XD-01 evidence decision — by elimination, not by exhaustion (2026-09-28)

A day of work took `library/core` from 3363 failed roots to 2881, the source-bound
proof route from 494 refusals to 12, and emitted objects from 67 to 549. The
default proof-required lane stayed at **0 of 18** programs throughout. This report
shows that is not a matter of more engineering: the remaining gap is closed by one
decision and cannot be closed without it.

## The argument

1. **Every beat-llvm program's `main` contains a loop.** That is what makes them
   benchmarks — `p1_xorshift` is `while i < n { x ^= x << 13; ... }`.

2. **The source-bound body theorem admits only straight-line bodies.** Its source
   view is built by `chain_to` in `source_bound_source.rs`, which follows the entry
   block "through unconditional `Jump`s to a `Return`". The match arm is
   `L::Jump { dest } if last.args.is_empty() && last.results.is_empty()`, and every
   other terminator hits `_ => return None`. Conditional branches and loops are
   therefore outside the domain BY CONSTRUCTION, not by an unfinished slice.

3. **So the body theorem can never cover `main`.** Measured, per function:
   `_RNv11p1_xorshift4main` refuses with exactly `not a bounded unconditional
   chain`.

4. **`main`'s opcodes must therefore be covered by the RECONSTRUCTED route** — the
   only other route that can reach them.

5. **The reconstructed route's evidence for a register copy is a syntactic
   tautology.** Quoted from committed `verdict_db/tier0.vdb` entry 201, the
   obligation is `(declare-const recon_src (_ BitVec 64))` /
   `(assert (not (= recon_src recon_src)))` — `NOT (x = x)`. All four ways to
   credit it were tried and each refuses correctly: portable DRAT ("a DRAT over
   that canonical formula would carry no information about the obligation"),
   tier-0 (keyed to a solver identity that no host has), live solve (the route
   requires a committed artifact and spends no solve on a miss), and statistical
   sampling (not credit since `8d4e83b54`).

6. **Therefore whole-program compilation requires structural credit for the
   register-copy obligation** — the XD-01 question. There is no engineering path
   around it.

## What that means for the work that WAS done today

All of it was necessary and none of it was sufficient, which the numbers show
exactly:

| change | effect | root-level effect |
| --- | --- | ---: |
| `and_pos` retry (in-repo) | the whole `and_pos` failure class emptied | 3363 -> 3160 |
| AY 0.26.0 -> 0.27.0 | 15 of 17 failing snapshot queries fixed, 0 regressed | 3160 -> 3062 |
| Clean bump (1561 commits) | replay failures on the trivial binary -> zero | 3062 -> 2881 |
| stack-slot domain widening | largest exclusion 4632 -> 0; 3418 bodies admitted | **no change** |

The source-bound route went 494 -> 12 while the sampling route did not move a
single root at any step. That asymmetry is the argument above showing up in the
data: solver and checker work can only ever help the route that reasons about
BODIES, and `main` is permanently outside it.

## Why the per-program distance is stuck at exactly 7

Every program is refused on the same seven roots — the Rust runtime startup chain
plus its own `main` and `done` — and after the stack-slot widening each refused
body has a DIFFERENT single blocker:

| body | blocker |
| --- | --- |
| `p1_xorshift::main` | not a bounded unconditional chain (the loop) |
| `std::rt::lang_start::<()>` | `StackAddr` |
| `lang_start::{closure#0}` | `Load` |
| `…call_once::vtable` shim | `StackAddr`, `Trap` |
| `p1_xorshift::done` | `GuardDivZero` |
| `<fn() as FnOnce>::call_once` | `CallIndirect` |
| `<closure as FnOnce>::call_once` | parameter types |
| `___rust_no_alloc_shim_is_unstable_v2` | exactly-one-result rule |

Eight distinct conditions, one per body, ALL of which must pass for ONE program.
Clearing any one promotes one body and no program. And the `main` row cannot be
cleared at all without making the theorem handle loops — a different theorem.

These DO pass and replay valid, which is worth recording as the positive control:
`___rust_alloc`, `___rust_dealloc`, `___rust_realloc`, `___rust_alloc_zeroed`,
`___rust_begin_short_backtrace` and `Termination::report`.

## The evidence ALREADY EXISTS and is ALREADY AUDITED — what is missing is an instance binding

This is the sharpest available statement of the blocker, and it is not "invent new
evidence".

`proof_database.rs` carries `GENUINE_IDENTITY_ALLOWLIST`, and on it, verbatim:

```
"x86_64: Copy_I32 -> MOV r32,r32 preserves bits",
"x86_64: Copy_I64 -> MOV r64,r64 preserves bits",
```

Its rationale states the principle outright: for these lowerings "**the identity IS
the faithful proof and it pins the emitted opcode**", because both sides
independently denote the same thing and a WRONG lowering would make them differ and
refute — `Iadd -> SUB` would yield `bvadd == bvsub` and refute. The audited
families explicitly include "Bitcast same-width + **Copy/MOV bit-preserving
lowerings**" and "x86-64 ALU/shift/FP/bitwise/bitcast/**copy**/conv/…".

And `coverage_gate.rs` agrees, in a comment tagged HONESTY (task #61):
`MovRR`/`MovRR32` "bind the GENUINE `Copy_I64` / `Copy_I32` bit-identity proofs (on
`GENUINE_IDENTITY_ALLOWLIST`) — they stay `EmittableNeedsProof` and **report
COVERED**".

So the FORMAL gate already credits the register copy on exactly the structural
ground XD-01 proposes. What the per-compile promotion path cannot do is credit it,
and the reason is precise: upstream `8d4e83b54` withdrew registry-NAME lookup as
credit (`REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT`), so the per-compile path may no
longer credit an audited proof by NAME — it must bind THE INSTANCE. It therefore
builds `RECONSTRUCTED x86_64 Copy_64 -> MovRR (real-operand)`, whose SMT form is
`NOT (x = x)`, and no solver route can supply instance evidence for a tautology.

Both halves of the missing link are already in the tree:

* the audited identity (`GENUINE_IDENTITY_ALLOWLIST`), and
* an exact instance binding — `x86_source_operand_binding.rs` and
  `discharge_reconstructed_obligation_with_exact_source_binding`, which is already
  the route the reconstruction obligation travels.

What does not exist is the step that says: when the exact source-operand binding
HOLDS and the obligation is an allowlisted genuine identity, that pair is complete
evidence — decided, with no solver and no name lookup. That step is XD-01, and it
is a much narrower change than "a new evidence taxonomy": it connects two
mechanisms the project has already built and already audited.

The `CoveredElsewhere` status is the precedent for the SHAPE of such a step: it
already promotes opcodes "whose only candidate would be the `target == target`
tautology" on the ground that "correctness is established by the SURROUNDING
proofs", and it exists precisely so the gates do not disagree about the universal
`lang_start -> FnOnce::call_once` entry path. Its own comment warns the list is
CLOSED and must not become a blanket allowlist — which is why adding the most
common opcode in the ISA to it was not done here (XD-01, ruled 2026-10-02,
keeps the list closed).

## The decision, stated as narrowly as the evidence allows

> Does a total, exactly-transcribed result-bit-to-source-bit table equality count
> as complete evidence that an emitted register move denotes its source operand?

If yes, the reconstructed route covers `MovRR`/`MovRR32` — 2578 + 436 roots' first
blocker — without the body theorem admitting loops, memory or calls. The precedent
is `x86_sse_lane_proofs`, which already credits exactly this shape for ten SSE rows
on the stated ground that "a routing instruction's meaning is a total function from
result-bit index to which bit of which operand, and two such functions denote the
same instruction iff their tables are equal … the comparison is a decision".

Ruled 2026-10-02 (XD-01 in the decision record): not yet. The
equality is not admitted until operand correspondence is carried and
cross-checked, so the route is the source-bound body theorem below.

If no, the alternative is making the source-bound body theorem general over loops,
memory, guard carriers and indirect calls — a different theorem from the one that
exists, and the only other route to the same roots.

## Provenance

`ay 0.27.0+build.11385`, Clean `e75141b7b` (`carcara-verify`), bridge rebuilt from
this tree, stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)`, Trust repo
`ceb94fe99`, `PATH=/usr/bin:$PATH CC=/usr/bin/gcc`. Per-function blockers from
`-Ztrust-ir-cg-args=x86-body-trace` on `p1_xorshift`; census figures from
`2026-09-28-linux-x86-64-clean-bump` and the post-widening run; the chain
restriction quoted from `source_bound_source.rs`; the obligation quoted from the
committed tier-0 DB. 0 MISMATCH in every lane measured today.
