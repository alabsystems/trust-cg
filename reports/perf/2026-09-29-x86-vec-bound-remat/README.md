# h1's trip-bound rematerialization: IMPLEMENTED and tested, and the blocker MOVED one gate (2026-09-29)

`h1_vec_push_sum` is the corpus's largest per-program gap — **2.488x LLVM -O3**, of which
[an earlier decomposition](../2026-09-28-linux-x86-64-vec-bounds-check/) attributes **1.979x
to LLVM's vectorization** and 1.334x to residual scalar quality. Upstream named the required
step:

> A header-local reload is not enough: the new VP0 reads len before the original header, so
> admitting that shape also requires a proven-safe dominating rematerialization in the plan.

This is that rematerialization. It works. h1 still does not vectorize, because the blocker
is now the NEXT gate — and that gate is one upstream deliberately declined to weaken.

## Three corrections to what I had recorded

Before any code, the measurements corrected three things I had written down:

1. **`vectorize-late` does NOT get past the trip bound.** I had recorded that it did, and
   that the remaining blocker there was the element load's `MovRMSib` spelling. Re-measured,
   the late position's bail is the SAME
   `len_reg VReg { id: 95, class: Gpr64 } not loop-invariant`. `MovRMSib` is the tier's
   SECOND blocker, reached only after the bound check passes — as the tier's own source says.
   All three vectorizer positions fail on the bound.
2. **The heap tier — the one written for h1's shape — had NO bail trace.** Every rejection
   was a bare `return None`, so `trace-vectorize-bail` reported the reg-arg and window tiers
   while the tier whose doc comment literally describes `while k < v.len()` over a `Vec`
   declined in silence. 35 traced bails added; same existing lever.
3. **Upstream's objection is narrower than I recorded, and their test says so.** The comment
   on `rejects_regarg_header_length_reload_before_vector_entry` reads: *"The address is
   invariant and the loop never writes memory, but the sole length definition is in the
   original header. VP0 would use it before that header; **value invariance is not definition
   availability**."* That is a use-before-def objection, not a trap-safety one. The fix is
   therefore not to prove a hoist safe — it is to **replay** the computation.

## What h1's hot loop actually looks like

With the heap tier traced and the reg-arg bail made self-describing:

```
Preheader Block(8):   [1] MovRR v88 <- v80            ; the Vec's base pointer
Header   Block(10):   [0] MovRR v93 <- v89            ; iv copy
                      [1] Lea   v94 <- [v88 + 16]     ; &v.len
                      [2] MovRM v95 <- [v94 + 0]      ; THE BOUND
                      [3] MovRR v96 <- v95
                      [4] MovRR v97 <- v96
                      [5] CmpRR v93, v97              ; iv <u len
                      [6..12] Setcc/Movzx/AndRI/CmpRI/Jcc/Jmp
```

So the bound is two instructions deep, and their only external input `v88` is defined **in
the preheader** — which dominates the vector preheader. Everything needed is available.

This also explains why the heap tier cannot take h1 even once traced: its bound must be a
`slot_field_load`, and h1's is `MovRM [v94+0]` where `v94` is a **register** Lea, not a frame
address. Wrong tier. h1 belongs to the reg-arg tier, with a bound remat.

## The implementation and its safety argument

`bound_remat_slice` computes the backward slice of the bound within the header, and the
emitter replays it into FRESH vregs at the top of VP0. Four conditions, each checked:

* **It executes on a path the scalar program already takes.** Every slice instruction is in
  the HEADER and precedes the header's terminator. A block is straight-line, so each runs on
  EVERY entry to the header, including the zero-trip entry. VP0 sits on the preheader → header
  edge, and the header's only non-body predecessor is that preheader (the tier already
  establishes this). So the replayed load reads an address the scalar program reads on exactly
  the same paths: **no new memory access, no new trap, no new UB.**
* **Every input is available at VP0.** Each operand is either defined by an earlier slice
  instruction, or has a unique def OUTSIDE the loop body in a block dominating the preheader
  (`dominates` is reflexive, so the preheader itself qualifies — which is where `v88` is).
* **The value is fixed across the loop.** The tier already proves the body performs NO
  stores, so nothing can change the memory read or any register the slice depends on.
* **Only pure, non-trapping opcodes are replayed** — `Lea`, `MovRR`, `MovRR32`, `MovRI`, the
  64-bit `MovRM` — and never a proof carrier. Replaying has no effect beyond its fresh defs.

The scalar loop is untouched: its own `len_reg` and its whole header computation survive
byte-for-byte, and the vector bound comes from the replay.

Also needed: the tier's body-memory classifier skips the slice's header indices. Its 64-bit
load would otherwise be rejected as "neither an element address nor an invariant address" —
its base is computed in the header, so `is_reg_loop_invariant` correctly says no. That
decline is precisely what the replay exists to answer.

## DEFAULT OFF, on purpose

`-Ztrust-ir-cg-args=x86-vec-bound-remat`, default off, threaded through the pass rather than a
`OnceLock` so the test binary can run both arms.

The capability makes upstream's committed refutation vectorize. **I am not flipping a
committed refutation silently**, in the most safety-critical pass, on the same day review
repaired six defects in my work — one of them a live miscompile in width-sensitive reasoning.
Default off keeps `rejects_regarg_header_length_reload_before_vector_entry` passing
byte-for-byte, and makes the capability a measurable lever instead of a unilateral policy
change. Turning it on is a decision for whoever owns that pin.

Four tests, in both directions:

| test | asserts |
| --- | --- |
| `bound_remat_vectorizes_the_header_length_reload` | upstream's exact fixture DOES vectorize with the opt-in, **and** no `AndRI` reads the header's own `len` (i.e. the bound really comes from the replay), **and** a replayed load was emitted |
| `bound_remat_is_off_by_default` | FALSIFIABILITY — the identical fixture with nothing but the opt-in changed declines |
| `bound_remat_still_refuses_a_body_store` | the no-stores premise still gates it |
| `bound_remat_refuses_an_address_defined_inside_the_loop` | moving the address's def into the latch makes the slice not close |

## Result: it fires, and the blocker MOVED — no speedup

With the lever on, h1's reg-arg bail advances from

```
len_reg VReg { id: 95, class: Gpr64 } not loop-invariant and its header slice is not replayable
```

to

```
guard Block(11) bound VReg { id: 107, class: Gpr64 } != len_reg VReg { id: 95, class: Gpr64 } (CROSS-LENGTH)
```

**The remat succeeds.** The new blocker is the own-length identity rule: the per-element
bounds-check guard reloads the length into a SECOND vreg (`v107`), so the header's bound and
the guard's bound are not the same register.

That is a gate I had previously tried to relax (`same_value_or_same_reload`) and **upstream
reverted it, leaving the reason in the source**:

> Same-address loads need reaching-memory equivalence, not merely a write-free loop: a
> preheader store may separate the trip-bound load from the element guard's reload. Until that
> equivalence is established, retain exact copy-canonical register identity.

**I am not re-attempting it.** It was reverted once with a stated missing premise — a
reaching-memory equivalence analysis (the `reaching_const` module is the shape of the
sanctioned route) — and hand-waving it in this pass is exactly the mistake that produced the
miscompile review caught today.

So: **no performance claim here, and h1's gap is unchanged at 2.488x.** What landed is the
prerequisite upstream named, implemented, tested in both directions, with the next blocker
precisely located and named.

## Measured cost: zero

| check | result |
| --- | ---: |
| lever ON vs OFF, all 18 programs | **byte-identical**, same exit codes |
| execution differential vs LLVM (default build) | **18/18 MATCH** |
| SIMD counts vs baseline (p4 78 `paddq`, v1 359 total / 6 `paddd`, h2/h4 65, p7/v3 63, base 62) | unchanged |
| heap tier acceptances on the corpus | 0 — the dialect widening is behaviour-neutral here |
| `trust-cg-opt` lib suite | 3826 pass, 0 fail |
| clippy on the crate | 162, identical to the pre-change baseline |

A note against over-reading my own numbers: an intermediate run showed v1_saxpy's SIMD total
as 354 rather than the 359 baseline. That was my `grep` pattern dropping `pmull[wd]`, not a
codegen change — re-measured with the original pattern it is 359 with 6 `paddd`. Recorded
because a 5-instruction "regression" in a vectorized program is exactly the kind of artifact
that would otherwise get written up as real.

## The default-on change in this commit

One change here is NOT behind a lever: the heap tier's header and guard tests now accept the
header idiom in EITHER spelling (`chase_below_branch_either`) rather than only the
materialized-boolean chain. The reg-arg tier has accepted both since that helper was added;
the two spellings are the same predicate (`lhs <u rhs ? taken : fall`) and the fused form
additionally refuses a proof-carrier compare. It is dialect coverage, not a weakening of any
legality condition — and it is what let h1's inner loop reach the heap tier's own checks at
all, which is how the `slot_field_load` mismatch above was found. Measured acceptances on the
corpus: zero.

## What would finish h1

1. **Reaching-memory equivalence** for two same-address loads separated only by write-free
   code, to discharge the own-length identity rule without assuming it. This is the live
   blocker and it is an analysis, not a predicate tweak.
2. Then `MovRMSib` in the element-load classifier, for the late position.
3. Then the residual 1.334x scalar-quality component, which vectorization does not address.
