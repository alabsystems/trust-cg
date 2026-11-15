# Why none of the five "vectorizable" programs vectorizes — the decline map

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · HEAD after `9bb9f7879`

## The fact to establish first

**Not one of the five vectorizable programs has any SIMD in its hot loop.** Counting xmm
uses per function in the emitted binaries, every one of the 174-176 packed instructions
lives in std code — `backtrace_rs::symbolize::gimli`, `core::str::count::do_count_chars`,
`core::fmt::Formatter::pad`. `main` has **zero** in v1_saxpy, v2_memfill, v3_popcount,
p4_matmul and p7_sieve alike.

That is consistent with every ratio in the diagnostic lane (v1 4.28x, v2 53.5x, v3 6.92x,
p4 2.45x, p7 2.08x) and it means the gap is not "poor vectorization" but **no
vectorization**. It is also a regression against the era recorded in
`benchmarks/LEDGER.md`-adjacent notes, where v3 ran 0.103x and v1 0.649x.

## How the reasons were obtained

`recognize_saxpy_loop` — the saxpy-**D** tier, the 32-bit-element one that emits
`Pmulld`/`Paddd` and therefore the tier that owns the `[i32; N]` shape these programs are
made of — had **no bail trace at all**: 46 early returns, every explicit one a bare
`return None`. So `trace-vectorize-bail` named the heap, regarg, rowreg, saxpy-Q and window
tiers while the tier that owns v1/v2/v3 declined in silence, and the only summary available
was `DECLINED by every recognizer`.

This instruments it (`saxpyd-bail`, same contract as the Q tier): 21 explicit `return None`
sites, 14 `?` propagations, the preheader bind that used to sit ABOVE the macro, and the
latch check whose INNER `?` swallowed its own decline before the `bail!` beneath it could
run.

## The map

| program | header | the named condition |
|---|---|---|
| p7_sieve | **all four** (2, 5, 8, 20) | `recognize_header` |
| v1_saxpy | 6 | `recognize_header` |
| v1_saxpy | 2 (init loop) | `op != MovMR32 \|\| store.is_some()` — two stores, correctly refused |
| v2_memfill | 2 | `recognize_header` |
| v2_memfill | 5 | `op != MovMR32 \|\| store.is_some()` |
| v3_popcount | 6 | `recognize_header` |
| v3_popcount | 2 | body opcode not whitelisted |
| v3_popcount | 9 | `op != MovRM32` |
| p4_matmul | 6, 9 | `recognize_header` |
| p4_matmul | 16, 21 | `has_trap_edge && !block_has_iv_bound_compare` |
| p4_matmul | 2 | body opcode not whitelisted |

**`recognize_header` is the dominant condition**, and it is the whole story for p7_sieve.

## What `recognize_header` actually refuses, from its own diagnostic

Two distinct shapes, and the distinction matters:

**(a) The candidate is not the counter at all.** `outside_defs=0 inside_defs=2
[Movzx(iv+1=false), AndRI(iv+1=false)]`. That is `(r as usize) % N` — a `Movzx` plus an
`AndRI 4095` mask — compared against a constant in the header. `recognize_header` scans
every compare in the header, tries each operand as an IV candidate, and refuses this one.
**Correctly.** It then keeps scanning, so this is not itself the blocker.

**(b) A real counter shape, refused on its init and increment.** p7_sieve header=Block(20):
`outside_defs=1 [Block(19)/MovRR(is_preheader=true,init=None)] inside_defs=1
[Block(24)/MovRR(iv+1=false)]`. Exactly one outside def, in the preheader, and one in-body
def — the right structure — but the init does not trace to a literal 0 and the writeback is
not recognised as `iv + 1`.

## The correction this forces on my own earlier note

I had recorded this as `is_counter` "refusing on SPELLING", implying a cheap widening. For
the **increment** that may hold. For the **zero init** it does not: `is_counter`'s own
comment states the precondition and why it is load-bearing —

> The zero entry is the emitters' load-bearing precondition, not a stylistic preference: no
> `apply_*_plan` initialises the counter — the vector header they build is `iv <u vN` with
> `vN = (n_trip / LANES) * LANES` and the body indexes with the raw counter and steps it by
> `LANES`. That guard proves the packed footprint is `[0, vN)` and the scalar remainder
> `[vN, N)` ONLY from a zero entry; from `iv = r != 0` the last admitted iteration touches
> up to element `vN + LANES - 2`, i.e. out of slot.

And the per-access bounds-check diamonds are **deliberately elided** inside that footprint.
So admitting a non-zero start without changing the emitters would be a miscompile, not a
widening. The sibling `is_counter_any_init` exists precisely for tiers whose emitters can
take it.

## Therefore the next step, scoped honestly

Two independent pieces, in value order:

1. **The increment spelling** — recognise an in-place `AddRI iv, 1` (and p7's `MovRR`
   writeback) as the unit increment, keeping the fail-closed "any other in-body def
   refuses" arm intact. This is the cheap half and it is what `iv+1=false` names.
2. **The non-zero start** — requires `apply_*_plan` to compute the packed footprint from a
   runtime start, including the remainder bound, before `is_counter` may admit it. This is
   the expensive half and carries the elided-bounds-check obligation above. It must not be
   attempted by relaxing the predicate alone.

Neither is attempted here. What this commit delivers is that the five worst programs now
name their condition instead of reporting `DECLINED by every recognizer`.

## Also recorded: a refuted hypothesis and a refuted fix

* The faithful-panic-raise sink is **not** the binding constraint. The `is_divergent_sink`
  admission is byte-identical in SIMD count on all six vectorizable programs and within
  noise on all 18 runtime rows. Every tier declines upstream of the sink test.
* Inserting unique loop preheaders (`x86-loop-simplify`, which is registered immediately
  BEFORE `X86Vectorize`, so ordering is not the issue) changes nothing: xmm stays 0 on all
  five. The preheader bail added here never fires.

---

## UPDATE: the instrumentation is now complete, and v1's HOT loop names its condition

The first pass left three silent paths (two multi-line `elem_addr_slot(..)?`, a
`LoopLocality::check(..).ok()?`, and five `_ => return None,` match arms my conversion
regex did not match). With those traced, **v1_saxpy's inner hot loop reports for the first
time**:

```
hdr=Block(9): LoopLocality::check — Live { reg: Virtual(VReg { id: 80, class: Gpr64 }),
                                           into: Block(15) }
```

That loop **passes everything else** — header recognition, the body opcode scan, both
element addresses, the exit plan. It dies because a vreg defined inside the loop is LIVE
OUT into Block(15), which violates the handoff contract `LoopLocality::check` is given
(`Handoff::HeaderOrExit`, with only `iv` exempt). So v1 is not a dialect gap at all; it is
a **live-range** condition.

### The corrected header idiom finding

I earlier read `inside_defs=2 [Movzx, AndRI]` as `(r as usize) % N`. **That was wrong.**
The dump shows it is the ISel boolean materialization of the loop test itself:

```
MovRR  [v76, v72]              ; iv copy
MovRI  [v77, Imm(4096)]        ; the bound IS a compile-time constant
CmpRR  [v76, v77]              ; iv <u 4096
Setcc  [v78, B] · Movzx ×2 · AndRI [v79, v79, 1]
CmpRI  [v79, Imm(0)] · Jcc NE
```

`recognize_header` scans every compare in the header, so it finds `CmpRI v79, 0` and asks
whether the **boolean** is a counter — hence that diagnostic. It also finds `CmpRR v76,
v77` first, with a constant bound, so for v1 the real IV *is* reachable. Where the bound is
NOT a constant (a parameter, or a `black_box`'d `reps`), only the boolean compare has a
constant side and the loop has no admissible header at all.

Note the idiom is already matched, strictly, inside `recognize_runtime_byte_fill_loop`
("`Setcc L / Movzx* / AndRI ,1 / CmpRI ,0 / Jcc NE`") — the capability exists in-tree but is
locked in that one tier and `recognize_header` cannot see it.

## The complete per-program blocker list

| program | hot-loop blocker |
|---|---|
| v1_saxpy | `LoopLocality::check` — VReg 80 live into Block(15). Everything else passes. |
| v2_memfill | `op != MovMR32 \|\| store.is_some()` (Block 5); Block 2 on `recognize_header` |
| v3_popcount | `op != MovRM32` (Block 9); `body opcode not whitelisted` (Block 2) |
| p4_matmul | `has_trap_edge && !block_has_iv_bound_compare` (Blocks 16, 21) |
| p7_sieve | `recognize_header` at **all four** headers |

Each is now a named condition with a reproducing command, which is what the next piece of
work needs. None of them is the panic-raise sink, the preheader, or the constant bound —
all three of those are refuted above.

**Which block is genuinely hot still needs confirming per program** (int3-patch the
candidate loop, per the method note in `reports/perf/`), because a decline on a cold or
dead loop costs nothing. That check is not done here.

---

## ROOT CAUSE for v1_saxpy, and the fix located exactly

`main` contains **6 calls to `core::panicking::panic_bounds_check`** — upstream's faithful
raise. And `assert_panic::emit` marshals `index`/`len` **into the raise block**. So:

```
block Block(10) succs=[Block(14), Block(15)]
    MovRR [v80, v72]      ; v80 = a copy of the IV
    CmpRR [v80, v81]      ; the bounds check
    ... Jcc -> Block(14) / Block(15)
block Block(15)           ; the RAISE: reads index (v80) and len
```

`v80` is therefore live out of the loop into Block(15), and that is precisely the refusal:
`LoopLocality::check — Live { VReg 80, into Block(15) }`.

**So the panic raise IS what blocks v1 — via the LIVE-RANGE rule, not the trap-sink
predicate.** That vindicates the original bounds-check-raise report's mechanism claim in
spirit while correcting it in substance: `is_divergent_sink` was applied at the wrong gate.
Before the raise, the failure block was `[Ud2]` and read NOTHING, so no register was live
into it; the faithful raise reads the index, and the loop's state escapes.

### The fix is two parts, and the first is a sibling-tier asymmetry

1. **saxpy-D never claims its guard edges as proven-dead.** Compare the two call sites:

   | tier | call |
   |---|---|
   | saxpy-D (3459) | `header_test_exits(.., &[])` |
   | saxpy-Q (4169) | `header_test_exits(.., &pre_guarded)` |

   The D tier *proves* those edges dead at its trap-edge sites
   (`block_has_iv_bound_compare`) but then passes an EMPTY pre-guarded list, so the exit
   plan never records them. Accumulating and passing them, exactly as the Q tier does, is a
   direct port of an in-tree pattern.

2. **`loop_state_escapes` ignores `proved_not_taken` in its register scan.** `accounts_for`
   honours it for the exit scan (`reproduced || proved_not_taken`), but
   `Handoff::HeaderOrExit` pushes *every* out-of-loop successor into `starts` and then
   flags any tracked register `live_into` one of them. A block reached only by an edge the
   plan proves untaken cannot observe stale state after the rewrite, so it does not belong
   in `starts`.

   **Soundness condition, which must not be skipped:** `index.live_into` is
   path-insensitive, so skipping the successor is only sound when the block is unreachable
   *after* the rewrite — i.e. every loop-exit edge targeting it is in `proved_not_taken`
   **and** it has no predecessors outside the loop. That holds for the raise block, which
   `ctx.fresh_block_id()` creates per assert with the guard as its single predecessor, but
   it must be checked rather than assumed.

**Not implemented here.** Part 2 changes the loop-state rule that every vectorizer tier
depends on for its correctness argument; a rushed version risks a miscompile, which is the
worst possible outcome in this backend. It needs the unreachability condition above, its
own negative tests (a sink with an outside predecessor must still refuse), and the 18/18
differential plus the core census before any default.

---

## The remaining matched-ISA gap: h1_vec_push_sum at 1.888x, with its conditions named

After the loop-state fix, h1_vec_push_sum is the **worst program at the ISA the target
defines** (1.888x, `xmm=0` in `main`) — and unlike the `-march=native` rows it needs no AVX
and no owner ruling. Traced with the instrumentation this report added:

| tier | condition |
|---|---|
| heap | `bound VReg{56} (canon VReg{2}) is not a 64-bit stack-slot field load; def=(MovRI, Imm(300000))` |
| heap | `L4940: step guard — lhs VReg{149, Gpr32} is not a zero-init unit counter` |
| regarg | `iv VReg{149, Gpr32} not gpr64 counter` |
| regarg | `guard Block(11) bound {176} != len_reg {161} (CROSS-LENGTH): MovMR in Block(11) writes memory` |
| regarg | `load {173} <- [{172}] in Block(11) is neither an element address nor an invariant address (elem=0 inv=0)` |
| saxpy-D | `recognize_header` (Block 10) |
| rowreg | `no INNER loop found inside this k loop` |

Three distinct gaps, in rough value order:

1. **A 32-bit induction variable.** `VReg{149}` is `Gpr32`, and both the heap and regarg
   tiers demand a `Gpr64` counter. h1 is `for i in 0..N { v.push(..) }` then
   `v.iter().sum()`; the counter is selected into a 32-bit register and every tier declines
   on the class. This is the same width-dialect family as the `MovRM32`/`MovMR32` conditions
   recorded above, and the one most likely to unblock the sum loop.
2. **A constant trip bound where a `len` field load is required.** The heap tier reads
   `v[i]` through the Vec's data pointer and wants the trip count to BE the `len` field; h1's
   bound is `MovRI 300000`. Note this is NOT the same gap that
   `same_len_by_equal_immediate` closed — that proved two bounds EQUAL; this one is about a
   tier requiring a particular *provenance* for the bound.
3. **The push loop stores.** `MovMR in Block(11) writes memory` correctly stops the
   cross-length proof there. The push loop is not the vectorizable one, so the right move is
   to recognise the SUM loop separately rather than to weaken that check.

**Not attempted here.** (1) runs through `is_counter`, whose zero-init precondition is
load-bearing for the emitters' footprint argument (see the correction recorded in this
series), so a 32-bit path needs the same care — and the same kind of non-vacuous tests that
caught my first draft of the loop-state tests.

### h1's cause, located exactly: one address spelled two ways

Instrumenting the heap tier the same way (hoisting its `bail!` macro above the preheader
bind and the PHI scan, then tracing its 12 remaining `?` propagations) finally makes the sum
loop report. Its three loops now each name a condition:

| header | loop | condition |
|---|---|---|
| Block(3) | the `v.push` loop | bound is `MovRI 300000`, not a len-field load — correct, it stores |
| Block(7) | the outer `p: u32` loop | `Gpr32` counter — correct, it is not the vectorizable loop |
| **Block(10)** | **the `v[k]` sum loop** | **`heap_elem_base(..)`** |

And the dump shows why. The loop reads two Vec header fields, and they are spelled
differently:

```
Block(10):  Lea   [v160, MemAddr { base: v0, disp: 16 }]   ; v.len  — a FOLDED displacement
            MovRM [v161, [v160 + 0]]

Block(11):  MovRI [v167, Imm(8)]                            ; v.ptr — a MATERIALIZED constant
            MovRR [v169, v168]                              ;         (v168 = v0)
            MovRR [v170, v167]
            AddRR [v171, v169, v170]                        ;         v171 = v0 + 8
            MovRM [v173, [v172 + 0]]
```

`heap_elem_base` accepts `Lea [base + disp]` but not `AddRR(base, <MovRI k>)` — the same
address, one form folded into a displacement and one built by adding a materialized
constant. That is exactly what the regarg tier's independent message said of the same
instruction: "load v173 <- [v172+0] in Block(11) is neither an element address nor an
invariant address (elem=0 inv=0)".

**This is the same spelling-gap family as the constant trip bound** that
`same_len_by_equal_immediate` closed: a value the backend sometimes folds and sometimes
materializes, with the recognizer written against only one spelling.

**The fix, scoped:** teach the field-address resolver to accept `AddRR(base, <MovRI k>)` as
`base + k`, with the fail-closed conditions this series has settled on — both operands
single-def, class-exact, a class-blind alias scan on the constant's vreg id, and no
redefinition between the materialization and the use. Not attempted here: it is address
recognition inside a tier that elides bounds-check diamonds, so it wants its own negative
tests (a non-constant addend must still refuse; a redefined addend must still refuse) before
any measurement, and the loop-state work in this series took four iterations precisely
because address and liveness reasoning resists one-pass changes.

### h1, concluded: the slice descriptor is REBUILT inside the loop

Fixing the materialized-displacement spelling (`AddRR(base, <MovRI k>)`) moved h1's wall
from `heap_elem_base` to `no single reduction accumulator found`. Dumping the block that
follows shows why that second message is a symptom, not the cause — **Block(11) is not the
accumulate at all, it is slice construction**:

```
MovRM [v173, [v172 + 0]]        ; v172 = v0 + 8   -> the Vec's ptr field
Lea   [v175, [v0 + 16]]
MovRM [v176, [v175 + 0]]        ;                 -> the Vec's len field
MovMR [[v182 + 0], v180]        ; STORE ptr into a stack temp (v1)
MovMR [[v184 + 0], v181]        ; STORE len into v1 + 8
CmpRR [v166, v178]              ; k <u len
```

Every iteration reloads both Vec header fields, **stores them into a local slice
descriptor**, and indexes through that. So the body contains stores, the element address is
two loads deep, and no single `AddRR(acc, elem)` is reachable — which is exactly the
condition recorded earlier in this project as h1's blocker ("a vreg-based slice temp plus
two-level loads"), reached here from the opposite direction.

**This is a pass-ORDER problem, not a recognizer gap.** The slice construction is loop
invariant; hoisting it is SROA/LICM's job, and both run AFTER `X86Vectorize` in the x86
pipeline, so neither can enable the vectorizer. That ordering is itself load-bearing
elsewhere, and the O3 manager runs to a FIXPOINT in which two rules that disagree
oscillate, so resequencing it is not a local change.

**Therefore h1 is NOT a further spelling fix.** The options, in increasing order of blast
radius: teach the heap tier to see through a store-then-load of an invariant descriptor
within one iteration; or give the vectorizer a pre-pass that hoists an invariant slice
construction; or revisit the pipeline order. All three are larger than anything else in
this report, and none should be attempted without first confirming which block h1 actually
spends its time in (the int3 check) — this project has already costed one gap against a
dead loop.
