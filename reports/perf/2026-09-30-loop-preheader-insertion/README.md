# Preheader insertion: the blocker was real and is now removed; p4's next blocker is named

Ported from LLVM 22.1.2 `InsertPreheaderForLoop`
(`llvm/lib/Transforms/Utils/LoopSimplify.cpp:115-149`) ->
`SplitBlockPredecessorsImpl` (`BasicBlockUtils.cpp:1298-1385`), with machine-level edge
mechanics from `MachineBasicBlock::SplitCriticalEdge`
(`MachineBasicBlock.cpp:1187-1416`). Opt-in `x86-loop-simplify`.

## Why it was worth building

`mach_view::find_preheader` yields a preheader ONLY when a header has exactly one
non-loop predecessor, and every loop-consuming x86 pass reads
`GenericLoop::preheader`. So a header fronted by a bounds-check diamond is declined for
CFG SHAPE, not for any property of the loop. `p4_matmul`'s k loop was reported that way:
`rowreg-bail[hdr=Block(18)]: k loop has no preheader`, blocking the tier that "holds the
(k-stationary) c row in `N/2` XMM accumulators across the whole k-loop, eliding the
per-(k,j) c store/reload" — p4's recorded gap, already implemented.

This is genuinely new work rather than a port of a machine pass: LLVM canonicalizes only
pre-ISel, and its machine-level `MachineLICM::getOrCreatePreheader`
(`MachineLICM.cpp:1692-1709`) BAILS on exactly this shape, because
`getLoopPredecessor` (`GenericLoopInfoImpl.h:242-248`) returns null the moment a second
out-of-loop block branches to the header.

## One shot was not enough — and that is LLVM's design, not a bug in mine

Run once at the head of the pipeline, the pass did NOTHING to p4, and its own trace said
why: **every p4 loop already had a preheader at that position**
(`preheader=Some(..)`, one `outside_pred` each), and `Block(18)` was a LATCH there, not a
header. The vectorizer runs up to THREE times (early, post-SROA, late), and the later runs
analyse a CFG that intervening block-merging and rotation have restructured — so the
property established at the head of the pipeline is gone by the time a later consumer
needs it. LLVM treats loop-simplify form as a per-consumer REQUIREMENT re-established
before each pass that needs it (`IndVarSimplify.cpp:2055-2059` names the requirement), not
a one-shot. The pass is idempotent — a test asserts a second run is a no-op — so it now
runs before each vectorizer run.

**That fixed it.** `rowreg-bail[hdr=Block(18)]: k loop has no preheader` is GONE.

## Correctness and performance

7 of 18 programs change (h1, h2, h4, p4, p7, v2, v3); all exit-match trust-cg/LLVM. With
the knob off, all 18 are byte-identical, so the opt-in gate holds.

| program | off | off2 (floor) | on | verdict |
| --- | ---: | ---: | ---: | --- |
| `h1_vec_push_sum` | 0.7734 | 0.7736 | **0.7681** | 0.7% faster, 26 floors — real but small |
| `h2_vec_grow` | 1.0011 | 1.0010 | 1.0016 | neutral |
| `p4_matmul` | 1.0818 | 1.0815 | 1.0818 | **exactly neutral** |
| `p7_sieve` | 0.7143 | 0.7206 | 0.7117 | inside floor |
| `v2_memfill` | 1.0032 | 1.0012 | 1.0009 | inside floor |
| `v3_popcount` | 0.1005 | 0.1002 | 0.1001 | inside floor |
| `h4_vec_dropper` | 1.0472 | 1.0334 | 1.0421 | **UNREADABLE** — floor 0.0138 |

The only movement is h1's 0.7%, on a program already 23% faster than LLVM. Nothing crosses
parity in either direction.

⚑ h4's two byte-identical copies differ by 1.4% in this batch, so no h4 conclusion is
drawn from it. That program's clean-batch floor is 0.0076, the corpus's worst.

## p4's NEXT blocker, named

With the preheader established, `rowreg` declines one step later:

```
hdr=Block(14): more than one nested loop strictly inside this one
               (hdr=Block(18) and hdr=Block(35)) — this tier is two-level only
hdr=Block(18): no INNER loop found inside this k loop
```

**p4's j loop has ALREADY been split into a vector loop plus a scalar remainder by the
earlier vectorizer run**, so from `rowreg`'s perspective the k loop now contains TWO inner
loops and it is two-level only. `Block(18)` is innermost and contains none.

That is a design tension inside `rowreg`, not a missing canonicalization, and it has two
possible resolutions, neither of which is a guess:

1. **Recognize a vector+remainder pair as ONE logical inner loop.** Their headers are
   sibling loops created by a known plan, so the pair is identifiable rather than inferred.
2. **Try `rowreg` before the inner tier applies.** Recognition already happens for all
   loops before any application (the plans are collected, then applied), and `rowreg` is
   tried before `saxpyq` in the else-if chain — so this may already hold on the EARLY run
   and fail only on the later ones. The trace does not currently separate runs, which is
   the next diagnostic to add.

Recorded rather than pursued because the remaining budget does not cover building and
measuring either. The preheader pass stays: it removes a real, LLVM-named blocker, it is
correct on 7 programs, and it is the prerequisite for both resolutions above.

---

# Follow-up: which vectorizer run declines p4, and one inference retracted

The bail macros now print a RUN INDEX (`rowreg-bail[run31/...]`), because the schedule
holds up to three `X86Vectorize` instances and each sees a different CFG — the early run's
applied plans SPLIT an inner loop into vector + remainder, so a two-level nest becomes
three-level for every later run. A histogram that cannot say which run emitted a line
cannot distinguish "this tier never accepts this nest" from "it accepted on the early run
and the later runs see the loop it already transformed", and those call for opposite work.

For `p4main`, only two runs emit bails, and they differ:

```
run31: hdr=Block(2)  no INNER loop found
run31: hdr=Block(6)  more than one nested loop (hdr=Block(9) and hdr=Block(14))
run31: hdr=Block(9)  more than one nested loop (hdr=Block(14) and hdr=Block(18))
run31: hdr=Block(18) no INNER loop found
       -- no bail at all for Block(14)

run32: hdr=Block(14) more than one nested loop (hdr=Block(18) and hdr=Block(35))
run32: ... plus the rest
```

So on the EARLY run, `Block(14)` — the k loop — produces no bail from `rowreg` or from
`saxpyq`. On the later run it is declined for holding two inner loops, which is the
vector+remainder split the early run created.

**INFERENCE RETRACTED.** I first read "no bail from either tier" as `rowreg` having
ACCEPTED `Block(14)`, since it is tried first. That does not follow: the tiers are an
`else if` chain and FOUR recognizers precede `rowreg` — `recognize_elementwise_loop`,
`recognize_fill_loop`, `recognize_runtime_byte_fill_loop`, `recognize_saxpy_loop`. Any of
them accepting `Block(14)` yields exactly the same signature. The run index narrowed the
question; it did not answer it.

The codegen agrees that nothing material happened: p4's `main` is **484 instructions with
and without the pass**, with identical `pmuludq` (12), `paddq` (24) and `movdqa` (18)
counts and one extra `imul`. Whatever accepted `Block(14)` on the early run, the
XMM-accumulator transform is NOT in the emitted code, which is consistent with p4's time
being unchanged to within 0.0003.

**What would settle it**, and neither is a guess: give the four preceding tiers the same
bail trace the saxpy-Q tiers now have, so an acceptance is distinguishable from a silent
decline; or log the tier NAME on acceptance. Both are diagnostics, not transforms, and
until one is in place the claim "rowreg fires on p4" must not be made.
