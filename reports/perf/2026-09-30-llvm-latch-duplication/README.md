# b1's gap, read out of LLVM 22.1.2 instead of guessed: it clones the LATCH into both arms

Source read at `$HOME/trust/src/llvm-project` (LLVM 22.1.2,
`cmake/Modules/LLVMVersion.cmake:4-11`, commit `ceb94fe99cbc7db4bbe617b53fd04a61acbd4467`).
Every claim below was read from source and then independently re-opened by a second pass
that confirmed 42 of 43 citations; the corrections that pass produced are folded in and
marked.

## The observation that settles which transform this is

`b1_mispredict`'s `main`, disassembled from both compilers:

| | backward branches | targets | span |
| --- | ---: | --- | ---: |
| trust-cg | **1** | `0x2095b` | 149 B |
| LLVM -O3 | **2** | `0x20880` and `0x20894` | 86 B, 89 B |

Two backedges to two DIFFERENT targets is the signature of latch duplication: each arm of
the in-loop diamond ends with its own copy of the counter update and its own backedge. It
is not loop-body duplication in the "two copies of everything" sense I had assumed from
the earlier note, and it is not a branch-elimination transform — LLVM KEPT the branch.

## Which pass, confirmed by pass-attribution experiment

MachineBlockPlacement's *integrated* tail duplication ("TailDupPlacement") — NOT the
standalone `TailDuplication` pass and NOT any `Transforms/` pass:

    MachineBlockPlacement::run -> buildCFGChains -> buildLoopChains -> buildChain
      -> repeatedlyTailDuplicateBlock -> maybeTailDuplicateBlock
      -> TailDuplicator::tailDuplicateAndUpdate -> TailDuplicator::tailDuplicate

It runs POST-RA and post-PEI (`MachineBlockPlacement.cpp:3610`, `const bool PreRegAlloc =
false;`), scheduled at `TargetPassConfig.cpp:1216`. Attribution was measured, not inferred,
on a synthetic xorshift loop with an `if (s&1) add else xor` body: the duplicated latch
instruction appears twice by default, twice with `-disable-tail-duplicate`, twice with
`-disable-early-taildup`, and **once with `-tail-dup-placement=false`**.

## Why it fires on exactly this CFG — the no-profile rule

`hasBetterLayoutPredecessor` (`MachineBlockPlacement.cpp:1636`) rejects the latch as a
plain fall-through candidate when

    freq(armB->latch) * HotProb >= freq(armA->latch) * (1 - HotProb)

with `HotProb = StaticLikelyProb = 80/100` when there is no profile
(`MachineBlockPlacement.cpp:1445-1447`). For a 50/50 data-dependent branch that is
`0.4 >= 0.1` — **always true**. The latch is therefore pushed into `DupCandidates`
(`MachineBlockPlacement.cpp:1711-1712`). This is the structural reason the transform exists
for this shape, and it is why it is reachable with no PGO.

**Correction from verification:** `isProfitableToTailDup` is called from exactly ONE site
(`MachineBlockPlacement.cpp:1747-1748`, Path B). Path A in `buildChain`
(`MachineBlockPlacement.cpp:1939-1941`) sets `ShouldTailDup` with **no profitability call at
all** — legality plus size is the whole gate on that path.

## The size gate, and why b1 is inside it

`TailDuplicator.cpp:661-667`:

    if (MI.isBundle())              InstrCount += MI.getBundleSize();
    else if (!MI.isPHI() && !MI.isMetaInstruction()) InstrCount += 1;
    if (InstrCount > MaxDuplicateCount) return false;

`MaxDuplicateCount` for x86-64 via MBP is **4 at -O3**, 2 below it
(`TargetInstrInfo.h:2344-2345`; `TailDupPlacementAggressiveThreshold = 4` at
`MachineBlockPlacement.cpp:178-183`), and **1 when the block is optimized for size** —
which is a PER-BLOCK ProfileSummaryInfo query (`TailDuplicator.cpp:583-584`), not a global
`-Os` switch. Terminators count; PHIs and meta instructions (DBG_*, CFI, labels, KILL,
IMPLICIT_DEF) do not. Threshold sweep confirmed the boundary exactly: a 3-instruction latch
duplicates at `-tail-dup-placement-threshold=3` and above, not at 1 or 2.

**b1's latch in trust-cg is `lea 0x1(%rdi),%rax ; mov %rax,%rdi ; cmp $K,%rax ; jb` — four
instructions, exactly at the -O3 limit.** So the transform is applicable here, and would
still be applicable at three if the latch-advance collapse fired first.

**Correction from verification:** one relaxation is live post-RA —
`TailDuplicator.cpp:618-619`, `if (HasComputedGoto && !PreRegAlloc) MaxDuplicateCount =
std::max(MaxDuplicateCount, 10u);`. Irrelevant to b1 (no computed goto) but it means K is
not a single constant.

## What LLVM's model does NOT contain

There is **no branch-prediction modelling anywhere in this decision.** Greps for
mispredict / branch predict / predictor / local history / global history across
`MachineBlockPlacement.cpp` and `TailDuplicator.cpp` return only two incidental comments.
The entire model is taken-branch/fall-through counting plus a 2% icache penalty
(`TailDupPlacementPenalty = 2`). `MisfetchCost` and `JumpInstCost` exist but are used only
in `rotateLoopWithProfile`, which requires profile data and is therefore dead here.

**So my working hypothesis — that b1's 9.3% is branch-prediction accuracy from shorter
per-copy history — is not LLVM's rationale.** By LLVM's own cost model the win is
incidental to a fall-through-motivated transform. That does not make the hypothesis wrong
about the hardware, but it does mean I should not cite LLVM as evidence for it.

## The counting rule that stops it over-firing

`canTailDuplicateUnplacedPreds` (`MachineBlockPlacement.cpp:1225-1311`), no-profile path:
`NumDup + 1 <= succ_size(T)`. For a two-arm diamond latch that is **2 <= 2 — exactly at the
boundary**, and it is the whole benefit model without PGO. It is also what prevents the
transform firing on a 3- or 4-way join.

Verification also caught three things the first read got wrong here, all of which make the
rule LESS restrictive than reported: the `Duplicate` all-or-nothing flag has a trellis
escape (`MachineBlockPlacement.cpp:1233-1268`), there is an early
`if (Succ->succ_empty()) return true;` (`:1287-1288`) that bypasses the counting rule, and
the EH-pad/inline-asm-br predecessor check lives in `duplicateSimpleBB`
(`TailDuplicator.cpp:754,762`), a function the MBP path never reaches.

## Preconditions to implement, post-RA

ON THE TAIL `T` (the latch):
1. `succ_size(T) >= 2` (`MachineBlockPlacement.cpp:841-850` refuses `succ_size()==1`).
2. `T` is not its own successor.
3. `analyzeBranch(T)` succeeds, or `T` cannot fall through.
4. Non-PHI non-meta instruction count `<= 4`.
5. No convergent instruction, no `INLINEASM_BR`, nothing non-duplicable. Post-RA, calls and
   returns ARE allowed — LLVM refuses those only when `PreRegAlloc`.

ON EACH PREDECESSOR `P` cloned into:
6. `succ_size(P) <= 1` and its only successor is `T`.
7. `analyzeBranch(P)` succeeds AND the condition list is EMPTY — i.e. `P` ends in an
   unconditional branch or a bare fall-through. This is the diamond-arm shape, and
   requiring BOTH is load-bearing: LLVM does
   `PredBB->removeSuccessor(PredBB->succ_begin())` then asserts `succ_empty()`
   (`TailDuplicator.cpp:933-935`), so with two successors you delete the wrong edge and
   silently retarget a branch.

TRANSFORM: pick the layout predecessor `L`; for every other qualifying `P`, drop `P`'s
terminator, append a verbatim clone of every instruction of `T` (operands, subregs,
kill/dead/undef flags unchanged — no renaming post-RA), set `succ(P) := succ(T)`, and
re-materialize `P`'s terminators for its new layout successor, reversing the condition when
the new layout successor is the other edge. Then if `T` has exactly one predecessor `L`
which falls through to it unconditionally **and `T`'s address is not taken**, splice `T`
into `L` and delete it.

**Correction from verification:** "`T`'s address is not taken" is NOT a precondition on
CLONING — `hasAddressTaken` is consulted only by the splice guard
(`TailDuplicator.cpp:964`) and dead-block removal (`:189`). Implementing it as a
precondition on duplication would be strictly more conservative than LLVM.

Post-RA there is no PHI insertion, no SSA repair and no live-in recomputation to do — and
that is only true because a WHOLE block is cloned into a predecessor whose sole successor
was that block.

---

# Ported, and it fires on NOTHING: the shape is gone by the time the pass runs

`x86_latch_dup` implements every gate above, post-RA, behind the tracked opt-in
`x86-latch-dup`. 7 unit tests cover the firing case and five declines; the full
`trust-cg-opt --lib` suite is 3891 passed / 0 failed. Then:

| arm | result |
| --- | --- |
| knob OFF vs the committed default | **18 of 18 byte-identical** (the opt-in gate holds) |
| knob ON | **18 of 18 byte-identical** — the pass fires on nothing |
| b1 backward branches | off 1, on 1, LLVM **2** |

So the transform is correct, tested, inert, and did not move the signature it was
built to reproduce.

## Why, from the pass's own trace rather than a guess

`trace-x86-latch-dup` names the failing gate for every candidate block in b1's `main`:

```
Block(0) declined — succ_size=1 < 2
Block(1) declined — not a backedge target (no successor earlier in layout)
Block(2) declined — not a backedge target
Block(3) declined — succ_size=1 < 2
Block(4) declined — succ_size=1 < 2
Block(5) declined — succ_size=1 < 2
Block(6) declined — instruction count 7 > budget 4      <-- the closest candidate
Block(7) declined — succ_size=0 < 2
```

and on later invocations the nearest candidate is `Block(4)` with **16** instructions.
Across the whole compilation the decline histogram is 27 `succ_size=0`, 9 `succ_size=1`,
9 not-a-backedge-target, 3 "tail is its own successor (single-block loop)", and 3 over
budget.

**⚑ THE PARAGRAPH THAT WAS HERE WAS WRONG, and the CFG dump refuted it.** I concluded
from the decline histogram that b1's latch had been merged away by rotation and block
merging, i.e. that this was a pass-POSITION problem. It is not. Dumping the CFG the pass
actually sees (`trace-x86-latch-dup` now prints it) shows the shape intact:

```
Block(0) insts=18 succs=[1, 5]                      entry/guard
Block(1) insts=13 succs=[2, 3]  preds=[0, 4]        loop header, the diamond branch
Block(2) insts=11 succs=[4]     preds=[1]           arm A
Block(3) insts=10 succs=[4]     preds=[1]           arm B
Block(4) insts=16 succs=[1, 5]  preds=[2, 3]        THE LATCH, backedge to 1
Block(5) insts=34 succs=[]                          exit
```

Every structural gate passes: two successors, a backedge target, two single-successor
`Jmp`-terminated arms, `dup + 1 == succ_size == 2`. The ONE failing gate is SIZE — the
latch holds **16** instructions, against a budget of 4.

The lesson is about the budget, not the shape. I took "4" from the FINAL DISASSEMBLY,
where b1's latch tail is `lea 0x1(%rdi),%rax ; mov %rax,%rdi ; cmp $K,%rax ; jb`. But
LLVM's `MaxDuplicateCount = 4` counts POST-RA machine instructions
(`MachineBlockPlacement.cpp:3610` sets `PreRegAlloc = false`), whereas this pass runs
PRE-RA, where the same block still carries 16 instructions that register allocation,
coalescing and the peephole later collapse to four. **An instruction budget lifted from
another compiler is only meaningful at the same pass position** — the same class of error
as reading a pass's input off the final binary ([[dump-position-vs-pass-position]]).

There is a second, smaller adjustment the dump makes visible. LLVM's post-RA count
includes ONE terminator for a conditional block whose other edge is the implicit
fall-through; this IR names BOTH edges (`Jcc` + `Jmp`), so the identical block counts one
higher. A faithful port must therefore exclude a trailing `Jmp` whose target is the
block's layout successor — which, for `Block(4)` above, is exactly `Block(5)`. With the
pass moved post-RA and that exclusion applied, b1's latch counts 4, matching LLVM.

LLVM does not have this problem because its tail duplication is INSIDE
MachineBlockPlacement: MBP is what both chooses the layout and merges blocks, so the
duplicator sees the CFG before any merging. trust-cg splits those responsibilities across
separate passes, so there is no point in its schedule that has both a chosen layout AND
an unmerged latch.

## What that leaves

MOVE THE PASS POST-RA, which is where LLVM runs it, and count instructions the way LLVM
counts them at that position:

* place the call alongside the other post-RA stages (after `fixup_two_address` and the
  `MovRR` coalescer, after frame lowering, before `resolve_x86_branches`) — the same
  region as `elide_redundant_x86_spill_reloads`, and the analogue of MBP running post-PEI;
* exclude a trailing `Jmp` to the block's layout successor from the count, since LLVM's
  equivalent block leaves that edge implicit;
* keep every other gate exactly as ported and verified.

`block_order` is final by then, so the layout predecessor the transform needs is still
well defined — the reason the pass was placed after branch layout in the first place.

Recorded as a negative result with its refutation rather than deleted: the admission
logic is ported and checked against LLVM, and the only thing that was wrong is where it
runs and how it counts.

---

# FINAL: the transform fires, reproduces LLVM's signature exactly, and is 3% SLOWER

Two further corrections were needed before this could be measured at all, and both were
mine:

1. **The pass was installed on two dead code paths.** `x86_64/pipeline.rs` has THREE
   copies of the post-RA sequence; only
   `compile_function_with_fixups_frame_and_evidence_after_x86_passes` is the
   object-emission path the rustc backend uses (its own Phase 2b comment says so). The
   other two have a bare coalescer call, the live one wraps it in
   `backend_timing::timed(...)`, so a textual anchor written against the first two matched
   exactly the wrong sites. The pass compiled, was knob-wired, was unit-tested, and
   changed 0 of 18 binaries — indistinguishable from "never applies". What caught it was
   the trace printing a decline for EVERY candidate plus the whole CFG: zero output is
   distinguishable from many declines.
2. **b1's latch is 9 instructions post-RA, not 4.** The "exactly 4, right at LLVM's
   limit" claim earlier in this document was taken from the FINAL BINARY's loop tail, not
   from the post-RA block. So with LLVM's own constant, **LLVM would decline b1's latch
   too.** Raising the budget is a new policy, not a port, so it became a tracked knob
   (`x86-latch-dup-max-insts`) whose doc says exactly that.

## The sweep

At budget 4 (LLVM's value) the default build is **18 of 18 byte-identical** — the pass
declines everything in the corpus. Raising the budget changes exactly ONE program, b1,
and it fires there at 9 and above. All arms exit-match trust-cg/LLVM.

| b1_mispredict | backward branches | insns in `main` | vs LLVM -O3 |
| --- | ---: | ---: | ---: |
| default (budget 4, declines) | 1 | 130 | 1.0943 / 1.0938 (floor 0.0005) |
| budget 9 | **2** | **100** | **1.1267** |
| budget 12 | 2 | 100 | 1.1258 |
| budget 16 | 2 | 100 | 1.1261 |

**The transform works exactly as designed.** It reproduces LLVM's structural signature —
two backedges where trust-cg had one — and it even shrinks `main` from 130 instructions to
100. And b1 gets **3.0% SLOWER**, far outside its 0.0005 floor. The three budgets agree to
0.0009, as they must once the 9-instruction latch is admitted: they all produce the same
clone.

## What this settles

* **b1's gap is NOT latch duplication, and not loop specialization of this shape.** This
  was the last named candidate in b1's refutation set. The two-backedge layout is
  reproducible, cheaper in instructions, and slower. Do not re-derive it from the LLVM
  diff a fourth time.
* **LLVM's budget of 4 is vindicated on its own terms.** It declines b1's latch, and
  declining it is the right call on this host. The constant was not conservatism.
* **Another instance of instruction count not being b1's lever** — 30 fewer instructions
  in `main`, 3% slower. That now holds for the copies, the extra `jmp`, `bt` vs `test`,
  the JCC padding, the latch `mov`, loop-head alignment, branch count, and now the whole
  loop layout.

The pass stays in the tree, DEFAULT OFF at LLVM's budget, with 8 tests and this
measurement in its module doc. It is a correct, gated implementation of a real LLVM
transform with a known verdict on this corpus: if a program ever presents a diamond whose
latch is genuinely small, it will fire under LLVM's own policy. What it must not be used
for is b1.
