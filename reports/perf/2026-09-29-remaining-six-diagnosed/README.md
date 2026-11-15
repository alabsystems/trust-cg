# The six programs still above LLVM, each diagnosed to a distinct cause (2026-09-29)

With h1 at parity the corpus's shape changed, so the remaining gaps were re-diagnosed from
scratch rather than carried over. They do NOT share a cause, and two of the six had never been
examined at all — they sat below the harness's 50 ms resolvability floor until in-batch
identical-binary controls made their gaps readable.

| program | vs LLVM | control | cause |
| --- | ---: | ---: | --- |
| b1_mispredict | 1.1308x | 1.0020 | misprediction-bound; **LLVM duplicates the loop body so one arm is branch-free** |
| h3_box_leak | 1.0990x | 1.0036 | **memory-latency bound** — a dependent `Box` pointer chase; instruction count does not matter |
| p4_matmul | 1.0922x | 1.0015 | only **1.026x clang**; the big number is the gcc/LLVM gap, not ours |
| h4_vec_dropper | 1.0537x | 1.0095 | **the vector loop's induction variable is spilled and reloaded ONCE PER USE** |
| p2_collatz | 1.0190x | 0.9996 | a redundant header copy (spec written, site documented as silently miscompiling) |
| h2_vec_grow | 1.0117x | 0.9988 | same IV spill as h4 |

## h3_box_leak: memory-latency bound, so the 8-instruction deficit is irrelevant

h3's inner loop is h1's shape with one more indirection — `Vec<Box<u64>>`, so `*v[k]` loads the
`Box` pointer and then dereferences it.

```
tcg, 14 instructions            LLVM, 6 instructions
  mov  (%rdi),%rax   len          mov  (%r9),%r11
  cmp  %rax,%rbx                  add  (%r11),%rdi     <- load+add fused, memory operand
  jae  exit                       inc  %r10
  mov  %rbx,%rcx                  add  $0x8,%r9        <- pointer increment, not indexed
  mov  (%r8),%rdx    ptr          cmp  %r8,%r10
  mov  (%rsi),%rax   len AGAIN    jne  loop
  cmp  %rax,%rcx     BOUNDS CHECK
  jae  panic
  mov  (%rdx,%rcx,8),%rax
  mov  (%rax),%rcx   the Box deref
  add  %rcx,%r14
  add  $0x1,%rbx
  jmp  loop
```

**This was tested, not assumed.** `x86-bce-ptr-reload` (BCE case 5) *does* fire on h3 — the
binaries differ — and the runtime does not move: 1.0042x with an in-batch control of 1.0036x.
Removing the bounds check and a length reload from a loop whose critical path is a dependent
two-level load buys nothing, because the loads dominate. That is why h3 is only 10% behind while
running 2.3x the instructions.

So h3's remaining levers are LLVM's, not instruction count: a memory-operand `add` that fuses
the load, and a pointer increment instead of a scaled index.

## A correction: BCE case 5's 11.1% on h1 is now SUBSUMED, and it stays default-off

Earlier today case 5 measured **11.1% faster on h1**. That number was correct then. It is no
longer available, because h1 now **vectorizes** — its scalar loop is the remainder tail and barely
runs. Re-measured on the current default build, h1 with case 5 on versus off is
**1.0032x against a 0.9981 control, i.e. neutral**.

So case 5 currently buys nothing measurable anywhere: neutral on h1 (subsumed), neutral on h3
(memory-bound), and it does not fire elsewhere. It correctly stays DEFAULT OFF — a sound
capability with, at present, no demonstrated benefit. Recording this because the earlier 11.1%
would otherwise read as a live argument for turning it on.

## h4 and h2: the vector loop reloads its induction variable once per USE

Both are already vectorized. h4's vector loop, 12 instructions:

```
mov    -0x78(%rbp),%r10     <- reload the IV
lea    (%rsi,%r10,8),%rax
movdqu (%rax),%xmm0 ; paddq %xmm0,%xmm2
movdqu 0x10(%rax),%xmm0 ; paddq %xmm0,%xmm1
mov    -0x78(%rbp),%r10     <- reload the SAME slot again
add    $0x4,%r10
mov    %r10,-0x78(%rbp)     <- store it
mov    -0x78(%rbp),%r10     <- and reload it a THIRD time
cmp    %rdx,%r10
jb     loop
```

**Four of twelve instructions are spill traffic for a loop counter**, and three of them are
reloads of one slot with no intervening write to it. One reload at the top and one store at the
bottom would do: 8 instructions instead of 12.

Surveyed across every vectorized loop in the corpus, this hits **exactly h4 and h2** — the two
programs whose `Vec` is constructed inside an outer loop, so the IV is live across it:

| program | vector loop insns | stack-relative ops |
| --- | ---: | ---: |
| h1_vec_push_sum | 6 | **0** |
| v1_saxpy | 9 | **0** |
| p7_sieve | 11 | **0** |
| v3_popcount | 26 | **0** |
| p4_matmul | 45 | **0** |
| **h4_vec_dropper** | 12 | **4** |
| **h2_vec_grow** | 12 | **4** |

So the vectorizer emits clean loops; the allocator spills under outer-loop pressure and then
reloads per use rather than once per iteration.

## x86 has no spill-reload CSE either — a SECOND AArch64-only pass

`elide_redundant_spill_slot_reloads` exists, with a cross-block mode, a kill switch
(`TCG_SPILL_RELOAD_CSE_OFF`), a bisect key and native tests. It takes an **`IrMachFunction`** —
the AArch64 machine IR — and is called only from the generic pipeline. Nothing in the x86 path
calls it, and `X86ISelFunction` has no equivalent.

This is the same structural asymmetry as
[the missing scheduler](../2026-09-29-x86-no-scheduler/) — but unlike the scheduler, which
measured out at ~1%, this one has a concrete measured target: h4 and h2's redundant reloads are
2 of 12 instructions in their hot vector loops. Whether that converts to runtime is UNMEASURED,
and both programs are dominated by `Vec` allocation traffic rather than the sum loop, so it
should be measured before it is built.

## b1_mispredict, the largest remaining gap

Its hot loop is 42 instructions against LLVM's 26, and the four named items were listed in
[the cross-block flag report](../2026-09-29-x86-sib-crossblock-flags/). The dominant one is
structural: **LLVM duplicates the loop body so that the `s & 1 == 0` arm is entered with no
taken branch at all**, by making the back edge land directly in that arm. On a program whose
branches are unpredictable by construction, that is worth more than the three small items
(`bt` versus `test`, the `lea`+`mov` increment, the extra copies) which together are ~5
instructions. Loop specialization on a loop-carried predicate is a real optimization trust-cg
does not have.

## p4_matmul is mostly not our gap

Restating, because a single "vs LLVM" number hides it: trust-cg is **1.026x clang** on p4, and
**gcc is 1.133x faster than LLVM** there. So most of p4's 1.0922x is the gcc/LLVM difference,
which LLVM does not close either.

## Status of the clause

Not met. Six programs above LLVM, from 1.01x to 1.13x, with five distinct causes — memory
latency, allocator spill placement, loop duplication, a documented-unsafe rename site, and one
that is mostly a gcc/LLVM difference. The 2.5x outlier is gone and eight of eighteen programs beat
LLVM outright.

## Addendum: sizing the h2/h4 fix, and why it is NOT a small one

Three further facts were established before deciding not to build it in this session.

**1. It is not a configuration mistake.** The x86 pipeline already uses the good allocator:
`X86PipelineConfig::default` sets `regalloc_mode: Full(AllocStrategy::Greedy)` — the "LLVM-style,
processes by spill weight with eviction and splitting for better code quality" strategy, with
coalescing, remat and live-range splitting all on. `LinearScan` is used only by the
`host_jit_fast` profile. So the spill is a considered decision of a real allocator under
whole-function pressure, not a fallback path.

**2. Spill rematerialization is already on and does not apply.** `x86_spill_remat_enabled()`
defaults ON (`TCG_NO_X86_SPILL_REMAT` is the opt-out, and being a `TCG_*` env var it is
unreachable through `trustc` anyway). It recomputes spilled values whose sole def is a constant or
a frame address; h2/h4's spilled value is a loop-carried counter, so it is not a remat candidate.
`materialize_x86_spills` also already carries a targeted elision for a different h2 pattern
(`mov -0x70(%rbp),%r10; mov %r10,-0x70(%rbp)`, a self-copy of a spilled vreg), so this area has
been worked before.

**3. The right fix — a block-local spill-reload CSE — sits in the one place with NO validator
covering the class of mistake it could make.** The rules are simple and would remove both of h4's
redundant reloads (`avail[slot] == dst` ⇒ delete), taking the vector loop from 12 to 10
instructions. The natural home is immediately after `materialize_x86_spills`, beside the existing
phase-2b `MovRR` coalescer. But that coalescer's own soundness note says, of TV-5:

> its documented v1 misses (wrong-value renames of NON-tied use slots, **spill-slot/memory
> dataflow**) mean a bad rename of a PLAIN read would still miscompile silently — exactly the class
> the first draft of this pass exhibited before TV-5 existed

So a spill-slot dataflow transform here is precisely the case TV-5 does not check, in a pass whose
sibling *did* miscompile silently on its first attempt. Every other change landed today had either
a differential, a census, a committed refutation or a translation validator standing behind it;
this one would have none. It is deferred for that reason and not for lack of a design — the rules,
the location, the expected instruction counts and the two target programs are all recorded above.

What would make it safe: extending TV-5's post-RA dataflow to cover spill-slot memory (which is
listed as a known v1 gap), or a byte-level differential across a wide corpus in both arms. Either
is a prerequisite, not an afterthought.

## Addendum 2: h2/h4's spill is NOT an emitter defect — the emitter is already clean

Before assuming the vectorizer emits bad code, the emitted IR was checked against the
disassembly. It does not: `apply_heap_sumq_plan`'s x4 body is

```
LeaSib   pe,  [ptrv + viv*8]
MovdquRM xe,  [pe]        ; Paddq vacc,  vacc,  xe
MovdquRM xe1, [pe + 16]   ; Paddq vacc1, vacc1, xe1
AddRI    viv, viv, 4                        <- in-place, "carrier-RMW form, no fixup copy"
Jmp      vh
```

with `CmpRR viv, vn ; Jcc` in VH. That is already what a good emitter produces: a **dedicated
vector induction variable** (`viv`, not the scalar loop's `iv`), an **in-place** advance with no
write-back copy, and three uses total.

So the four stack operations in h2/h4's vector loop are **entirely register-allocator spill code**
for `viv` — a reload before each of its three uses plus a store after its def — and not something
the vectorizer wrote. That localizes the fix and rules an emitter change out:

| candidate | verdict |
| --- | --- |
| emit a fresh vector IV instead of the scalar one | **already done** |
| emit an in-place advance instead of add + write-back | **already done** |
| reduce `viv`'s uses from 3 to 2 by advancing a pointer instead of indexing | swaps one live value for another (`pe` becomes loop-carried too) — no clear pressure win |
| eliminate `viv` by comparing pointers against a precomputed end | LLVM's shape, but `iv` must still be reconstructed for the scalar tail, which puts the use back |
| block-local spill-reload CSE | the right fix, and blocked on TV-5 covering spill-slot dataflow (Addendum 1) |
| a better spill placement for a loop-carried value used 3 times | an allocator change; `Greedy` with eviction and splitting is already the default |

The two remaining rows are the only real candidates, and both are projects rather than fixes.
