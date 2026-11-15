# b1_mispredict: 1.1518x -> 1.1326x LLVM, by giving the SIB fold the cross-block flag proof (2026-09-29)

A real, measured speedup — the first of this stretch. Small (1.43%) and cleanly attributed.

## Where it came from: diffing b1's hot loop against LLVM's

After the [scheduler refutation](../2026-09-29-x86-no-scheduler/) removed the wrong
explanation, I diffed b1's actual hot loop against LLVM's. Anchoring on the xorshift
constants (`shl $0xd` / `shr $0x7` / `shl $0x11`) and taking the tightest backward branch
enclosing them:

| | hot loop insns | span | branches | memory ops | `mov` | `imul` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| LLVM | **26** | 84 B | 2 | 1 | 6 | 0 |
| trust-cg | **44** | 173 B | 4 | 5 | 16 | 2 |

One difference was flagrant. For `t[j] = t[j].wrapping_add(acc)`, trust-cg's LOAD already
uses a scale-8 SIB, and then its STORE re-derives the byte offset with an `imul`:

```
209d4:  mov    %rax,%rbx                  <- feeding copy
209d7:  mov    -0xa0(%rbp,%rax,8),%rdx    <- LOAD: scale-8 SIB, index rax. Good.
209df:  add    %rsi,%rdx
209e2:  imul   $0x8,%rbx,%rax             <- 2 WASTED INSTRUCTIONS
209e6:  mov    %rdx,-0xa0(%rbp,%rax,1)    <- STORE: scale-1 SIB on the pre-multiplied index
```

`sib_scale1_index_fold` exists precisely for this and was already default-on. So why not?

## The answer was written down in the codebase, by the test that pins the failure

`sib_fold_falls_back_to_scale_1_and_retains_the_chain_when_flags_may_be_live`, and its doc:

> This is the shape the `b1_mispredict` benchmark ships (`imul $8,%rsi,%rax` /
> `add %rax,%rcx` / `mov %rbx,-0xa8(%rbp,%rax,1)`), so this test is where to start when
> revisiting that sequence. [...] so the cost is NOT recoverable by a dead-code pass, only by
> **widening the flag-deadness proof** or by scaling inside the operand.

The fold may only delete the `imul` if the `imul`'s RFLAGS write is dead, and
`sib_fold_flags_dead` is **block-local** — it refuses at `is_terminator()` and again if it
falls off the end. Confirmed against the real IR with the `trace-peephole-entry` instrument:
the `ImulRRI v91, v89, Imm(8)` is the second-to-last instruction of its block, and the
`AndRI _, _, 6` that discharges the obligation is in the fall-through SUCCESSOR.

And the widening the doc asks for **already existed**. `crates/trust-cg-opt/src/x86_flag_liveness.rs`
is a cross-block RFLAGS `may-be-observed` analysis whose own module doc says:

> The measured case that motivated this is the `b1_mispredict` hot loop, where a value-dead
> `add` is the second-to-last instruction of its block and the `and $0x6,%rcx` that discharges
> its flag obligation is the second instruction of the fall-through successor.

It was written for this exact shape, it is already the basis of x86 DCE's flag reasoning —
and **`x86_peephole` never used it.** Every flag-deadness query in the peephole was still the
block-local scan. That is the whole change: the scale-1 index fold now asks
`X86FlagLiveness::flags_dead_after` instead.

Snapshot validity is the analysis's own documented argument: a consumer may compute it once and
then delete instructions, provided every deletion is justified by "the flags this instruction
writes are dead" — which is exactly this fold's precondition, and cannot move a block's entry
verdict from dead to live. The caller re-analyzes after any block changes regardless.

## Result

`-Ztrust-ir-cg-args=no-x86-sib-crossblock-flags` is the ISOLATING lever
(`no-x86-sib-scale1-fold` cannot isolate it — that disables the whole fold).

| | hot loop insns | span | `imul $8` in `main` |
| --- | ---: | ---: | ---: |
| block-local proof (arm OFF) | 44 | 173 B | 1 |
| cross-block proof (DEFAULT) | **42** | 166 B | **0** |
| LLVM | 26 | 84 B | 0 |

Runtime, `taskset -c 2`, 20 interleaved rounds + 3 warm-up, `min` plus `P(a<b)`, **with a
byte-identical copy of the ON binary in the same batch as the noise control**:

| arm | min ms | ratio | P(arm < OFF) |
| --- | ---: | ---: | ---: |
| block-local (OFF) | 219.38 | 1.0000 | 0.000 |
| cross-block (ON) | 216.29 | **0.9859** | **1.000** |
| cross-block, identical copy | 216.45 | 0.9867 | 0.700 |
| LLVM -O3 | 190.97 | 0.8705 | 1.000 |

**1.43% faster, P = 1.000**, against an in-batch identical-binary floor of **0.08%** — 18x the
floor. b1 versus LLVM improves from **1.1518x to 1.1326x**.

## Attribution is clean, and there is no regression surface

Across the whole 18-program corpus, the arm changes **b1 and nothing else** — byte-identical on
the other 17. So the win is attributable to this fold on this shape, and a default-on change
cannot have regressed a program it does not alter.

| check | result |
| --- | ---: |
| programs whose binary the arm changes | **1 of 18** (b1 only) |
| execution differential vs LLVM, default arm | **18/18 MATCH** |
| `library/core` at O3 | 6 failed roots, 0 typed refusals, 0 harness errors — identical to before |
| `trust-cg-opt` lib suite | 3826 pass, 0 fail |
| `sib_fold_falls_back_to_scale_1_...when_flags_may_be_live` | still passes (its fixture is a single block with no successors, which the analysis reads as live) |

## What is still in b1's loop: 42 vs LLVM's 26

The remaining 16 instructions, from the same diff, named so the next attempt does not have to
re-derive them:

1. **`bt $0x0,%r12 ; jae .+11 ; jmp <odd>` — 3 instructions where LLVM uses 2**
   (`test $0x1,%r8b ; je`). Two defects in one: `bt` on bit 0 is strictly worse than `test`
   (5 bytes vs 4, and a narrower dispatch), and the un-inverted branch pays an extra taken
   `jmp` on roughly half of all iterations of a deliberately unpredictable branch.
2. **`lea 0x1(%rdi),%rax ; mov %rax,%rdi` instead of `inc %rdi`** — 1 instruction, and the
   flags ARE dead here (a `cmp` follows immediately), so this is the same class of proof that
   this commit widened; the lea-write-back collapse is simply not firing on it.
3. **+9 `mov`** (15 vs 6): redundant copies in the xorshift chain — trust-cg re-copies `s` into
   a scratch for each shift step where LLVM threads a fresh register through.
4. **LLVM duplicated the loop body so one arm is branch-free**, entering the even arm directly
   on the back edge. That is loop specialization on the `s & 1` test, and it is the largest
   structural difference remaining.

Items 1 and 2 are small, local, and mechanical. Item 4 is a real optimization trust-cg does not
have.

## Status of the clause

Still NOT met, and now: h1 2.488x, b1 **1.1326x** (was 1.1518x), p4 1.0929x, p2 1.0191x
versus LLVM.
