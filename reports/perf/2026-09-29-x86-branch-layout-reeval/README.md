# Re-evaluating `branch-layout-fallthrough`: its documented reason is obsolete, and the real one is 10x bigger (2026-09-29)

## Why re-measure a lever I had already rejected

`b1_mispredict`'s hot loop contains

```
20989:  bt     $0x0,%r12
2098e:  jae    20999        <- 20999 is the instruction AFTER the jmp
20994:  jmp    209bc
20999:  mov    %r12,%rcx    <- the jae target
```

Both paths take a branch. The single-branch form `jb 209bc`, falling through to 20999, is one
instruction shorter and leaves the fall-through path with ZERO taken branches. That is exactly
what `-Ztrust-ir-cg-args=branch-layout-fallthrough` does, and it is DEFAULT OFF because:

> DEFAULT OFF: it assumes layout-successor == hot, which regressed p6_branch_match by 4.3%
> **back when a match dispatch was a compare tree**

That premise no longer holds. Earlier this session p6's dense-switch **jump table** became
default-on, which is what closed p6's gap. The compare tree the regression was measured against
does not exist any more, so the lever's stated reason had to be re-tested.

## The lever works, everywhere

It removes `jmp`s from all 18 programs, with the execution differential intact:

| program | `jmp` in main, off → on | | program | `jmp` in main, off → on |
| --- | ---: | --- | --- | ---: |
| p4_matmul | 9 → 1 | | h4_vec_dropper | 6 → 1 |
| p6_branch_match | 10 → 9 | | v1_saxpy | 5 → 0 |
| h2_vec_grow | 7 → 3 | | h1/h3 | 4 → 1 |
| p7_sieve | 7 → 2 | | v3_popcount | 4 → 0 |
| p2/p3 | 4 → 2 | | b1_mispredict | 3 → 1 |

18/18 MATCH against LLVM in the ON arm. So this is a correctness-neutral, strictly
instruction-reducing transform — and it is still the wrong thing to enable globally.

## Measured: `taskset -c 2`, interleaved, with a byte-identical control IN EVERY BATCH

| program | off (ms) | on (ms) | ratio | control | P(on<off) | verdict |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| p4_matmul | 63.78 | 63.15 | **0.9901** | 0.9990 | **1.000** | **FASTER 0.99%** |
| p3_gcd | 260.10 | 258.51 | **0.9939** | 0.9993 | 0.850 | **FASTER 0.61%** |
| p6_branch_match | 1548.50 | 1546.26 | 0.9986 | 1.0001 | 0.917 | neutral |
| p1_xorshift | 448.36 | 448.40 | 1.0001 | 1.0000 | 0.500 | neutral |
| p5_struct_acc | 448.42 | 448.45 | 1.0001 | 1.0000 | 0.583 | neutral |
| m1_call_chain | 67.54 | 67.58 | 1.0006 | 1.0001 | 0.417 | neutral |
| p2_collatz | 167.40 | 168.02 | 1.0037 | 0.9996 | 0.000 | slower 0.37% |
| b1_mispredict | 215.56 | 216.52 | 1.0044 | 1.0002 | 0.250 | slower 0.44% |
| p8_closure_nest | 149.81 | 150.47 | 1.0044 | 1.0000 | 0.000 | slower 0.44% |
| **p7_sieve** | **22.50** | **27.79** | **1.2346** | 0.9945 | **0.000** | **SLOWER 23.5%** |

(Programs under the harness's 50 ms resolvability floor — h1, h2, h3, h4, m2, v1, v2, v3 — are
not read as results. p7 is listed because a 23.5% difference is resolvable at any duration: it
was re-measured on its own at n=40, where the identical control sits at 0.9945 and the effect is
**42x** that floor.)

## Two findings, and they point opposite ways

1. **The documented reason is OBSOLETE.** p6_branch_match now measures **neutral** (0.9986,
   P=0.917). Making the dense switch a jump table removed the compare tree whose layout the
   lever mishandled. Anyone reading the old knob text would conclude the only obstacle was a
   4.3% p6 regression that no longer exists, and flip it.
2. **The real reason is 10x bigger and was never recorded: p7_sieve regresses 23.5%** — while
   its hot loop gets *smaller*, 126 → 112 instructions and 627 → 527 bytes, with `jmp` 6 → 2.
   One visible correlate: the OFF arm's loop carries **13 `nopw`** of JCC-erratum padding and
   the ON arm only 3, so changing the branch addresses dissolved most of the alignment padding
   that arm had been getting. I am not claiming that IS the mechanism — hardware counters are
   unavailable here (`perf_event_paranoid=4`) — only that the loop shrank and got much slower,
   which is the same non-monotonicity this round has now hit four times.

## What follows

The lever stays DEFAULT OFF, and its description is corrected in `knobs.rs` to say so for the
measured reason instead of the stale one.

But **p4 is a target program and this is a real 0.99% on it at P=1.000**, with p3 another 0.61%.
A global flip cannot have them, because it costs p7 23.5%. Capturing them needs a **per-loop**
policy — invert only where the fall-through path is the one the loop actually takes — rather
than the whole-function switch measured here. That is the actionable item this leaves behind.

## Status of the clause

Unchanged by this report: h1 2.488x, b1 1.1326x, p4 1.0929x, p2 1.0191x versus LLVM. What it
adds is a corrected knob contract, a 23.5% regression documented before anyone could ship it,
and a located 0.99% on p4 waiting on a narrower policy.
