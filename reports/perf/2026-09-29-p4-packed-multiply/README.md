# p4_matmul: the vectorized loop goes to SCALAR for the multiply, and the comment saying that is right is wrong (2026-09-29)

p4_matmul is 1.0920x LLVM and has been "already vectorized, 16 `paddq`" in every account of it.
Diffing its innermost vector loop against LLVM's for the first time shows what that vectorization
actually does:

| | insns | span | instruction mix |
| --- | ---: | ---: | --- |
| trust-cg | **45** | 189 B | `mov` 8, **`imul` 8**, **`movq` 8**, `movdqu` 8, **`punpcklqdq` 4**, `paddq` 4 |
| LLVM | 141 | 730 B | **`pmuludq` 36**, `paddq` 36, `movdqa` 26, `psrlq` 13, `psllq` 12 |

**Twenty of trust-cg's 45 instructions are a round trip to scalar**: eight 64-bit `imul`s in GPRs,
eight `movq` transfers between GPR and XMM, and four `punpcklqdq` to re-pack the products. LLVM
never leaves SIMD — it does the 64x64 lo-product with the classic
`PMULUDQ`/`PSLLQ`/`PSRLQ`/`PADDQ` decomposition.

## This is deliberate, and the reason given for it is false

The route is selected by a `scalar_mul` flag whose comment reads:

> This is LLVM's own SSE2 strategy for 64-bit lane products: two pipelined scalar IMULs beat the
> 3xPMULUDQ + 2-shift + 2-add lo64 compose. `TCG_NO_X86_SAXPYQ_SCALAR_MUL` restores the
> PMULUDQ-compose path (broadcast preheader + packed multiply) for a one-dylib A/B.

Both halves are false on the only corpus program where this tier fires:

* **LLVM does not use scalar IMULs here.** Its p4 inner loop is the compose, above — 36 `PMULUDQ`,
  13 `PSRLQ`, 12 `PSLLQ`, and not one `imul`.
* **The scalar route is slower.** Measured: `taskset -c 2`, 40 interleaved rounds, `min`, with a
  byte-identical control:

| arm | min ms | vs LLVM | vs scalar |
| --- | ---: | ---: | ---: |
| LLVM -O3 | 58.39 | 1.0000 | 0.9158 |
| scalar IMUL route (default) | 63.76 | 1.0920 | 1.0000 |
| **packed PMULUDQ compose** | **63.20** | **1.0824** | **0.9912** |
| packed, identical copy | 63.24 | 1.0830 | 0.9918 |

**The packed compose is 0.88% faster**, against a 0.06% in-batch floor — taking p4 from 1.0920x to
1.0824x LLVM. It changes p4 and nothing else in the corpus, and the differential is 18/18 MATCH.

## Why the claim was never checked

The A/B its own comment invites ("for a one-dylib A/B") was **unreachable**. Its only lever was the
environment variable `TCG_NO_X86_SAXPYQ_SCALAR_MUL`, and `trustc` refuses every `TCG_*` variable
before the backend loads. So the route shipped default-on with a claim that could not be tested
through the compiler it ships in.

This is the **sixth** lever or instrument found this round whose only channel was an env var the
compiler refuses — after the BCE branch-form trace, the BCE carrier trace, the SIB-fold log, and
the peephole/vectorizer dump positions. `-Ztrust-ir-cg-args=no-x86-saxpyq-scalar-mul` is now the
tracked channel.

## What shipped

**The default is now the packed compose**, plus the tracked knob and the corrected comment.

The eight `vectorizes_saxpyq_*` tests that pinned the scalar route's composite-proven sequence
instruction by instruction (the `0bfe4e1e` IMUL/IMUL/MOVQ/MOVQ/PUNPCKLQDQ shape) were not rewritten
— they now **select** that route explicitly with `with_saxpyq_scalar_mul(true)`, so they keep
testing exactly what they were written to test. A new
`saxpyq_default_route_is_the_packed_pmuludq_compose` covers the default, and it compares the two
arms rather than asserting absolutes: the packed route still uses ONE `MovqToXmm` + ONE
`Punpcklqdq` in the preheader to broadcast `[K;2]`, which is the route's own broadcast rather than a
per-group lane pack, and the fixture's address idiom contributes `ImulRR`s of its own. Both
sequences are per-instruction certified, so the flip changes which certified emission is default,
not whether one is covered.

Re-measured on the DEFAULT build after the flip (40 interleaved rounds, identical control 1.0006):

| | min ms | vs LLVM |
| --- | ---: | ---: |
| LLVM -O3 | 58.42 | 1.0000 |
| old default (scalar) | 63.83 | 1.0926 |
| **new default (packed)** | **63.24** | **1.0825** |

Verified after the flip: the arm changes **p4 and nothing else** in the corpus; differential
**18/18 MATCH**; Trust checksum `267826962111695130` with verification ON; Clean **5/5**; TY
**9/9**; `library/core` at O3 unchanged (6 pre-existing failed roots, 0 typed refusals, 0 harness
errors); `trust-cg-opt` 3846 pass; `trust-cg-codegen` 4418 pass with the 2 known pre-existing
failures; fmt clean.

## What p4's remaining 8.2% is

Not the multiply. trust-cg runs 45 instructions where LLVM runs 141 and is only 9% slower, so
per-instruction cost, not instruction count, is the difference — consistent with the GPR↔XMM
transfer latency on the critical path. gcc, meanwhile, is **1.133x faster than LLVM** on p4, so
most of the remaining gap is something neither LLVM nor trust-cg does; trust-cg is 1.026x clang.

## Status of the clause

Still not met — six programs remain above LLVM — but p4 improves: **1.0926x → 1.0825x**.
