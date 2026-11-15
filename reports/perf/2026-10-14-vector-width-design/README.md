# Leveraging the hardware: what wider vectors would actually buy, measured per ISA level

Date: 2026-10-14 · Host AMD Ryzen 9 9900X3D (**Zen 5, full AVX-512**: `/proc/cpuinfo` lists
avx512f/dq/bw/vl + avx512_vpopcntdq) · gcc 15.2.0, min of 7 runs, ms

## The premise was wrong, so it was measured instead

The brief was "the gap is AVX2". It is not. gcc on the three vector kernels at each ISA
level, against trust-cg:

| program | `-march=x86-64` | `-v2` (SSE4.2) | `-v3` (AVX2) | `-v4` (AVX-512) | `native` | **trust-cg** |
|---|---:|---:|---:|---:|---:|---:|
| v1_saxpy | 113.0 | 39.8 | 20.8 | 11.5 | 11.5 | **48.8** |
| p4_matmul | 50.7 | 50.5 | 28.3 | 12.6 | 12.4 | **61.1** |
| v3_popcount | 220.1 | 47.1 | 46.5 | 46.6 | 8.7 | **12.7** |

Emitted asm was read for each row, so the decomposition is mechanism, not inference:

* **v1_saxpy** — v2→v3 = 1.91x, v3→v4 = 1.81x. Pure width (`vpmulld`/`vpaddd`, zmm at native).
* **p4_matmul** — gcc **does not vectorize at all at `-v2`** (scalar `imulq`). v2→v3 = 1.79x
  via 36 `vpmuludq` (the 3-multiply i64 emulation at 4 lanes). v3→v4 = 2.25x via
  **`vpmullq`, which is AVX-512DQ and has no AVX2 form at all**.
* **v3_popcount** — AVX2 and AVX-512F/BW/DQ/VL buy **1.01x, i.e. nothing**. The entire 5.35x
  of native over `-v4` is `vpopcntd` (AVX512_VPOPCNTDQ, not in x86-64-v4). And **trust-cg's
  12.7ms already beats gcc 3.7x at every level up to `-v4`** (46.5ms), because its
  PSADBW/SWAR tier is better than gcc's byte-widening approach.

**Consequences.** AVX2 alone buys ~1.8-1.9x on two of three vector kernels and **zero** on
the third. The two largest single named capabilities are both AVX-512 (`vpmullq`,
`vpopcntd`), and both are usable at 128/256-bit under AVX512VL — which reorders the phases.

**The cheap-win ceiling, also measured.** At the ISA trust-cg actually targets (`-v2`): gcc
39.8 / 50.5 / 47.1 against trust-cg at 48.8 / 61.1 / 12.7 — **1.23x and 1.21x behind on two,
3.7x ahead on the third. Total available without new encodings is ~1.2x on 2 of 18
programs.**

## What the build-out costs, checked against the tree

* **No AVX opcodes exist**: `grep -cE 'Vpaddd|Vmovdqu|Ymm|Vex|Avx'` over
  `crates/trust-cg-ir/src/x86_64_ops.rs` returns **0**.
* **No register class above 128 bits**: the widest is `Fpr128`; the physical set is XMM0-15,
  and two are reserved as FPR spill scratch.
* So the work is: a new register class and physical registers; **VEX (and for 512-bit, EVEX)
  prefix encoding**; the opcode set; register-allocator support; the vectorizer at
  `LANES = 8` with matching plan appliers; and target-feature gating, since AVX2 is not in
  the target's feature set.

## The constraint that actually sets the scale — and it is a decision, not an encoder

`crates/trust-cg-verify/tests/coverage_gate_tests.rs` pins x86-64 at **206/206 = 100%** with
`expected_red` an **explicitly empty set**, commented *"An empty set is the strongest form of
this assertion"*. Every emittable x86 opcode today has a non-degenerate accepted obligation.

**~25-40 AVX opcodes means that many new proof rows, each needing a credit or a named RED
deferral.** If they are not all credited, the project trades its strongest x86 claim — zero
evidence debt — for throughput. That is an owner decision and it should be taken *before* any
encoder work, not discovered after.

## Ordered plan

**Phase 0 — re-baseline. Mandatory, 0.5-1 day.** Every trust-cg number on record is
headline-ineligible (dirty tree and/or the `no-proof-certs` diagnostic lane). Nothing below
should be scoped against them.

**Phase A — cheap wins, no new encodings. 1-2 weeks, ceiling measured at ~1.2x on 2 of 18.**
 * A1: m128 operand folding — the only item with a mechanism visible in gcc's own output.
 * A2: unreserve XMM14/15 (reserved as FPR spill scratch and unused in the default build) —
   bounded, and genuinely unmeasured.

**Phase B — AVX2.** New register class + VEX encoding + opcodes + regalloc + `LANES = 8`.
Gated behind the coverage-gate decision above.

**Phase C — AVX-512, reordered by the measurements.** `vpmullq` (AVX-512DQ) and `vpopcntd`
(AVX512_VPOPCNTDQ) are the two biggest named wins and **both work at 128/256-bit under
AVX512VL**, so they do not require a 512-bit register class first. On this corpus that makes
targeted AVX512VL instructions a better early move than full zmm width.

## Honest framing

v3_popcount is the one program where trust-cg already beats gcc at every level below native,
and it is also the program where AVX2 buys nothing. The `-march=native` deficit is
concentrated in exactly two kernels and is an ISA gap, not a code-quality gap — but closing
it is a new encoding scheme and a new register class in a backend where every encoding
carries a proof obligation, and the proof-row decision dominates the engineering.
