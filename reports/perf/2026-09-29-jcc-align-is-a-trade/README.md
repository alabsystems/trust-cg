# The x86 JCC-boundary padding is a per-program TRADE on AMD, not a pessimization

Host AMD Ryzen 9 9900X3D (family 26), Linux, one dylib, `taskset -c 2`,
interleaved rounds, minimum statistic, and **both arms carried twice as
byte-identical copies** so every delta is read against its own noise floor.
Arms differ only by the tracked knob `-Ztrust-ir-cg-args=no-x86-jcc-align`;
`cmp` confirmed the knob changes the binary for all six programs.

## What prompted it, and the refutation that came first

`p4_matmul`'s inner loop carries **19 bytes of alignment NOPs inside a 117-byte
hot loop** (a 9-byte `nopw` and a 3-byte `nopl` aligning the first `cmp` to
`0x20fe0`, a 3-byte at `0x20ffd`, a 4-byte at `0x2103c`), each one placing a `jcc`
inside a 32-byte block. LLVM's loop has none — LLVM does not apply this workaround
by default. The obvious inference is that the NOPs cost p4 real time.

**They cost it nothing.** 60 interleaved rounds, base = LLVM -O3:

| arm | min ms | vs LLVM |
| --- | ---: | ---: |
| LLVM -O3 | 58.186 | 1.0000 |
| padding ON (default) | 63.002 | 1.0828 |
| padding ON, byte-identical dup | 62.956 | 1.0820 |
| padding OFF | 62.920 | 1.0814 |

ON-vs-dup is 0.0008, and OFF sits inside that. The AMD front end absorbs the NOPs;
p4's 8.2% is elsewhere. This is the third time this campaign that a visible
instruction-count difference in a hot loop turned out to be free.

## The measured trade

| program | LLVM | padding ON | ON dup | padding OFF | verdict |
| --- | ---: | ---: | ---: | ---: | --- |
| `p2_collatz` | 1.0000 | 1.0185 | 1.0196 | **1.0013** | OFF wins 1.8% — its WHOLE gap |
| `b1_mispredict` | 1.0000 | 1.1197 | 1.1199 | **1.1309** | OFF LOSES 1.1% |
| `p4_matmul` | 1.0000 | 1.0828 | 1.0820 | 1.0814 | inside noise |
| `h4_vec_dropper` | 1.0000 | 1.0408 | 1.0335 | 1.0311 | inside noise |
| `p1_xorshift` | 1.0000 | 1.0000 | 0.9997 | 0.9993 | inside noise |
| `p7_sieve` | 1.0000 | 0.7352 | 0.7302 | 0.7268 | inside noise |

So the padding is **not** an Intel-only pessimization that can simply be dropped.
On a CPU with no JCC erratum the knob still buys `b1` 1.1% and costs `p2` 1.8%, so a
blanket default either way trades one program for another.

**⚠ Attribution correction.** An earlier version of this paragraph said b1's 1.1% "can
only be incidental branch alignment". That is not supported, and the knob's own doc in
`pipeline.rs` says why: `no-x86-jcc-align` disables **three** coupled things — the
per-branch NOP padding, the per-function 32-byte padding in `combined_code`, and the
`__text` section alignment of 2^5 — and they must move together, because the erratum is a
property of the ABSOLUTE address while the pass only sees a function-relative offset.
Its doc states the consequence directly: "An A/B therefore measures the combined
alignment regime, not the cost of each padding byte alone."

So every number in this report is the COMBINED regime. Which of the three mechanisms
moves b1, and which moves p2, is NOT determined by this measurement. Separating them
needs three independent levers, which do not exist today — and the doc warns that
splitting them is exactly what made the pass half-effective once before (function starts
land at `0 mod 32` and `16 mod 32` in nearly equal numbers, so padding alone aligned the
wrong grid for half of them).

## The cost this puts on today's AMD target-cpu allowlist

`x86_cpu_family_lacks_jcc_erratum` (landed earlier today) disables the padding
whenever `-C target-cpu` names an AMD family. Verified firing: at
`-C target-cpu=znver4`, the default build and the `no-x86-jcc-align` build are
byte-identical for both programs. Measured consequence, base = LLVM -O3 at znver4:

| program | LLVM znver4 | bridge generic | bridge znver4 | znver4 dup |
| --- | ---: | ---: | ---: | ---: |
| `p2_collatz` | 1.0000 | 1.0203 | **1.0012** | 1.0011 |
| `b1_mispredict` | 1.0000 | 1.1553 | **1.1691** | 1.1675 |

The allowlist buys `p2` 1.9% and reaches parity; it costs `b1` 1.2%, and `b1` is
the worst program in the suite. Under a max-gap objective — every program at least
matching LLVM — that is the wrong direction for `b1`, even though it is
semantically right not to apply an Intel erratum workaround on AMD.

**Not reverted, and why.** The allowlist only fires under an explicit AMD
`-C target-cpu`; the generic default is untouched, so nothing regresses for a
default build. The finding is that ONE knob conflates the Skylake-family erratum
workaround (correctly Intel-only) with a general ALIGNMENT regime that is arch-neutral
and worth 1.1-1.2% on `b1` here. The real fix is to separate them — skip the
erratum-specific padding on AMD while keeping whichever alignment actually pays — not to
re-apply an Intel workaround to get b1's alignment back.

That separation is unimplemented, and note it is a prerequisite for even ASKING the
question: until the three mechanisms have independent levers, no measurement can say
whether b1 wants the branch NOPs, the function alignment, or the section alignment.

## Reproduce

```sh
DRV=trust/build/host/stage2/bin/trustc
DYLIB=$PWD/target-bridge/release/librustc_codegen_trust_cg.so
C="-Ztrust-verify=off --edition=2021 --crate-type bin -Cpanic=abort -Copt-level=3"
for p in p2_collatz b1_mispredict p4_matmul; do
  $DRV -Zcodegen-backend=$DYLIB -Ztrust-ir-cg-args=no-proof-certs $C \
       -o /tmp/$p.on benchmarks/beat-llvm/progs/$p.rs
  $DRV -Zcodegen-backend=$DYLIB -Ztrust-ir-cg-args=no-proof-certs \
       -Ztrust-ir-cg-args=no-x86-jcc-align $C \
       -o /tmp/$p.off benchmarks/beat-llvm/progs/$p.rs
  $DRV $C -o /tmp/$p.llvm benchmarks/beat-llvm/progs/$p.rs
  cp /tmp/$p.on /tmp/$p.on2   # the noise floor
done
```

## SETTLED 2026-09-30: it IS the per-branch NOPs, and there is no policy that wins

The attribution correction above says the knob toggles three mechanisms and that no
measurement could say which one moves which program. A fourth lever now separates them:
`-Ztrust-ir-cg-args=no-x86-jcc-branch-pad` suppresses ONLY the per-branch NOP padding,
leaving the per-function 32-byte padding and the `__text` section alignment in place
(verified: `.text` alignment stays 64 in every arm).

### The mechanism, finally attributed

| program | default | NOPs off, ALIGNMENT KEPT | all three off |
| --- | ---: | ---: | ---: |
| `p2_collatz` | 1.0188 | **1.0005** | 1.0008 |
| `b1_mispredict` | 1.1210 | **1.1328** | 1.1320 |

Removing only the NOPs reproduces the full effect of removing all three, in BOTH
directions. So p2's entire 1.9% gap and b1's entire 1.2% benefit are the **per-branch NOP
padding**; the function and section alignment contribute nothing measurable to either. The
withdrawn claim is now supported — by a lever that isolates it, rather than by assertion.

### And the hoped-for free win does not exist

Because both effects are the same mechanism, p2 and b1 are in direct tension: any global
setting trades one for the other. The obvious escape was a per-loop policy keyed on loop
size (p2's hot loops are 11-21 instructions, b1's is 41). **Measured across ten programs,
that is refuted** — 30 interleaved rounds each, base carried twice as the floor:

| verdict | programs |
| --- | --- |
| NOPs off WINS | `p2_collatz` 0.9823, `m2_call_heavy` 0.9950 |
| NOPs off LOSES | `b1_mispredict` 1.0103, `v1_saxpy` 1.0098, `p8_closure_nest` 1.0043 |
| inside noise | `p1_xorshift`, `p3_gcd`, `p5_struct_acc`, `m1_call_chain`, `p4_matmul` |

The sign does not track loop size: `v1_saxpy`'s hot loop is NINE instructions and it LOSES,
`p2_collatz`'s is ELEVEN and it WINS. Nor does it track NOPs-in-the-hot-loop — p2's
innermost loop contains ZERO nop instructions, so its gap is not even a NOP it executes.
What is left is where the padding happens to land relative to 32- and 64-byte boundaries,
which is the same unpredictable layout sensitivity already recorded at 14.8% on `h3_box_leak`
with a byte-identical hot loop.

**So the default stays ON.** Flipping it would trade p2 (-1.8%) and m2 (-0.5%) for b1
(+1.0%), v1 (+1.0%) and p8 (+0.4%) — and b1 is already the suite's worst program, so under a
max-gap objective that is the wrong direction. A size-keyed policy would be fitting a
threshold to two points of a ten-point sample whose sign is uncorrelated with size.

The knob ships as a measurement instrument with this data attached, not as a tuning
recommendation. **p2's 1.9% is not cheaply recoverable**, which confirms the earlier
"not the easy one" note rather than overturning it.
