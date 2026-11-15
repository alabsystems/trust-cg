# h1's residual scalar gap: four hypotheses tested, four refuted, one win (2026-09-29)

`h1_vec_push_sum`'s 2.638x vs LLVM decomposes into **1.979x vectorization** and
**1.334x residual scalar codegen quality**
(`../2026-09-29-x86-sib-scale1-fold/README.md`). This file is the record of what the
1.334x is NOT, because every plausible cause tested here made things worse or nothing,
and a list of refuted causes is what stops the next attempt repeating them.

All measurements: one bridge dylib per pair, the change's own tracked lever, a
10x-scaled h1 (~230ms, clearing the harness's 50ms resolvability floor), one pinned
core, 13-17 INTERLEAVED samples, plus a rank statistic.

| hypothesis | lever | result | verdict |
| --- | --- | ---: | --- |
| the un-eliminated `Vec` bounds check | `no-x86-bce-reload` / `no-x86-bce` | byte-identical output | **refuted** — the arm does not fire; the check is still there and is not the cost |
| the serial `acc += v[k]` dependency chain | 4 accumulators in the source | **1.121x slower** (254.06 vs 226.68ms) | **refuted** |
| the three loop-invariant `Vec`-header reloads | `licm-pointer-loads` | **1.49x slower** (338.45 vs 226.85ms), P(ON<OFF)=0.000 | **refuted** |
| Intel JCC-erratum padding applied on an AMD host | `no-x86-jcc-align` | **1.03x slower** min, 1.05x median, P(OFF<ON)=0.133 | **refuted** |
| an `imul` stride in the address chain | `no-x86-sib-scale1-fold` | **0.892x FASTER**, P(ON<OFF)=1.000 | **the one win** |

## The two that are most worth not repeating

**Hoisting the invariant reloads makes it 49% slower.** h1's inner loop reloads `len`
twice and `ptr` once per iteration, all loop-invariant, and one of them feeds the
element load's address. Hoisting them yields a **9-instruction loop with one memory
access** instead of a 12-instruction loop with four — and it runs 1.49x slower, with
every sample in the slow arm worse than every sample in the fast arm. The same arm
measured 1.46x slower on a different backend weeks earlier, so this reproduces across
two independent builds. Instruction count and load count are simply not predictive
here.

One objective difference was found, and is reported as an observation rather than a
cause, because attributing it needs counters this host cannot provide (see below): the
FAST loop fits in ONE 64-byte fetch line with no padding inside it (47-byte span, head
at 13 mod 64); the SLOW one straddles TWO lines and three 32-byte blocks and contains a
**9-byte NOP inside the loop body**, executed every iteration.

**Padding for the Intel JCC erratum is NOT free to remove, even on AMD.** The pass
(`x86_jcc_erratum_pad`) is on by default and has **no vendor or target-CPU gate**, and
the erratum it mitigates is a Skylake-family Intel defect that does not exist on this
host's Zen 5. That looks like a clear win to switch off. It is not: disabling it is
1.03-1.05x SLOWER. The reason is in the pass's own documentation — the same flag also
owns per-function 32-byte padding and the `__text` section alignment, "all three must
move together or none should", and it is the alignment that is earning its keep here.
Binary size barely moves either (3586128 -> 3586064 bytes) and the whole-binary NOP
count changes by two (796 -> 794).

So the actionable note for anyone who spots the missing vendor gate: **do not
vendor-gate this flag as it stands.** Splitting the erratum padding from the
function/section alignment would be needed first, and only then is the AMD question
answerable.

## What cannot be measured here

Which microarchitectural resource actually bounds the loop. Hardware counters are
unavailable: `/proc/sys/kernel/perf_event_paranoid` is 4, and raising it is a
system-wide security setting, not a benchmark knob. Every statement above is a wall-
clock A/B with a rank statistic; none of it is an attribution to a port, a fetch window
or a cache level, and the fetch-line observation above is deliberately not dressed up
as one.
