# The x86 branch-layout family, measured for the first time: worth 3.9% on the worst program, and three of its five rules fire on nothing

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 25 interleaved rounds per program,
`taskset -c 2`, minimum statistic, base arm carried twice as its own floor.

## Why this was unmeasurable

The OPT-8 branch-layout pass has five rules, and FOUR of its control channels were
environment variables, which `trustc` refuses before the backend loads. So neither the pass
nor any individual rule could be A/B'd through the bridge:

| rule / gate | default | channel before | now |
| --- | --- | --- | --- |
| whole pass | ON | `TCG_NO_BRANCH_LAYOUT` only | `no-x86-branch-layout` |
| `latch_rule` | ON | hardcoded `true` | unchanged |
| `fallthrough_rule` | ON (flipped 2026-09-30) | env only until today | `no-branch-layout-fallthrough` |
| `cold_trap_rule` | ON | `TCG_NO_X86_COLD_TRAP_LAYOUT` only | `no-x86-cold-trap-layout` |
| `loop_exit_rule` | ON | `TCG_NO_X86_LOOP_EXIT_LAYOUT` only | `no-x86-loop-exit-layout` |
| `cold_arm_sink_rule` | OFF (awaiting a soak) | `TCG_X86_COLD_ARM_SINK` only | `x86-cold-arm-sink` |

That brings this campaign's count of instruments found env-only to **fifteen**. The
cold-arm-sink case is the sharpest: its own doc says "OPT-IN for its soak … After the paired
A/B the intended flip shape is a `TCG_NO_X86_COLD_ARM_SINK` kill switch with the rule
default-ON", and the A/B it was waiting for could not be run at all.

## Three of the five rules fire on NOTHING

Checked by byte comparison across all 18 programs:

| lever | binaries changed |
| --- | ---: |
| `no-x86-branch-layout` (whole pass) | **18 / 18** |
| `no-x86-cold-trap-layout` | **0 / 18** |
| `no-x86-loop-exit-layout` | **0 / 18** |
| `x86-cold-arm-sink` | **0 / 18** |

So on this corpus the pass's observable effect is the `latch` and `fallthrough` rules alone.
The cold-trap and loop-exit inversions, both default-ON and both described as
profile-free-correct, are inert here — and **the cold-arm-sink soak cannot be run on this
corpus at all**, because the rule never fires. That is the answer to the question its doc
asked, even though it is not the answer the doc expected.

## What the pass is worth

| program | pass ON | pass OFF | pass contributes |
| --- | ---: | ---: | ---: |
| `p7_sieve` | 0.7028 | 0.7456 | **6.1%** |
| `h3_box_leak` | 0.9953 | 1.0552 | **6.0%** |
| `b1_mispredict` | 1.0962 | 1.1391 | **3.9%** |
| `h2_vec_grow` | 0.9987 | 1.0084 | 1.0% |
| `p4_matmul` | 1.0831 | 1.0933 | 0.9% |
| `m2_call_heavy` | 0.7509 | 0.7543 | 0.5% |
| `p8_closure_nest` | 1.0001 | 1.0035 | 0.3% |
| `h1_vec_push_sum` | 1.0033 | 0.9886 | **-1.5%** (the pass COSTS h1) |
| `p2_collatz` | 1.0231 | 1.0109 | **-1.2%** (the pass COSTS p2) |
| others | — | — | inside noise |
| **suite geomean** | **0.8325** | 0.8397 | 0.9% |
| **suite WORST** | **1.0962** | 1.1391 | **3.9%** |

The pass is a clear net win and the single largest layout lever measured on this host. Its
two costs, `h1_vec_push_sum` and `p2_collatz`, are the same two programs the `fallthrough`
rule's flip moved the wrong way — consistent, and it localises both regressions to that one
rule rather than to the pass as a whole.

No default changes follow from this: the pass is already on, and the three inert rules cannot
be evaluated on this corpus. What follows is that the levers exist now, with numbers attached.

## Method note

This is the fourth time this campaign that a pass was found to be ON by default and
unmeasurable, or OFF by default with a refutation that no longer reproduced. The pattern is
worth stating as a rule: **an env-gated pass inside the bridge is an unfalsifiable claim.**
Before trusting any recorded per-pass measurement in this backend, check whether its channel
is a `TCG_*` variable — if it is, the measurement was taken somewhere other than through the
bridge, and on this host it may not reproduce.
