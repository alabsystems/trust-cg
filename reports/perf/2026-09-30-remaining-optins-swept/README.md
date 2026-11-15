# The last six env-only opt-ins, swept: four inert, two that fire, neither worth flipping

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 60-90 interleaved rounds,
`taskset -c 2`, minimum statistic, the base arm carried twice as its own floor.

Four levers in this backend paid off once made askable through the bridge (the branch-layout
fallthrough rule, the two-address expansion's reachability, the LEA-writeback collapse, and the
vectorizer's reduction unroll factor). This is the rest of that seam, swept to exhaustion so
the question is closed rather than left open.

Tracked channels added for six previously env-only OPT-INS — each had only a `TCG_*` variable,
which `trustc` refuses before the backend loads:

`x86-sroa-multi-block`, `runtime-partial-unroll`, `x86-licm-guarded-hoist`, `x86-bce-carrier`,
`and-cmp-fuse-rr`, `x86-spill-reload-cse-xblock`.

## Four are inert on this corpus

Byte-compared across all 18 programs:

| lever | binaries changed |
| --- | ---: |
| `runtime-partial-unroll` | **0 / 18** |
| `x86-licm-guarded-hoist` | **0 / 18** |
| `and-cmp-fuse-rr` | **0 / 18** |
| `x86-spill-reload-cse-xblock` | **0 / 18** |

The last one matters beyond itself: `h4_vec_dropper`'s gap has been attributed to post-RA
spill reloads, and the cross-block spill/reload CSE solve is exactly the tier that would
address them. **It fires on nothing**, so that attribution cannot be acted on through this
lever, and the recorded explanation for h4 needs re-deriving rather than re-trying.

## Two fire, and neither helps the objective

### `x86-sroa-multi-block` — a trade that ADDS a violation

Fires on `h2_vec_grow` and `h4_vec_dropper`.

| program | off | on | |
| --- | ---: | ---: | --- |
| `h4_vec_dropper` | 1.0357 | **1.0135** | helps a violation, 2.1% |
| `h2_vec_grow` | 0.9995 | **1.0097** | crosses parity: a NEW violation |

Under a max-gap objective this is net negative — the violation count goes 4 to 5. Not flipped.

### `x86-bce-carrier` — does not touch the violation it was aimed at

Fires on `p4_matmul`, `p7_sieve`, `v1_saxpy`, `v2_memfill`, `v3_popcount`. It was tried
because p4 is the second-worst violation and bounds-check elimination is the obvious lever for
a matmul.

| program | off | on | |
| --- | ---: | ---: | --- |
| `p4_matmul` | 1.0800 / 1.0803 | 1.0793 | **inside the 0.0003 floor — no effect** |
| `p7_sieve` | 0.7236 / 0.7205 | **0.7015** | 2.7% faster, already 28% BELOW parity |
| `v1_saxpy`, `v2_memfill`, `v3_popcount` | — | — | noise |

So the only real gain lands on a program that already beats LLVM by a wide margin, and p4 —
the reason for trying it — is unmoved. Not flipped: enabling a previously unmeasured arm of
bounds-check elimination, which is soundness-sensitive, is not justified by a geomean gain that
leaves every violation where it was.

## What this closes

The env-only seam is now exhausted for x86 opt-ins. Every lever in it has been made askable
and measured; four paid, six did not. The remaining four violations — `b1_mispredict` 1.0947,
`p4_matmul` 1.0829, `h4_vec_dropper` 1.0341, `p2_collatz` 1.0103 — have no unmeasured lever
left pointing at them.

Default codegen is unchanged by this work: all 18 programs are byte-identical to the
pre-sweep baseline, since every new channel defaults to the value its env var already implied.

## Follow-up: h2's regression under `x86-sroa-multi-block` is LAYOUT, not a semantic cost

The trade recorded above (h4 1.0357 -> 1.0135, h2 0.9995 -> 1.0097) was treated as a genuine
exchange. Disassembling both says otherwise:

| build | `main` insns | hot loop |
| --- | ---: | --- |
| h2 base | 214 | 10 insns, SIMD (`movdqu` 2, `paddq` 2) |
| h2 + sroa | **167** | **10 insns, IDENTICAL opcode histogram** |
| h4 base | 249 | 10 insns, SIMD |
| h4 + sroa | **170** | changed shape |

**h2's hot loop does not change.** Only `main` shrinks, by 47 instructions, and h2 then runs 1%
slower. That is the layout lottery already recorded at 14.8% on `h3_box_leak` with a
byte-identical hot loop — not a cost the SROA tier imposes on h2's inner loop.

So the honest reading is: h4 gains 2.2% semantically (its loop really does change), while h2
loses 1% to where its unchanged loop happens to land after the function shrinks.

### Why the default still does not flip

It is tempting to discount h2's loss as "only layout" and take h4's gain. Declining to, for two
reasons:

1. **The measurement is the measurement.** A 1% regression that crosses parity is a regression on
   this host and this binary, whatever its mechanism. Discounting a measured loss because its
   cause is unsatisfying is the same move as crediting a measured gain whose cause is unknown, and
   this campaign has refused that repeatedly in the other direction.
2. **It raises the violation count 4 -> 5 without lowering the maximum**, which stays `b1` at
   1.0947. Against a MAX-GAP objective the flip buys nothing at the margin that matters.

Recorded so the next attempt does not re-derive the trade and reach the opposite conclusion by
treating the h2 number as semantic. If a future change makes h2's placement moot — a real loop
aligner acting on it, say — this flip becomes free and should be revisited.
