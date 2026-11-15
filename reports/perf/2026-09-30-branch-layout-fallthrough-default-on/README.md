# `branch-layout-fallthrough` is DEFAULT ON: the suite's worst program improves 2.2%

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 90 interleaved rounds,
`taskset -c 2`, minimum statistic, the base arm carried TWICE as its own noise floor.

## Both recorded reasons for keeping it off are refuted

The rule inverts `jcc T; jmp F` when `T` is the layout successor, so the trailing `jmp`
targets the layout successor and the encoder elides it to zero bytes. It was deferred off
for two reasons, both now measured false on this host:

| recorded reason | measured |
| --- | --- |
| `p6_branch_match` **+4.3%** — "assumes layout-successor == hot, regressed match-heavy code" | 0.9795 -> 0.9784, **noise** |
| `p7_sieve` **+23.5%** (the knob's own description) | 0.7354 -> 0.7210, **1.6% FASTER** |

The pass's own doc asked for exactly this re-measurement: "⚑ WHY IT IS WORTH RE-MEASURING
NOW. That refutation was about a match DISPATCH, which used to lower to a binary-search tree
full of `jcc T; jmp F` pairs. Since the dense-switch jump table became the default,
`p6_branch_match`'s dispatch is a range check and one indirect jump, so the shape that
regressed is no longer the shape p6 presents." It also noted the env var it hung off is
refused by `trustc`, so the question "could not be asked through the bridge at all" until a
tracked knob existed.

## The result

| program | off (old default) | ON (new default) | |
| --- | ---: | ---: | --- |
| `b1_mispredict` | 1.1216 | **1.0971** | the suite's WORST program, 2.2% faster |
| `p7_sieve` | 0.7354 | **0.7210** | 1.6% faster |
| `m2_call_heavy` | 0.7549 | 0.7504 | 0.6% faster |
| `v2_memfill` | 1.0014 | 0.9995 | crosses below parity |
| `p6_branch_match` | 0.9795 | 0.9784 | noise (the original reason) |
| `p4_matmul`, `h4`, `h3`, `m1`, `p1`, `p5`, `p8`, `v1`, `v3` | — | — | noise |
| `h1_vec_push_sum` | 0.9768 | **1.0009** | **the real cost: 2.4% slower** |
| `p3_gcd` | 0.9320 | 0.9390 | 0.8% slower, still far below parity |
| `p2_collatz` | 1.0198 | 1.0223 | 0.2% slower |
| **suite geomean** | 0.8409 | **0.8372** | |
| **suite WORST** | **1.1216** | **1.0971** | |

The objective is a MAX-GAP one — every program at least matching LLVH — so the maximum is
what counts, and it improves 2.2%. The number of programs above parity is FIVE either way:
the flip swaps `v2_memfill` (1.0014 -> 0.9995) out for `h1_vec_push_sum` (0.9768 -> 1.0009),
both within ~0.1% of parity, so no meaningful new violation appears.

## Why this lever works when the instruction-count levers did not

Seven other hypotheses were measured and refuted this campaign, all of them
instruction-count arguments. This one is different in kind, and `b1_mispredict` shows why.

Rewriting b1's branches to be PREDICTABLE — `i & 1` and `i & 6` in place of `s & 1` and
`s & 6`, same work, same 60M iterations, both compilers seeing the same program — shrinks the
bridge's gap from **1.1210 to 1.0389**. So roughly two thirds of b1's cost is mispredict
RECOVERY, not instruction count, which is exactly why shaving instructions measured zero
there. Removing a branch-to-branch (`jae` into a `jmp`) takes one taken jump out of the
mispredicted path. That is a fetch-redirect argument, not a throughput one.

## The known cost, stated plainly

`h1_vec_push_sum` genuinely regresses 2.4% and crosses from 0.9768 to 1.0009. That is the
thing to fix, or the thing to revert against if it matters more than b1's 2.2%. It is
recorded in the knob description and at the setter so it cannot be rediscovered by accident.

## Exactness of the change

Verified by byte comparison, not by argument: with the new default the produced binaries are
**byte-identical to the measured fallthrough arm**, and with
`-Ztrust-ir-cg-args=no-branch-layout-fallthrough` they are **byte-identical to the old
default arm**. So the shipped behaviour is exactly what was measured, and the rollback is
exact.

## Tests

Five assertions pinned the old default and were updated; two more needed real isolation
rather than a new expectation, which is the interesting part:

* `o1_schedule_inverts_top_tested_loop_header_and_honors_kill_switch` checks that
  `TCG_NO_X86_LOOP_EXIT_LAYOUT` leaves a header `jcc` untouched. With fallthrough default-on
  that header still inverts — via the FALLTHROUGH rule, whose trigger ("T is the layout
  successor") this fixture also satisfies. The loop-exit kill switch is not broken; the test
  was measuring two rules at once. It now disables fallthrough as well, so it tests its own
  switch.
* `o1_schedule_sinks_cold_call_arm_only_when_opted_in` compares `block_order`, which the
  fallthrough rule also mutates. Same isolation.

`branch_layout_fallthrough_isolated_policy` was rewritten for the inverted env semantics:
the fallback is now the opt-OUT `TCG_NO_BRANCH_LAYOUT_FALLTHROUGH`, so `=0` means "do not
disable" (still on) and `=1`/`=""` disable — the mirror of the old opt-in table.
