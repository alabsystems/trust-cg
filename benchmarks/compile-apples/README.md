# compile-apples — proofs-off compile time vs LLVM

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

## What this measures

`benchmarks/beat-llvm` measures the **production** lane (certs + solver + cache
on) and deliberately refuses to mark a proof-weakened run `headline_eligible`.
That is the right policy for a headline number, but it leaves the lane we
actually optimise against untracked.

This harness measures the narrow, specific target: with verification **off** on
both sides — rustc's LLVM backend at `-C opt-level=N` versus trust-cg at the
same `-C opt-level=N` — trust-cg should be strictly faster to compile on *every*
program. Verification cost gets added back only once that holds.

```sh
./run.py --opt 2 -n 7                    # median-of-7, interleaved A/B
./run.py --opt 3 -n 15 --out-dir /tmp/x
```

## Why it reports CPU time as the primary signal

These compiles are ~120 ms wall and the difference being chased is 5–15 ms —
**the same size as the scheduling noise on a shared box.** Two runs of the
identical binary moved `p1_xorshift` from 1.153x to 0.994x and `m1_call_chain`
from 1.049x to 0.884x. Wall-clock ranking at this scale is not evidence.

Child CPU time (`RUSAGE_CHILDREN`, user+sys) is not perturbed by descheduling,
so it separates *"our compiler did more work"* from *"the machine was busy"*.
The spread tightens from 0.86–1.21 (wall) to 1.11–1.29 (CPU), and the ordering
becomes stable across runs.

Both are reported. They say different things and both are true.

## The finding that motivated the switch

Measured at `-C opt-level=2`, median-of-5, interleaved, on a quiet 20-core box:

| lane | geomean vs LLVM | trust-cg faster on |
| --- | --- | --- |
| wall clock | **1.029x** | 4/18 |
| CPU time | **1.186x** | **0/18** |

rustc's LLVM backend runs at `cpu/wall = 1.00` through this path — exactly
single-threaded. trust-cg runs at 1.13–1.18, i.e. it spends **~19% more total
CPU** and hides part of it behind threads. Near-parity on wall clock is bought
with cores.

That trade is real, not waste. Forcing `TRUST_CG_MAX_PARALLELISM=1`:

| | geomean CPU | geomean wall |
| --- | --- | --- |
| default parallelism | 1.186x | **1.029x** |
| `TRUST_CG_MAX_PARALLELISM=1` | **1.121x** | 1.058x |

Single-threaded wins CPU on 17/18 and loses wall on 11/18. So roughly 6.5 points
of the CPU gap is thread-pool overhead that genuinely buys wall-clock time; the
remaining ~12% is extra work trust-cg does that LLVM does not.

**This matters for the goal.** A single interactive `rustc` invocation cares
about wall clock, where we are close. A real build is `cargo -j N` with every
core already busy — there is no idle core to hide CPU behind, and the CPU number
is what the user pays. Claiming compile-time superiority on wall clock alone,
while losing 18/18 on CPU, would not survive contact with a parallel build.

## Discipline

* **Interleaved A/B** — each repetition compiles LLVM then trust-cg back to
  back, so drift hits both arms equally.
* **Real output files** — never `-o /dev/null`.
* **Median, not mean.**
* **Load gate** — refuses to run above a 1-minute load of 2.0 (`--allow-loaded`
  overrides, and the row is then not evidence).
* **Staleness gate** — refuses to measure a dylib older than any `.rs` in the
  tree, so results are never attributed to the wrong build.
