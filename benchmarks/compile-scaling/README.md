# compile-scaling — catch superlinear compile-time blowups

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

## Why

Every other gate compiles **small** programs. The 18-program `beat-llvm` corpus
averages ~120ms and its functions have tens of blocks, so a defect that is
superlinear in program size is invisible to all of them. Two were found by hand
this session and **neither was caught by any gate**:

| defect | cost |
| --- | --- |
| trust-ir `validate::compute_dominators` is O(N³) in block count | 2.9ms → 5.88s from 418 → 1618 blocks |
| `run_extended_loop_rotation` ran three whole-function scans per candidate loop per driver iteration | 16.7s of a 19.03s compile, against LLVM's 0.48s |

A compiler meant to replace LLVM cannot be validated only on 120ms programs.

## What it measures

Four shapes, each growing **one** dimension so a regression names its own cause:

| shape | grows | stresses |
| --- | --- | --- |
| `blocks` | N sequential calls in one function (calls terminate MIR blocks) | anything per-block or per-dominator |
| `loops` | N independent loops in one function | loop analyses, per-loop drivers |
| `funcs` | N small functions, tiny `main` | per-function and per-module cost |
| `arraysize` | one function, stack array grows to N bytes | data-size-dependent lowering, with block/instruction/loop counts all FIXED |

For each it fits the growth **exponent** `k` from `t ~ n^k`, for LLVM and for
trust-cg. LLVM is the control: if both grow at the same rate, the backend simply
costs a constant factor more — a different and far less serious problem than
growing *faster*.

```
k ~ 1.0  linear      healthy
k ~ 2.0  quadratic   a whole-function scan inside a per-item loop
k ~ 3.0  cubic       dense-set dataflow, e.g. dominator sets
```

Fails when trust-cg's exponent exceeds LLVM's by more than `--max-excess`
(default 0.6).

## Usage

```sh
./run.py                       # all four shapes, median-of-3
./run.py --shapes loops -n 5
./run.py --max-excess 0.3      # tighten the ratchet
```

## Current state

It is a **ratchet**. It was committed failing on two shapes; `loops` has since been
brought under the threshold. The remaining failure is root-caused and attributed
by measurement (`TRUST_CG_DISABLE_PASSES=looplatch` A/B):

| shape | exponent (tcg vs LLVM) | cause |
| --- | --- | --- |
| `blocks` | 1.71 vs 0.28 | trust-ir `compute_dominators`, O(N³). Rotation contributes **nothing** here (6456ms vs 6595ms with it off). Fix written and validated in `patches/trust-ir-compute-dominators-idom.patch`; landing it is gated on a dependency pin bump. |
| `loops` | **~0.93 vs ~0.31 — BORDERLINE** (excess +0.57 to +0.62 across runs, against a 0.6 threshold) | was 1.04 / +0.71. The rotation driver still recomputes `DomTree` + `LoopAnalysis` after **every single** rewrite (441 times on the stress shape) — deliberate, since "stale loop info is deliberately avoided" and batching rewrites per analysis would change which rotations fire. Instead the analyses themselves got cheaper: `dom.rs` now uses the fixed-seed `fast_hash` maps (−18% on `loops_120`). |
| `arraysize` | 0.13 vs 0.02 — OK | lowering has an O(array-size) component (5.2ms at N=256 → 28.3ms at N=65536) that emits CONSTANT-size code, so it is pure compile-time work on an intermediate later collapsed into the array-fill helper. Diluted by fixed compile cost today (ratio still climbs 1.36x → 2.12x across the ladder), so it passes — the shape exists to catch it worsening. |
| `funcs` | 0.37 vs 0.28 | **OK** — per-function scaling is healthy, which is why the whole-corpus ratio is a constant factor rather than a curve. |

`loops` straddles the threshold run to run. That is the gate behaving correctly:
the rotation driver's 441 analysis recomputes really are mildly superlinear, and
the honest reading is "borderline", not "green". Raise `-n` before reading it as a
regression.

Do not "fix" a failure here by relaxing `--max-excess`. Either land the upstream
patch, or change the driver design deliberately and say so.
