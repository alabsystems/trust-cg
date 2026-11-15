# Authoritative per-program parity, end of 2026-09-29 — and why the harness's `worst 1.222x` is not a regression

Host AMD Ryzen 9 9900X3D, x86-64 Linux. Default build, `-Copt-level=3`, one dylib.
Method: `taskset -c 2`, INTERLEAVED rounds, MINIMUM statistic, and the bridge arm carried
TWICE as byte-identical copies so every row is read against its own noise floor.

## The table

| program | vs LLVM -O3 | own noise floor | verdict |
| --- | ---: | ---: | --- |
| `b1_mispredict` | **1.1216 / 1.1222** | 0.0006 | real, and the suite's worst |
| `p4_matmul` | **1.0800 / 1.0803** | 0.0003 | real |
| `h4_vec_dropper` | **1.0404 / 1.0365** | 0.004 | real |
| `p2_collatz` | **1.0191 / 1.0190** | 0.0001 | real |
| `h2_vec_grow` | 1.0043 / 1.0049 | 0.0006 | real but marginal (0.4%) |
| `h3_box_leak` | 0.9948 / 0.9891 | 0.006 | at or better than parity |

The remaining reported ratios range from ~0.10 to 1.003: `m2` 0.757, `p3` 0.892,
`p6` 0.978, `p7` 0.772, `v1` 0.654, `v3` ~0.10, `h1` 0.982, `p8` 0.979, `p1` 1.003,
`p5` 1.000, `m1` 0.994, `v2` 0.998. Suite geomean 0.849x; 18/18 MATCH, 0 MISMATCH.

FOUR programs have measured gaps above 1% relative to LLVM -O3; `h2_vec_grow` has
an additional marginal measured gap of 0.4–0.5%. The objective "at least matching
LLVM and clang" is a MAX-GAP requirement, so it is not met, and the binding constraint is
`b1_mispredict` at 1.122x.

## ⚠ The harness's `worst 1.222x` is `h3_box_leak`, and it is NOT a regression

`benchmarks/beat-llvm/run.py` reported `runtime geomean 0.849x ... worst 1.222x` on this
exact tree. That worst row is `h3_box_leak` (llvm 0.0297s, bridge 0.0363s). Carefully
measured, h3 is **0.9948x** — slightly FASTER than LLVM.

Two independent reasons the harness row is not evidence, both already documented in this
repository:

1. h3's LLVM median is **0.0297s**, below the harness's OWN resolvability threshold
   (it prints a second geomean "resolvable-rows-only ... with llvm median >= 0.05s"
   precisely to exclude rows like this one).
2. h3 is the program that **code LAYOUT alone has moved 14.8%** with its hot loop
   byte-identical (`reports/perf/` layout study; memory `x86-layout-swings-14-percent`).

A previous session recorded h3 at 1.085x, then 0.989x, on the same code — the
`measured-defaults-expire` note. Anyone reading a `worst Nx` line from this harness should
first check WHICH program it is, and re-measure it with duplicated arms before treating it
as a gap. Left unchecked, this row would have been recorded as a fresh 22% regression in
the worst program on a day when that program is at parity.

## Status of each real gap, so none is re-investigated from scratch

- **`b1_mispredict` 1.122x.** 31-32 insns/iter vs LLVM's 26-27. All three named causes are
  MEASURED and refuted: the extra register copies (the commuted-tie arm, once made
  reachable, moves b1 1.1203 -> 1.1213 against a 0.0004 floor); the branch-to-branch `jmp`
  (the `branch-layout-fallthrough` knob is recorded "slightly negative on b1 ~0.4%"); and
  code alignment (removing the JCC padding makes b1 1.1% WORSE, and `-C target-cpu=znver4`
  makes it 1.2% worse). The plausible residual is branch-prediction behaviour, which this
  host cannot measure — `perf_event_paranoid=4`, no hardware counters.
- **`p4_matmul` 1.080x.** Its previously-recorded cause was analysis of a DEAD loop.
  The later [copy-cost probe](../2026-09-29-p4-real-hot-loop/README.md#refuted-by-direct-measurement-the-xmm-commuted-tie-cannot-pay)
  supersedes the proposed XMM commuted-tie lever: removing two `movdqa` copies from
  the isolated multiply-accumulate unit shows no improvement on this AMD core.
  The subsequent [inner-loop probe](../2026-09-29-p4-real-hot-loop/README.md#the-loop-nest-hypothesis-is-also-refuted-collapsing-a-level-is-worth-013)
  reports only a 0.12–0.15% gain from full inner-loop unrolling, insufficient to
  explain the measured 8% gap. Both probes are bounded to their synthetic work
  and host. The full-program cause remains unresolved; the enclosing loop levels
  have not been isolated, and no replacement compiler lever is established.
- **`h4_vec_dropper` 1.040x.** 4% of a 7.8ms program. Its loop nest differs structurally
  from LLVM's (tcg: a stride-4 vector loop plus a LIVE stride-1 scalar loop; LLVM: two
  18/22-insn loops), so this is not an instruction-level delta to shave — it needs the
  loop structure compared first.
- **`p2_collatz` 1.019x.** Entirely attributable to the JCC-erratum ALIGNMENT REGIME (an
  Intel Skylake workaround, on an AMD host). Recoverable in full (`-C target-cpu=znver4`
  gives 1.0012x) but it COSTS `b1` 1.2%, so it is a trade, not a win. Note the knob
  toggles per-branch NOPs, per-function 32-byte padding and section alignment TOGETHER,
  so which of the three each program cares about is undetermined —
  `2026-09-29-jcc-align-is-a-trade/`.
