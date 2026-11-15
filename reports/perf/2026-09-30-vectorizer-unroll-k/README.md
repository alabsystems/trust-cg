# The vectorizer's reduction unroll factor was an unexamined magic number: K=2 -> 4 makes h1 23% FASTER than LLVM

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 90 interleaved rounds for the sweep,
`taskset -c 2`, minimum statistic, arms duplicated as their own floor.

## It had never been swept

`regarg_unroll_k()` sets K for the SSE2 vectorizer's reg-arg PADDQ reduction — the number of
INDEPENDENT packed accumulators the hot body emits per iteration, over `K * LANES_Q` elements.
Its doc described the default as "K=2 (2 PADDQ/iter, 4 i64/iter — **LLVM-parity structure**)".

Both of its channels were `TCG_NO_X86_VEC_UNROLL` and `TCG_X86_VEC_UNROLL_K`, and `trustc`
refuses every `TCG_*` variable before the backend loads. So the unroll factor of the LARGEST
optimization in this backend — the vectorizer, measured at 3x-54x on this corpus — could not
be swept through the bridge, and "LLVM-parity structure" had never been checked against LLVM
on this host.

## The sweep

`h1_vec_push_sum` against LLVM -O3:

| K | h1 vs LLVM |
| ---: | ---: |
| 1 | 1.8169 |
| 2 (old default) | 0.9975 |
| **4 (new default)** | **0.7719** |
| 8 | 0.6651 |

Monotone, and mechanically so: each extra accumulator breaks more of the serial PADDQ
dependency chain, which is why K=1 is 1.82x — fully serial. The doc's claim was exactly
right and exactly the problem: K=2 IS LLVM-parity structure, and parity was not the ceiling.

`h1_vec_push_sum` is the ONLY corpus program this tier fires on. `h2_vec_grow`,
`h4_vec_dropper`, `v1_saxpy`, `v2_memfill`, `v3_popcount` and `p4_matmul` are all
BYTE-IDENTICAL across K in {1,2,4,8}, so the change costs nothing measurable elsewhere —
verified by byte comparison after the flip, along with h1 matching the measured K=4 arm.

## Why 4 and not 8, when 8 measured better

One program is not enough evidence to spend half the XMM register file, and there are two
costs that this corpus cannot see:

* K=8 holds EIGHT packed accumulators live. Sixteen XMM registers exist; a vector loop doing
  anything else alongside the reduction would spill.
* The packed-body gate is `len & -(K * LANES_Q)`, so a larger K pushes MORE of a short
  reduction into the remainder loop. K=8 needs `len >= 16` to enter the packed body at all;
  K=4 needs `len >= 8`.

K=4 takes the large majority of the win — 23% faster than LLVM against 33% — at half the
register pressure and half the entry threshold. Raising it to 8 wants a corpus containing
short reductions and register-starved vector loops, which this one does not.

## Effect on the objective

| | before | after |
| --- | ---: | ---: |
| programs above parity | 5 | **4** |
| suite WORST | 1.0968 | **1.0947** |
| suite geomean | 0.8328 | **0.8241** |
| `h1_vec_push_sum` | ~1.003 (a violation) | **0.7727** (beats LLVM by 23%) |

Remaining violations: `b1_mispredict` 1.0947, `p4_matmul` 1.0829, `h4_vec_dropper` 1.0341,
`p2_collatz` 1.0103. Eight programs now beat LLVM and six are at parity.

## The generalisable point

This is the fourth lever this campaign that was invisible because its channel was a `TCG_*`
variable, and the second whose recorded characterisation was accurate but incomplete — "LLVM-
parity structure" was true and was being treated as a goal rather than a waypoint. A magic
number inside the backend's largest optimization went unexamined for exactly as long as it was
unreachable. Sweeping numeric knobs is cheap once they are askable; the expensive part was
making them askable.
