# WITHDRAWN AND CORRECTED: the 1.875x was an ISA artifact. At EQUAL ISA trust-cg beats clang on both families (2026-09-28)

> **This report's original conclusion — "trust-cg does NOT match clang on the
> vectorizable family, 1.875x" — IS WITHDRAWN. It was wrong, and the cause was my
> measurement, not the backend.**
>
> The clang driver on this host is `~/.local/bin/cc`, a `zig cc` wrapper, and
> **zig cc defaults to the NATIVE CPU**. Its `-O3` lane was emitting **AVX-512**
> (`vmovdqa64`, `vpmulld %zmm`, 16xi32 per operation) while the Rust lanes run at
> `-C target-cpu` DEFAULT, i.e. the x86-64 baseline with SSE2 only. That is a 4x
> vector-width advantage, and it accounted for essentially the whole gap. The tell
> was visible in the original table and I did not read it: plain `-O3` (19.1 ms)
> and `-march=native` (19.7 ms) were the SAME speed, which cannot happen if the
> plain lane were really baseline.
>
> `-target x86_64-linux-gnu` produces a genuine baseline build from zig cc (zero
> `%zmm`/`%ymm` across the whole set, verified). At that equal ISA, 15 runs each:
>
> | family | trust-cg vs clang | vs gcc | worst vs clang |
> | --- | ---: | ---: | ---: |
> | scalar (5 kernels) | **0.934x** | 0.916x | 1.024x |
> | vectorizable (3 kernels) | **0.415x** | 0.715x | 1.009x |
>
> Per program: `v1_saxpy` clang 70.5 ms vs trust-cg at 47.7 ms (**0.676x**);
> `v3_popcount` clang 118.2 ms vs 12.4 ms (**0.105x**); `v2_memfill` 1.009x.
>
> So at matched ISA trust-cg MEETS OR BEATS clang on every family measured, and
> the worst single program is 1.024x. The original 1.875x is what clang achieves
> when allowed AVX-512, which trust-cg does not emit at all — that is a real and
> nameable gap (no AVX2/AVX-512 vectorization), but it is not "slower than clang
> at the same instruction set".
>
> The one genuine loss is unchanged and is against GCC, not clang: `v2_memfill`
> **15.297x**. gcc eliminates the whole fill because every byte is set to the same
> `v`, so `a[idx] == v` for any `idx`; it still exits 44. clang, LLVM-rustc and
> trust-cg all keep the stores.
>
> The measured numbers below are retained exactly as taken, because they are
> correct readings of an unequal comparison and the withdrawal is only about what
> they mean.

# (WITHDRAWN) trust-cg does NOT match clang on the vectorizable family: 1.875x, while reading 0.401x against LLVM-through-rustc (2026-09-28)

The objective is "at least LLVM/clang performance". Every vectorizable number this
project has recorded compares against **LLVM through rustc**, where trust-cg reads
0.543x (corpus) and 0.401x (here) — a large win. Against **clang** the same
kernels read **1.875x**. This report is that correction, and it materially worsens
the performance clause.

## Result

Three C ports written and fidelity-checked for this report (`progs_c/v1_saxpy.c`,
`v2_memfill.c`, `v3_popcount.c`), 15 runs each, medians, ms:

| program | gcc | clang | gcc -native | clang -native | LLVM-rustc | trust-cg | t/clang | t/clang-native | t/LLVM |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| v1_saxpy | 113.4 | 19.1 | 11.6 | 19.7 | 73.8 | 47.4 | **2.480** | 2.406 | 0.642 |
| v2_memfill | **0.2** | 2.6 | 0.2 | 2.6 | 2.7 | 2.7 | 1.034 | 1.037 | 0.994 |
| v3_popcount | 219.5 | 4.8 | 8.7 | 4.8 | 122.1 | 12.4 | **2.571** | 2.573 | 0.101 |

**GEOMEAN — vs clang 1.875x, vs clang -march=native 1.859x, vs LLVM-rustc 0.401x.**

## What that means

The two baselines disagree by a factor of ~4.7 on this family, and clang is the
stronger one by a wide margin:

* `v3_popcount`: clang 4.8 ms, LLVM-rustc 122.1 ms. trust-cg's 12.4 ms is **10x
  faster than LLVM-rustc and 2.6x slower than clang.** The project's headline
  0.0997x/0.101x for this program is true and is measured against the weaker
  baseline; it is not a clang result.
* `v1_saxpy`: clang 19.1 ms against LLVM-rustc's 73.8 ms. trust-cg at 47.4 ms sits
  between them — 0.642x vs LLVM-rustc, 2.480x vs clang.
* `v2_memfill` is the one row at parity with clang (1.034x), and it is also where
  **gcc finds an optimisation nobody else does**: 0.2 ms against clang's 2.6 ms.
  Every byte of `a` is set to the same `v`, so `a[idx] == v` for ANY `idx` and the
  whole fill is dead; gcc eliminates it and still exits 44, the same checksum as
  everyone else. clang, LLVM-rustc and trust-cg all keep the stores.

So on the family where trust-cg looked strongest, it is not matching clang, and the
appearance came from comparing against rustc's LLVM rather than clang. The
`--bridge-cg-arg no-proof-certs` caveat applies as always: this is the diagnostic
lane, the only one in which trust-cg compiles these programs.

## Fidelity

Each port was exit-code cross-checked against gcc, clang and the Rust original
before timing, per `run_gcc_baseline.sh`'s rule that "a port that disagrees is a
broken port, not a result": v1_saxpy 118, v2_memfill 44, v3_popcount 38 — all three
agree across all lanes. Rust's `wrapping_*` on `i32` is modelled with `uint32_t`
arithmetic so the C port keeps Rust's DEFINED wrap instead of C's signed-overflow
UB, and `u32::count_ones` maps to `__builtin_popcount`. The arrays are function
locals in both languages (not `static`), so the storage class matches.

## Why these three and not the rest

`progs_c/` previously held ports for five SCALAR kernels only, on the recorded
ground that the other families "exercise Rust `Vec`, closures and `std` that have
no faithful C equivalent". That is true of the heap family (`Vec` growth, `Box`,
drop order) but NOT of the vectorizable family, which is fixed-size arrays and
integer arithmetic — the most mechanically portable code in the corpus, and the
family whose numbers most needed a second baseline. `run_gcc_baseline.sh`'s default
`PROGS` list is extended to include them.

The heap family (`h1`-`h4`) is deliberately still absent: a C port would have to
reproduce `Vec`'s growth schedule and allocator interaction to be comparable, and
the exit checksum would agree even if the allocation pattern did not — so such a
port could look faithful while measuring something else. `h1_vec_push_sum`'s 2.625x
therefore remains an LLVM-only number.

## Provenance

Host `x86_64-unknown-linux-gnu`, AMD Ryzen 9 9900X3D. gcc
`(Ubuntu 15.2.0-16ubuntu1) 15.2.0`; clang `21.1.0` via `~/.local/bin/cc`
(`zig cc` wrapper); Rust lanes through stage2
`trustc 1.99.0-dev (3a3e781fe 2026-09-14)`; bridge from this tree with
`ay 0.27.0+build.11385` and Clean `e75141b7b`. 15 timed runs per binary, median
reported. Not a `run.py` results JSON, so not ledger evidence.
