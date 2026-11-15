# Equal-ISA per-program parity vs clang AND gcc (2026-09-29)

The objective names **LLVM and clang**. Every per-program table in this round so far
measured LLVM-through-rustc only. This is the missing half: the 14 ported C programs
against `gcc -O3` and `clang -O3`, at EQUAL ISA, on the current backend (which now
carries the dense-switch jump table, the SIB scale fold and the dead-bit-test fix).

## Method

`gcc -O3 -march=x86-64` and, because this host has no standalone clang,
`zig cc -target x86_64-linux-gnu -O3 -march=x86_64` — zig cc IS clang. `-march=x86-64`
is not decoration: `-march=native` makes both C compilers emit AVX-512 while the Rust
lanes run `-C target-cpu` default (SSE2), which produced a 1.875x figure earlier in this
round that had to be WITHDRAWN. Verified here by disassembly: zero `zmm`, zero `ymm` in
the C binaries.

Exit codes compared three ways first — all 14 agree. Then 11 interleaved samples per
program per compiler on one pinned core (7 for `p6_branch_match`, which runs 1.5s), `min`
reported, plus `P(trust-cg sample < reference sample)`. "Slower" means ratio > 1.005 AND
P < 0.25.

## The table

| program | gcc | clang | trust-cg | vs gcc | vs clang | verdict |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| v3_popcount | 226.13 | 121.72 | **12.54** | 0.055x | 0.103x | beats both |
| v1_saxpy | 116.08 | 72.28 | **48.78** | 0.420x | 0.675x | beats both |
| m2_call_heavy | 60.03 | 60.04 | **45.40** | 0.756x | 0.756x | beats both |
| p7_sieve | 24.17 | 30.14 | **22.56** | 0.933x | 0.748x | beats both |
| p3_gcd | 288.38 | 282.05 | **260.06** | 0.902x | 0.922x | beats both |
| p6_branch_match | 1593.12 | 1572.61 | **1548.81** | 0.972x | 0.985x | beats both |
| p1_xorshift | 448.37 | 448.34 | 448.35 | 1.000x | 1.000x | matches both |
| p5_struct_acc | 448.49 | 448.48 | 448.43 | 1.000x | 1.000x | matches both |
| p8_closure_nest | 149.64 | 149.65 | 149.65 | 1.000x | 1.000x | matches both |
| m1_call_chain | 67.52 | 67.52 | 67.58 | 1.001x | 1.001x | matches both |
| **p2_collatz** | 229.72 | 164.18 | 167.05 | **0.727x** | **1.017x** | beats gcc, trails clang |
| **p4_matmul** | 51.32 | 61.97 | 63.77 | **1.243x** | **1.029x** | trails both |
| **b1_mispredict** | 196.41 | 183.87 | 218.64 | **1.113x** | **1.189x** | trails both |
| **v2_memfill** | 0.34 | 2.70 | 2.86 | **8.523x** | 1.058x | trails gcc |

**geomean: 0.861x vs gcc, 0.804x vs clang.**

## What this changes about the remaining work

* **`p4_matmul` vs clang is 1.029x, not the 1.093x measured against
  LLVM-through-rustc.** The bar on this program is set by **gcc** (1.243x), which beats
  clang here too (51.32ms against 61.97ms). So "match LLVM and clang" is nearly met on
  p4 while "match gcc" is not, and any work aimed at it should be aimed at what gcc
  does, not at clang's vectorizer.
* **`p2_collatz` BEATS gcc by 27%** while trailing clang by 1.7%. Its remaining gap is
  specifically a clang gap.
* **`v2_memfill` 8.523x vs gcc is gcc proving the fill DEAD** (0.34ms against clang's
  2.70ms — clang does not do it either). At 2.86ms the row sits far below the harness's
  50ms resolvability floor, and the gap is a dead-store-elimination proof, not codegen
  quality.
* **`b1_mispredict` is the one program that trails EVERY reference** — 1.113x gcc,
  1.189x clang, 1.168x LLVM. It is the most consistent real gap in the corpus, and it is
  the program deliberately written to defeat if-conversion (each arm does different work
  and stores to a different scratch slot).
* The heap family has no C ports, for the reason recorded in
  `../2026-09-28-linux-x86-64-clang-13-programs/README.md`: their `Vec` indexing carries
  a bounds check that C does not have, so a port would not contain the obligation under
  measurement.

## Union of real per-program gaps, across all three references

`b1_mispredict` (all three), `p4_matmul` (all three, worst against gcc), `p2_collatz`
(clang only), `h1_vec_push_sum` (LLVM only — no C port), and `v2_memfill` (gcc only,
below the resolvability floor). Ten of the fourteen ported programs match or beat BOTH
reference compilers.
