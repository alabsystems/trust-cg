# gcc 15.2.0 parity on the subset that still compiles (Linux x86-64)

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · gcc (Ubuntu 15.2.0-16ubuntu1)
`-O3 -march=x86-64` · LLVM via rustc's in-tree LLVM 22.1.2 · trust-cg via the bridge
with `no-proof-certs`

The standing goal names LLVM **and clang** as the bar. The clang/gcc comparison in this
repo had only ever been run by `benchmarks/beat-llvm/run_gcc_baseline.sh`, whose own
header scopes it to "an x86_64 **macOS** diagnostic (zsh, Homebrew gcc, …)". This is the
first time that lane has been measured on this Linux host.

⚑ Scope, stated first: **8 of 18 programs**, because the other 10 do not currently
compile — see `../2026-10-01-panic-cohort-blocks-the-loop-passes/`. And **clang has no
driver on this host** (`/usr/bin/clang*` is absent; the in-tree LLVM ships only
`clang-offload-packager`), so the LLVM bar is measured through rustc's LLVM 22.1.2 and
clang itself is not measured. gcc IS measured directly.

Protocol: 60 interleaved rounds, `taskset -c 2`, `min` statistic, with gcc carried TWICE
as byte-identical copies for the floor. Every program's three binaries were
**exit-code checked against each other before timing** — a C port that disagrees is a
broken port, not a result — and all 8 agreed.

| program | gcc ms | llvm ms | trust-cg ms | vs gcc | vs llvm | gcc floor |
|---|---:|---:|---:|---:|---:|---:|
| m2_call_heavy | 59.989 | 60.100 | **45.392** | **0.7567** | 0.7553 | 0.0001 |
| p2_collatz | 229.434 | 163.802 | 165.660 | **0.7220** | 1.0113 | 0.0013 |
| p3_gcd | 267.410 | 287.301 | **257.036** | **0.9612** | 0.8947 | 0.0023 |
| p6_branch_match | 1592.618 | 1581.615 | **1558.116** | **0.9783** | 0.9851 | 0.0005 |
| p5_struct_acc | 448.100 | 448.194 | 448.200 | 1.0002 | 1.0000 | 0.0000 |
| p1_xorshift | 448.494 | 448.621 | 448.689 | 1.0004 | 1.0002 | 0.0002 |
| p8_closure_nest | 149.611 | 149.701 | 149.689 | 1.0005 | 0.9999 | 0.0002 |
| m1_call_chain | 67.346 | 67.461 | 67.426 | 1.0012 | 0.9995 | 0.0000 |

**geomean 0.9204x vs gcc, 0.9517x vs LLVM.**

## What this establishes, and what it does not

* On the subset that compiles, trust-cg is **faster than both references on average**,
  and the single genuinely above-parity row against LLVM is `p2_collatz` at 1.0113 —
  which simultaneously **beats gcc by 28%**. The bar on p2 is LLVM, not gcc.
* The four rows above 1.0 against gcc (m1 1.0012, p1 1.0004, p5 1.0002, p8 1.0005) are
  0.02%–0.12%. Their gcc floors are 0.0000–0.0002, so m1's is about 6x its floor and the
  rest are at it: real but negligible, and all four are at or below parity against LLVM.
* It does **not** establish the goal's performance clause. Ten programs are excluded
  because they do not compile, and they include every row that was known to trail —
  h1 (1.887x LLVM), h4 (1.195x), h2 (1.111x), p4, b1, and `v2_memfill`, which the macOS
  table recorded at **8.5x gcc**. The excluded set is where the work is.
* clang proper remains unmeasured on this host for want of a driver. Since the LLVM bar
  is the same LLVM 22.1.2 that clang would use, the gap between them is frontend and flag
  choice rather than codegen, but that is an argument, not a measurement.

## Why this was worth measuring now

With 10 of 18 programs blocked behind upstream's v52 panic cohort, the only honest
question left about performance was whether the REMAINING subset meets the bar. It does,
against both references, with one 1.1% exception whose cause is already decomposed to two
instructions (`../../../.claude` notes aside, see
`reports/perf/2026-09-29-p2-collatz-diagnosed/` and the in-place-preference analysis:
the loop-carried register should go to the two-address `shr`, not the three-address
`lea`). So no performance work on the compilable subset is being deferred for lack of
measurement.
