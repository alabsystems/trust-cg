# gcc on Linux, against the CURRENT backend — and why clang is unmeasurable here

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · gcc (Ubuntu 15.2.0-16ubuntu1) 15.2.0

## Why this run exists

The standing goal names LLVM **and clang**. Every performance figure in this series
compares against rustc's own LLVM backend; the gcc/clang side had one measurement on this
host, taken before today's vectorizer work, over the 8 programs that then compiled. That
figure is stale in both senses, so it is re-taken here with the current backend over the
whole C corpus.

**clang IS measurable on this host — via `zig cc`.** No binary named `clang` exists
(`$HOME/trust/build/host/llvm/bin` ships only `clang-offload-packager`; `/usr/bin`,
`/usr/local/bin` and the cargo bin dir have none), which is why earlier runs here recorded
clang as unavailable. **That conclusion was wrong**: it was reached by looking for a file
called `clang`. `zig` 0.16.0 is installed at `/home/ayates/.local/bin/zig`, and `zig cc`
reports `clang version 21.1.0`, target `x86_64-unknown-linux-gnu`. It compiles and runs the
whole corpus. The clang results are in their own section below.

Scope note: `zig cc` is used ONLY to compile the C benchmark corpus. It must not become the
host CC for building trust-cg itself — that breaks the DRAT checker, the i128 differentials
and the bridge link, a separate recorded hazard that nothing here changes.

The repo's own `benchmarks/beat-llvm/run_gcc_baseline.sh` cannot run here either: it is zsh
and macOS-specific (Homebrew `gcc-NN`, `-march=native`, `--target x86_64-apple-darwin`, a
`.dylib` backend). This run uses its corpus (`progs_c/`, 14 C ports) and its discipline.

## Validity first: every port agrees

The script's own rule is that "a port that disagrees is a broken port, not a result". All
**14 of 14** C ports produced the same exit code as their Rust counterpart compiled by
trust-cg (b1 44, m1 61, m2 26, p1 41, p2 88, p3 104, p4 111, p5 87, p6 62, p7 72, p8 46,
v1 118, v2 44, v3 38). No row is excluded as a broken port.

## Two ISA levels, deliberately

| baseline | geomean, 14 rows | geomean, resolvable 11 | rows won or tied |
|---|---:|---:|---|
| gcc `-O3 -march=x86-64` | **0.823** | **0.891** | **12 / 14** |
| gcc `-O3 -march=native` | 1.323 | — | 9 / 14 |

`-march=x86-64` is the apples-to-apples row: it is the ISA rustc targets for
`x86_64-unknown-linux-gnu` (baseline SSE2), which is also all this backend emits.
`-march=native` is what the macOS script hands gcc, and on this Ryzen it unlocks AVX-512
that neither Rust lane uses.

"Resolvable" excludes the three rows where either side is under 40ms — p7_sieve (24 vs 25),
v2_memfill (4 vs 1) and v3_popcount (14 vs 228) — because this harness's own noise floor
makes sub-40ms ratios unreliable. v3's win survives the caveat in direction if not in
magnitude: its gcc side is a well-resolved 228ms.

### Per program, vs gcc at matched ISA

| program | trust-cg | gcc x86-64 | ratio | gcc native |
|---|---:|---:|---:|---:|
| v3_popcount | 14 | 228 | 0.061 | 10 |
| v1_saxpy | 50 | 117 | 0.427 | 13 |
| p2_collatz | 167 | 231 | 0.723 | 241 |
| m2_call_heavy | 47 | 61 | 0.770 | 61 |
| p7_sieve | 24 | 25 | 0.960 | 20 |
| p3_gcd | 259 | 268 | 0.966 | 323 |
| p6_branch_match | 1559 | 1596 | 0.977 | 1593 |
| b1_mispredict | 197 | 198 | 0.995 | 197 |
| m1/p1/p5/p8 | — | — | 1.000 | — |
| p4_matmul | 65 | 52 | 1.250 | 14 |
| v2_memfill | 4 | 1 | 4.000 | 1 |

## What this establishes, and what it does not

**At matched ISA trust-cg beats gcc on this corpus** — 0.891 over the resolvable rows,
0.823 over all 14, winning or tying 12 of 14. Together with geomean 0.880x against LLVM
-O3, both available references are met at the ISA the backend targets.

**Given `-march=native`, gcc wins** (1.323), and the gap is concentrated exactly where
vector width decides it: p4_matmul 14ms against our 65, v1_saxpy 13 against our 50,
v3_popcount 10 against our 14. That is not a code-quality gap but an ISA gap — this backend
emits SSE2 only, so it is working 128 bits at a time against gcc's 512. **Widening the
vectorizer to AVX2/AVX-512 is the named next frontier**, and it is the honest reading of
why `-march=native` gcc is ahead.

**clang is measured too** — see below. The earlier claim that it could not be, repeated
several times in this series, was my error.

Figures are wall-clock best-of-5 under `taskset -c 2`, the Rust lane in the diagnostic
compile lane (`no-proof-certs`); see `../2026-10-01-x86-evidence-lane-unavailable/` for why
no x86-64 run here is ledger evidence, and what actually blocks that.

---

## clang 21.1.0, same corpus, same discipline

Obtained through `zig cc` (see the corrected note above). All **14 of 14** ports compile and
agree on exit codes with their Rust counterparts.

| baseline | geomean, 14 rows | geomean, resolvable 11 | rows won or tied |
|---|---:|---:|---|
| clang `-O3 -march=x86_64` | **0.799** | **0.941** | 11 / 14 |
| clang `-O3 -march=native` | 1.315 | — | 8 / 14 |

(`-march=x86_64`, with an underscore, is zig's spelling of the baseline CPU; `-march=x86-64`
is rejected with a CPU list, which is what made the first attempt fail on all 14 rows.)

### Per program, vs clang at matched ISA

| program | trust-cg | clang x86_64 | ratio | clang native |
|---|---:|---:|---:|---:|
| v3_popcount | 14 | 123 | 0.114 | 6 |
| v1_saxpy | 50 | 74 | 0.676 | 15 |
| p7_sieve | 24 | 32 | 0.750 | 22 |
| m2_call_heavy | 47 | 61 | 0.770 | 61 |
| p3_gcd | 259 | 284 | 0.912 | 283 |
| p6_branch_match | 1560 | 1580 | 0.987 | 1577 |
| m1/p1/p5/p8/v2 | — | — | 1.000 | — |
| p2_collatz | 167 | 165 | 1.012 | 165 |
| p4_matmul | 65 | 64 | 1.016 | 9 |
| b1_mispredict | 197 | 186 | 1.059 | 184 |

## The three-way summary, at the ISA this backend targets

| reference | geomean | corpus |
|---|---:|---|
| LLVM -O3 (rustc's own backend) | **0.880** | 18 Rust programs |
| gcc 15.2.0 `-march=x86-64` | **0.891** resolvable / 0.823 all | 14 C ports |
| clang 21.1.0 `-march=x86_64` | **0.941** resolvable / 0.799 all | 14 C ports |

**trust-cg is at or ahead of all three at matched ISA.**

And the same caveat applies to both C references: at `-march=native` they win (gcc 1.323,
clang 1.315), concentrated on the vector kernels — p4_matmul 9–14ms against our 65,
v1_saxpy 13–15 against our 50, v3_popcount 6–10 against our 14. That is an **ISA gap**: this
backend emits SSE2 only, 128 bits at a time against their 512. Widening the vectorizer to
AVX2/AVX-512 is the named next frontier and is what that row is really measuring.
