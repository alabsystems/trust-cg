# First clang and gcc comparison on x86-64 Linux: PARITY with clang, faster than gcc, on the five C-portable kernels (2026-09-28)

The objective names "at least LLVM/clang performance". Every performance
measurement on this host so far has compared trust-cg against **LLVM through
rustc** only. The clang half had never been measured here, and the completion
plan's host line even recorded "Ubuntu gcc 15.2.0, **no clang**" — which is false:
the machine has a clang-family driver at `~/.local/bin/cc`, a `zig cc` wrapper
reporting **clang 21.1.0** (the same correction XD-03 already carries).

This is that measurement.

## Result

Five kernels, 21 runs each, medians, `-Copt-level=3` / `-O3`:

| program | gcc | clang | LLVM-rustc | trust-cg | tcg/clang | tcg/gcc | tcg/LLVM |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| p1_xorshift | 434.5 | 434.7 | 434.5 | 434.5 | 0.999 | 1.000 | 1.000 |
| p2_collatz | 223.2 | 158.6 | 159.0 | 162.9 | 1.027 | 0.730 | 1.025 |
| p3_gcd | 261.2 | 278.8 | 282.2 | 252.0 | 0.904 | 0.965 | 0.893 |
| p5_struct_acc | 434.3 | 434.3 | 434.9 | 434.6 | 1.001 | 1.001 | 0.999 |
| p7_sieve | 23.7 | 21.9 | 32.2 | 23.8 | 1.083 | 1.002 | 0.739 |

**GEOMEAN: trust-cg vs clang 1.001x, vs gcc 0.933x, vs LLVM-rustc 0.925x.**

And against the STRONGER baseline the project's own `run_gcc_baseline.sh` uses
(`-march=native` for the C lanes, which the Rust lanes do not get — they run at
`-C target-cpu` default):

| program | gcc -native | clang -native | trust-cg | tcg/clangN | tcg/gccN |
| --- | ---: | ---: | ---: | ---: | ---: |
| p1_xorshift | 434.5 | 434.5 | 434.7 | 1.001 | 1.000 |
| p2_collatz | 232.9 | 158.7 | 162.9 | 1.027 | 0.700 |
| p3_gcd | 307.3 | 277.7 | 251.8 | 0.907 | 0.820 |
| p5_struct_acc | 434.3 | 434.6 | 434.7 | 1.000 | 1.001 |
| p7_sieve | 19.5 | 21.5 | 22.9 | 1.067 | **1.177** |

**GEOMEAN vs clang -march=native 0.999x, vs gcc -march=native 0.925x.**

So on this subset trust-cg is at PARITY with clang (0.999x-1.001x) and FASTER than
gcc (0.925x-0.933x), and the parity survives giving the C compilers a
microarchitecture advantage the Rust lanes do not have.

## Where it loses, named

* `p7_sieve` is the worst row both ways: 1.083x vs clang, and **1.177x vs
  gcc -march=native** — gcc at 19.5 ms against trust-cg's 22.9 ms. It is also the
  shortest kernel (~20 ms), so it is the least resolvable of the five.
* `p2_collatz` is 1.027x vs clang. Note gcc is much SLOWER here (223-233 ms vs
  clang's 159 ms), so the gcc geomean win is carried substantially by this one row
  — worth stating rather than banking.
* `p3_gcd` is the best row (0.904x vs clang) but its inter-run spread was the
  widest measured (0.20), so treat it as soft.

## What this does and does not establish

It DOES give the clang half of the objective its first number on this host, and it
is a parity result on the kernels that can carry it.

It does NOT cover the objective. Five of the eighteen corpus programs have C ports,
and they are exactly the SCALAR ones — `progs_c/` has no port for the heap
(`h1`-`h4`), vectorizable (`v1`-`v3`, `p4`) or branch (`b1`) families, because
those exercise Rust `Vec`, closures and `std` that have no faithful C equivalent.
So this says nothing about `h1_vec_push_sum` (2.625x vs LLVM) or the vectorizable
family (0.543x vs LLVM).

It is also a DIAGNOSTIC-lane number for trust-cg: the bridge lane needs
`-Ztrust-ir-cg-args=no-proof-certs`, because the default proof-required lane
compiles 0 of 18 programs. The comparison is therefore between clang/gcc/LLVM at
full strength and trust-cg with its evidence gate off, which is the only
configuration in which trust-cg compiles these programs at all.

Every port was exit-code cross-checked across all four toolchains before timing,
per the protocol in `run_gcc_baseline.sh` ("a port that disagrees is a broken port,
not a result"): all five agree — p1 41, p2 88, p3 104, p5 87, p7 72.

## Provenance

Host `x86_64-unknown-linux-gnu`, AMD Ryzen 9 9900X3D. gcc
`(Ubuntu 15.2.0-16ubuntu1) 15.2.0` at `/usr/bin/gcc`; clang `21.1.0` via
`~/.local/bin/cc` (`zig cc` wrapper); Rust lanes through stage2
`trustc 1.99.0-dev (3a3e781fe 2026-09-14)`, bridge from this tree with
`ay 0.27.0+build.11385` and Clean `e75141b7b`. 21 timed runs per binary,
median reported, max inter-run spread per row shown in the working notes. C
sources `benchmarks/beat-llvm/progs_c/*.c`; Rust sources
`benchmarks/beat-llvm/progs/*.rs`. This is not a
`benchmarks/beat-llvm/run.py` results JSON and carries no `headline_eligible`
stamp, so it is not ledger evidence.
