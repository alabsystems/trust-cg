# clang and gcc on 13 of 18 programs at EQUAL ISA: trust-cg at 0.791x vs clang, worst program 1.170x (2026-09-28)

The objective says "at least LLVM/**clang** performance". Before today the clang
half had never been measured on this host and `progs_c/` held five scalar ports.
This extends the C corpus to **thirteen of the eighteen** corpus programs and
measures all of them at a MATCHED instruction set.

## Why "equal ISA" is load-bearing

The clang driver here is `~/.local/bin/cc`, a `zig cc` wrapper, and **zig cc
defaults to the native CPU**: its plain `-O3` lane emits AVX-512 (`vmovdqa64`,
`vpmulld %zmm`), while the Rust lanes run at `-C target-cpu` DEFAULT — x86-64
baseline, SSE2. That is a 4x vector-width advantage, and an earlier reading of this
corpus was published and withdrawn because of it (it reported the vectorizable
family at "1.875x slower than clang"; the real equal-ISA figure is 0.415x).

Every C lane below is `-target x86_64-linux-gnu` (zig) or `-march=x86-64` (gcc),
verified to contain **zero** `%zmm`/`%ymm` across the whole set.

## Result

15 runs for the eight earlier ports, 11 for the five new ones; medians.

| program | family | trust-cg vs clang | vs gcc |
| --- | --- | ---: | ---: |
| v3_popcount | vectorizable | **0.105** | 0.057 |
| v1_saxpy | vectorizable | **0.676** | 0.423 |
| p7_sieve | scalar | 0.767 | 0.965 |
| m2_call_heavy | multifn | 0.768 | 0.760 |
| p3_gcd | scalar | 0.903 | 0.915 |
| p1_xorshift | scalar | 0.998 | 1.001 |
| p8_closure_nest | closure | 1.000 | 1.000 |
| m1_call_chain | multifn | 1.001 | 0.977 |
| p5_struct_acc | scalar | 1.002 | 1.002 |
| v2_memfill | vectorizable | 1.009 | **15.297** |
| p2_collatz | scalar | 1.024 | 0.729 |
| p6_branch_match | branch/match | 1.038 | 1.026 |
| b1_mispredict | branch | **1.170** | 1.112 |

**OVERALL, 13 programs: vs clang 0.791x, vs gcc 0.884x** (0.697x excluding the
`v2_memfill` outlier below). Per family: scalar 0.934x, vectorizable 0.415x,
branch+multifn+closure 0.987x, all against clang.

Only four programs are slower than clang at all, and three of those by under 4%:
`b1_mispredict` 1.170x, `p6_branch_match` 1.038x, `p2_collatz` 1.024x,
`v2_memfill` 1.009x.

## UPDATE: 14 of 18 with `p4_matmul` added

`p4_matmul` ports faithfully too (exit 111 across all four lanes) and was added
after the table above:

| program | family | vs clang | vs gcc | vs LLVM-rustc |
| --- | --- | ---: | ---: | ---: |
| p4_matmul | vectorizable | 1.028 | **1.238** | 1.096 |

**OVERALL, 14 programs at equal ISA: vs clang 0.806x, vs gcc 0.906x.** Worst vs
clang still `b1_mispredict` at 1.170x. Five of fourteen are above 1.005x vs clang:
`b1_mispredict` 1.170, `p6_branch_match` 1.038, `p4_matmul` 1.028,
`p2_collatz` 1.024, `v2_memfill` 1.009.

`p4_matmul` adds a THIRD named gap and it is against gcc, not clang: 1.238x
(50.0 ms vs 61.9 ms) on a 24x24 i64 triple loop. clang is 60.2 ms, so trust-cg is
within 3% of clang there and gcc is the outlier — the reverse of `v2_memfill`,
where gcc's win is a dead-store proof. Both gcc gaps are worth separating from the
clang clause when prioritising.

## The two real gaps, named

**`b1_mispredict`, 1.170x vs clang — the worst program, and already diagnosed.**
It reads 1.158x against LLVM-rustc too, so it is not a clang-specific gap. Its
cause was established today and it is NOT instruction count: removing the two
dead instructions from its hot loop (the cross-block RFLAGS-liveness fix) changed
the runtime by 0% because the loop is branch-misprediction bound and the pair sat
on the mispredicted path. The remaining candidates recorded in X14 are a redundant
`cmp` that a scheduling rule would remove and an `incq` strength reduction.

**`v2_memfill`, 15.297x vs GCC — a nameable missing optimisation, not a clang
gap** (it is 1.009x vs clang). Every byte of `a` is set to the same `v`, so
`a[idx] == v` for ANY `idx`, so the entire fill is dead. gcc proves that and
deletes it, still exiting 44 — the same checksum as every other lane. clang,
LLVM-rustc and trust-cg all keep 819 MB of stores. That is a uniform-store /
dead-fill elimination neither LLVM lane performs either.

**And one gap that is real but outside this comparison: trust-cg emits SSE2 only.**
Given AVX-512, clang beats it on the vectorizable family (1.875x). Closing that
means new vector ISA support — which would also ADD uncovered opcodes to the proof
gate, so it trades against the correctness clause rather than being free.

## Why the heap family CANNOT be ported to C faithfully — the precise reason

An earlier draft said a C port "would have to reproduce `Vec`'s growth schedule".
That is true but not the binding reason, and the binding reason matters because it
also says what the h1 number means.

Rust's growth schedule IS reproducible: `RawVec` starts at 4 elements for an
8-byte type and doubles, so `cap = cap ? cap * 2 : 4` with `realloc` is faithful.
The obstacle is elsewhere. `h1_vec_push_sum`'s runtime is dominated by
300 passes x 300,000 indexed reads, and in Rust each of those reads carries a
bounds check. C has no bounds check to eliminate, so a C port would not contain
that obligation at all: it would be strictly easier code, and clang would win by
not doing work Rust requires.

CORRECTION TO AN EARLIER DRAFT OF THIS PARAGRAPH. It said the un-eliminated bounds
check "IS the 2.625x". That is withdrawn — but NOT because the check was removed: on
the current backend h1's Vec bounds check is still there, and bounds-check
elimination declines the loop on its index operand. It is withdrawn because the gap
was decomposed and the check is not in it. Measured on a resolvable 10x-scaled copy:
**1.979x is LLVM's vectorization** (four `paddq` on `xmm`) and **1.334x is residual
scalar codegen quality**. See
[the Vec bounds-check report](../2026-09-28-linux-x86-64-vec-bounds-check/README.md).
The reason the heap family is unportable stands unchanged — the *obligation* is
absent from C either way — but the check is no longer a cost claim.

That is why `h1`-`h4` have no ports, and it is also why the comparison that matters
for them is trust-cg vs **LLVM-through-rustc**: both compile the SAME Rust source
with the same bounds checks, so the 2.625x is an apples-to-apples statement about
two backends given identical obligations. Adding a clang column there would compare
different programs.

(The same reasoning does NOT block the ported programs: their indices are provably
in range against a compile-time bound, so the check is eliminable and every backend
including trust-cg does eliminate it — which is why their C ports measure the same
work.)

## Coverage, and what is deliberately missing

Thirteen of eighteen. The five absent are the HEAP family (`h1`-`h4`) and
`p4_matmul`. The heap family is absent on purpose: a faithful C port would have to
reproduce `Vec`'s growth schedule and allocator interaction, and the exit checksum
would agree even if the allocation pattern did not — so the port could look
faithful while measuring something else. `h1_vec_push_sum`'s 2.625x therefore
remains an LLVM-only number, and it is the largest per-program gap in the corpus.

## Fidelity

Every port is exit-code cross-checked against gcc, clang and the Rust original
before timing, per `run_gcc_baseline.sh`'s rule that "a port that disagrees is a
broken port, not a result". All thirteen agree. Rust `u64`/`u32` wrapping
arithmetic maps to C unsigned arithmetic (same bits, defined in both, avoiding C's
signed-overflow UB); `rotate_left` maps to a `rotl64` that masks the amount and
special-cases 0, because Rust's `rotate_left(0)` is the identity while a C shift by
64 is UB; `count_ones` maps to `__builtin_popcount`; `#[inline(never)]` maps to
`__attribute__((noinline))`; arrays are function locals in both languages.

## Provenance and scope

Host `x86_64-unknown-linux-gnu`, AMD Ryzen 9 9900X3D. gcc
`(Ubuntu 15.2.0-16ubuntu1) 15.2.0`; clang `21.1.0` via `~/.local/bin/cc`; Rust
lanes through stage2 `trustc 1.99.0-dev (3a3e781fe 2026-09-14)`; bridge from this
tree with `ay 0.27.0+build.11385` and Clean `e75141b7b`.

The trust-cg lane is the DIAGNOSTIC lane (`-Ztrust-ir-cg-args=no-proof-certs`),
because the default proof-required lane compiles 0 of 18 programs. So this compares
clang and gcc at full strength against trust-cg with its evidence gate off — the
only configuration in which trust-cg compiles these programs at all. Not a
`run.py` results JSON, so not ledger evidence.
