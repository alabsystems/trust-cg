# The bounds-check raise trade, measured: correct on all 18, and it costs the vector class

> **CORRECTION (same day).** Both arms below ran with
> `-Ztrust-ir-cg-args=no-proof-certs`, which `benchmarks/beat-llvm/run.py` labels "a
> DIAGNOSTIC lane: the row is never evidence". These ratios are therefore **not** contract
> or ledger evidence against LLVM. They remain valid as a relative A/B — the knob skips
> per-compile lowering certificates, not any optimization, and only the subject knob differs
> between the arms — so the correctness verdicts and the scalar-vs-vector contrast stand,
> while the absolute parity reading does not. The evidence lane is unavailable on this host
> for a pre-existing reason; see `../2026-10-01-x86-evidence-lane-unavailable/`.

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · Reference: rustc's in-tree LLVM 22.1.2

## The question this answers

`wasm32_bounds_check_raises`'s own doc states the native lanes' position and then defers
the choice:

> Every other session keeps the [TCG-ASSERT-PANIC] refusal: the native AArch64/x86-64
> lanes trade this failure edge against the fused guard carrier their loop passes consume,
> **which is a separate decision**

The faithful route is already implemented and executed on wasm32
(`emit_bounds_check_panic_raise`: core's genuine `panic_bounds_check` lang item with
rustc's caller location, so the handler sees the real payload and location before the
abort). What was missing is the DATA for that decision — while the refusal holds, the
affected programs do not compile, so they cannot be measured at all.

This adds a tracked opt-in, `-Ztrust-ir-cg-args=bounds-check-panic-raise`, **DEFAULT
OFF**, letting a non-wasm32 `panic=abort` session take the existing route. It proposes no
default; it makes the trade measurable.

## 1. The default is unchanged

| arm | coverage | geomean vs LLVM -O3 |
|---|---|---|
| knob off (default) | **8/18 MATCH, 10 INCOMPLETE, 0 MISMATCH** | 0.951x over the 8 |
| knob on | **18/18 MATCH, 0 INCOMPLETE, 0 MISMATCH** | 1.750x (1.419x resolvable) |

## 2. With the opt-in, every program compiles and every one is CORRECT

**18/18 MATCH, zero MISMATCH, zero fail-closed.** The faithful raise is behaviourally
right on all ten programs the refusal was blocking.

## 3. The cost is real, and it is CONFINED to the vector class

Two independent cuts of the same data, and the second is the controlled one.

**(a) Within the raise-ON build** — one build, one dylib, so no era confound:

| class | geomean |
|---|---:|
| scalar | **0.981x** |
| vectorizable | **2.03x – 54.93x** |

| vectorizable program | raise ON |
|---|---:|
| v2_memfill | **54.925** |
| v3_popcount | **6.899** |
| v1_saxpy | **5.391** |
| p4_matmul | **2.533** |
| p7_sieve | **2.032** |

**(b) The 8 programs that compile in BOTH arms** — the knob is the only difference:

| program | off | on |
|---|---:|---:|
| m1_call_chain | 1.011 | 1.005 |
| m2_call_heavy | 0.754 | 0.760 |
| p1_xorshift | 1.001 | 1.001 |
| p2_collatz | 1.008 | 1.010 |
| p3_gcd | 0.892 | 0.894 |
| p5_struct_acc | 1.002 | 0.992 |
| p6_branch_match | 0.984 | 0.985 |
| p8_closure_nest | 0.990 | 1.007 |

Largest move is 1.7% (p8), i.e. noise. **The raise costs nothing where the loop passes
were not going to fire, and everything where they were.** That is precisely the mechanism
the doc names: the raise replaces the compare/assert pair the loop passes consume as a
fused guard carrier with a side-exit branch, and every vectorizer tier then declines.

For scale, a pre-refusal era run (`bl3`, 18/18, geomean 0.889x) had v3 at 0.103, v2 0.999,
v1 0.649, p7 0.700, p4 1.088 — so these programs were at or well under LLVM when the
carrier was intact. That run predates other knob changes (its compile geomean is 1.301x vs
1.144x here), so treat the cross-era deltas as indicative; cut (a) and cut (b) above are
the controlled evidence and neither depends on it.

## Conclusion: the refusal is VINDICATED, and the prerequisite is named

Upstream's choice to refuse rather than take this trade is right on this evidence.
Enabling the faithful route as-is would restore compilation by destroying vectorization on
exactly the programs that depend on it.

**So the real prerequisite is in `trust-cg-opt`, not the bridge**: the loop passes must
accept a panic-raise failure edge where they currently demand a pure `Ud2` trap
(`x86_trap_block::is_pure_trap_block`, the single definition shared by `x86_vectorize`,
`x86_bounds_check_elim`, `x86_branch_layout` and `x86_cmov_swap`). That analysis — each
consumer's own unreachability proof, the exact block shape to accept, and the two committed
negative tests that must be revisited deliberately rather than quietly widened — is in
`../2026-10-01-panic-cohort-blocks-the-loop-passes/`.

**This report supplies the number that makes that work worth doing: without it, the
faithful route costs 54.9x on v2_memfill; with the 8-program cut above showing the raise is
free elsewhere, the entire prize is in that one predicate.**

The knob stays default-off until then. Its value is that the trade is now a measurement
rather than an open question.
