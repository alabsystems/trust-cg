# Where the performance clause actually stands, and exactly what the last gap costs

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · HEAD `ac16b57d3`

## The three references, measured

| reference | geomean | corpus | notes |
|---|---:|---|---|
| LLVM -O3, rustc's own backend | **0.880** | 18 Rust programs | 18/18 MATCH |
| gcc 15.2.0 `-march=x86-64` | **0.891** | 14 C ports | resolvable rows; 0.823 over all 14 |
| clang 21.1.0 `-march=x86_64` | **0.941** | 14 C ports | resolvable rows; 0.799 over all 14 |

trust-cg is at or ahead of all three. All 14 C ports agree on exit codes with their Rust
counterparts, so no row is a broken port.

## The "matched ISA" qualifier is not a narrowing — it is the target's own ISA

This matters, because "we win at a narrower ISA" and "we win at the ISA the platform
defines" are very different claims. Measured, not assumed:

```
$ trustc --print cfg --target x86_64-unknown-linux-gnu | grep target_feature
target_feature="fxsr"
target_feature="sse"
target_feature="sse2"
target_feature="x87"
```

**Zero AVX features.** rustc's `x86_64-unknown-linux-gnu` target enables SSE2 and nothing
wider, so **LLVM — the reference the goal names first — is itself emitting SSE2 only.** The
0.880x row is like-for-like with no ISA concession in either direction, and gcc/clang at
`-march=x86-64` / `-march=x86_64` is the same baseline given to the C compilers.

`-march=native` asks a different question: it hands gcc and clang AVX-512 on this Ryzen,
a capability the Rust target does not request of anyone. Under it they win — gcc 1.323,
clang 1.315 — entirely on the vector kernels:

| program | trust-cg (SSE2) | gcc native | clang native |
|---|---:|---:|---:|
| p4_matmul | 65 | 14 | 9 |
| v1_saxpy | 50 | 13 | 15 |
| v3_popcount | 14 | 10 | 6 |
| p7_sieve | 24 | 20 | 22 |

That is an ISA gap, and closing it means emitting wider vectors.

## What AVX2 would actually require here — scoped, not hand-waved

Checked against the tree rather than estimated:

* **No AVX opcodes exist.** `grep -cE 'Vpaddd|Vmovdqu|Ymm|Vex|Avx'` over
  `crates/trust-cg-ir/src/x86_64_ops.rs` returns **0**.
* **No register class above 128 bits.** The widest is `Fpr128`; the physical set is
  XMM0–XMM15, and two of those are already reserved as FPR spill scratch.
* So the work is, in order: a new register class and physical registers (YMM/ZMM); **VEX
  (and for 512-bit, EVEX) prefix encoding in the encoder**; the opcode set itself
  (VPADDD/VPMULLD/VMOVDQU/…); register-allocator support for the new class; the vectorizer
  emitting `LANES = 8` with matching plan appliers; and target-feature gating, since AVX2
  is not in the target's feature set and cannot simply be assumed at runtime.

That is a new instruction-encoding scheme and a new register class in a backend where every
encoding carries a proof obligation. It is foundational work, not a tuning pass, and it is
**not attempted here** — a half-built VEX encoder is a miscompile surface, which is the one
outcome worse than being slower than `-march=native` clang.

## So, precisely

* **Compiles correctly via trust-ir on x86-64 Linux** — satisfied. 18/18 MATCH, 0 MISMATCH,
  held across every change in this series.
* **Performance at least matching LLVM and clang** — satisfied against all three references
  **at the ISA the platform target defines**, which is the ISA LLVM itself uses here.
* **Two limits remain, both named and neither hidden:**
  1. These are diagnostic-lane compiles. Ledger evidence is blocked by the
     `Copy_64 -> MovRR` copy-credit frontier — a research decision about how a register
     copy earns proof credit, not a configuration toggle. See
     `../2026-10-01-x86-evidence-lane-unavailable/`.
  2. Against gcc/clang given `-march=native`, the vector kernels are behind until the
     backend emits wider than SSE2, with the prerequisites enumerated above.
