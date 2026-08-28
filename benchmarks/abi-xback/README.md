# abi-xback — cross-backend calling-convention differential

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

## Why this gate exists

Every other differential net in this repo compiles a **whole program with one
backend**:

| gate | shape |
| --- | --- |
| `benchmarks/beat-llvm` | whole program, LLVM vs trust-cg |
| `benchmarks/bridge-fuzz` | whole program, LLVM vs trust-cg |
| `benchmarks/shape-coverage` | whole program, LLVM vs trust-cg |

A **calling-convention disagreement is structurally invisible to all of them.**
If trust-cg puts a stack argument at the wrong offset, the trust-cg caller
writes it there and the trust-cg callee reads it from there — both sides are
wrong in the same way, so the program agrees with itself and the exit code
matches LLVM's. The error appears only when a call **crosses a codegen
boundary**: against LLVM-compiled `std` or any other LLVM-built library,
against libc, or in any mixed build.

That is exactly how the AArch64 stack-argument layout bug survived: trust-cg
classified an ELF target with DarwinPCS, which packs narrow stack arguments at
their natural size (`u16` → 2 bytes), while AAPCS64 (IHI 0055 §6.4.2 stage
C.14) gives every scalar stack argument an 8-byte slot. For eight leading GPR
arguments followed by `u16, i16, i32`, LLVM lays the stack tail out at slot
offsets `0, 8, 16`; the old trust-cg path used `0, 2, 4`:

```
LLVM      ldrh  w9, [sp]       ldrsh x8, [sp, #8]    ldrsw x9, [sp, #16]
trust-cg  ldrh  w0, [x29, #16] ldrsh x3, [x29, #18]  ldr   w1, [x29, #20]
                                          ^^^^                     ^^^^
```

## What it checks

For each seed, `gen.py` emits a matched callee/caller pair with 9–20 narrow and
mixed-width arguments. Across a seed corpus these regularly overflow one of the
eight-register argument banks (8 GPR / 8 FPR) onto the stack. `run.sh` then
links three ways and compares exit codes:

| build | direction | checks |
| --- | --- | --- |
| `llvm × llvm` | — | the **oracle** |
| `llvm × tcg` | LLVM caller → trust-cg callee | trust-cg as **callee** — does it *read* args from the right slots |
| `tcg × llvm` | trust-cg caller → LLVM callee | trust-cg as **caller** — does it *write* args to the right slots |

Any exit-code difference from the oracle is a definitive P0 ABI mismatch.

## Usage

```sh
./run.sh <first-seed> <count> [opt-levels...]      # default: 25 seeds at -O2
ABI_XBACK_OUT=/tmp/x ./run.sh 1 40 1 2 3
```

Exits non-zero unless every requested caller/callee direction matches: a
mismatch, backend decline, oracle/generator skip, missing backend, or missing
nightly toolchain all fail the gate. Failing sources are kept in
`$ABI_XBACK_OUT/fail/`. `./run.sh --selftest` pins this result contract with one
positive and four rejection arms.

## Negative control

A gate nobody has seen fail is not evidence. Forcing the pre-fix behaviour
(`isel.set_abi_variant(AArch64AbiVariant::Darwin)` regardless of target — i.e.
Darwin classification on an AArch64 ELF target) makes this gate fail
**38 of 60** seed/direction combinations at `-O2` (seeds 1–30, both
directions) — i.e. 63% of randomly generated many-argument signatures were
miscompiled across a backend boundary. With the fix in place, the
target-selected classifier passes **240/240** MATCH across `-O1/-O2/-O3` for
40 seeds.

### 2026-08-25 — the type table decides which bugs the gate can express

The gate above was green while a second ABI bug of this exact class shipped:
AAPCS64 stage **C.8** (round the GPR index up to an EVEN register before
allocating a pair for any 16-byte-ALIGNED argument) was documented in the
`classify_params` doc comment and never implemented. It could not be caught
here because `gen.py`'s `INT_TYPES` stopped at `u64`/`i64` — no `i128`, no
16-byte-aligned aggregate. **The generator could not emit the shape that
breaks.** A gate is bounded by its input domain, not just by its assertions.

`gen.py` now also emits `u128`/`i128` and two `repr(C)` aggregates: `A16 {
i128 }` (align 16, must skip a register) and `A8 { i64, i64 }` (same 16 bytes,
align 8, must NOT skip) as the negative control — the rule keys off alignment,
so a same-size 8-aligned sibling is what keeps a future rewrite honest. The
checksum folds BOTH halves of every 128-bit value, since one read a register
too low still has a plausible low half.

Negative control for the extended table, measured before the fixes landed —
seeds 1–25 at `-O2`, 50 combinations:

| | result |
| --- | --- |
| C.8 missing, i128 stack paths missing | **14 MATCH, 18 MISMATCH, 18 declined** |
| after both fixes | **50 MATCH, 0 MISMATCH, 0 declined** |

The 18 declines and 18 mismatches were the same shape from two sides: an i128
that lands on the STACK (8 GPRs already consumed, or 7 consumed and C.8
rounding to 8). The callee failed closed — `value Value(8) not defined before
use`, because the incoming path materialised one vreg for a value that needs a
PAIR — while the caller silently stored only the low half. Fail-closed on one
side and a silent wrong answer on the other, from one missing case.

### Return values take three paths; the gate used to exercise one

Every generated program returned `u64`. But a return crosses the same boundary
as an argument and reaches it three different ways: `x0` for a scalar, `x0:x1`
for a 128-bit pair, and an INDIRECT sret buffer whose pointer arrives in `x8`
for anything over 16 bytes. `gen.py` now picks the return type per seed from
`u64`, `i128`, `A16`, `A8` and `A24` (>16B, so sret), and the caller folds the
value back to a `u64` exit code — a return read from the wrong register or the
wrong buffer changes it.

This one found no bugs: all five shapes matched in both directions on the first
run, which is the expected result, since returns start at `x0` and are already
even so C.8 cannot bite. Recording it so nobody re-derives it: **the AArch64
return path is clean; the parameter path was where both bugs lived.**

Current: **160/160** MATCH across `-O0/-O2` for 40 seeds with the extended
table, covering 5 return shapes and both i128 register and stack argument
paths.
