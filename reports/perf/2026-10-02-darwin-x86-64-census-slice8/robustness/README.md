# Slice 8 mutation robustness probe (2026-10-02)

This probe tests whether the slice-8 whole-body theorem (aggregates in
general-purpose registers) ever credits a wrong machine stream as Formal.
Each slice-8 fixture's real pre-RA stream is mutated, and every mutant is
judged three ways:

- by the owner, `source_bound_x86_body`;
- by the solver-free sampler of the library gate (`slice8::theorem_refuted`)
  and by the replayed theorem (`ay --strict-proofs`, then Clean) with the
  verifier's crediting;
- by an independent concrete interpreter of the LIR and of the x86 stream,
  which serves as ground truth.

The probe is diagnostic only and is not a gate.

**Result: no wrong stream was credited.** Of the 2383 mutants, 1795 are wrong
by ground truth, and none of those received a Verified replay or credit.
271 streams were credited (the 40 originals and 231 mutants), and every one
is correct by ground truth: an equivalent register or extension where the
difference is never observed (a sign extension of a byte the caller reads at
8 bits), a dead row dropped, a store of bytes nothing reads.

**The sampler refutes everything AY refutes.** In every class the number of
theorems AY refutes with a counterexample equals the number the sampler
refutes (column "AY CE not sampled" is 0 everywhere), and every built theorem
ended as an AY counterexample or AY Valid (no timeout, no rejected proof).

## Setup

- **Tree:** `feat/x86-body-slice8-aggregate-registers` at `e6dd83f85` (the
  owner; the probe and the sampler as committed with this report).
- **Replay:** stage-1 AY 0.27.0 build 10530 (`d14080122`, sha256
  `9a149c35…`) with `~/clean-checker/bin/clean` (Clean 5f09e36c, sha256
  `949365b6…`), through `fails-before/qualify.sh`.
- **Wall time:** 195 s with replay, 34 s without.
- **Base streams:** O0 selector output for all 22 fixture shapes, plus each
  distinct O1, O2 and O3 optimizer output: 40 streams. Ground truth matches
  the source on all 40, and all 40 replay Verified and are credited.
- **Ground truth:**
  - An aggregate of `n` bytes travels in `ceil(n / 8)` registers, eightbyte
    `k` in the low `min(8, n - 8k)` bytes of the `k`-th; the rest of each
    register is the sender's garbage. This placement is the interpreter's
    own rule, written from psABI §3.2.3 for INTEGER eightbytes, not taken
    from either classifier.
  - A callee is a deterministic pseudo-random function of its name and the
    bytes its parameters own. An aggregate result's bytes are pseudo-random,
    with a zero low prefix (a zero tag beside a nonzero payload) in one call
    of four, and the register bits above them are garbage.
  - A virtual register's bits above an 8- or 16-bit write are garbage
    (register allocation may place it anywhere). A physical register's 8-
    or 16-bit write keeps the bits above, as the hardware does.
  - Each mutant runs on 400 inputs. Observables: the bits a caller reads of
    the return (a scalar at its return bits, an aggregate's own bytes in RAX
    and RDX), the call log (callee and the bytes it may read), incoming
    accesses and final incoming memory, and the callee-saved registers.

## Table

`unsup` = owner unsupported (no claim); `mism` = named mismatch; `thm` =
theorem built; `smp` = refuted by the solver-free sampler; `CE` / `Valid` =
the AY replay; `cred` = every covered row Formal; `wrong` = wrong by ground
truth; `w-cred` = wrong and credited or Valid; `ok-ref` = correct by ground
truth and refuted.

| Mutation class | n | unsup | mism | thm | smp | CE | CE not sampled | Valid | cred | wrong | w-cred | ok-ref |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| C0 original | 40 | 0 | 0 | 40 | 0 | 0 | 0 | 40 | 40 | 0 | **0** | 0 |
| C1 wrong eightbyte register | 390 | 0 | 279 | 111 | 61 | 61 | 0 | 50 | 50 | 328 | **0** | 0 |
| C2 wrong offset (swapped halves) | 887 | 0 | 616 | 271 | 265 | 265 | 0 | 6 | 6 | 725 | **0** | 0 |
| C3 wrong access width | 354 | 74 | 66 | 214 | 177 | 177 | 0 | 37 | 37 | 171 | **0** | 6 |
| C4 sign/zero extension swapped | 59 | 0 | 0 | 59 | 7 | 7 | 0 | 52 | 52 | 7 | **0** | 0 |
| C5 wrong source register | 249 | 64 | 16 | 169 | 123 | 123 | 0 | 46 | 46 | 201 | **0** | 0 |
| C6 row dropped | 388 | 1 | 271 | 116 | 76 | 76 | 0 | 40 | 40 | 347 | **0** | 0 |
| C7 wrong shift amount | 10 | 0 | 0 | 10 | 10 | 10 | 0 | 0 | 0 | 10 | **0** | 0 |
| C8 tied form as a move | 6 | 0 | 0 | 6 | 6 | 6 | 0 | 0 | 0 | 6 | **0** | 0 |

Of the 1795 wrong mutants, 62 make no claim, 1014 are named mismatches and
719 are refuted by both the sampler and AY.

## Conservative outcomes (correct mutants not credited)

240 correct mutants are not credited:

- **222 named `StackSlotBounds` mismatches.** An access moved past its
  slot's size (C2 and C3). The interpreter gives each slot a 64 KiB region,
  so the access harms nothing there; the real frame packs slots, so the
  owner's rule (a machine access outside its slot is a mismatch) is right.
- **12 named undefined reads of RAX or RDX** (C1). The mutant reads a result
  register no call defined, into bytes nothing observes. Reading an
  undefined physical register is never a correct lowering's form.
- **6 refuted** (C3). A byte or word load into a physical register (`mov
  al, m8`) where the register already held the right bits above: the
  hardware keeps them, and the walk treats them as a free input (the
  narrow-load rule, which is exact for a virtual register and conservative
  for a physical one).

## Finding

**The first ground-truth callee was too weak.** It zeroed an aggregate
result's whole first eightbyte at once, so it never produced "zero tag,
nonzero payload". Six C2 mutants of `CallResultBranch` (the tag read at
offset 1, 2 or 4 instead of 0) were judged correct by the interpreter while
the sampler and AY refuted them. The interpreter now zeroes a random low
prefix of the eightbyte, and those six are wrong by ground truth and refuted
(the table above is after the fix). The sampler was already strong enough:
its structured partial zeroing (`slice8::zeroed_byte`) zeroes the bytes of
every input below or above a boundary that steps through every byte of a
word.

## Reproduce

Plug the probe in as a child of the x86 body test module, next to
`mod slice8;` in `crates/trust-cg-verify/src/x86_source_bound_body_tests.rs`:

```rust
#[path = "../../../reports/perf/2026-10-02-darwin-x86-64-census-slice8/robustness/x86_source_bound_body_slice8_robust_tests.rs"]
mod slice8_robust;
```

Then run it with the qualification toolchain's AY and Clean:

```sh
zsh reports/perf/2026-10-02-darwin-x86-64-census-slice8/fails-before/qualify.sh \
  <log> x86_source_bound_body::tests::slice8_robust:: --ignored --test-threads=1
```

- `ROB8_NO_REPLAY=1` skips the solver. The AY columns are then empty, and
  the sampler column still fills.
- `ROB8_ONLY=<shape>` restricts the run to one fixture shape.
