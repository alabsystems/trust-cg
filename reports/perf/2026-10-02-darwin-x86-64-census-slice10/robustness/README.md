# Slice 10 mutation robustness probe (2026-10-02)

This probe tests whether the slice-10 whole-body theorem (checked
arithmetic, `not`, `neg`, `popcnt`, shifts by CL and `call r64`) ever
credits a wrong machine stream as Formal. Each slice-10 fixture's real
pre-RA stream is mutated, and every mutant is judged three ways:

- by the owner, `source_bound_x86_body`;
- by the solver-free sampler of the library gate (`slice10::theorem_refuted`)
  and by the replayed theorem (`ay --strict-proofs`, then Clean) with the
  verifier's crediting;
- by an independent concrete interpreter of the LIR and of the x86 stream,
  which serves as ground truth.

The probe is diagnostic only and is not a gate.

**Result: no wrong stream was credited.** Of the 1230 mutants, 1041 are wrong
by ground truth, and none of those received a Verified replay or credit:
10 make no claim, 551 are named mismatches and 480 are refuted by both the
sampler and AY. 81 streams were credited (25 originals and 56 mutants), and
every one is correct by ground truth: a condition that agrees on a 0/1
value, `seto` for `setb` after an instruction that sets CF = OF, a dead
copy dropped, an `and` mask that keeps the only live bit.

**The sampler refutes everything AY refutes.** In every class the number of
theorems AY refutes with a counterexample equals the number the sampler
refutes (column "CE not sampled" is 0 everywhere). Of the 595 theorems
built, 484 are AY counterexamples, 82 are AY Valid and 29 end as AY's
strict self-check rejection; those 29 are all multiply streams (below).

## Setup

- **Tree:** `feat/x86-body-slice10-instructions` at `99c2ca5cf` plus the
  sampler strengthening committed with this report (the owner is the
  committed one).
- **Replay:** stage-1 AY 0.27.0 build 10530 (`d14080122`, sha256
  `9a149c35…`) with `~/clean-checker/bin/clean` (Clean 5f09e36c, sha256
  `949365b6…`), through `fails-before/qualify.sh`.
- **Wall time:** 312 s with replay, 42 s without.
- **Base streams:** O0 selector output for all 25 fixture shapes, plus each
  distinct O1, O2 and O3 optimizer output (`AddI32`, `AddPanics`,
  `MulPanics` and `ShlChecked` at O1; every other optimized stream equals
  one already listed): 29 streams. 28 match the source by ground truth; 25
  replay Verified and are credited; the three 64-bit multiply shapes at O0
  are the recorded AY gap. `MulPanics` at O1 tests the carry with `bt`,
  which neither the owner (no claim) nor the interpreter models; all 69 of
  its mutants make no claim.
- **Mutation classes:** C1 a flag reader's condition replaced by every
  other; C2 the operands of `add`/`sub`/`imul`/`cmp` swapped; C3 another
  operation of the same shape (`sub`/`imul`/`or` for `add`, `neg`/`popcnt`/
  a move for `not`, the other shifts, sign for zero extension, `or`/`xor`
  for the tied `and`); C4 an ABI or implicit register (RDI, RSI, RDX, RAX,
  RCX) replaced by another; C5 a source register replaced by an earlier
  virtual register of its class (`mul`'s and `call r64`'s only operand
  too); C6 a value row dropped; C7 another immediate; C8 a reader of a
  modelled flag writer (`add`, `sub`, `imul`, `mul`) with the condition's
  other signedness, or reading a flag the writer leaves undefined.
- **Ground truth:**
  - LIR: checked arithmetic is Rust's `overflowing_*` at the operand width
    and signedness, `Bnot` `!x`, `Ineg` `wrapping_neg`, `CtPop`
    `count_ones`. A shift by a variable amount is trust-ir's below the width
    and undefined at or above it: an input that reaches one is skipped, so
    it judges nothing.
  - Machine, from the Intel SDM rather than from either translator: `add`
    and `sub` set CF to the carry or borrow and OF to the signed overflow,
    `imul` sets CF = OF to "the signed product does not fit", `mul` writes
    RDX:RAX (EDX:EAX, each zero-extended) and sets CF = OF to "the high half
    is not zero". A flag the SDM leaves undefined is fresh garbage, as is
    every flag after any other ALU row but `cmp`, `test`, `and`, `or`,
    `xor`. A shift by CL uses the low byte of RCX masked to 5 bits (6 for a
    64-bit operand). `call r64` calls the function the register's 64 bits
    name.
  - A callee is a deterministic pseudo-random function of its identity (a
    symbol, or the pointer value an indirect call goes through) and the
    bits its parameters own. A virtual register's bits above a narrow write
    are garbage; a physical register's 8- or 16-bit write keeps the bits
    above.
  - Each mutant runs on 3000 inputs. Each register is drawn per input from
    one of: uniform random; a value below 16 or below 72; a shift-count edge
    (0, 1, 2, 7, 8, 15, 16, 31, 32, 33, 63, 64); an edge word (0, 1, all
    ones, the signed minimum and maximum, the 32-bit and 8-bit edges, and
    the repeating patterns `0x5555…`, `0xaaaa…`, `0x3333…`, `0xcccc…`); a
    random word with alternate bytes or halves cleared, or with the sign bit
    set; zero. One input in eight gives every register the same word. Observables: the returned
    bits a caller reads, the call log (callee and argument bits), incoming
    accesses and final incoming memory, and the callee-saved registers.

## Table

`unsup` = owner unsupported (no claim); `mism` = named mismatch; `thm` =
theorem built; `smp` = refuted by the solver-free sampler; `CE` / `Valid` /
`other` = the AY replay; `cred` = every covered row Formal; `wrong` = wrong
by ground truth; `w-cred` = wrong and credited or Valid; `ok-ref` = correct
by ground truth and refuted; `n/a` = ground truth has no model (the `bt`
row).

| Mutation class | n | unsup | mism | thm | smp | CE | CE not sampled | Valid | other | cred | wrong | w-cred | ok-ref | n/a |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| C0 original | 29 | 1 | 0 | 28 | 0 | 0 | 0 | 25 | 3 | 25 | 0 | **0** | 0 | 1 |
| C1 wrong condition code | 105 | 0 | 0 | 105 | 94 | 94 | 0 | 8 | 3 | 8 | 94 | **0** | 0 | 0 |
| C2 operands swapped | 11 | 0 | 2 | 9 | 2 | 2 | 0 | 6 | 1 | 6 | 4 | **0** | 0 | 0 |
| C3 wrong operation | 97 | 12 | 4 | 81 | 61 | 61 | 0 | 16 | 4 | 15 | 75 | **0** | 0 | 2 |
| C4 ABI or implicit register replaced | 420 | 20 | 340 | 60 | 44 | 44 | 0 | 8 | 8 | 8 | 384 | **0** | 0 | 20 |
| C5 wrong source register | 157 | 4 | 14 | 139 | 132 | 132 | 0 | 7 | 0 | 7 | 144 | **0** | 2 | 4 |
| C6 row dropped | 192 | 14 | 155 | 23 | 12 | 12 | 0 | 6 | 5 | 6 | 167 | **0** | 0 | 9 |
| C7 wrong immediate | 54 | 3 | 0 | 51 | 43 | 43 | 0 | 6 | 2 | 6 | 41 | **0** | 2 | 3 |
| C8 signedness or width of the flag reader | 165 | 30 | 36 | 99 | 96 | 96 | 0 | 0 | 3 | 0 | 132 | **0** | 0 | 30 |

Every named mismatch is on a mutant that is wrong by ground truth.

## Conservative outcomes (correct mutants not credited)

39 mutants that are correct by ground truth are not credited:

- **29 multiply streams end as AY's self-check rejection.** The three 64-bit
  multiply shapes at O0 and 26 of their mutants that ground truth finds
  equivalent (a dead copy of RAX after `mul` retargeted or dropped, `seto`
  for `setb` after `mul`/`imul`, the operands of `imul` swapped, `movsx` for
  `movzx` of a 0/1 byte, an `and` mask of a 0/1 value widened). This is the
  recorded multiply gap (`KNOWN_UNCERTIFIED_SLICE_TEN`), not a refutation.
- **4 refuted where trust-ir is undefined.** `ShlU8` and `SarI16` with the
  narrow count's mask changed to all ones (C7) or the shift reading the
  unmasked count (C5). They differ from the source only at an amount at or
  above the width, where trust-ir has undefined behaviour and ground truth
  skips the input; the theorem states the refinement "amount modulo the
  width" there (the selector's masked lowering) and refutes them. This is
  the deliberate strictness the main README records.
- **5 make no claim (C6).** Dropping a `cmp` or `test` leaves a `setcc`
  reading flags of a row whose flags the walk does not model.
- **1 partial credit (C3).** `SarI16` with `shr` for `sar`: the operand is
  sign-extended to 32 bits and the count masked to 4 bits, so the low 16
  bits agree. AY replays the theorem Valid, but the TV-2 provenance
  cross-check of the changed row fails, so 7 of 8 rows are Formal and the
  function is not credited.

## Findings

**The first ground truth was too weak.** It drew its registers mostly at
random, so a shift amount was almost always at or above the width (an
input it skipped) and boundary inputs never occurred (two zero addends,
which separate `setbe` from `setb` after an add; an amount of exactly 32
at a checked shift's range compare). It judged 16 sampler-refuted mutants
correct (`setbe`/`seta` for `setb`/`setae` after an add or a shift check,
`neg` for `not` in the 32-bit signed-add fallback, `sar` for `shr` and the
reverse, `movzx` for `movsx` before a narrow arithmetic shift, and the
bound of a checked shift's range compare changed from 32 to 16, 33 or 288,
each differing only at amounts from 16 to 287). With the per-register
draws above and 3000 inputs, all 16 are wrong by ground truth and refuted;
the four left are the undefined-input cases.

**The sampler missed one needle that AY refuted.** In the first replay,
`AddI32` at O0 with `mov v7, -1` for `mov v7, 0` (C7) was refuted by AY and
not by the sampler. The mutant reads "`v6 < -1`" instead of "`v6 < 0`" for
the fallback's overflow word `v6 = !(a ^ b) & (a ^ (a + b))`, which differs
only where `v6` is all ones, that is only at `a = b = 0x55555555`. The
sampler's edge words had no repeating bit pattern and it drew operands
independently. It now has `0x5555…`, `0xaaaa…`, `0x3333…` and `0xcccc…`
among its edge words and, on odd seeds, gives every input the same word
(`slice10::edge_word`); ground truth has the same patterns. After the fix
the sampler refutes it, ground truth counts it wrong (C7 wrong 40 to 41),
and "CE not sampled" is 0 in every class. No wrong stream was credited
before the fix either (AY refuted this one).

## Reproduce

Plug the probe in as a child of the x86 body test module, next to
`mod slice10;` in `crates/trust-cg-verify/src/x86_source_bound_body_tests.rs`:

```rust
#[path = "../../../reports/perf/2026-10-02-darwin-x86-64-census-slice10/robustness/x86_source_bound_body_slice10_robust_tests.rs"]
mod slice10_robust;
```

Then run it with the qualification toolchain's AY and Clean:

```sh
zsh reports/perf/2026-10-02-darwin-x86-64-census-slice10/fails-before/qualify.sh \
  <log> x86_source_bound_body::tests::slice10_robust:: --ignored --test-threads=1
```

- `ROB10_NO_REPLAY=1` skips the solver. The AY columns are then empty, and
  the sampler column still fills.
- `ROB10_ONLY=<shape>` restricts the run to the fixture shapes whose name
  contains it.

Logs: `robustness_replay.log` and `robustness_no_replay.log` in
[PAYLOADS.md](../PAYLOADS.md).
