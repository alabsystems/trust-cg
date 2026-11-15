# Slice 15 mutation robustness probe (2026-10-06)

This probe tests whether the slice-15 whole-body theorem (float constants
and sign-bit operations, registers of mixed width, a forwarded `bool`
parameter, accesses through an address that may derive from an escaped
slot, an `I128` in the stack argument areas) ever credits a wrong machine
stream as Formal. Each slice-15 fixture's real pre-RA stream is mutated,
and every mutant is judged three ways:

- by the owner, `source_bound_x86_body`;
- by the solver-free sampler of the library gate (`slice11::theorem_refuted`,
  the structured sampler every slice since 11 uses) and by the replayed
  theorem (`ay --strict-proofs`, then Clean) with the verifier's crediting;
- by an independent concrete interpreter of the LIR and of the x86 stream,
  which serves as ground truth.

The probe is diagnostic only and is not a gate.

**Result: no wrong stream was credited.** Of the 1341 mutants (24 base
streams included), 969 are wrong by ground truth, and none of those
received a Verified replay or credit: 144 make no claim, 408 are named
mismatches and 417 are refuted by both the sampler and AY. 222 streams
were credited (24 originals and 198 mutants), and every one is correct by
ground truth.

**The sampler refutes everything AY refutes.** In every class the number
of theorems AY refutes with a counterexample equals the number the sampler
refutes (column "CE not sampled" is 0 everywhere): 467 of 467. Every
theorem built either replays Valid (222) or is an AY counterexample (467).

## Setup

- **Tree:** `feat/x86-body-slice15-residue`, the owner's code as committed
  in `448e38848` (later commits change its comments only), with the probe
  plugged in as below.
- **Replay:** AY 0.27.0 build 12713 (`b1b0b9de0`) with Clean 5f09e36c,
  through the x86-stage1-ay12713 overlay, the lane's qualification
  toolchain.
- **Wall time:** 709 s with replay (on a shared host, with a bridge build
  running).
- **Base streams:** O0 selector output for all 22 fixture shapes, plus
  each distinct O1, O2 and O3 optimizer output (`ThreeBytes` and
  `DerivedLoadOffset` at O1; every other optimized stream equals its O0
  one): 24 streams.
- **Mutation classes:** as in the slice-13 probe, C1 a flag reader's
  condition replaced by every other; C2 the two source operands of a
  three-address row swapped; C3 another operation of the same shape (now
  also `pxor`, `andps` and `andpd` for one another, and the constant-pool
  `movss` and `movsd` for each other); C4 an ABI register operand replaced
  by another of its register file; C5 a source register replaced by an
  earlier virtual register of its class; C6 a value row dropped; C7 another
  immediate; C8 a memory operand's displacement moved by -8, -4, +4 or +8
  bytes; C9 an atomic row's proof origin dropped; and, new:
  - C10 a constant-pool entry with one bit flipped (bit 0, 22, 31, 51 or
    63, where the entry has it: payload, exponent and sign bits);
  - C11 a `bool` parameter's entry `movzx` replaced by the 32-bit copy the
    selector emitted before slice 15;
  - C12 a general-purpose register operand of a `mov`, `add`, `and`, `or`
    or `xor` row flipped between its 32- and 64-bit widths;
  - C13 a word stored into private slot 0 just before each incoming load
    or store after the first call (a slot written behind an access through
    a derived address).
- **Ground truth** (independent of the owner: none of its float, width,
  `bool`, retention or placement rules is reused). As in the slice-13
  probe: concrete bytes, the slot binding, a concrete frame and stack
  pointer, callees as deterministic pseudo-random functions of their
  identity, the bits their parameters own and the bytes of every slot they
  can REACH (by the probe's own reachability). In addition:
  - Floats: a constant is `(imm as f32).to_bits()` or `imm.to_bits()`, and
    `Fneg`/`Fabs` are Rust's `-x` and `x.abs()` on the bit pattern; the
    machine reads a constant-pool entry's bytes and runs `pxor`/`andps`/
    `andpd` on whole 128-bit registers.
  - Callees return pointers into a slot they can reach, into incoming
    memory or anywhere, and when they overwrite a reachable slot they write
    such pointers into it too, so a load or store through what they
    returned or left really reaches an escaped slot sometimes.
  - A row of mixed register widths runs as the encoder emits it, with
    REX.W: all 64 bits, and a 32-bit virtual register read at 64 bits holds
    garbage above bit 31.
  - Each input picks a caller convention: a psABI caller clears bits 1..7
    of a `bool` argument register only and reads AL of a `bool` result; a
    clean-bool caller clears bits 1..31 and reads EAX. A callee reads a
    `bool` argument as the clean 32-bit bool.
  - An `I128` past the integer registers lies in two eightbytes of the
    stack areas, the first 16-byte aligned.
  - Each mutant runs on 3000 inputs, drawn as in the slice-11 probe.
    Observables: the returned bits a caller reads, the call log (callee,
    argument bits and the bytes of the slots it can reach), incoming
    accesses and final incoming memory, the callee-saved registers and RSP
    at the return.

## Table

`unsup` = owner unsupported (no claim); `mism` = named mismatch; `thm` =
theorem built; `smp` = refuted by the solver-free sampler; `CE` / `Valid` /
`other` = the AY replay; `cred` = every covered row Formal; `wrong` = wrong
by ground truth; `w-cred` = wrong and credited or Valid; `ok-ref` = correct
by ground truth and refuted; `n/a` = ground truth has no model.

| Mutation class | n | unsup | mism | thm | smp | CE | CE not sampled | Valid | other | cred | wrong | w-cred | ok-ref | n/a |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| C0 original | 24 | 0 | 0 | 24 | 0 | 0 | 0 | 24 | 0 | 24 | 0 | **0** | 0 | 0 |
| C1 wrong condition code | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **0** | 0 | 0 |
| C2 operands swapped | 6 | 0 | 0 | 6 | 4 | 4 | 0 | 2 | 0 | 2 | 4 | **0** | 0 | 0 |
| C3 wrong operation | 47 | 15 | 1 | 31 | 18 | 18 | 0 | 13 | 0 | 13 | 32 | **0** | 0 | 0 |
| C4 ABI register replaced | 354 | 8 | 166 | 180 | 94 | 94 | 0 | 86 | 0 | 86 | 258 | **0** | 0 | 0 |
| C5 wrong source register | 170 | 26 | 4 | 140 | 132 | 132 | 0 | 8 | 0 | 8 | 161 | **0** | 1 | 0 |
| C6 row dropped | 194 | 7 | 117 | 70 | 38 | 38 | 0 | 32 | 0 | 32 | 161 | **0** | 0 | 0 |
| C7 wrong immediate | 89 | 28 | 3 | 58 | 40 | 40 | 0 | 18 | 0 | 18 | 71 | **0** | 0 | 0 |
| C8 wrong memory displacement | 216 | 32 | 144 | 40 | 38 | 38 | 0 | 2 | 0 | 2 | 192 | **0** | 0 | 0 |
| C9 atomic origin dropped | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **0** | 0 | 0 |
| C10 constant-pool bit flipped | 47 | 0 | 0 | 47 | 46 | 46 | 0 | 1 | 0 | 1 | 46 | **0** | 0 | 0 |
| C11 `bool` parameter not zero-extended | 3 | 0 | 0 | 3 | 3 | 3 | 0 | 0 | 0 | 0 | 3 | **0** | 0 | 0 |
| C12 register width flipped | 174 | 93 | 0 | 81 | 45 | 45 | 0 | 36 | 0 | 36 | 36 | **0** | 45 | 0 |
| C13 escaped slot written before an access | 17 | 0 | 8 | 9 | 9 | 9 | 0 | 0 | 0 | 0 | 5 | **0** | 4 | 0 |

The fixtures have no flag reader and no atomic row, so C1 and C9 are
empty. Every C11 mutant (the pre-slice-15 selector's entry copy, at
`ForwardBool`, `ForwardBoolMixed` and `ForwardBoolReturn`) is wrong for a
psABI caller and refuted by both the sampler and AY. The one credited C10
mutant is correct: `NegAbsBits` computes `abs(-x)`, and with the negation
mask's sign bit cleared the `pxor` is the identity, which the `andpd`
that follows makes irrelevant.

## Conservative outcomes (correct mutants not credited)

150 correct mutants are not credited, each fail-closed by rule:

- **65 make no claim.** 57 C12 width flips leave the stream outside the
  lane: 52 name one virtual register at two widths, and 5 read a private
  address through a mixed-width `mov` (which lets the slot escape, no
  claim); 6 C8 mutants move a dead read of a stack
  parameter (`d` of `StackParamI128ThenScalar`, which returns `e`) off
  every parameter's displacement (an RBP access that reads no stack
  parameter makes no claim); `NegAbsBits` with the negation mask
  loaded by `movss` (its zero low half: the identity again) reads a
  constant-pool entry at another size; and `DerivedLoadOffset`'s `or` for
  an `add` of disjoint address bits is a row form outside the lane.
- **35 are named mismatches.** 16 C8 and 8 C13 mutants access a 3-byte
  slot of `ThreeBytes` outside its bytes (the owner names every access
  outside a private slot); 10 C4 mutants and 1 C6 mutant read a register
  no row defined (an unused register parameter's copy from RAX, a dropped
  dead copy), which the owner names whatever its use.
- **50 are refuted.** 45 C12 mutants flip a physical operand of a `mov`
  between `edi` and `rdi` (or the like): the encoder's REX.W row moves all
  64 bits either way, but the owner's mixed-width rule keeps only the low
  32 bits and states the bits above as a free input, so a 64-bit value
  through such a row is refuted (stronger than the encoding needs). 4 C13
  mutants write a word of `DerivedLoadOffset`'s escaped slot that no later
  read reaches in the probe's world; the theorem observes every escaped
  byte at a derived access (OD-114), which is stronger than needed. 1 C5
  mutant of `ForwardBoolReturn` returns the parameter instead of `flip`'s
  result, which the probe's one concrete `flip` (a fixed pseudo-random
  function of its argument) happens to make the identity; for an arbitrary
  callee it is wrong.

## Findings

**No credit hole.** Building the probe found only ground-truth defects,
fixed in the run above (the first run, sampler only, payload
`robustness_no_replay_first.log`): the probe's callee masked a `bool`
argument to its bit 0 (so a forwarded raw register looked correct: the 3
C11 mutants and 14 C4 and C6 mutants of the forwarding fixtures were judged
correct, and refuted), and its de-duplication of mutants ignored the
constant pool (so every C10 mutant was dropped as a copy of its
original). After these fixes no original is wrong and no credited stream is
wrong.

## Reproduce

Plug the probe in as a child of the x86 body test module, next to
`mod slice15;` in `crates/trust-cg-verify/src/x86_source_bound_body_tests.rs`:

```rust
#[path = "../../../reports/perf/2026-10-06-darwin-x86-64-census-slice15/robustness/x86_source_bound_body_slice15_robust_tests.rs"]
mod slice15_robust;
```

Then run it with the qualification toolchain's AY and Clean:

```sh
zsh reports/perf/2026-10-06-darwin-x86-64-census-slice15/fails-before/qualify.sh \
  <log> x86_source_bound_body::tests::slice15_robust:: --ignored
```

- `ROB15_NO_REPLAY=1` skips the solver. The AY columns are then empty, and
  the sampler column still fills.
- `ROB15_ONLY=<text>` restricts the run to the fixture shapes whose name
  contains it.

Logs: `robustness_replay.log` (this table) and
`robustness_no_replay_first.log` in [PAYLOADS.md](../PAYLOADS.md).
