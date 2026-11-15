# Slice 11 mutation robustness probe (2026-10-03)

This probe tests whether the slice-11 whole-body theorem (`I128` register
pairs with `adc`/`sbb` and the tied shifts by CL, and float bit patterns in
SSE registers) ever credits a wrong machine stream as Formal. Each slice-11
fixture's real pre-RA stream is mutated, and every mutant is judged three
ways:

- by the owner, `source_bound_x86_body`;
- by the solver-free sampler of the library gate (`slice11::theorem_refuted`)
  and by the replayed theorem (`ay --strict-proofs`, then Clean) with the
  verifier's crediting;
- by an independent concrete interpreter of the LIR and of the x86 stream,
  which serves as ground truth.

The probe is diagnostic only and is not a gate.

**Result: no wrong stream was credited.** Of the 3602 mutants (51 base
streams included), 2419 are wrong by ground truth, and none of those
received a Verified replay or credit: 633 make no claim, 773 are named
mismatches and 1013 are refuted by both the sampler and AY. 450 streams
were credited (42 originals and 408 mutants), and every one is correct by
ground truth: any condition of a `cmov` whose two inputs coincide at the
fixture's constant shift count, the operands of a commutative row or of a
row no observable reads swapped, such a row changed, retargeted or
dropped, an immediate whose changed bits no observable reads.

**The sampler refutes everything AY refutes.** In every class the number of
theorems AY refutes with a counterexample equals the number the sampler
refutes (column "CE not sampled" is 0 everywhere): 1016 of 1016. Of the
1485 theorems built, 1016 are AY counterexamples, 455 are AY Valid and 14
end otherwise (10 `u128` multiply streams time out, the recorded gap; 4
are below).

## Setup

- **Tree:** `feat/x86-body-slice11-wide-float` at `d7b2c3534` (the owner and
  sampler committed there), with the probe plugged in as below.
- **Replay:** stage-1 AY 0.27.0 build 10530 (sha256 `9a149c35…`) with
  `~/clean-checker/bin/clean` (Clean 5f09e36c), the qualification
  toolchain.
- **Wall time:** 2670 s with replay (on a shared host, with a census running
  for part of it), 714 s without (the first ground truth, below).
- **Base streams:** O0 selector output for all 36 fixture shapes, plus each
  distinct O1, O2 and O3 optimizer output: 51 streams. At O1 and O2 the
  optimizer turns the zero constant of the four `I128` shift and negate
  bodies into the zero idiom `xor r, r`, a two-operand form outside the
  walk's lane, so those 8 streams and their mutants make no claim.
- **Mutation classes:** C1 a flag reader's condition (`setcc`, `cmovcc`,
  `jcc`) replaced by every other; C2 the two source operands of a
  three-address row swapped; C3 another operation of the same shape (`adc`
  for `add` and the reverse, `sbb` for `sub` and the reverse, `adc`/`sbb`
  swapped, the other direction or signedness of a shift, `movss` for
  `movsd` and the reverse, `movd` for `movq` and the reverse in either
  direction, the other SSE load or store width, `movsx` for `movzx`); C4 an
  ABI register operand (RDI, RSI, RDX, RCX, R8, R9, RAX, XMM0-XMM2) replaced
  by another of its register file; C5 a source register replaced by an
  earlier virtual register of its class; C6 a value row dropped; C7 another
  immediate; C8 a memory operand's displacement moved by -8, -4, +4 or +8
  bytes.
- **Ground truth:**
  - LIR: values are Rust integers of their width up to `u128`; add,
    subtract and multiply wrap; compares are signed or unsigned at the
    width; a shift by an amount below the width shifts (at or above it
    trust-ir is undefined, and an input that reaches one judges nothing);
    an `I128` `Iconst` is its immediate sign-extended and `Iconst128` is
    `(hi << 64) | lo`; a `Bitcast` keeps the bits. A 16-byte load or store
    is its two 8-byte halves, low first, each classified as private or
    incoming at its own address (a non-atomic access's granularity is not
    observable).
  - Placement is the interpreter's own: an `I128` takes the next two
    integer registers, low half first, a float the next of XMM0-XMM7, a
    result RAX:RDX or XMM0 (an integer lane beside a float one in RAX). A
    `bool` parameter's register satisfies the psABI `_Bool` rule (bit 0 the
    value, bits 1 to 7 zero, the bits above anything).
  - Machine, from the Intel SDM rather than from either translator: `adc d,
    a, b` is `a + b + CF` and `sbb d, a, b` is `a - b - CF`, each setting CF
    to the unsigned carry or borrow and OF to the signed overflow; `add`,
    `sub`, `cmp`, `test`, `and`, `or` and `xor` set their flags and every
    other ALU row leaves garbage flags; a shift by CL shifts by the low
    byte of RCX masked to 5 or 6 bits (a zero count keeps the flags);
    `movss`/`movsd` between registers copy the low 32 or 64 bits (a virtual
    destination's bits above are garbage, register allocation's pure
    definition; a physical one keeps them, the hardware merge); SSE loads
    zero the bits above; `movd`/`movq` to a general-purpose register take
    the low 32 (zero-extended) or 64 bits, and to an XMM register
    zero-extend; a call clobbers every caller-saved general-purpose
    register and every XMM register.
  - A callee is a deterministic pseudo-random function of its identity and
    the bits its parameters own (an `I128` result is sometimes all ones or
    fits 64 bits).
  - Each mutant runs on 3000 inputs. Each register is drawn per input from
    one of: a value below 16 or below 130; an edge word (0, 1, all ones, the
    signed minimum and maximum, the 32-bit and 8-bit edges, and the
    repeating patterns `0x5555…`, `0xaaaa…`, `0x3333…`, `0xcccc…`); a word
    with alternate bytes cleared or the sign bit set; zero; a random word.
    One input in eight gives every register the same word, and one in four
    pairs the halves of two `I128` operands (equal high halves, or equal
    low ones). Observables: the returned bits a caller reads, the call log
    (callee and argument bits), incoming accesses and final incoming
    memory, and the callee-saved registers.

## Table

`unsup` = owner unsupported (no claim); `mism` = named mismatch; `thm` =
theorem built; `smp` = refuted by the solver-free sampler; `CE` / `Valid` /
`other` = the AY replay; `cred` = every covered row Formal; `wrong` = wrong
by ground truth; `w-cred` = wrong and credited or Valid; `ok-ref` = correct
by ground truth and refuted; `n/a` = ground truth has no model.

| Mutation class | n | unsup | mism | thm | smp | CE | CE not sampled | Valid | other | cred | wrong | w-cred | ok-ref | n/a |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| C0 original | 51 | 8 | 0 | 43 | 0 | 0 | 0 | 42 | 1 | 42 | 0 | **0** | 0 | 0 |
| C1 wrong condition code | 585 | 270 | 0 | 315 | 222 | 222 | 0 | 93 | 0 | 93 | 334 | **0** | 0 | 0 |
| C2 operands swapped | 46 | 13 | 0 | 33 | 10 | 10 | 0 | 19 | 4 | 19 | 15 | **0** | 0 | 0 |
| C3 wrong operation (carry, shift, width) | 166 | 72 | 8 | 86 | 47 | 47 | 0 | 35 | 4 | 30 | 81 | **0** | 3 | 0 |
| C4 ABI register replaced (GPR or XMM) | 1002 | 232 | 446 | 324 | 238 | 238 | 0 | 82 | 4 | 82 | 803 | **0** | 0 | 0 |
| C5 wrong source register | 786 | 348 | 2 | 436 | 340 | 340 | 0 | 96 | 0 | 96 | 525 | **0** | 0 | 0 |
| C6 row dropped | 604 | 212 | 300 | 92 | 43 | 43 | 0 | 48 | 1 | 48 | 424 | **0** | 0 | 0 |
| C7 wrong immediate | 238 | 122 | 0 | 116 | 76 | 76 | 0 | 40 | 0 | 40 | 133 | **0** | 0 | 0 |
| C8 wrong memory displacement | 124 | 0 | 84 | 40 | 40 | 40 | 0 | 0 | 0 | 0 | 104 | **0** | 0 | 0 |

Of the 1277 mutants that make no claim, 1229 are mutants of the eight
zero-idiom streams (O1 and O2 of the `I128` shifts and negation); of the
other 48, 40 leave a row outside the lane (a two-operand form after a
changed or dropped row) and 8 an incoming-access trace that no longer
pairs with the source's.
Of the 840 named mismatches, 773 are on mutants wrong by ground truth.

## Conservative outcomes (correct mutants not credited)

Besides the 644 correct mutants that make no claim, 89 correct mutants are
not credited:

- **67 named mismatches on a value no observable reads.** A row reads a
  register no row defined (26 virtual registers, 13 RCX, 3 RDX, 3 RAX, 2
  RFLAGS) where the `I128` shift bodies discard the value (the half a
  `cmov` does not select, the unused low half of `a >> 64`, the high half
  `as u64` drops), or a private slot access moved outside its 16 bytes
  together with its partner (20: the two halves of an `I128` slot copy
  shifted alike). The owner names every read of an undefined register and
  every access outside a private slot, whatever its use: fail-closed.
- **3 refuted: `movss` for `movsd` into XMM0 at a return or call.** A
  physical destination keeps its bits above 32 (the hardware merge), and
  XMM0 already holds the same `f64`, so ground truth finds them correct; the
  owner states every `movss` destination's bits above 32 as a free input
  (register allocation's pure definition, which is what a virtual
  destination gets), so the theorem is refuted. Conservative by design.
- **10 `u128` multiply streams time out** (the original and 9 mutants that
  ground truth finds equivalent): the recorded multiply gap
  (`KNOWN_UNCERTIFIED_SLICE_ELEVEN`).
- **4 Clean rejections.** `sar` for `shr` (or `shl`) in the half of
  `u128 >> 64` that the `cmov` discards: AY proves the theorem and Clean
  rejects the proof (`AY reported UNSAT but` the checker, which verified a
  known-good control proof, did not). Never credited, never refuted.
- **5 partial credits (C3).** `add` for `sub` in the three constant `I128`
  shifts, in a row whose result only reaches the half a `cmov` discards:
  AY replays the theorem Valid, but
  the TV-2 provenance cross-check of the changed row fails, so all rows
  but that one are Formal and the function is not credited.

## Findings

**The first ground truth was wrong in two ways** (payloads
`robustness_no_replay.log`, `robustness_replay_first.log`). It drew a
`bool` parameter's register with garbage in bits 1 to 7, which no psABI
caller passes, so it judged three `SelectU128` mutants wrong that the owner
correctly holds (an `and v, 1` dropped or widened before an 8-bit test);
it now applies the psABI `_Bool` rule, the weaker of the two caller
conventions the owner states. And it logged a 16-byte access as one entry
classified at its first byte, so at an address 8 bytes below the top of
the address space the source logged nothing while the machine's second
8-byte access wrapped to an incoming address; it now splits the access
into its two halves, each classified at its own address, as the owner's
semantics and the machine do. After both fixes no original is wrong and no
credited stream is wrong.

**The sampler's evaluators truncated a wide field.** Building the
slice-11 controls (before this probe) found that the shared SMT evaluators
cut an `Extract` wider than 64 bits to 64 bits; see the main README. The
probe ran on the fixed evaluators.

**The x86 optimizer's zero idiom is outside the lane.** At O1 and O2 the
optimizer writes the zero constant of the `I128` shift and negation bodies
as `xor r, r`, a two-operand form the walk does not admit, so those bodies
make no claim at O1 and above.

## Reproduce

Plug the probe in as a child of the x86 body test module, next to
`mod slice11;` in `crates/trust-cg-verify/src/x86_source_bound_body_tests.rs`:

```rust
#[path = "../../../reports/perf/2026-10-03-darwin-x86-64-census-slice11/robustness/x86_source_bound_body_slice11_robust_tests.rs"]
mod slice11_robust;
```

Then run it with the qualification toolchain's AY and Clean:

```sh
zsh reports/perf/2026-10-03-darwin-x86-64-census-slice11/fails-before/qualify.sh \
  <log> x86_source_bound_body::tests::slice11_robust:: --ignored --test-threads=1
```

- `ROB11_NO_REPLAY=1` skips the solver. The AY columns are then empty, and
  the sampler column still fills.
- `ROB11_ONLY=<text>` restricts the run to the fixture shapes whose name
  contains it.

Logs: `robustness_replay.log`, `robustness_replay_first.log` and
`robustness_no_replay.log` in [PAYLOADS.md](../PAYLOADS.md).
