# Slice 7 mutation robustness probe (2026-10-01)

This probe tests whether the slice-7 whole-body theorem (calls through
memory) ever credits a wrong machine stream as Formal. Each slice-7 fixture's
real pre-RA stream is mutated, and every mutant is judged three ways:

- by the owner, `source_bound_x86_body`;
- by the replayed theorem (`ay --strict-proofs`, then Clean) and the
  verifier's crediting;
- by an independent concrete interpreter of the LIR and of the x86 stream,
  which serves as ground truth.

The probe is diagnostic only and is not a gate.

**Result: no wrong stream was credited.** Of the 757 mutants, 730 are wrong
by ground truth, and none of those 730 received a Verified replay or credit.
14 mutants were credited, and all 14 are correct by ground truth:

- dead stores into the slot;
- wider reads of a `bool` byte that are re-extended to 8 bits;
- passing the same slot again.

## Setup

- **Tree:** `feat/x86-body-slice7-calls-through-memory` at `b4946e662`.
- **Replay:** stage-1 AY 0.27.0 build 10530 (d1408012) with
  `~/clean-checker/bin/clean` (Clean 5f09e36c). The checker binary's digest
  was not compared with the pin.
- **Wall time:** about 150 s.
- **Base streams:** O0 selector output for all 15 shapes, plus the distinct
  O1 optimizer outputs. O2 and O3 equal O1. That makes 23 streams.
  - Ground truth matches the source on all 23.
  - 22 replay Verified and are credited.
  - SretBranch at O1 uses `bt`, which the owner does not admit, so it makes
    no claim.
- **Ground truth:** the interpreter makes every uninitialised slot byte,
  every undefined register and the bits above a narrow write pseudo-random
  garbage. A callee is a deterministic pseudo-random function of its name,
  its scalar arguments and the bytes of every buffer it receives, and it
  overwrites every byte of each buffer it receives. In *retaining* mode it
  also overwrites every buffer any earlier call received, which is the
  model's adversary. Each mutant runs on 500 inputs in both modes.

## Table

| Mutation class | n | owner unsupported | owner mismatch | theorem built | AY counterexample | AY Valid + credited | GT-wrong (retention-only) | credited and wrong |
|---|---|---|---|---|---|---|---|---|
| C1 other slot/offset | 193 | 8 | 185 | 0 | 0 | 0 | 193 | **0** |
| C2 wrong call / argument position | 23 | 15 | 7 | 1 | 0 | 1 (correct) | 22 | **0** |
| C3 slot read before the call | 26 | 1 | 0 | 25 | 25 | 0 | 24 (3) | **0** |
| C4 pre-call copy reused | 36 | 1 | 0 | 35 | 35 | 0 | 32 (3) | **0** |
| C5 initialising store skipped | 12 | 0 | 0 | 12 | 12 | 0 | 12 | **0** |
| C6 store after the call | 94 | 2 | 0 | 92 | 83 | 9 (correct) | 82 | **0** |
| C7 byte the call did not define | 172 | 5 | 61 | 106 | 106 | 0 | 172 | **0** |
| C8 two calls swapped | 4 | 0 | 4 | 0 | 0 | 0 | 4 | **0** |
| C9 call dropped | 53 | 4 | 49 | 0 | 0 | 0 | 53 | **0** |
| C10 slot read/store size | 144 | 7 | 0 | 137 | 133 | 4 (correct) | 136 | **0** |

Every theorem the owner built ended as either an AY counterexample or
Verified, never as anything else.

Retention is covered. Six mutants are correct when callees only write their
own buffers, but wrong when callees retain addresses. Examples are
OutParamThenCall reading `v` before `g1`, and SretTwoBuffers reading the
first buffer before the second call. All six were refuted.

## Findings

1. **The solver-free sampler missed 18 wrong theorems that AY refutes.** The
   `slice7::theorem_refuted` sample check passed 18 mutants in SretOption and
   OptionOutParam at O0 and O1:
   - 14 C7 mutants, which read the `Option` tag at offset +1, +4, +8 or +16;
   - 4 C10 mutants, which read the tag as 4 bytes instead of 8.

   Every third sample set *all* call-defined bytes to zero at once. It
   therefore never produced "tag zero, payload non-zero" or "low half zero,
   high half non-zero". Before the fix, only the replay caught a regression
   of this kind.

   **Fix:** every sixth sample still zeroes all call-defined bytes. The
   samples at seeds `6k + 3` now zero the bytes on one side of a boundary.
   The boundary steps through every offset of a 32-byte slot, and both sides
   are covered (`zeroed_call_byte`). So each word is zero while its
   neighbour is not, and each half of a word is zero while the other is not.

   A first attempt zeroed each byte independently with probability one half.
   It still missed the +1 tag read, because "eight zero bytes, then a
   nonzero byte" is a 1-in-512 event at that rate.

   **Evidence:**
   - The new test `a_misplaced_or_narrowed_option_tag_read_is_refuted_on_samples`
     covers these mutants. Under the old sampler it fails with
     "SretOption: the tag read at offset 1: the theorem must refute the wrong
     lowering". With the boundary sampler, all 23 `slice7::` tests pass,
     including every check that a correct theorem holds.
   - Re-run without the solver (`ROB7_NO_REPLAY=1`), the probe's
     sample-refuted column now equals the AY counterexample column in every
     class:

     | Class | AY counterexample | Sampler, before | Sampler, after |
     |---|---:|---:|---:|
     | C3 | 25 | 25 | 25 |
     | C4 | 35 | 35 | 35 |
     | C5 | 12 | 12 | 12 |
     | C6 | 83 | 83 | 83 |
     | C7 | 106 | 92 | **106** |
     | C10 | 133 | 129 | **133** |

     No wrong mutant with a theorem escapes the sampler.
2. **Eight correct mutants are refuted.** This is over-approximation, not
   unsoundness. In OutParamField, `bump(&mut s.1)` makes the whole slot
   call-defined, so reusing `s.0` across the call is refuted at O0 and O1
   (C3, C4 and C6 variants). This is deliberate. The pointer is
   `gep(s, 8)`, and the theorem's callee contract does not assume Rust's
   field-provenance rule. A callee compiled by another backend sees an
   address into the whole allocation.

## Assumptions the probe cannot reach

No machine-stream mutation can break the following assumptions. They are
listed in [LIMITATIONS.md](../../../../LIMITATIONS.md) under slice 7.

- **Slot size and alignment are not checked against the callee's pointee.**
  LIR states neither. Slot layout and non-overlap belong to the frame
  layout, which is outside the theorem.
- **A callee writes only during the call.** A retained pointer written by
  another thread or by a signal handler between calls is outside the model.
  In the source, that would be a data race.
- **Results do not depend on a slot's address.** This holds because the walk
  pins the exact slot and offset of every private-address argument. Today's
  x86 frame gives every slot its own offset and never reuses one. A future
  stack-colouring pass would have to treat an escaped slot as live until the
  end of the function.
- **Benign over-approximations:**
  - a `&T` argument is assumed writable;
  - the whole slot is assumed written when the callee gets an interior
    pointer;
  - RAX is undefined after an sret call.

## Reproduce

Plug the probe in as a child of the x86 body test module, next to
`mod slice7;` in `crates/trust-cg-verify/src/x86_source_bound_body_tests.rs`:

```rust
#[path = "../../../reports/perf/2026-10-01-darwin-x86-64-census-slice7/robustness/x86_source_bound_body_slice7_robust_tests.rs"]
mod slice7_robust;
```

Then run it with the qualification toolchain's AY and Clean:

```sh
TCG_X86_BODY_QUALIFY_AY=<stage1>/bin/ay \
TCG_EXTERNAL_CLEAN_CHECKER=<clean-5f09e36c>/bin/clean \
targo --unverified test -p trust-cg-verify --lib \
  x86_source_bound_body::tests::slice7_robust:: -- --ignored --nocapture
```

- `ROB7_NO_REPLAY=1` skips the solver. The table's AY columns are then
  empty, and the sample-refuted column still fills.
- `ROB7_ONLY=<shape>` restricts the run to one fixture shape.
