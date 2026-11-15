# Slice 13 mutation robustness probe (2026-10-05)

This probe tests whether the slice-13 whole-body theorem (a private stack
address stored as data, parameters and arguments on the stack, the C
memory routines and scalar atomics) ever credits a wrong machine stream as
Formal. Each slice-13 fixture's real pre-RA stream is mutated, and every
mutant is judged three ways:

- by the owner, `source_bound_x86_body`;
- by the solver-free sampler of the library gate (`slice11::theorem_refuted`,
  the structured sampler every slice since 11 uses) and by the replayed
  theorem (`ay --strict-proofs`, then Clean) with the verifier's crediting;
- by an independent concrete interpreter of the LIR and of the x86 stream,
  which serves as ground truth.

The probe is diagnostic only and is not a gate.

**Result: no wrong stream was credited.** Of the 1111 mutants (24 base
streams included), 849 are wrong by ground truth, and none of those
received a Verified replay or credit: 116 make no claim, 609 are named
mismatches and 124 are refuted by both the sampler and AY. 185 streams
were credited (24 originals and 161 mutants), and every one is correct
by ground truth.

**The sampler refutes everything AY refutes.** In every class the number of
theorems AY refutes with a counterexample equals the number the sampler
refutes (column "CE not sampled" is 0 everywhere): 126 of 126. Every
theorem built either replays Valid (185) or is an AY counterexample
(126).

## Setup

- **Tree:** `feat/x86-body-slice13-memory` at `4eb6c6a34` (the owner as committed in `f571ba79e`), with the probe
  plugged in as below.
- **Replay:** stage-1 AY 0.27.0 build 10530 (sha256 `9a149c35…`) with `~/clean-checker/bin/clean` (Clean 5f09e36c), the qualification toolchain.
- **Wall time:** 308 s with replay (on a shared host, with a census
  running).
- **Base streams:** O0 selector output for all 20 fixture shapes, plus
  each distinct O1, O2 and O3 optimizer output (`AddrInLocalReadBack` at O2
  and O3, `MemcpyIntoLocal` and `TwoAddrsToOut` at O1; every other
  optimized stream equals its O0 one): 24 streams.
- **Mutation classes:** as in the slice-11 probe, C1 a flag reader's
  condition replaced by every other; C2 the two source operands of a
  three-address row swapped; C3 another operation of the same shape; C4 an
  ABI register operand (RDI, RSI, RDX, RCX, RAX, XMM0-XMM2) replaced by
  another of its register file; C5 a source register replaced by an earlier
  virtual register of its class; C6 a value row dropped (the RSP
  adjustments included); C7 another immediate (the outgoing area's size
  included); C8 a memory operand's displacement moved by -8, -4, +4 or +8
  bytes (a stack parameter's `[rbp + 16 + 8k]`, an outgoing argument's
  `[rsp + 8k]`, a slot access); and, new, C9 an atomic row's proof origin
  dropped (a plain `mov` where the source access is atomic).
- **Ground truth** (independent of the owner: none of its escape,
  placement or atomic rules is reused):
  - Memory is concrete bytes. Each private slot lives at its own address
    range on both sides (the slot binding), and a stored address is the
    number it is. The frame and stack pointers are concrete: the `k`-th
    incoming stack eightbyte is at `[rbp + 16 + 8k]` and the callee reads
    its `k`-th stack argument at `[rsp + 8k]` at the call. Callee-saved
    registers and RSP are observed at the return.
  - A callee is a deterministic pseudo-random function of its identity, the
    bits its parameters own and the bytes of every slot it can REACH: a
    slot whose address is an argument, lies in incoming memory or in a
    reachable slot (to a fixpoint), or was reachable at an earlier call
    (the probe's own model of escape, never the owner's). Three calls in
    four it then overwrites the reachable slots' bytes.
  - `memcpy`, `memmove` and `memset` run concretely on both sides: the
    source's `Memcpy`/`Memmove`/`Memset` and the machine's call alike.
  - Atomic accesses are plain ones (one thread). LIR values are Rust
    integers of their width; the machine follows the Intel SDM as in the
    slice-11 probe.
  - Each mutant runs on 3000 inputs, drawn as in the slice-11 probe (small
    words, edge words and repeating patterns, sign-bit and alternate-byte
    words, zero, random; one input in eight gives every register the same
    word). Observables: the returned bits a caller reads, the call log
    (callee, argument bits and the bytes of the slots it can reach),
    incoming accesses and final incoming memory, the callee-saved registers
    and RSP at the return.

The same probe on AY build 12713 (this branch merged with the lane's
requalification, `90608b684`, through the x86-stage1-ay12713 overlay; 217
s) gives the same table, cell for cell, and no finding (payload
`robustness_replay_ay12713.log`).

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
| C2 operands swapped | 6 | 0 | 0 | 6 | 0 | 0 | 0 | 6 | 0 | 6 | 0 | **0** | 0 | 0 |
| C3 wrong operation | 19 | 3 | 7 | 9 | 9 | 9 | 0 | 0 | 0 | 0 | 18 | **0** | 0 | 0 |
| C4 ABI register replaced | 404 | 20 | 274 | 110 | 24 | 24 | 0 | 86 | 0 | 86 | 296 | **0** | 0 | 0 |
| C5 wrong source register | 158 | 38 | 38 | 82 | 56 | 56 | 0 | 26 | 0 | 26 | 130 | **0** | 2 | 0 |
| C6 row dropped | 185 | 18 | 126 | 41 | 10 | 10 | 0 | 31 | 0 | 31 | 148 | **0** | 0 | 0 |
| C7 wrong immediate | 73 | 22 | 18 | 33 | 21 | 21 | 0 | 12 | 0 | 12 | 61 | **0** | 0 | 0 |
| C8 wrong memory displacement | 236 | 16 | 214 | 6 | 6 | 6 | 0 | 0 | 0 | 0 | 196 | **0** | 0 | 0 |
| C9 atomic origin dropped | 6 | 6 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **0** | 0 | 0 |

The selector's straight-line streams have no flag reader, so C1 is empty.
Of the 123 mutants that make no claim, 116 are wrong by ground truth (a
row outside the lane after a changed operation, register or immediate; an
access trace that no longer pairs with the source's); of the 677 named
mismatches, 609 are.

## Conservative outcomes (correct mutants not credited)

Besides the 7 correct mutants that make no claim (the 6 C9 mutants, which
pair a plain machine access with an atomic source access, refused by rule
under OD-83; and `or` for an `add` of disjoint address bits, a row form
outside the lane), 70 correct mutants are not credited:

- **68 named mismatches, each fail-closed by rule.** 40 move a private
  slot's address or access outside the slot (C8 on the `lea` that forms
  it or on the access itself: `AddrInLocalReadBack` 16, `TwoAddrsToOut`
  16, `AddrToOut` 4, `BoolFromByte` 4). In the probe's concrete memory
  every access through that address moves alike, or the moved bytes are
  dead, so no observable changes; the owner names every access outside a
  private slot. 28 read a register no row defined (an argument register
  replaced by RAX or RCX, or the copy that defined a virtual register
  dropped) where the value reaches nothing observed: the copy of a
  register parameter the body never uses (`StackParam` 5,
  `StackParamsNarrow` 6), a value stored into a slot that escapes just
  before the return, with no later call to read it (`TwoAddrsToOut` 12,
  `AddrToOut` 4), and an address stored into a local the optimized
  `AddrInLocalReadBack` no longer reads (1). The owner names every read of
  an undefined register, whatever its use.
- **2 refuted: `AtomicStoreThenLoad` returning the stored value.** The
  mutant returns the value it stored instead of the value it then loads.
  With one thread they are equal, so ground truth finds it correct; the
  theorem states every incoming load as a fresh input (memory is modelled
  by its access trace, slice 4), so it is refuted. Conservative by design.

## Findings

**A dropped `add rsp, n` built a theorem that held.** The first run,
sampler only (payload `robustness_no_replay_first.log`), found two wrong
mutants, `StackArgs` and `StackArgAddress` with the row that closes the
outgoing argument area dropped, whose theorems the sampler did not refute
(and AY would have proved): the owner checked RSP's balance only at the
next adjustment, so a return with the area still open, the stack pointer
`n` bytes low, which every caller observes, went unstated. The
owner now names it (`PreservedWrite` of RSP at the return,
`the_stack_argument_areas_admit_only_their_exact_rows`, and the
`rsp-open-at-return` fails-before mutant). The probe's own ground truth
was corrected twice in the same run: it lacked `movzx` from memory (so
mutants of the `bool` byte loads had no model), and its de-duplication of
mutants ignored proof origins (so every C9 mutant was dropped as a copy of
its original). After these fixes no original is wrong and no credited
stream is wrong.

## Reproduce

Plug the probe in as a child of the x86 body test module, next to
`mod slice13;` in `crates/trust-cg-verify/src/x86_source_bound_body_tests.rs`:

```rust
#[path = "../../../reports/perf/2026-10-05-darwin-x86-64-census-slice13/robustness/x86_source_bound_body_slice13_robust_tests.rs"]
mod slice13_robust;
```

Then run it with the qualification toolchain's AY and Clean:

```sh
zsh reports/perf/2026-10-05-darwin-x86-64-census-slice13/fails-before/qualify.sh \
  <log> x86_source_bound_body::tests::slice13_robust:: --ignored
```

- `ROB13_NO_REPLAY=1` skips the solver. The AY columns are then empty, and
  the sampler column still fills.
- `ROB13_ONLY=<text>` restricts the run to the fixture shapes whose name
  contains it.

Logs: `robustness_replay.log` (this table), `robustness_replay_19.log`
(the same probe before `TwoAddrsToOut` was added: 972 streams, 774 wrong,
none credited), `robustness_no_replay.log` and
`robustness_no_replay_first.log` in [PAYLOADS.md](../PAYLOADS.md).
