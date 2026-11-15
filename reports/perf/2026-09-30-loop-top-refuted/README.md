# b1_mispredict: LLVM's loop-top selection, reproduced exactly, and 4.7% slower

Date: 2026-09-30 · Host: AMD Ryzen 9 9900X3D, Linux · `perf_event_paranoid=4`
(no hardware counters) · Reference: in-tree LLVM 22.1.2 (`-C opt-level=3`)

## What was tested

`x86_loop_top` (new, `-Ztrust-ir-cg-args=x86-loop-top`) ports
`MachineBlockPlacement::findBestLoopTopHelper` pattern 2
(`llvm/lib/CodeGen/MachineBlockPlacement.cpp:2155-2167`): place a two-arm
in-loop diamond's latch immediately before its header, so the backedge becomes
a fall-through.

The hypothesis under test was recorded in `x86-b1-is-loop-top-selection`: that
b1's 9.4% gap is the **2 taken branches per iteration** this backend emits
against LLVM's 1.

## The transform delivered its claim

It fires on exactly one function in the corpus, b1's `main`, and the emitted
binary changed as predicted — blocks reordered to `[arm, latch, header, arm]`,
the preheader jumping into the middle of the loop exactly as LLVM's does:

| | trust-cg default | with the pass | LLVM |
|---|---|---|---|
| taken branches / iteration, either path | **2** | **1** | **1** |
| loop body instructions | 38 | 40 | 33 |
| blocks | 4 | 4 | 4 |

## And it is a 4.7% loss

90 interleaved rounds, `taskset -c 2`, `min` statistic, both arms carried twice
as byte-identical copies to expose the floor:

| arm | min ms | med ms | vs LLVM |
|---|---|---|---|
| llvm | 190.276 | 191.159 | 1.0000 |
| off (default) | 208.201 | 209.347 | 1.0942 |
| off2 | 208.254 | 209.507 | 1.0945 |
| **on** | **217.930** | 219.420 | **1.1453** |
| on2 | 217.936 | 219.475 | 1.1454 |

Floors: 0.0003 (off/off2) and 0.0001 (on/on2). The 0.0511 gap is ~170× the
floor. `on` and `on2` are byte-identical binaries; `off` and `on` differ, so
the lever is isolated and did act.

**The taken-branch count is not b1's gap.** The reorder bought the predicted
branch and cost 2 instructions; on a loop whose data branch is unpredictable by
construction, a taken branch on the *perfectly predicted* backedge is worth
less than two instructions.

## Where b1's 5 instructions actually are

Instruction-for-instruction against LLVM's loop, all four blocks:

### 1. Commutative two-address operand selection — 3 instructions

`s ^= s >> 7`:

```
  LLVM      mov %r9,%r8 ; shr $0x7,%r8 ; xor %r9,%r8          3
  trust-cg  mov %r12,%rcx ; shr $0x7,%rcx ; mov %r12,%rbx ; xor %rcx,%rbx   4
```

XOR is commutative and the shifted temp dies at the XOR, so the dying operand
can be the tied destination and the copy of the LIVE operand (`s`) is
unnecessary. This backend always copies the first source. It costs 1
instruction in each of the two xorshift steps that have this shape, and 1 more
in the odd arm (`acc ^= s.wrapping_mul(K)` — same pattern).

LLVM's rule is `TwoAddressInstructionPass::tryInstructionCommute`.

### 2. One reusable copy of `s` — 1 instruction

LLVM makes a single copy in the header (`mov %rdx,%r9`, 0x208cd) and consumes
it destructively in whichever arm runs (`shr $0x3,%r9` / `imul %rcx,%r9`). This
backend re-copies `s` inside each arm, paying twice for what LLVM pays once.

### 3. Demanded bits through `x ^ (x << k)` — 1 instruction

The low `k` bits of `x ^ (x << k)` equal the low `k` bits of `x`. LLVM uses
this twice to read the *earlier, dead* value destructively:

```
  0x208d0  test $0x1,%r8b     # %r8 = s2, not the final s3 — bit 0 is the same
  0x20894  and  $0x6,%r8d     # bits 1..2 likewise; destroys a dead register
```

Against `mov %r12,%rcx ; and $0x6,%rcx` here, because the final `s` is live
across the backedge and cannot be clobbered.

`3 + 1 + 1 = 5 = 38 − 33`.

## Byproduct: a latent defect in the default-ON latch rule

`x86_branch_layout`'s latch rule swapped a backedge onto the conditional
branch "regardless of layout". Its premise — that a backedge riding the `jmp`
costs a taken branch — is false when the `jmp` target is the layout successor,
because the encoder elides it; the swap then converts a free fall-through into
a taken `jcc`. The generic fall-through rule in the same `match` already
carried exactly this guard.

The shape was unreachable before this pass existed (nothing else moved
`block_order`), so it had never bitten. It bites hard the moment it is
reachable: at O3 the pass manager runs `run_to_fixpoint`, so branch layout
re-runs on the reordered function, and the two rules flip the same pair every
iteration — the emitted orientation decided by the parity of the iteration
budget. The first measurement of this pass was taken in that state (reorder
applied, latch re-inverted, 2 taken branches AND the extra instructions).

Fixed in the rule itself: `latch_rule && !exit.jump_is_layout_next`, pinned by
`latch_rule_declines_a_back_edge_that_already_falls_through`.

## Follow-through: the capability for (1) exists, and still nets a loss

`x86-twoaddr-expand` + `x86-twoaddr-commute` + `x86-twoaddr-expand-all` produces
**LLVM's 3-instruction xorshift exactly** (header 13 -> 11) and the odd arm's
4 -> 3. All three knobs are required: the expansion alone is byte-identical on
b1, because the loop-scope call gate declines its call-free hot loop and the
block-local deadness scan fails closed at the end of the header block.

It still lost, for a reason the pass's own doc anticipates in general terms: the
inserted `MovRR` lands between a load and the ALU of a `t[j] ^= s` memory RMW,
and the peephole's fusion (1 instruction) declines, giving 3. Both of b1's arms
carry one. Net 38 -> **41**.

A profitability guard now makes the expansion DEFER to the fusion — an ALU
sandwiched between a load of its LHS and a store of its def is left alone. The
addresses are deliberately not compared: `rmw_fuse` carries a canonical-spelling
apparatus precisely because the two EAs are spelled differently here, and a
first version of the guard that required structural equality **never fired on
the arms it was written for**.

With the guard:

| | insns | reg-reg movs | fused memory-RMW | vs LLVM |
|---|---|---|---|---|
| LLVM | 33 | 7 | 2 | 1.0000 |
| default | 38 | 12 | 2 | 1.0939 |
| three knobs + guard | 38 | 10 | **1** | **1.1011** |

(90 rounds, floors 0.0005 / 0.0004.) Two copies removed, one fusion still lost:
net zero instructions and a 0.7% regression, ~15x the floor. **b1 is not
improved.**

### The lost fusions, found with a new instrument

The first guard protected only the EVEN arm. `rmw_fuse` has **fifteen** decline
points and every one of them declined in SILENCE, so a lost fusion could not be
attributed by reading the output. A decline trace
(`-Ztrust-ir-cg-args=trace-x86-rmw-fuse`, diagnostics only) names them, and on
b1's `main` exactly one condition appears with the expansion knobs on and never
without them:

```
rmw-fuse-bail[.../anchor=3:AddRR]: condition A: the loaded value and the fused
                                   source are one id, or t aliases d
```

Condition A is `s.id == t.id || t.id == d.id` — "one id playing both roles
defeats the two deadness scans". The expansion rewrites the ALU to the TIED form
`Op [d, d, b]`, so `t.id == d.id` holds and the fusion refuses it **permanently**:
at O3 the pass manager runs to fixpoint, so the peephole sees the expanded form
on a later iteration.

That also explains why the first guard missed one arm. It required the load to be
the IMMEDIATELY preceding instruction, but `rmw_fuse` tolerates a window either
side (its W1/W2 purity rules), and b1's `t[j] += acc` arm has its load further
up. The guard now scans the whole block in both directions — deliberately a
SUPERSET of the fusion's acceptance, since over-declining costs one copy and
under-declining costs the fusion's two.

Two wrong versions of this guard, both diagnosed rather than guessed:

| guard | insns | movs | fused RMW | vs LLVM |
|---|---|---|---|---|
| no guard | 41 | 11 | 0 | — |
| strict adjacency, LHS only | 38 | 10 | 1 | 1.1013 |
| **block-wide window, either source** | **37** | **9** | **2** | see below |
| (default, knobs off) | 38 | 12 | 2 | 1.0937 |
| LLVM | 33 | 7 | 2 | 1.0000 |

### The timing effect is below this program's noise, so no default moves

90 rounds: off 1.0937 / off2 1.0926 / on 1.0916 / on2 1.0913. Replicated at 150
rounds relative to `off`: off2 0.9993, **on 0.9949, on2 0.9984**.

The two `on` arms are BYTE-IDENTICAL copies and they disagree by 0.0035 — more
than the on-vs-off difference. **The effect is not resolvable at this noise
level.** What is solid is structural: 37 instructions against the default's 38,
three fewer register moves, and both memory-RMW fusions intact, where the
unguarded form was 41 with neither.

So every knob here stays DEFAULT OFF, and b1 remains the suite's worst program
at ~1.09. Two of the three instructions named above are now actually removable;
closing the rest needs the reusable-copy placement and the demanded-bits rule,
neither of which this backend has.

## Status

* `x86_loop_top` — correct, 8 tests, DEFAULT OFF on the measurement above.
* latch-rule guard — DEFAULT ON, a defect fix, keeps the fixpoint from
  oscillating.
* two-address RMW deference — in the DEFAULT-OFF expansion; 4 tests.
* `trace-x86-rmw-fuse` — a decline trace for all fifteen of `rmw_fuse`'s
  conditions; diagnostics only, and the instrument that found condition A.
* Gates: `trust-cg-opt` 3914 pass / 0 fail; pipeline schedule pins 6/6;
  `must_refuse_corpus` 2/0 and 1/0 (an upstream trust-ir pin bump landed
  mid-session); 18-program differential 20
  MATCH-lines; `library/core` at O3 **0 failed roots / 1284 objects / 0
  refusals** in the lowering lane.

⚑ Two harness traps hit while gating this: a census run without
`--extra-flag=-Ztrust-ir-cg-args=no-proof-certs` measures the PROOF lane (1123
failed roots, all `[TCG-PROOF-465]`) and is not comparable to the lowering
baseline; and a census `--out-dir` under `/tmp` dies on the tmpfs quota with
`Disk quota exceeded`, which the report surfaces as 0 objects rather than as a
disk error.
