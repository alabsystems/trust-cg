# b1_mispredict 1.1332x -> 1.1199x: the RMW fusion's window was stricter than its own rewrite needs (2026-09-29)

**1.17% faster on b1, with the in-batch identical control agreeing to 0.02%.** A real win on the
corpus's largest remaining gap, and it came from a condition that was provably stronger than the
transformation requires.

It also only became reachable because of an earlier fix in this same round.

## The chain that led here

b1's odd arm contains `t[j] = t[j] + acc` — a load, an add, and a store to the same slot. The
memory-destination RMW fusion (`rmw_fuse`) exists for exactly that, producing one `AddMRSib`. It was
not firing, and the reason had two layers:

1. **Until earlier today the load and store addresses did not even match.** The store's index was a
   pre-scaled `imul $8` product addressed at scale 1, while the load used scale 8 — so
   `rmw_fuse_same_ea` correctly refused. [Wiring the cross-block flag
   proof](../2026-09-29-x86-sib-crossblock-flags/) into the SIB fold removed that `imul`, and both
   sides became `scale: 8`. That fix was worth 1.43% on its own; this is a second win it unlocked.
2. **With the addresses matching, the W1 window refused it anyway** — and that is the bug.

## The condition, and why it was too strong

Reading the IR (`trace-peephole-entry`, not the disassembly) gives b1's triple exactly:

```
MovRMSib [v84, Sib{ base: StackSlot(0), index: v74, scale: 8 }]   <- the load,  t = v84
MovRR    [v85, v68]                                               <- a def of `s`
AddRR    [v86, v84, v85]                                          <- the anchor, d = v86, s = v85
MovMRSib [Sib{ base: StackSlot(0), index: v75, scale: 8 }, v86]    <- the store
```

(`v75` is a single-def `MovRR` copy of `v74`, which `rmw_fuse_same_ea` already canonicalizes — the
address was never the problem once the `imul` was gone.)

Condition W1 scanned the window between the load and the anchor and refused any **def of `s`**.
Line 2 defines `s`, so the candidate died there; the commuted form then failed because `s`'s def is
a copy rather than a load.

That refusal is stronger than the rewrite needs, and the rewrite itself says why: **the replacement
is spliced at the STORE's position** — the latest of the three. So the fused instruction reads `s`
*after* any def of `s` between the load and the anchor. What actually has to hold is that `s` carries
unchanged from the anchor to the store, and the **W2 window already refuses a def of `s` on exactly
that stretch**. A def in W1 is not even deleted: only the load and the ALU are, so `s` is still
computed where it was.

Everything else in W1 stays: the window is still `imul_fuse_window_ok` (which excludes every memory
operation), still refuses any mention of `t`, and still refuses a def of the EA registers — the last
of which genuinely matters, because the fused instruction reads memory at the store's position using
the *load's* operand spelling.

## Result

| | hot-loop insns | span | `mov` | memory-destination adds |
| --- | ---: | ---: | ---: | ---: |
| W1 strict (before) | 42 | 166 B | 15 | 0 |
| **W1 relaxed (default)** | **41** | **162 B** | **13** | **1** |

`taskset -c 2`, 40 interleaved rounds, `min`, byte-identical control in the batch:

| arm | min ms | vs LLVM | vs strict |
| --- | ---: | ---: | ---: |
| LLVM -O3 | 190.52 | 1.0000 | 0.8825 |
| W1 strict | 215.89 | 1.1332 | 1.0000 |
| **W1 relaxed (default)** | **213.36** | **1.1199** | **0.9883** |
| relaxed, identical copy | 213.40 | 1.1201 | 0.9885 |

**1.17% faster**, control 0.02%. Two `mov`s become one memory-destination add; b1 goes
**1.1332x → 1.1199x LLVM**.

Note this is better than the ~0.7%-per-instruction scaling b1 has shown, which is expected: an
`AddMRSib` is not merely one instruction fewer than load + add + store, it is fewer uops and one
less register.

## Correctness

| check | result |
| --- | ---: |
| programs the relaxation changes | **1 of 18** (b1 only) |
| execution differential, default build | **18/18 MATCH** |
| Trust, 23 strict-verified functions, verification ON | checksum `267826962111695130` |
| Lean-through-Clean | **5/5** |
| TY | **9/9** |
| `trust-cg-opt --lib` | 3848 pass, 0 fail |
| fmt | clean |

`-Ztrust-ir-cg-args=no-x86-rmw-fuse-sdef` restores the stricter window. Two tests pin it in both
directions: `rmw_fuse_fuses_when_the_register_operand_is_defined_before_the_alu` (b1's shape, with
the falsifiability check that the stricter window still declines the identical fixture) and
`rmw_fuse_still_refuses_a_redef_of_s_between_the_alu_and_the_store` — the condition that does
remain, since that is the stretch `s` has to carry across.

## Also measured this round, and NOT shipped on

An `AddRR` arm was added to the sibling **RM** fusion (`imul_fuse`), so a locally-dead load feeding
an add becomes `AddRM`. `AddRM` is entirely first-class — encoded, coverage-gated, flag-modelled,
carrying labelled addressing proofs — and simply had never been created by any peephole. It fires 15
times in b1's `main` and is **runtime-neutral** (1.0002 against a 1.0007 control), because every one
of those 15 is OUTSIDE the hot loop. It is kept, default on, as a strict instruction-count
reduction with `no-x86-add-fuse` as the opt-out; the honest statement is that it buys code size and
no measured time.

That contrast is the useful part: the same corpus, the same day, one fusion firing 15 times outside
a hot loop for 0%, and another firing once inside it for 1.17%.

## Status of the clause

Still not met. b1 **1.1199x**, h3 1.0990x, p4 1.0825x, h4 1.0537x, p2 1.0190x, h2 1.0117x.
