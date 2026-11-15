# Copy propagation was blocked from ALL x86 arithmetic (2026-09-29)

A real, general analysis gap — found only after building the right instrument, measured, and
shipped OPT-IN because it does not pay.

## The gap

`x86_copy_prop`'s `is_copy_prop_barrier` treats every flag writer as a barrier, and its
escape hatch `can_rewrite_flag_barrier_uses` rescues only flag writers that produce NO value
— `CmpRR`, `TestRR`, `Ucomis*`, `Ptest`. On x86 essentially every ALU instruction writes
flags. The net effect: **copy propagation never rewrote the operands of any value-producing
arithmetic.**

What that costs, from a dump taken at the position the pass actually runs — `b1_mispredict`'s
xorshift block:

```text
  MovRR v15, v11 ; ShlRI v18, v15, 13 ; XorRR v19, v11, v18
  MovRR v20, v19 ; ShrRI v23, v20, 7  ; XorRR v24, v19, v23
  MovRR v25, v24 ; ShlRI v28, v25, 17 ; XorRR v29, v24, v28
```

Each `MovRR` exists only to feed the following shift. The shift is THREE-address, so it does
not destroy its input — it could read the original register and the copy is pure waste. Note
the `XorRR` on each line already reads the ORIGINAL (`v11`, `v19`, `v24`), which is what
makes the copies provably redundant rather than merely suspicious.

## Soundness

A copy establishes that two registers hold the same VALUE. A pure ALU instruction's result
AND its flags are functions of its operand values, so substituting a copy-equal register for
a use changes neither. Class safety is inherited: `copy_vregs` records only same-class copies
and `resolve_copy` refuses to cross a class boundary, so no aliased width view can be
substituted — the hazard that produced a miscompile in `x86_cse` this same day.

The load-bearing extra condition is `alu_operand0_is_pure_def`. `x86_operand0_may_be_read`
deliberately OVER-APPROXIMATES for the register-immediate ALU and shift opcodes — its own
comment says "The three-operand `[d, s, imm]` forms do not read `d`, but the passes' tied
list has always counted them; keep the over-approximation." That shared predicate is relied on
by other passes and is NOT changed here; a local arity test encodes the convention for
exactly the allowlisted opcodes instead.

## It fires, and it does not pay

`b1_mispredict`'s `main`: **137 -> 126 instructions**, exit code unchanged. First capability
added in this round that fires on a real program at all.

One bridge, the change's own lever, 15 interleaved samples per arm on a pinned core:

| program | widening OFF | ON | ON/OFF | P(on<off) |
| --- | ---: | ---: | ---: | ---: |
| b1_mispredict | 218.74ms | 221.05ms | **1.0106x** | 0.200 |
| p1_xorshift | 448.42ms | 448.52ms | 1.0002x | 0.600 |
| p2_collatz | 167.10ms | 167.12ms | 1.0001x | 0.427 |
| p3_gcd | 259.86ms | 259.66ms | 0.9993x | 0.693 |

Neutral everywhere except `b1_mispredict`, where it is slightly WORSE — the one program whose
instruction count it improves. That is consistent with everything else measured on this host
this round: removing instructions from a hot loop was cancelled or reversed by alignment four
separate times, and b1 is misprediction-bound, so eleven fewer instructions buy nothing.

So it ships **DEFAULT OFF** (`-Ztrust-ir-cg-args=x86-copyprop-alu`), with the numbers above as
what a future attempt has to beat. Default codegen is unchanged, verified: b1's `main` is 137
instructions with the knob absent, exactly the pre-change baseline.

## The instrument that made this findable

This was found only after adding `-Ztrust-ir-cg-args=trace-peephole-entry`, which dumps each
function's blocks AS THE PEEPHOLE SEES THEM. The x86 lane previously had dumps at exactly two
positions, both owned by the vectorizer: after SROA, and after the WHOLE cleanup cluster.
Nothing in between.

That gap had a measured cost. FIVE transformations in this round were designed against the
`vectorize-late` dump and every one fired on nothing, because that dump shows the body after
the cleanup passes have already run. The rule now recorded: before writing a transformation
for a pass, dump the IR as THAT pass sees it, and confirm the change fires with a
byte-identical A/B before investing in tests and a knob.

## Why it is slower, measured — and a correction to my own framing

I first reported this as "removed 11 instructions, got slower", and filed it with four other
cases this round under "removing hot-loop instructions gets cancelled by alignment". **That
framing was wrong for this case, and the real cause is plainer.**

I counted instructions in the FUNCTION. Counting the hot loop instead:

| | loop span | loop insns | mov | shr | shl | 32B fetch blocks | pad inside |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| copy-prop OFF | 179B | **47** | 16 | 4 | 2 | 6 | 0 |
| copy-prop ON | 200B | **53** | 19 | 5 | 3 | 7 | 1 |

`main` went 137 -> 126, but **the hot loop went 47 -> 53**. The eleven instructions removed
were OUTSIDE the loop, and the loop itself gained six — including more shifts, which copy
propagation cannot introduce on its own, so its rewriting perturbed a downstream decision
(layout or if-conversion) that pulled work INTO the loop. Neither arm spills in the loop (zero
`rbp`-relative operations in both), so this is not register pressure.

A 13% larger hot loop straightforwardly explains a 1.06% slowdown on a
misprediction-dominated program. No alignment mysticism required.

**The rule that follows, and it is sharper than what I had:** count instructions in the HOT
LOOP, not in the function. A function-level count can move the opposite way from the loop that
actually runs.

Re-examining the other cases with that rule: h1's `licm-pointer-loads` arm (9 versus 12
instructions per ITERATION, 1.49x slower) and p2's write-back collapse (one instruction
removed from the loop, 0.4% slower) were both counted at loop granularity already, and both
still show padding appearing inside the loop body. So the alignment observation stands for
those two and is withdrawn for this one.

