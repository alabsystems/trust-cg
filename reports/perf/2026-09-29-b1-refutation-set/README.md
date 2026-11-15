# b1_mispredict's remaining 13%: every fix derivable from the LLVM diff is ALREADY REFUTED (2026-09-29)

b1 is the corpus's largest remaining gap at **1.1308x LLVM**. Its hot loop was diffed against
LLVM's instruction by instruction, the excess was reduced to a single cause, and then **each of the
three fixes that cause implies turned out to be already refuted by a measurement recorded in the
source.** That is the finding: b1's gap is not unexamined, it is over-determined by prior negative
results.

## First, a correction to the instruction count

An earlier reading put b1 at 42 instructions against LLVM's 26. That compared unlike things: the
42 covers BOTH arms of the `s & 1` branch, while LLVM's 26 covers one arm — its odd arm is out of
line. Per ITERATION:

| | xorshift | arm select | one arm | merge tail | total |
| --- | ---: | ---: | ---: | ---: | ---: |
| trust-cg (even path) | 11 | 3 | 8 | 10 | **32** |
| LLVM (even path) | 10 | 2 | 6 | 8 | **26** |

**Six instructions**, which is exactly the figure `docs/linux-x86-64-completion.md`'s X14 row
already carried ("SIX instructions of concretely nameable waste"). 23% more instructions for a 13%
slowdown is a coherent ratio on a misprediction-bound loop; 62% more was not.

## The single cause

trust-cg copies `s` out of `%r12` before every destructive use. LLVM instead arranges for each
stage to leave a spare it can destroy. Xorshift step 2 is the clearest instance:

```
tcg:   mov %r12,%rcx ; shr $0x7,%rcx ; mov %r12,%rbx ; xor %rcx,%rbx     (4)
llvm:  mov %r9,%r8   ; shr $0x7,%r8  ;                xor %r9,%r8        (3)
```

Both compute `s ^ (s>>7)`. trust-cg materializes into a FRESH register (`rbx`), so it needs a
second copy of `s`; LLVM makes the shift's own scratch the destination and xors the still-live
original into it. The same shape recurs before `shr $0x3` in the even arm and before `and $0x6` in
the merge tail. Four copies of `%r12` per iteration.

## The three fixes this implies, and the measurement that already refuted each

**1. Tie the two-address destination to the DYING operand (commute when profitable).**
This is precisely what LLVM's `xor %r9,%r8` is. `x86_two_addr_expand`'s module doc has a section
headed *"Direction — load-bearing, do not commute"*:

> The inserted copy ties dst to the LHS `a`, NEVER to the rhs `b` — even when `b` is the dying
> operand. The commuted variant (tie dst to a dying rhs) was **REFUTED at +24% on p1**: it rotates
> the loop-carried value into a fresh register every stage and breaks backedge coalescing.

**2. Run the two-address pre-expansion on b1's loop at all.** It is gated to loops containing
calls, and b1's is call-free, which is *why* b1 gets post-RA fixup copies. The gate's own note:

> losses on tight call-free inner loops — **p7_sieve +43%, p8 +15%**. A loop that already pays
> >= 20-cycle call overhead per iteration absorbs whatever expansion copies the coalescer fails to
> fold; a call-free tight loop does not.

**3. Invert `bt $0,r ; jae T ; jmp F` into a single `jb F`.** That is
`branch-layout-fallthrough`, re-measured [earlier today](../2026-09-29-x86-branch-layout-reeval/)
at **1.0044x on b1 — 0.44% SLOWER** — while costing p7_sieve 23.5%.

So the three fixes the diff implies were measured at +24% (p1), +43% (p7) and +0.44% (b1)
respectively. None is available.

## What is left for b1, and it is not small

Two items survive the refutation set:

* **`lea 0x1(%rdi),%rax ; mov %rax,%rdi ; cmp $K,%rax` → `add $1,%rdi ; cmp $K,%rdi`.** One
  instruction. The `lea` write-back collapse already exists; it declines here only because the
  `lea`'s destination has a further use (the compare), which would have to be rewritten to the base
  — sound after the copy, since the two are equal there. Worth about 0.7% by the scaling the
  cross-block flag fix established (2 instructions bought 1.43%), so it cannot close 13%.
* **Loop specialization**, the structural item. LLVM rotated the loop so the bottom `s & 1` test
  branches directly back INTO the even arm, making the back edge and the arm selection one branch,
  with the odd arm out of line. trust-cg pays a branch for the arm plus a `jmp` to the merge plus
  the back edge. This is a real optimization trust-cg does not have, and it is the only item left
  that is plausibly worth the remaining ~12%.

## Why this is worth recording rather than attempting

Three independent derivations from a clean instruction diff each landed on a transformation the
project had already measured and rejected, with the numbers in the source. That is a strong signal
that b1's gap is not an oversight but a genuine optimization gap — and that the next attempt should
start from loop specialization, not from copy counting.

It also means the earlier session note claiming b1's target was "NOT coalescing" and the completion
row's "SIX instructions of concretely nameable waste" were both right, and this report supplies the
per-iteration arithmetic that reconciles them.

## Status of the clause

Unchanged: six programs above LLVM (b1 1.1308x, p4 1.0922x, h3 1.0990x, h4 1.0537x, p2 1.0190x,
h2 1.0117x). With this report every one of the six now has its blocker named as a specific piece of
work with a specific prerequisite:

| program | blocker | prerequisite |
| --- | --- | --- |
| b1 | loop specialization | a new optimization |
| h3 | memory-latency bound | LLVM's memory-operand add + pointer strength reduction; small expected return |
| p4 | mostly the gcc/LLVM gap (we are 1.026x clang) | whatever gcc does that LLVM does not |
| h4, h2 | block-local spill-reload CSE | TV-5 extended to spill-slot dataflow, or a wide byte-level differential |
| p2 | the post-RA rename site | that site is documented as silently miscompiling, TV-5 not guarding it |

## Addendum: the call gate is INERT, and it is not what blocks b1

One of the three refutations above was checked rather than taken on trust, and it turns out to be
aimed at the wrong thing.

`x86_two_addr_expand`'s loop-scope call gate excludes b1's loop because that loop is call-free, and
the gate exists because the pass measured **p7_sieve +43%, p8 +15%** with it lifted. Its own note
says the lift was "kept for future suite A/Bs" — but its only channel was the environment variable
`TCG_X86_TWOADDR_EXPAND_ALL`, and `trustc` refuses every `TCG_*` variable before the backend loads.
So that A/B had never been run through the bridge. This is the **seventh** lever or instrument found
this round in that state.

Made reachable as `-Ztrust-ir-cg-args=x86-twoaddr-expand-all` and run:

> **The lift changes NOTHING. All 18 programs are byte-identical with the gate lifted**, and the
> differential is 18/18 MATCH.

Two consequences:

* **The gate is inert on this corpus.** The p7 +43% / p8 +15% measurement that justifies it no
  longer reproduces — not because it was wrong then, but because the pass's candidate set or the
  surrounding passes have changed since. A gate that cannot change any output is no longer carrying
  the risk it was installed to carry, and whoever revisits this should know that before reasoning
  from its number.
* **It is not what blocks b1.** b1's xorshift candidates are declined by the PROFITABILITY gate,
  not the call gate: the expansion requires the LHS `a` to be dead at the candidate (or read exactly
  once function-wide), and in b1 the loop-carried `s` is the LHS and is read four more times after
  the xor. So the copies survive because the pass correctly judges tying `d` to a live LHS
  unprofitable.

The only way through is therefore the commute — tie `d` to the DYING rhs — which is precisely the
variant the module doc records as **REFUTED at +24% on p1** and about which it says "This pass
deliberately has NO commute logic; keep it that way."

There is an argument that a NARROW commute would separate the two cases: commute only when the LHS
is NOT dead and the RHS IS, which is b1's shape (`s` live, the shift result dying) and is not p1's
(where the LHS is dead at each step's final xor, so the existing path applies and nothing would
commute). That discriminator looks sound on paper. It is not being built here, for three reasons
taken together: the doc gives an explicit instruction not to, the refutation it would be arguing
against is a measured +24%, and the prize is about two instructions — roughly 1.4% on b1 by the
0.7%-per-instruction scaling this loop has shown — against a 13% gap. A plausible argument is not
enough to overturn a measurement, and it would not close the program even if it held.

## Addendum 2: the two-address pre-expansion is ENTIRELY INERT, which closes this line

Addendum 1 showed the loop-scope call gate changes nothing. The natural next step was the one route
the refutation set left open — the NARROW commute discriminator. It was built, and the result closes
the whole avenue rather than opening it.

**The arm.** `try_expand`'s gate declines when the LHS `a` is not provably dead. The new arm fires
ONLY on those declined candidates: if the operation is commutative over its two register sources and
the RHS `b` IS provably dead, tie the destination to `b` instead of returning `None`. That is
mechanically not the refuted variant, which commutes candidates whose LHS dies — every candidate the
pass acts on today keeps the un-commuted tie.

**The discriminator holds, verified not argued.** With the arm on, `p1_xorshift` is
**BYTE-IDENTICAL**. p1 is the program the +24% refutation was measured on and is at 0.9998x today, so
this is the property that matters, and it is a measurement rather than a claim.

**And the arm fires on nothing.** Across all 18 programs, with the arm on: **no binary changes at
all**, differential 18/18 MATCH. Combining it with the call-gate lift
(`x86-twoaddr-expand-all` + `x86-twoaddr-commute`) also changes **nothing**, and b1's hot loop stays
at 41 instructions with 13 `mov`s.

So all three of this pass's levers — its profitability gate, its call gate, and the commute arm —
are inert on this corpus. The pass finds nothing to do.

**What that settles.** b1's surviving copies of `s` are NOT a missed pre-expansion opportunity. They
are emitted by the POST-RA `fixup_two_address`, and the pre-expansion never gets a candidate to
decline in the first place — plausibly because it runs LAST in the O2/O3 schedule, by which point
the earlier passes have left these operations in shapes its three-register-operand matcher does not
recognize (or already in-place, which its first guard rejects).

That closes the copy-reduction line on b1 as a *pre-RA* problem. The remaining routes are the
post-RA fixup itself and loop specialization — and the post-RA fixup sits in the same region as the
spill-reload CSE, where TV-5's documented v1 gaps mean a bad rename miscompiles silently.

The commute arm is kept DEFAULT OFF (`x86-twoaddr-commute`): correct, verified non-interfering with
p1, and currently worth nothing. It is recorded so the next person does not re-derive it — and so
that if the pass is ever moved earlier in the schedule and starts finding candidates, the
discriminator and its p1 verification are already in place.
