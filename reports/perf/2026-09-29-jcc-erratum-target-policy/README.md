# `p2_collatz`'s whole remaining gap is an INTEL erratum workaround, and this host is AMD (2026-09-29)

`p2_collatz` had been 1.0190x LLVM -O3 with both of its two excess instructions
refuted, and was recorded as "not the easy one". Its entire gap is the Intel JCC
erratum padding.

| program | workaround ON (previous default) | workaround OFF |
| --- | ---: | ---: |
| **`p2_collatz`** | 1.0198 / 1.0191 | **1.0003 / 1.0005** |
| `b1_mispredict` | 1.1211 / 1.1208 | 1.1322 / 1.1322 |
| `p1_xorshift` | 1.0001 / 1.0000 | 0.9999 / 1.0000 |

`taskset -c 2`, 120 interleaved rounds, minimum of each, both arms carried twice as
byte-identical copies (spreads 0.01–0.04%). The knob
`-Ztrust-ir-cg-args=no-x86-jcc-align` — added earlier in this campaign precisely
because the pass had no reachable lever under `trustc` — is what makes this
measurable from one dylib.

## The mechanism, established rather than assumed: ONE 2-byte NOP in the loop

This corpus has already produced a 14.8% swing from pure code RELOCATION today, so
"padding made it slower" needed distinguishing from "padding moved the loop". The
disassembly settles it. Diffing `p2_collatz`'s `main` between the two arms, the whole
difference is four things:

```
  < nopw   0x0(%rax,%rax,1)      ; relocated (outside the loop)
  < jmp    209af  /  > jmp 209ad ; a 2-byte target change, consequent
  < xchg   %ax,%ax               ; REMOVED — and this one is INSIDE the hot loop
  > int3 int3                    ; trailing trap padding, after `ret`
```

and that `xchg %ax,%ax` sits here:

```
  20980:  (loop head — the target of the back edge)
   ...
  2099b:  mov    %rdx,%rcx
  2099e:  xchg   %ax,%ax     <- 2-byte NOP, retired EVERY iteration
  209a0:  cmp    $0x1,%rdx
  209a4:  jne    20980       <- back edge
```

The padder inserted it so the `jne` would not straddle the 32-byte boundary at
`0x209a0` — without it the branch spans `2099e..209a4`, exactly the erratum's shape.

Crucially **the loop body is at the SAME address in both arms** (head `20940`, back
edge `20980`), so this is NOT the relocation effect that produced h3's swing. It is a
NOP retired once per iteration, and it is `p2_collatz`'s entire gap.

## The erratum is Intel's, and the host is not

Intel doc 334524 describes a SKYLAKE-FAMILY defect: a jump whose last byte touches a
32-byte boundary is dropped from the decoded-instruction cache. The workaround is to
pad so branches do not straddle, which this backend does unconditionally
(`x86_jcc_erratum_pad`, plus the 32-byte function and section grid the pass's own
doc says must move with it).

This host is an **AMD Ryzen 9 9900X3D**. AMD Zen parts do not have the erratum. So
every runtime figure this campaign has published was taken with an Intel workaround
active on hardware that does not need it — costing `p2_collatz` its entire remaining
gap, gaining `b1_mispredict` one percent, and neutral on `p1_xorshift`. On unaffected
hardware the padding is not a workaround at all; it is a layout perturbation whose
sign varies per program, which is the same lesson `h3_box_leak`'s 14.8% taught
earlier today from the other direction.

## What landed: a target-CPU policy, deliberately one-sided

The workaround now stays ON unless `-C target-cpu` names a processor from an
ALLOWLIST of families that provably lack the erratum, and that allowlist contains
**only AMD families** (`znver*`, `bdver*`, `btver*`, `k8`, `amdfam10`, and the older
Athlon/Opteron/Geode spellings).

Everything else keeps the workaround: every Intel CPU, `x86-64` and the other
generic levels, and any name this backend does not recognise. The asymmetry is the
point — "an AMD part does not have an Intel erratum" needs no per-model table,
whereas deciding WHICH Intel parts are affected does, and getting that wrong removes
a workaround from hardware that needs it. `native` is deliberately excluded: it
resolves to whatever machine ran the compiler, so honouring it would make the
emitted code depend on the build host rather than on a named target.

Verified to fire exactly where intended, per program:

```
p2_collatz:    znver4 vs generic: DIFFERS (fired)
p2_collatz:    znver4 vs knob-off: IDENTICAL (same as the explicit opt-out)
p2_collatz:    skylake vs generic: IDENTICAL (workaround kept)
b1_mispredict: (same three)
p1_xorshift:   (same three)
```

The `znver4`-vs-knob-off identity is the useful one: it shows the target rule changes
NOTHING ELSE — the backend does not otherwise act on `-C target-cpu`, so this
isolates the policy from any feature-gate effect.

**The default lane is unchanged by construction, not merely by measurement.** The
policy value is `knobs::is_enabled(NO_X86_JCC_ALIGN) || target_lacks_erratum`, and
with no `-C target-cpu` the second term is `false`, so the install is the same
`false` it was before. One install, not two: the lock is install-once and a second
`set` would be reported as an incompatible policy and fail the compile.

## Measured on a named AMD target, both lanes at `-C target-cpu=znver4`

| program | LLVM -O3 | trust-cg | | vs LLVM |
| --- | ---: | ---: | ---: | ---: |
| **`p2_collatz`** | 163.898 ms | 164.144 / 164.290 ms | | **1.0015 / 1.0024** |
| `p1_xorshift` | 448.556 ms | 448.544 / 448.656 ms | | 1.0000 / 1.0002 |
| `b1_mispredict` | 184.695 ms | 215.558 / 215.472 ms | | 1.1671 / 1.1666 |

So on a target that names this host's family, **`p2_collatz` matches LLVM** (1.0015x
against a 0.09% copy-to-copy floor).

## And a refutation this settles about `b1_mispredict`

`b1` gets WORSE relative to LLVM at `znver4` — 1.121x generic, 1.167x at znver4 —
because LLVM gains more from the named target than trust-cg does (LLVM 190.25 ->
184.70 ms; trust-cg from 213.29 to 215.56 ms). That rules layout out as b1's cause: a
layout artifact would not track the target's capabilities. b1's gap is real codegen,
consistent with the standing diagnosis that LLVM duplicates the loop body so the
`s & 1` arm is entered with no taken branch.

## Why the DEFAULT was not simply flipped

The obvious alternative — turn the workaround off by default and match LLVM, whose
own `-mbranches-within-32B-boundaries` is opt-in — was tested and rejected on
evidence. A whole-corpus A/B of the knob changes **all 18 programs**, not the handful
that carry a padded branch in a hot loop:

```
DIFFERS  b1 h1 h2 h3 h4 m1 m2 p1 p2 p3 p4 p5 p6 p7 p8 v1 v2 v3   (18/18, all MATCH)
```

That is because the knob also moves the 32-byte function and section alignment grid
— the pass's own doc says the three must move together — so disabling it re-rolls
every binary's layout. Today's other measurement puts a number on what such a re-roll
is worth: 14.8% on `h3_box_leak`, from relocation alone, with its hot loop
byte-identical. A default flip would therefore buy an 18-program layout lottery in
exchange for one program's established 1.9%, and any net figure from it would be an
outcome rather than a mechanism.

The target-CPU rule has no such problem. It fires only where the workaround provably
has NO benefit to weigh against its cost, and it leaves the generic lane — and so
every published figure — untouched.

## What this does NOT claim

The generic-target lane is unchanged, so the corpus figures the campaign publishes
do not move: `p2_collatz` is still 1.019x there, and that 1.9% is now an EXPLAINED
cost — the price of a correct-by-default erratum workaround for an unnamed x86-64
target — rather than an unexplained codegen gap. A build that names its target gets
parity.
