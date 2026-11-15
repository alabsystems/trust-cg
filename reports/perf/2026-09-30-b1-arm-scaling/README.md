# b1's gap is WRONG-PATH WORK, not the branch — and it reconciles two claims I had wrong

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 50 interleaved rounds,
`taskset -c 2`, minimum statistic, the bridge arm carried twice as its own floor.

## The experiment

Three variants, identical unpredictable branch (`s & 1` off an xorshift stream), differing
only in how much work each diamond arm does. `b1_thin.rs` and `b1_fat.rs` are in this
directory; `b1_mid` is the shipped `b1_mispredict`.

| variant | arm bodies | LLVM | trust-cg | ratio |
| --- | --- | ---: | ---: | ---: |
| `b1_thin` | `acc += s` / `acc ^= s` | 67.472 ms | 67.542 ms | **1.0010** |
| `b1_mid` | array `t[j]` RMW, index math | 190.521 ms | 208.572 ms | **1.0947** |
| `b1_fat` | more array work per arm | 196.269 ms | 215.401 ms | 1.0975 |

**With thin arms the bridge is at parity.** The branch is equally unpredictable in all three —
same stream, same 60M iterations, same ~50% misprediction rate. So the branch itself, and the
xorshift chain feeding it, cost the bridge nothing.

The gap appears with arm CONTENT and then saturates: `b1_fat` is barely worse than `b1_mid`
despite considerably more work per arm.

## What this corrects

Two claims made earlier in this campaign were each half right, and the combination is what
explains b1.

**"b1's gap is mispredict recovery."** Too coarse. Mispredict cost is the penalty times the
WRONG-PATH WORK that has to be squashed. Thin arms have almost none, so the same mispredict
rate costs nothing. The branch is not the problem; what sits behind it is.

**"Instruction count does not matter on this core."** True on the PREDICTED path — that is what
the `movdqa` and loop-nest microbenchmarks measured, and they measured zero. It is NOT true in a
mispredicted shadow, where every extra instruction is work the machine performs and discards.

So the two findings are consistent, and the boundary between them is the branch: instructions on
a correctly-predicted path are nearly free here; instructions inside a frequently-mispredicted
diamond arm are not.

## What it implies for b1

The diamond arms are the target, and instruction count in them is a real cost — a direction
this campaign had closed off on the strength of predicted-path measurements. tcg's arms carry
about six more `mov` instructions than LLVM's across the diamond, with equivalent memory
operations (both fuse the array update into an RMW: `xor %r12,-0xa0(%rbp,%rcx,8)` against
LLVM's `xor %rdx,0x10(%rsp,%rdi,1)`).

Note this also explains why the two-address commute arm measured NEUTRAL on b1 when it was
finally made reachable: it removes copies from the xorshift chain, which is on the predicted
path, not from the arms.

## Next step

Attack copy count inside the diamond arms specifically, and measure against `b1_mid` rather
than against a microbenchmark — a predicted-path microbenchmark will report zero for a change
that matters here, which is exactly the trap this campaign fell into. `b1_thin` is the control:
any arm-directed change should leave it at parity and move `b1_mid`.

## Sharpened: the gap is the NON-IF-CONVERTIBLE diamond, and tcg wins when cmov applies

| build | loop insns | unconditional `jmp` | `mov` | vs LLVM |
| --- | ---: | ---: | ---: | ---: |
| `b1_thin` trust-cg | **19** | 0 | 6 | **1.0010** |
| `b1_thin` LLVM | 29 | 0 | 6 | — |
| `b1_mid` trust-cg | 38 | **1** | **12** | 1.0947 |
| `b1_mid` LLVM | 26 | 0 | 6 | — |

Two things follow, and the first is a positive result worth recording as such:

**When if-conversion applies, trust-cg emits a SMALLER loop than LLVM and is at parity.**
`b1_thin`'s arms are single operations, so `X86IfConvert` collapses the diamond to `cmov`,
both backends end up branch-free, and trust-cg's 19-instruction loop beats LLVM's 29 while
timing identically. There is nothing wrong with this backend's handling of an unpredictable
branch per se.

**The gap is the diamond that CANNOT be if-converted.** `b1_mid`'s arms each contain a store
to a different scratch slot — the shipped benchmark's comment says this is deliberate, "defeats
full if-conversion/cmov" — so both backends must branch. There the layouts diverge: trust-cg
keeps both arms inline and jumps over the untaken one, while LLVM sinks one arm out of line and
lets the other fall through into the merge. That is the extra `jmp`, and it sits on a path
mispredicted about half the time.

### What would close it, and what would not

The arm-directed direction is right, but note the accounting does not reduce to a simple
instruction count: trust-cg's 8-instruction arm A versus LLVM's 6 is partly PLACEMENT — LLVM
hoists a destroyable copy of `s` into the header (counted in its 12-instruction header) where
trust-cg makes it inside the arm. Per iteration the totals are about 31 against 26.

So the candidate is a LAYOUT change — sink one arm of a non-if-convertible diamond so the other
falls through — not a copy-count change. `x86-cold-arm-sink` is exactly that transformation and
is already present, but it is gated on the sunk arm being call-bearing, which is how it fires on
0 of 18 corpus programs. b1's arms contain no calls, so the rule cannot reach the one shape in
this corpus that wants it.

Measure any attempt against `b1_mid` with `b1_thin` as the control: an arm-layout change must
leave thin at parity (it is already branch-free there) and move mid.

## CORRECTION: the "extra jmp" does not exist, and the layout fix proposed above is WRONG

The section above says trust-cg pays an extra unconditional `jmp` that LLVM does not, and
proposes relaxing `x86-cold-arm-sink`'s call-bearing gate to remove it. **Both claims are
false.** LLVM's other arm is out of line at `0x208d6` and ends with `jmp 20894`:

```
208d6: imul %rcx,%r9        <- LLVM's arm B, sunk out of line
208da: xor  %rdi,%r9
208dd: mov  %r8d,%edi
208e0: shr  $0x5,%edi
208e3: and  $0x78,%edi
208e6: add  %r9,0x10(%rsp,%rdi,1)
208eb: jmp  20894           <- and it pays a jmp too
```

In a diamond whose arms reconverge, EXACTLY ONE arm pays an unconditional jump under any
layout: `[cond, A, B, M]` makes A jump over B, `[cond, A, M, … B]` makes B jump back to M.
Sinking an arm moves which arm pays; it does not remove the jump. For b1's arms — taken about
50/50 — that is neutral by construction.

**So `x86-cold-arm-sink`'s F9 gate is correct to keep, and relaxing it as proposed would have
been unjustified.** Its comment states the gate IS the justification — "COLD EVIDENCE, the
entire justification … the negation of the refuted profile-free `layout-next == hot` guess" —
and that reasoning holds. Sinking pays only when the sunk arm is genuinely colder, which a call
is static evidence for and a 50/50 branch is not.

### Where b1's gap actually is: diffuse, about 4 instructions per iteration

Counting the executed path (arm A taken) rather than a disassembly span:

| region | trust-cg | LLVM | delta |
| --- | ---: | ---: | ---: |
| header (xorshift + test + branch) | 13 | 12 | +1 |
| arm A | 8 | 6 | +2 |
| tail (rotate/cmov + induction + latch) | 9 | 8 | +1 |
| **per iteration** | **30** | **26** | **+4** |

About 13% more instructions for a measured 9.5% gap — consistent, and spread across all three
regions with no dominant contributor. Part of the arm delta is placement rather than count, since
LLVM hoists a destroyable copy of `s` into its header.

**There is no single lever here.** b1 needs about four instructions per iteration removed across
three regions, which is ordinary codegen quality rather than one missing capability.

### The method error, third occurrence

All three wrong readings of b1 and p4 in this campaign came from comparing DISASSEMBLY SPANS
between two compilers whose block layouts differ, so the spans covered different executed paths.
A span bounded by a backward branch is not an iteration. Count the executed path — pick the
taken-arm sequence explicitly, region by region — or the comparison silently measures different
things. This one nearly produced a change to a correctly-gated layout rule.
