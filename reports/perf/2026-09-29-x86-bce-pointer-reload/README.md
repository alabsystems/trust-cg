# h1: 2.6356x -> 2.3488x LLVM by eliminating the bounds check its loop condition already proved (2026-09-29)

**11.1% faster on h1, P = 1.000, against an in-batch identical-binary floor of 0.03%.** The
largest win of this round, and it lands on the program with the largest gap.

It also vindicates withdrawing my own claim, earlier today, that h1's bounds check "is not a
cost". It was.

## What the check looked like

h1's scalar loop reloaded `v.len()` **twice** per iteration and compared it twice — once for
`while k < v.len()`, once for the `v[k]` bounds check — with the second predicate identical to
the first:

```
mov  (%rdi),%rax        ; RELOAD v.len
cmp  %rax,%rbx          ; the while condition k <u len
jae  exit
mov  %rbx,%rcx          ; copy of k
mov  (%r8),%rdx         ; RELOAD v.ptr
mov  (%rsi),%rax        ; RELOAD v.len AGAIN
cmp  %rax,%rcx          ; the BOUNDS CHECK -- same predicate, three instructions later
jae  panic
```

`rsi` is a plain `MovRR` copy of `rdi` made in the loop preheader, and `rcx` a plain copy of
`rbx`, so both compares read **the same length from the same address** and **the same index**.

## Two things had to be fixed, and only the first was the one I expected

### Case 5: same POINTER, not same frame bytes

`x86_bounds_check_elim`'s case 4 (`same_value_by_frame_reload`) proves two loads equal only when
`resolve_frame_ref` resolves BOTH to the same **frame bytes**. h1's length address is a computed
pointer (`lea 0x10(%r10),%rdi` off a pointer loaded out of a slot), not `[rbp + disp]`, so case 4
cannot classify it and declined — exactly what the trace showed:

```
[bce] ...h1x104main:Block(9) decline: rhs not same-value: guard v95 vs check v107
```

Case 5 (`same_value_by_pointer_reload`) proves it the direct way: identical load opcode, the same
canonical `(base vreg, disp)` — `canon` already follows the `MovRR` — the shared base
**single-def function-wide** so the address cannot move, and **no store of any kind** in the
region between the loads. That last condition is deliberately STRICTER than case 4's aliasing
test: this arm has no frame target to compare a store against, so it refuses on any store, call,
`Push` or `Pop`. It is precisely the premise upstream named as missing when it declined to assume
a write-free loop sufficed — *"a store may separate the trip-bound load from the element guard's
reload"* — and it is discharged by scanning that region, not assumed.

The region is the one the pass already models: `region_between_loads` walks the same two ranges
as `no_aliasing_write_between` (guard load → end of guard block, then top of check block → check
load), and the caller's `CoveredWindow` guarantees that is the path.

### The interaction that actually blocked it: condition (4) flagged a definition as a redefinition

With case 5 in, the trace moved on and declined again:

```
[bce] ...Block(9) decline: a root [v89, v95] is redefined in the covered window
                           (guard Block(8)@0 .. check Block(9)@13)
```

`v95` is case 5's root — **the guard's own load**. The index was admitted by case 3b, which
lowers the redefinition scan's start to the guard-side copy's index (here 0). The widened window
then contains the length root's defining load at index 1, and `operand_redefined_between` is
positional, so it reported that *definition* as a *redefinition*.

The fix excludes **single-def roots** from the scan. The scan exists to catch a MULTI-def root
changing between the guard's read and the check's read; a vreg with exactly one definition in the
whole function cannot change value between two reads, and its one definition must dominate the
guard's read because the guard reads it. Case 4's own doc already asserted this was the intent —
*"both vregs are single-def here, so ... the scan is a trivially-passing no-op"* — which held
only while `scan_from` stayed at the guard compare. So this is a latent defect for **case 4 too**,
unexercised by its tests because they compare `iv` directly rather than a case-3b copy.

## Result

| | hot loop insns | span | per-iteration reloads | branches |
| --- | ---: | ---: | ---: | ---: |
| arm OFF | 12 | 41 B | 3 | 3 |
| **arm ON** | **9** | **29 B** | 3 | 2 |
| LLVM scalar | 5 | 13 B | 1 | 1 |

`taskset -c 2`, 20 interleaved rounds + 3 warm-up, `min` plus `P(a<b)`, h1 scaled 10x
(`passes` 300 → 3000) to clear the 50 ms floor, with a byte-identical copy of the ON binary in
the batch:

| arm | min ms | ratio | P(arm < OFF) |
| --- | ---: | ---: | ---: |
| BCE arm OFF | 228.07 | 1.0000 | 0.000 |
| **BCE arm ON** | **202.80** | **0.8892** | **1.000** |
| arm ON, identical copy | 202.87 | 0.8895 | 1.000 |
| LLVM -O3, no vectorize | 170.45 | 0.7474 | 1.000 |
| LLVM -O3 | 86.34 | 0.3786 | 1.000 |

**11.1% faster at P = 1.000, against a 0.03% floor — 370x the floor.**

| measure | before | after |
| --- | ---: | ---: |
| h1 vs LLVM -O3 | 2.6356x | **2.3488x** |
| h1 vs LLVM's SCALAR loop | 1.3353x | **1.1898x** |

## Correctness

| check | result |
| --- | ---: |
| execution differential, DEFAULT arm | **18/18 MATCH** |
| execution differential, ptr-reload arm ON | **18/18 MATCH** |
| `library/core` at O3, both arms | 6 failed roots, 0 typed refusals, 0 harness errors — identical to before |
| `trust-cg-opt` lib suite | 3834 pass, 0 fail |
| clippy | 162, the pre-change baseline |
| BCE acceptances, default arm, all 18 programs | **0** — the single-def-root fix changes nothing on its own here |
| BCE acceptances with the arm ON | h1: 1, h3_box_leak: 1, others 0 |

Case 5 ships **DEFAULT OFF** (`-Ztrust-ir-cg-args=x86-bce-ptr-reload`). This pass removes bounds
checks: a wrong answer is a memory-safety defect, not a slow program, so a new admission arm is
measured before any default is proposed. Eight tests, both directions: it eliminates on the
copy shape; it is off by default (which also preserves the committed
`keeps_reloaded_len_check_when_the_address_chain_is_not_slot_rooted` pin); and it refuses a store
between the loads, a call between the loads, different displacements, and a multi-def address
register. Two further tests pin the condition-(4) fix: the case-3b interaction must still
eliminate, and a genuinely multi-def root redefined in the window must still decline.

## Two diagnostics this required, both previously unreachable

The branch-form BCE path — the one that decides `while k < v.len() { .. v[k] .. }` — had **no
trace at all**; the carrier path's only trace sat behind `TCG_X86_BCE_CARRIER_DEBUG`, a `TCG_*`
environment variable `trustc` refuses before the backend loads. `-Ztrust-ir-cg-args=trace-x86-bce`
now prints the condition each candidate declined on, and the accept. Every step of the diagnosis
above came from it; without it the two blockers were indistinguishable.

Recorded because it keeps recurring: this is the fourth lever or instrument found this round
whose only channel was an env var the compiler refuses.

## What is left in h1's 9 instructions

* **A dead load survives.** `mov (%rsi),%rax` is immediately overwritten by the element load
  `mov (%rcx,%rbx,8),%rax` — its only consumer was the deleted compare. DCE runs after BCE and
  does not remove it. One more instruction, and a DCE question rather than a BCE one.
* The remaining 8-versus-5 gap is the two surviving invariant reloads (hoisting them is the
  `licm-pointer-loads` arm, measured 1.49x SLOWER), the `jmp` back-edge
  (`branch-layout-fallthrough`, 23.5% worse on p7 globally), and LLVM's index-to-pointer strength
  reduction, which trust-cg does not do here.

## Status of the clause

Still not met, and now: **h1 2.3488x** (was 2.488x at normal scale; 2.6356x scaled), b1 1.1326x,
p4 1.0929x, p2 1.0191x versus LLVM — but this is the first movement on h1 all round, and it came
from the component I had wrongly written off.
