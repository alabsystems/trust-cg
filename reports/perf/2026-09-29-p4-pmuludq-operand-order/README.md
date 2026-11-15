# p4_matmul's remaining 8%: the packed-multiply operand order is NOT the lever, and the reason is a documented decline in the XMM bridge collapse (2026-09-29)

`p4_matmul` is 1.0794x LLVM -O3. This is a REFUTATION report: a change that looked
like a clean 13% instruction win in its hot loop was built, measured, and reverted,
and what the measurement found is a different, nameable blocker.

## Where p4's gap actually is

Its innermost `j` loop is vectorized and fully unrolled, with no bounds checks —
so the diagnosis recorded earlier ("3 bounds checks + 2 invariant recomputations =
8 of 26 hot-loop insns") is STALE; the vectorizer handles those now.

Per 2-element lane pair, trust-cg emits 15 instructions and LLVM 11:

```
  trust-cg (15)                              LLVM (11)
    movdqu 0x10(%rcx),%xmm1   ; load b         movdqa %xmm15,%xmm0
    movdqa %xmm4,%xmm3        ; copy a_lo      psrlq  $0x20,%xmm0
    pmuludq %xmm1,%xmm3                        pmuludq %xmm12,%xmm0
    movdqa %xmm1,%xmm0        ; copy b         movdqa %xmm15,%xmm14
    psrlq  $0x20,%xmm0        ; b_hi           pmuludq %xmm13,%xmm14
    movdqa %xmm4,%xmm2        ; copy a_lo      paddq  %xmm0,%xmm14
    pmuludq %xmm0,%xmm2                        movdqu -0x80(%rsi),%xmm0
    movdqa %xmm5,%xmm0        ; copy a_hi      psllq  $0x20,%xmm14
    pmuludq %xmm1,%xmm0                        pmuludq %xmm12,%xmm15
    paddq  %xmm0,%xmm2                         paddq  %xmm15,%xmm5
    psllq  $0x20,%xmm2                         paddq  %xmm14,%xmm5
    paddq  %xmm2,%xmm3
    movdqu 0x10(%rax),%xmm0   ; LOAD c
    paddq  %xmm3,%xmm0
    movdqu %xmm0,0x10(%rax)   ; STORE c
```

Two separate differences, and it is worth keeping them apart:

1. **4 `MOVDQA` against LLVM's 2.** Both compilers need the same three `PMULUDQ`
   products (SSE2 has no `PMULLQ`), but `PMULUDQ` is TWO-ADDRESS: the destination
   must hold operand 1, so whichever source sits there is either coalesced onto or
   copied. LLVM ties every product to a `b`-derived value, which DIES; trust-cg
   ties them to the loop-invariant `a_lo`/`a_hi` broadcasts, which stay live, so
   each one pays a copy.
2. **c is re-loaded and re-stored every `k` iteration.** LLVM keeps the whole
   `c` row in XMM accumulators across the `k` loop (`paddq %xmm15,%xmm5`), which is
   MAC register blocking — a pass this repo HAS for AArch64
   (`crate::mac_reg_block`, on `MachFunction`) and does not have for x86.

## The change that looked obvious, and what it measured

Difference 1 has a two-line fix: reorder the compose so each product is written
with the dying `b`-derived operand in the tied position, emitting `bh` first and
`t1` (which consumes `b`) last. That is arithmetically free — `PMULUDQ` is
commutative and already listed in `is_x86_commutative_two_address_rr` — and it
should make two of the four copies coalesce away.

It was built with a tracked opt-out (`no-x86-pmuludq-b-first`) so both orders came
from ONE dylib, and measured:

| arm | main instructions | `movdqa` in main | min | vs LLVM -O3 |
| --- | ---: | ---: | ---: | ---: |
| `a`-first (previous) | 497 | 18 | 62.840 ms | 1.0794 |
| `a`-first, copy | — | — | 62.899 ms | 1.0804 |
| **`b`-first (the change)** | **497** | **18** | 62.975 ms | 1.0817 |
| `b`-first, copy | — | — | 62.940 ms | 1.0811 |

17 of 18 corpus programs byte-identical, p4 MATCH — so the change fires and changes
only p4. And it buys **nothing**: identical instruction count, identical `movdqa`
count, runtime inside the copy-to-copy floor. Reverted.

## Why it bought nothing — the actual blocker

The reorder does put the dying operand in the tied slot. The copies survive anyway,
because collapsing them is the job of the post-fixup XMM bridge collapse, and that
pass DECLINES here for a reason its own contract states:

> Every read of `d` from `copy_pos + 2` to `d`'s next full redefinition is renamed
> to `s`, so each must be a PURE use (a tied read-modify of `d` cannot be renamed
> without redirecting its def).

Each product is immediately consumed by a `PADDQ` that read-modifies it. So the
one read that would have to be renamed is itself a tied read, and the scan refuses
— correctly, under its current contract.

Removing these copies therefore needs the collapse extended to propagate a rename
through a CHAIN of tied ops (rename the tied read *and* redirect that op's
destination, transitively). That is a real increment with its own soundness
argument, not an operand-order tweak, and it is the prerequisite for the reorder
to pay. The reorder is not in the tree; it is two lines and this report records
exactly what it does and does not achieve.

Noted in passing: the XMM bridge collapse's only kill switch is
`TCG_NO_X86_XMM_BRIDGE_COLLAPSE`, an environment variable `trustc` refuses before
the backend loads — so it cannot be A/B'd through the bridge at all. That is the
ninth instrument found in that state this campaign.

## What this leaves

p4's 8% decomposes into two named capabilities, neither of which is a tuning knob:

* the XMM tied-chain rename above, worth 2 of 15 instructions per lane pair;
* MAC register blocking for x86, worth the other 2 (the `c` load and store), and
  the larger of the two because it also shortens the dependency chain.

And the standing caveat: p4 is **1.026x clang**, so a large part of the 8% is the
gcc-versus-LLVM gap on this kernel rather than anything this backend does.
