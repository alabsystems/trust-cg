# p2_collatz's 1.9%: exactly two excess instructions, and both are in already-refuted classes (2026-09-29)

p2 is the smallest remaining gap — **1.0190x LLVM**, needing 1.9%. Diffing its innermost loop against
LLVM's for the first time reduces it to **two** instructions, and names both.

| | insns | span |
| --- | ---: | ---: |
| trust-cg | **11** | 36 B |
| LLVM | **9** | 28 B |

```
tcg                                  LLVM
  mov    %rcx,%rdx                     mov    %esi,%r8d      <- 32-bit copy, for the parity test only
  shr    $0x1,%rdx                     lea    (%rsi,%rsi,2),%r9
  lea    (%rcx,%rcx,2),%rax            inc    %r9
  add    $0x1,%rax                     shr    $1,%rsi        <- shifts the CARRIED register IN PLACE
  bt     $0x0,%rcx                     test   $0x1,%r8b
  cmovb  %rax,%rdx                     cmovne %r9,%rsi       <- result lands in the carried register
  inc    %rsi                          inc    %rdx
  mov    %rdx,%rcx   <- [1]            cmp    $0x1,%rsi
  xchg   %ax,%ax     <- [2]            jne    loop
  cmp    $0x1,%rdx
  jne    loop
```

## [1] The loop-carried write-back — the refuted two-address tie

LLVM shifts `c` **in place** in the loop-carried register (`shr $1,%rsi`), having first saved only
the low byte it needs for the parity test (`mov %esi,%r8d`). Its `cmovne` therefore writes the
carried register directly, and there is no write-back.

trust-cg computes into a scratch (`mov %rcx,%rdx ; shr $1,%rdx`), keeps `%rcx` live for the `lea`
and the `bt`, and so must copy the result back: `mov %rdx,%rcx`.

Both make exactly one copy of `c`; the difference is *which register the result lands in*. Making
it land in the carried register is the two-address expansion tying the destination to a different
operand — which `x86_two_addr_expand`'s module doc records as **REFUTED at +24% on p1**, with
"This pass deliberately has NO commute logic; keep it that way." p1_xorshift is at 0.9998x today,
so that refutation is protecting a program currently at parity.

## [2] `xchg %ax,%ax` — two bytes of NOP inside the hot loop

That is JCC-erratum alignment padding, executed on every one of p2's ~250 million inner
iterations. Removing it is the `no-x86-jcc-align` lever, and removing JCC padding on this AMD host
was measured at **1.03x SLOWER**. Also refuted.

## So p2's 1.9% is two instructions, both already priced

This is worth recording precisely because 1.9% on an 11-instruction loop looks like the easiest of
the six gaps, and it is not: one excess instruction is protected by a +24% measurement on a program
currently at parity, and the other by a 1.03x measurement on this host's branch padding.

The only untried route for [1] is the NARROW commute discriminator described in
[the b1 refutation set](../2026-09-29-b1-refutation-set/) — commute only when the LHS is live and
the RHS dies. p2's shape fits it (`c` live for the `lea` and `bt`, the shift result dying into the
cmov). That remains unbuilt for the reasons given there: an explicit instruction in the pass not to,
a measured +24% to overturn, and — now — the observation that p2 would gain at most one instruction
of the two.

## Status of the clause

Unchanged by this report. b1 1.1199x, h3 1.0990x, p4 1.0825x, h4 1.0537x, p2 1.0190x, h2 1.0117x.

With this, all six remaining programs have been diffed at loop level and each one's excess is
attributed:

| program | excess | attributed to |
| --- | --- | --- |
| b1 | ~5 insns/iteration | loop specialization (unbuilt); three other routes refuted |
| h3 | 8 insns | memory-latency bound — removing 3 measured 0% |
| p4 | per-instruction cost, not count | mostly the gcc/LLVM gap; we are 1.026x clang |
| h4, h2 | 4 of 12 in the vector loop | allocator spill; fix needs TV-5 extended to spill-slot dataflow |
| p2 | **2 insns** | the two-address tie (+24% p1) and JCC padding (1.03x this host) |
