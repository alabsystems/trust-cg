# The one non-refuted item on b1, built and measured: it buys 0.39% and costs 1.7% elsewhere (2026-09-29)

[The b1 refutation set](../2026-09-29-b1-refutation-set/) left exactly one item that prior
measurement had not already rejected: collapsing b1's latch advance in place. This is that item,
built, tested and measured. **It works, and it does not pay.** It ships DEFAULT OFF with the
numbers, and the default instruction stream is byte-identical to before.

## What was missing, and a correction on the way

b1's latch reads, in the disassembly,

```
lea 0x1(%rdi),%rax ; mov %rax,%rdi ; cmp $0x3938700,%rax ; jb
```

and `latch_advance_collapse_run_on_block` exists precisely for
`AddRI n,c,k ; MovRR c,n ; Cmp n,K ; Jcc` → `AddRI c,c,k ; Cmp c,K ; Jcc`. So why did it decline?

**First correction: the `lea` is not a `Lea`.** Checking the IR with `trace-peephole-entry` rather
than the disassembly, b1's advance is already `AddRI [v109, v9, Imm(1)]` — the handled spelling.
The `lea 0x1(%rdi),%rax` is just how the ENCODER spells a three-address `AddRI` on a
two-address ISA. A `Lea` arm was added anyway (it is a strict generalization of the same rewrite,
and the flag write it introduces is overwritten by the matched `Cmp`), but it is not what b1 needed.

**The actual blocker is adjacency.** b1's latch in the IR is:

```
AddRI [v109, v9, Imm(1)]        <- the advance
MovRR [v11, v29]                <- an UNRELATED carried copy
MovRR [v9,  v109]               <- the write-back
MovRR [v10, v107]               <- another unrelated copy
CmpRI [v109, Imm(60000000)]
Jcc
```

The matcher required all four adjacent. The ISel interleaves the loop's *other* carried copies
between them, so the window never matched — on b1 or anywhere else with more than one carried
value.

## The widened window, and the two conditions it needs

Searching forward instead of requiring adjacency needs exactly two scans, and they are the whole
soundness argument:

* **Between the advance and the write-back, nothing may MENTION `c`.** After the rewrite `c` is
  clobbered at the advance, so a reader in that range would observe the *advanced* value instead of
  the old one. (Class-blind on the register id, as everywhere else in this file.)
* **Between the write-back and the compare, nothing may DEFINE `c` or `n`, and nothing may read
  the flags.** The compare is rewritten to read `c`, so `c` must still hold the advanced value when
  it is reached.

Both are pinned by refutations: `latch_collapse_refuses_when_c_is_read_before_the_write_back` and
`latch_collapse_refuses_when_c_is_redefined_before_the_compare`.

## Measured: it fires widely and is a NET LOSS

Widened, it changes **9 of the 18** programs, with the differential intact (18/18 MATCH).
`taskset -c 2`, 18–30 interleaved rounds, `min`, with a byte-identical control per program:

| program | new/old | control | verdict |
| --- | ---: | ---: | --- |
| b1_mispredict | **0.9961** | 0.9993 | 0.39% FASTER |
| h3_box_leak | **1.0173** | 0.9986 | **1.7% SLOWER** |
| v3_popcount | 1.0028 | 0.9992 | 0.28% slower |
| h1, h4, m2, p1, p5, p6 | 0.9982–1.0038 | — | neutral |

So it buys **0.39% on the largest gap** and costs **1.7% on h3_box_leak** — and h3 is itself one of
the six programs still above LLVM, so the change makes the clause *worse*, not better
(h3 1.0990x → 1.1149x). Removing an instruction from h3's loop made it slower: the fifth time this
corpus has shown that non-monotonicity, after p7 (23.5% on a smaller loop), h1's LICM arm (1.49x),
p2's write-back (0.4%) and b1's copy-prop (1.06%).

## What shipped

`-Ztrust-ir-cg-args=x86-latch-window`, **DEFAULT OFF**. With it off the matcher keeps the exact
previous behaviour — `AddRI` spelling only, strict adjacency — and the default build is
**byte-identical to the pre-change build on all 18 programs**, verified rather than assumed.
`latch_collapse_window_is_off_by_default` pins both directions: the non-adjacent shape declines
with the gate off and collapses with it on, so neither arm is vacuous.

Eight tests now cover the transform: the original counted-loop latch, the two pre-existing
refutations, the `Lea` spelling, a `Lea` whose temp escapes, the non-adjacent window, the two
window soundness conditions, and the gate itself.

## Status of the clause

Unchanged, and deliberately so: shipping this would have moved b1 1.1308x → 1.1264x while moving
h3 1.0990x → 1.1149x. Six programs remain above LLVM. What this adds is the closing of the last
non-refuted cheap item on b1 — with a number rather than a guess — which leaves **loop
specialization as the only remaining candidate for b1's ~12%**.
