# `get_unchecked` falls off a vectorizer cliff: 1.90x vs LLVM, worse than any corpus violation

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 60 interleaved rounds,
`taskset -c 2`, minimum statistic, the bridge arm carried twice as its own floor.

## The measurement

`p4_unchecked.rs` (in this directory) is `p4_matmul` with its three hot indexing sites
rewritten to `get_unchecked` / `get_unchecked_mut`. Identical arithmetic, identical result
(both exit 111).

| program | LLVM | trust-cg | |
| --- | ---: | ---: | --- |
| `p4_matmul` (checked) | 58.428 ms | 63.190 / 63.242 ms | **1.0815** |
| `p4_unchecked` | 58.449 ms | 111.174 / 111.141 ms | **1.9021** |

LLVM is indifferent to the rewrite — 58.428 vs 58.449 ms, identical to within noise, and
36 `pmuludq` either way. trust-cg loses **76%** relative to its own checked build.

## The cause, pinned

| binary | `pmuludq` |
| --- | ---: |
| `p4_checked` trust-cg | 12 |
| `p4_checked` LLVM | 36 |
| **`p4_unchecked` trust-cg** | **0** |
| `p4_unchecked` LLVM | 36 |

The vectorizer declines COMPLETELY on the unchecked form. The tier responsible is the
saxpy-Q row-register nest, identified by toggling `x86-saxpyq-scalar-mul`: it changes the
checked binary (so the tier fires) and leaves the unchecked binary BYTE-IDENTICAL (so the
tier does not fire).

**And it declines silently.** `trace-vectorize-bail` prints nothing for this tier. The
heap, regarg and winscan tiers all report a condition — the unchecked bail set differs from
the checked one only by two `winscan-bail: outer header idiom` lines and one more
`heap-bail: bound ... is not a 64-bit stack-slot field load` — but none of those is the tier
that matters here. So the 76% loss produces no diagnostic at all.

## Why this matters more than the number

`get_unchecked` in a hot loop is ordinary Rust, not a corner case: it is what code does after
it has already proved its indices. The 18-program corpus contains no such program, so **the
corpus understates this backend's real-world gap.** Against the objective's "every Rust
program … at a performance at least matching LLVM and clang", this single shape is a larger
violation (1.90x) than any of the four the corpus reports (`b1` 1.0947, `p4` 1.0829,
`h4` 1.0341, `p2` 1.0103).

It also reframes the corpus result: the checked-vs-unchecked pair shows the vectorizer's
recognizers are keyed to a specific MIR/ISel spelling rather than to the loop's semantics —
the same dialect-sensitivity already recorded when three recognizer spellings were fixed
earlier in this campaign. A recognizer keyed on spelling will keep finding new shapes it does
not know.

## What was NOT established

This experiment does not isolate what the bounds checks themselves cost. It was run to test
exactly that — tcg's `k` loop carries 4 `jae` per iteration where LLVM's carries none, over
11.5M iterations — but `get_unchecked` changes two things at once: it removes the checks AND
it moves the loop outside the recognizer's dialect. The bounds-check cost therefore remains
open, and answering it needs affine bounds-check elimination inside the compiler, where
vectorization is preserved. It cannot be answered from the source side.

## Suggested next step, in order

1. Add a bail trace to the saxpy-Q row-register nest tier, the way `trace-vectorize-bail`
   covers the others. Its silence is what made a 76% loss invisible; nothing else can be
   diagnosed until that exists.
2. With the condition named, decide whether the recognizer can key on the loop's semantics
   rather than its spelling.

## Step 1 done: the saxpy-Q tier now traces, and it RELOCATES the problem

The tier's 22 bare `return None` sites are now traced as `saxpyq-bail[fn]: reason`, on the
same `trace-vectorize-bail` lever as the heap, regarg and window tiers. The heap tier's own
comment records this same fix being applied to it earlier, for the same reason — "every
rejection was a bare `return None`, so `trace-vectorize-bail` reported the regarg and window
tiers while the tier written for the owning-container shape declined in silence."

Diagnostics only: all 18 corpus programs are BYTE-IDENTICAL with the trace added.

### What it says, and it is not what the section above assumed

| build | `saxpyq-bail` lines in `main` |
| --- | --- |
| `p4_checked` | 2x "side effect (or trap) — refuse", 1x "loop has no preheader" |
| `p4_unchecked` | 2x "side effect (or trap) — refuse" |

The checked build reaches the recognizer THREE times and vectorizes; the unchecked build
reaches it only TWICE. So **the matmul inner loop never reaches the recognizer at all** in the
unchecked build. The tier is not rejecting the loop on any of its 22 conditions — it is never
being asked about it.

That moves the defect upstream of `recognize_saxpyq_loop`, into whatever selects loop
candidates. The window tier's own trace is consistent with this: the unchecked build reports
two extra `winscan-bail: outer header idiom` lines that the checked build does not, so the two
builds' loop nests are being classified differently before any saxpy-Q question is asked.

### Revised next step

Not "teach the recognizer the unchecked dialect" — the recognizer never sees the loop. Find why
the inner loop drops out of candidate selection when the indexing changes, starting from the
`winscan` classification difference (`outer header idiom`), and confirm with an invocation
counter rather than a bail counter, since absence of a bail is what carries the signal here.

## Root cause, reached through THREE layers of silence

The trace had to be added three times before the answer appeared. Each layer looked like the
answer and was not.

| layer | what it said | why it was not the answer |
| --- | --- | --- |
| 1. `recognize_saxpyq_loop`, 22 `return None` sites | unchecked reached it 2x, checked 3x | suggested the loop never reached the recognizer — wrong |
| 2. `recognize_saxpyq_rowreg_loop`, 34 sites + 3 `?` exits | unchecked: 2x "the inner loop is not a saxpy-Q" | so the loop DID reach it; the decline moved back down a level |
| 3. `recognize_saxpyq_loop`'s 7 remaining `?` exits | unchecked: "header is not the recognized `iv <u bound` idiom" | **the answer** |

**`recognize_header` does not accept the loop header that `get_unchecked` produces.** With
checked indexing the header presents the `iv <u bound` shape the recognizer keys on; without
the bounds check the same loop's header is spelled differently, and every tier downstream is
then unreachable. That is the whole 1.90x.

Two things about the shape of this investigation are worth keeping:

* **An `?` operator is a silent `return None`.** Instrumenting the explicit `return None`
  statements in layer 1 produced a confident, WRONG conclusion — that the recognizer was never
  invoked — because the real exits were `?`. Bail counts cannot be trusted as invocation
  counts when `?` is in play.
* **Absence of a bail carried the signal twice.** At layer 1 the unchecked build logged FEWER
  bails than the checked one, which reads as "less rejection" and actually meant "exited
  earlier, unlogged".

## Revised next step

Teach `recognize_header` the unchecked header spelling, or key it on the loop's semantics
(induction variable, monotone bound, trip count) rather than on the comparison's surface form.
This is a vectorization LEGALITY recognizer, so widening it needs the same care as the
`memory_aggregate` work earlier in this campaign: the condition it is really asserting is
"trip count known and iv monotone", and the `iv <u bound` idiom is one spelling of that, not
the property itself.

All three trace layers are diagnostics only: 18/18 corpus programs byte-identical,
`trust-cg-opt --lib` 3879 passed / 0 failed.

## ROOT CAUSE, corrected twice: there is no straight-line vectorizer

The section above named `recognize_header`. That is the proximate symptom, not the cause, and
the correction matters because it changes what the fix is.

Disassembling both builds' loop nests:

| build | inner loop | stride | `imul` | `pmuludq` |
| --- | --- | ---: | ---: | ---: |
| checked | 65 insns | `$0x8` (8 elements) | 0 | **12** |
| unchecked | 318-397 insns | `$0x18` (=24, a whole row) | 96-102 | **0** |

**The unchecked build has no inner `j` loop at all** — it is already unrolled by 24 when the
vectorizer runs. `recognize_header` reports "header is not the recognized `iv <u bound` idiom"
because there is no such header to find, not because the idiom is too narrow.

And it is NOT trust-cg's unrolling. Two tracked kill switches were added for the unroll passes,
which were also env-only (`no-partial-unroll`, `no-const-addr-unroll`), and **neither restores
vectorization** — `pmuludq` stays 0 with either, or both. By elimination the loop arrives from
rustc's MIR already flattened: with `get_unchecked` the frontend's own optimizer unrolls the
constant-trip inner loop before trust-cg sees it.

Which exposes the actual gap:

    $ grep -oE "fn recognize_[a-z0-9_]+" x86_vectorize.rs | sort -u
    ... 15 recognizers, EVERY ONE of them `recognize_*_loop`
    $ grep -ciE "superword|slp|straight.line vector|basic.block vector" x86_vectorize.rs
    0

**trust-cg's vectorizer is exclusively LOOP-based. It has no SLP (superword-level
parallelism) path, so it cannot vectorize straight-line code at all.** LLVM has both, which is
why LLVM emits 36 `pmuludq` for either source form and is indifferent to the rewrite.

So the 1.90x is not a tuning gap or a recognizer dialect gap. It is a missing pass class, and
it fires whenever the frontend hands over an already-unrolled loop — which idiomatic
`get_unchecked` code causes it to do. Widening `recognize_header` would not help; there is no
loop for it to accept.

### Why the earlier answers were wrong, recorded because the pattern repeats

1. "the recognizer's dialect does not know `get_unchecked`" — wrong; the recognizer never sees
   the loop.
2. "`recognize_header` is too narrow" — wrong; its report is accurate, the header genuinely
   does not exist.

Both came from reading a decline message as a cause. A recognizer that says "I did not find X"
is reporting its own view, not the reason X is absent.

## CORRECTION 2: the "missing pass class" conclusion is WITHDRAWN. `recognize_header` was right.

The section above concludes the inner loop does not exist at vectorizer time, that the frontend
unrolled it, and that closing this needs an SLP vectorizer — new capability, a multi-session
project. **That is wrong, and it would have misdirected the next attempt badly.**

### The evidence that settles it

`recognize_saxpyq_rowreg_loop` reaches this line only when it has ALREADY found an inner loop:

```rust
let Some(inner) = recognize_saxpyq_loop(func, preds, idom, inner_lp) else {
    bail!("the inner loop is not a saxpy-Q (its own trace names the condition)");
};
```

That bail fires **twice** on `p4_unchecked`. So an inner loop IS found, and
`recognize_saxpyq_loop` rejects it. Its only decline reasons on this program are
`TrapDivZeroExact` (from the `% 100` in the init loop, present in the CHECKED build too) and
**"header is not the recognized `iv <u bound` idiom"**. So the loop exists and the header
recognizer rejects it — exactly what CORRECTION 1 said before it was retracted.

Corroborating: `-Zmir-opt-level` 0, 1, 2, 3 and 4 all produce `pmuludq=0`. If a MIR pass were
flattening the loop, some level would have changed that. And on x86 only `X86LoopUnroll` is
registered — `MacRowUnroll`, `StridedStoreUnroll` and `ScalarUnroll` are not in the x86 pipeline
at all — and it is opt-in behind a `TCG_*` variable `trustc` refuses. No pass in either compiler
was unrolling anything.

### The error, which is a new one worth naming

The flattened 24-stride shape in the final binary is real, but it is the output of the WHOLE
pipeline, not the input to the vectorizer. Later passes produced it after the vectorizer had
already declined. **Reading a pass's input off the final binary is invalid**: every pass between
that one and the encoder gets to change the picture. A pass's own trace is the only thing that
reports what it saw.

This is distinct from the disassembly-span error recorded in the b1 report, and it is worse,
because the span error produced a wrong measurement while this one produced a wrong ARCHITECTURAL
conclusion — "this backend lacks a pass class" — from a binary that could not have shown that
either way.

### Restored next step

Widen `recognize_header`, or key it on the property it is really asserting (induction variable
monotone, trip count known) rather than the `iv <u bound` surface form. It is a vectorization
LEGALITY recognizer, so the widening needs a soundness argument, not just a new pattern — but it
is a recognizer change in one function, NOT a new pass class.
