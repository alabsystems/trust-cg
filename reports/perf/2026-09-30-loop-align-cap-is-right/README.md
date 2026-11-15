# The loop-head alignment cap fires on NOTHING in b1 or p4 — and raising it is wrong

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 90 interleaved rounds,
`taskset -c 2`, min statistic, the default arm carried twice as its own floor. Reading
pre-registered before the numbers were read (`loopalign-prereg.md`).

## Why this was worth asking

`x86_loop_align_max_body`'s own doc says the four levers of this pass had been reachable
only through `TCG_*` environment variables, which `trustc` refuses before the backend
loads, so **"its defaults (all four chosen on AArch64 evidence) could not be re-measured
on x86"** — for a pass whose refusal to pad one seam measured 14.8% on `h3_box_leak`.

And `b1_mispredict` is the one program in this corpus demonstrably sensitive to code
PLACEMENT rather than instruction count: it runs ~1.1% FASTER with per-branch JCC-erratum
NOPs that this AMD host does not need at all. It is also the corpus's most trustworthy
row, with a byte-identical-copy floor of 0.0001.

## The pass pads nothing in either of the two worst violations

From the pass's own trace (`-Ztrust-ir-cg-args=trace-x86-loop-align`):

```
[loop-align] `b1_mispredict::main`: heads=1 already=0 padded=0 (+0 bytes) miss=0
             | declines: nested_head=0 pad_too_big=0 body_too_big=1 already_contained=0 live_seam=0
[loop-align] `p4_matmul::main`:     heads=4 already=0 padded=0 (+0 bytes) miss=0
             | declines: nested_head=0 pad_too_big=0 body_too_big=4 already_contained=0 live_seam=0
```

Every loop head in both programs is declined by the one-fetch-line body cap
(`max_body = 64`). The aligner is inert on b1 and p4.

## Raising the cap: b1 gets WORSE, p4 is unmoved

`max_body` 96 and 128 leave b1 byte-identical (its body is larger than either); 192, 256
and 384 change it. All exit-match.

| b1_mispredict | vs LLVM -O3 |
| --- | ---: |
| default (cap 64) | 1.0961 |
| default, 2nd copy (floor) | 1.0960 |
| `max_body=192` | **1.1042** |
| `max_body=256` | **1.1038** |
| `max_body=384` | **1.1040** |

**0.75% slower, consistently.** The three raised values agree to 0.0004 — once the cap
admits the body, the padding decision is the same however much higher it goes, which is a
useful internal check that the arms are doing what they claim.

| p4_matmul | vs LLVM -O3 |
| --- | ---: |
| default / 2nd copy | 1.0821 / 1.0833 (floor 0.0012) |
| `max_body=128 / 192 / 256 / 384` | 1.0810 / 1.0827 / 1.0818 / 1.0817 |

Every p4 arm is inside the floor. Unmoved.

## Why, measured from the binaries rather than argued

A 32-byte head alignment can only help by reducing how many 64-byte fetch lines the loop
body touches. So count them. Each program's `main` was disassembled and every backward
branch measured (b1 has exactly ONE, matching the trace's `heads=1`, so there is no
ambiguity about which loop):

| loop head | body | lines spanned | floor = ceil(body/64) |
| --- | ---: | ---: | ---: |
| b1 `0x2095b` (offset 27) | **149 B** | 3 | **3** |
| p4 `0x209ad` (offset 45) | 132 B | 3 | **3** |
| p4 `0x20ba8` (offset 40) | 460 B | 8 | **8** |
| p4 `0x20e63` (offset 35) | 275 B | 5 | **5** |
| p4 `0x20f8e` (offset 14) | 95 B | 2 | **2** |

**Every declined loop is ALREADY at its minimum fetch-line count.** Alignment cannot
remove a crossing from any of them; it can only relocate a loop that will still span the
same number of lines. b1's 0.75% loss is that relocation landing worse.

So the containment cap is principled for precisely the reason its doc gives: under 64
bytes, alignment can take a body from two lines to one; over 64 bytes it cannot take it
below the ceiling it already occupies. The AArch64-chosen default is **correct on x86**,
and this closes `max_body` in the raising direction with a measurement instead of an
assumption.

## What this also settles about b1

b1's 149-byte body already sits at its fetch-line floor, and padding it is a measured
loss. Combined with every small instruction-count item on b1 being priced at zero
(see `2026-09-30-latch-window-expired/`), the plain front-end-bytes reading of b1's gap
has no lever left in this pass. b1's remaining named candidate is loop specialization.
