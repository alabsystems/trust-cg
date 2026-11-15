# The widened latch-advance window: both halves of its recorded table have expired

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 90 interleaved rounds,
`taskset -c 2`, minimum statistic, ONE dylib, the lever's own tracked knob
(`-Ztrust-ir-cg-args=x86-latch-window`), and **both arms carried twice as
byte-identical copies** so every row has its own noise floor.

## Why re-measure a lever that was already measured

`latch_advance_window_enabled`'s doc justified DEFAULT OFF with a measurement, not a
caution:

| program | recorded new/old | recorded control |
| --- | ---: | ---: |
| `b1_mispredict` | 0.9961 (0.39% faster) | 0.9993 |
| `h3_box_leak` | **1.0173 (1.7% SLOWER)** | 0.9986 |
| `v3_popcount` | 1.0028 | 0.9992 |

That reasoning — "it buys 0.39% on the largest gap and costs 1.7% on `h3_box_leak`,
which is itself one of the programs still above LLVM" — was sound **when h3 was 1.085x
LLVM**. h3 is no longer that program: LICM's pointer-base invariant-load arm went
default-ON and took h3 to 0.99x. A default-OFF whose reason is a cost on one program is
only as current as that program's shape.

## Measured now: neutral, on every program it changes

It changes 9 of the 15 built programs (`b1`, `h1`, `h3`, `h4`, `m2`, `p1`, `p5`, `p6`,
`v3`); the other 6 are byte-identical. All 9 exit-match trust-cg/LLVM.

| program | off | off2 | on | on2 | floor | verdict |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| `b1_mispredict` | 1.0928 | 1.0927 | 1.0925 | 1.0927 | 0.0001 | **neutral** |
| `h1_vec_push_sum` | 0.7720 | 0.7723 | 0.7712 | 0.7703 | 0.0003 | neutral |
| `h3_box_leak` | 0.9907 | 0.9940 | 0.9927 | 0.9923 | 0.0033 | **neutral** |
| `h4_vec_dropper` | 1.0405 | 1.0329 | 1.0308 | 1.0451 | 0.0076 | neutral |
| `m2_call_heavy` | 0.7542 | 0.7554 | 0.7504 | 0.7507 | 0.0012 | neutral |
| `p1_xorshift` | 0.9999 | 0.9995 | 1.0002 | 0.9998 | 0.0004 | neutral |
| `p5_struct_acc` | 0.9991 | 0.9995 | 0.9998 | 0.9997 | 0.0004 | neutral |
| `p6_branch_match` | 0.9806 | 0.9808 | 0.9804 | 0.9805 | 0.0002 | neutral |
| `v3_popcount` | 0.1000 | 0.0997 | 0.0997 | 0.0998 | 0.0003 | neutral |

Every one of the nine is inside its own byte-identical-copy floor. Not one row moves.

**Neither half of the recorded table reproduces.** b1's 0.39% gain is now 0.0003 against a
0.0001 floor, and h3's 1.7% regression is 0.0020 against a 0.0033 floor. The default stays
OFF — but for a different reason than before: it now buys nothing, rather than trading one
program against another.

## Two things this measurement establishes beyond the lever

1. **`b1_mispredict` is the corpus's most trustworthy row.** Its identical-copy floor is
   0.0001 — one part in ten thousand. A 0.3% claim on b1 is measurable; the same claim on
   h4 is not.
2. **`h4_vec_dropper`'s floor is 0.0076** — its two identical copies differ by 0.76%, and
   the four arms here span 1.4%. Any h4 conclusion below ~1% is noise, which is the
   context its recorded 1.0341 needs.

## A soundness hole found by reading the widened path

Independent of the numbers, widening the window opened a gap that the strict window could
not have. Scan (1) — advance to write-back — rejects any instruction MENTIONING the
counter or the temp, but not a flag READER. That stretch is empty in the strict window
(`w == i + 1`) and up to 11 instructions long when widened, and `widened` is also exactly
what admits the flag-neutral `Lea` spelling of the advance. Rewriting `Lea n,[c+k]` to
`AddRI c,c,k` makes that position a flag WRITER, so

```text
  Lea   n, [c+1]      ; flag-neutral before the rewrite, flag-WRITING after
  Setcc r, E          ; reads RFLAGS — admitted by both existing scans
  MovRR c, n          ; the write-back
  CmpRI n, 100
  Jcc   B
```

would have had its `Setcc` read the advance's flags instead of the flags live-in to the
advance. Scan (2) already refuses a flag reader on its own stretch; scan (1) now refuses
one too, and only for the spelling that introduces the write — the `AddRI` spelling keeps
its flag write exactly where it was, so it still collapses.
`widened_latch_collapse_refuses_a_flag_reader_before_the_write_back` pins both directions.

The hole was reachable only through the opt-in knob, so no default build could have hit
it.
