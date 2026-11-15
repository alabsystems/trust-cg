# The LEA-writeback collapse: a flip criterion finally checkable, and both figures behind it had expired

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`. 90 interleaved rounds for the
decisive rows, `taskset -c 2`, minimum statistic, arms carried twice as their own floor.

## The criterion, and why it could never be checked

`x86_lea_writeback_collapse_enabled` carried an unusually specific promise:

> "FLIP CRITERION, explicitly: once an x86 loop-head aligner exists, re-measure and default
> this ON. The p1 win is layout-robust; only p7 is hostage to placement, and an aligner is
> exactly what stops it being hostage."

It rested on two measurements: `p1_xorshift` at **0.8535 ON/OFF** (14.6% faster, with
m2/p8/p5 between -1% and -4%), and a single blocker, `p7_sieve` regressing **1.44x** — which
the doc argued was not the rewrite's fault but a layout lottery, since p7's four-instruction
marking loop fits inside one 64-byte fetch line uncollapsed and removing three bytes makes it
straddle.

The named blocker is gone: `x86_loop_head_align`, a 64-byte fetch-line CONTAINMENT aligner,
now exists and is default-on. So the criterion became satisfiable.

**It had never been checkable at all.** The arm's only channel was
`TCG_X86_LEA_WRITEBACK`, and `trustc` refuses every `TCG_*` variable before the backend
loads. A tracked `x86-lea-writeback` option was added to ask the question, then inverted to
`no-x86-lea-writeback-collapse` when the default flipped.

## Both figures had expired

| recorded | re-measured | floor |
| --- | --- | --- |
| `p1_xorshift` 0.8535 ON/OFF — the whole justification | **0.9996 -> 0.9998** | 0.0002 |
| `p7_sieve` 1.44x regression — the only blocker | **0.7118 -> 0.7142** | 0.0053 |

Neither survives. The criterion cannot be honoured on its own terms: the win that motivated
it does not exist on this host and this code. That is the third recorded per-pass measurement
in this backend to evaporate once it became askable through the bridge, after the
branch-layout fallthrough rule's two reasons and the two-address commute arm's "fires on
nothing".

## The default flipped anyway, on a smaller and different basis

The arm fires on 11 of 18 corpus programs with every exit code matching LLVM. What it is
worth now:

| program | OFF | ON | |
| --- | ---: | ---: | --- |
| `p2_collatz` | 1.0231 | **1.0105** | a parity VIOLATION, halved |
| `m2_call_heavy` | 0.7506 | 0.7557 | 0.7% worse, stays 24% BELOW parity |
| `p6_branch_match` | 0.9796 | 0.9822 | 0.3% worse, stays below parity |
| `h3_box_leak` | 0.9936 | 0.9942 | noise (a 0.9% reading at 30 rounds did not survive 90) |
| `b1`, `p4`, `h4`, `h1`, `p1`, `p7`, others | — | — | inside noise |
| suite geomean | 0.8333 | 0.8328 | flat |
| suite WORST | 1.0964 | 1.0968 | unchanged (noise) |

The objective is MAX-GAP, so what matters is that a violation halves, no new violation
appears, and the maximum is unchanged. The two costs land on programs that stay comfortably
under parity. **The 14.6% figure must not be read as live** — it is recorded at the setter and
in the knob description precisely so it is not.

Verified by bytes, not argument: the default build is byte-identical to the measured ON arm
and `-Ztrust-ir-cg-args=no-x86-lea-writeback-collapse` is byte-identical to the measured OFF
arm, on all six programs checked.

## Two mistakes worth recording

**A test caught the flip, exactly as designed.**
`x86_lea_self_writeback_is_opt_in` asserted the OFF default and said so in terms:
"⚑ THE DEFAULT IS THE LOAD-BEARING HALF of this test … so flipping the polarity by mistake
cannot pass the suite." It did its job. It is now
`x86_lea_self_writeback_is_default_on_and_its_opt_out_restores_the_writeback`, asserting the
new polarity in both directions on a stream the arm is known to collapse, so the same
protection holds in the new direction, with the expired figures recorded in its doc.

**A name collision that compiled.** The new knob was first called `no-x86-lea-writeback`,
which already existed for the PEEPHOLE's lea-writeback fold — a different pass. An un-counted
string replacement then pointed the peephole's own forwarding at the new knob, leaving the
peephole's knob unforwarded. It compiled cleanly, because both names existed. Renamed to
`no-x86-lea-writeback-collapse`, with the distinction stated in the description, and both
forwardings verified to call their own setter exactly once.
