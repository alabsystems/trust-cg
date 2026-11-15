# x86 strength reduction: made measurable, diagnosed, and its p4 fix measured as a REGRESSION

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`, one dylib per arm.

## 1. The pass was ON by default and unmeasurable through the bridge

`X86StrengthReduce` (OPT-3a) rewrites a loop-body `imul iv, const-stride` into an add
recurrence, and its own module doc names the target: "the canonical win is a matmul-style
nested loop addressing `a[i*N + k]`, where `i*N` (stride `N` not SIB-encodable, e.g. 24)
is re-multiplied on every iteration of the INNER loop." That is `p4_matmul`.

Its kill switch was `TCG_NO_STRENGTH_REDUCE`, an **environment variable**, and `trustc`
refuses every `TCG_*` variable before the backend loads. So a pass that is on by default
and rewrites address arithmetic in hot loops had **never been A/B'd through the bridge**,
and "it is enabled and p4's `imul` is still there" was not actionable — the pass has 52
decline points and no diagnostics.

Added: tracked `no-x86-strength-reduce` (the opt-out, default ON as before, routed through
`tcg_env_flag` so `=0` means "do not disable") and tracked
`trace-x86-strength-reduce`, which names the condition each candidate died on. This is the
**eleventh** instrument found env-only in this campaign.

## 2. What the trace said

```
p4_matmul::main: loop header Block(18) depth 4 -> NO CANDIDATE
  decline: no induction variable matched in this loop
p4_matmul::main: loop header Block(35) depth 4 -> NO CANDIDATE
  decline: PREHEADER flags live at the seed-multiply insert point
p4_matmul::main: loop header Block(14) depth 3 -> NO CANDIDATE
  decline: PREHEADER flags live at the seed-multiply insert point
p4_matmul::main: loop header Block(9)  depth 2 -> REDUCING imul stride 24
```

The pass fired only on the depth-2 loop. Both **depth-3 and depth-4** loops — p4's hot
ones — declined on one named condition: the seed multiply (`ImulRRI r, iv, stride`) is
spliced immediately before the preheader's terminator, and a preheader ending `cmp; jcc`
has LIVE flags there. So the pass was declining on exactly the case it exists for.

## 3. The fix, and why it is DEFAULT OFF

The seed reads only the entering `iv`, so it need not sit last. Any instruction that FULLY
overwrites the flags kills the seed's flag write, so the slot immediately **before** the
preheader's last full flag overwriter is flag-safe by construction: nothing can observe the
seed's flags, because the very next instruction replaces them and there is nothing in
between. `preheader_seed_insert_pos` implements that, with two guards — the default slot is
preferred whenever it is already flag-dead (so this only ADDS candidates), and the slot is
rejected if `iv` is defined at or after it.

It works: p4's depth-3 `k` loop reduces (`REDUCING imul stride 24`), 7 reductions instead
of 5. **And it makes p4 slower.** 50 interleaved rounds vs LLVM -O3, arms duplicated
(floor 0.0001):

| arm | p4 vs LLVM |
| --- | ---: |
| pass OFF entirely | 1.0864 |
| pass ON, terminator-only placement (shipped) | **1.0800** |
| pass ON, flag-safe placement | **1.0926** |

So the extra reduction costs 1.2%. `b1_mispredict`, `p2_collatz` and `h4_vec_dropper` are
unchanged within noise.

### Where the cost actually is — measured, not inferred

A first draft of this report said the carrier "adds register pressure to an already tight
SIMD body". That is wrong about the location, and the disassembly says so. With the lever on
versus off:

| | innermost SIMD loop | whole `main` |
| --- | --- | --- |
| off | `0x20ea8..0x20fb9`, 65 insns, **0** frame refs | 497 insns, 58 frame refs |
| on | `0x20ebb..0x20fcc`, 65 insns, **0** frame refs | **472** insns, **64** frame refs |

The innermost loop is IDENTICAL in both arms — same instruction count, same opcode
histogram, no spills either way. The reduction did its job at the whole-function level:
**25 fewer instructions**. And it added **6 more frame references** (spills/reloads) in the
ENCLOSING nest, where the recurrence carrier is now live across the `k` loop.

So the honest mechanism is: 25 instructions traded for 6 memory accesses in the enclosing
loop bodies, measuring 1.2% slower. That is the same shape as LICM's pointer-base hoisting
(18 instructions cut to 10, 1.46x SLOWER) — a loop-carried VALUE bought at the price of
memory traffic — but it happens one loop level OUT from where the first draft put it.

It therefore ships **opt-in** as `-Ztrust-ir-cg-args=x86-sr-flag-safe-seed`, not as a
default. The capability is real and may pay on a loop that is not register-starved; it must
not be enabled without per-loop pressure evidence. Verified: the DEFAULT build is
**18/18 byte-identical** to the pre-change baseline across the whole benchmark suite.

Note also the middle row: the pass as shipped IS worth something — 1.0864 off versus 1.0800
on, about 0.6% on p4 — which is the first time its contribution has been measured at all on
this host.

## 4. Tests

`preheader_with_live_flags_is_rejected` asserted the old blanket rejection. It is replaced
by three tests that separate the concerns, because the rejection was never a soundness
requirement:

* `cmp_jcc_preheader_reduces_with_the_seed_placed_before_the_cmp` — opts in via the
  BUILDER (not the process-global installer, which would decide the default for every other
  test in the binary) and asserts the resulting ORDER `seed, cmp, jcc`, since that order IS
  the safety argument.
* `the_default_still_declines_a_cmp_jcc_preheader` — pins the shipped default, so enabling
  the lever can never be a silent change.
* `preheader_without_a_flag_overwriter_is_still_rejected` — the genuinely unsafe case (a
  bare `jcc` whose flags came from another block) still fails closed.
