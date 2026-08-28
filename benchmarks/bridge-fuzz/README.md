# benchmarks/bridge-fuzz — generative differential gate for the RUSTC BRIDGE

## Why this exists

`scripts/fuzz_campaign.sh` drives trust-ir-gen / csmith / yarpgen, but every one
of those feeds the **trust_ir** and **LLVM-import** frontends. The rustc
**bridge** — the primary user-facing path, the one `-Zcodegen-backend` selects —
had *no generative differential coverage at all*. Its entire correctness net was
hand-written programs only: 18 in `beat-llvm/progs` and, at the time, 24 in
`shape-coverage/progs` (that corpus has since grown to 72).

That is thin, and it is demonstrably thin: every one of the 14+ confirmed
wrong-code bugs found on 2026-08-19/20 was caught by differential testing on a
shape those hand-written programs did not contain. `18/18 MATCH` is a
regression net, not a correctness argument.

## Usage

    ./run.sh <first-seed> <count> [opt-levels...]      # default opt level: 3
    BRIDGE_FUZZ_OUT=/tmp/x ./run.sh 1 500 0 1 2 3

Exit status is 1 if any WRONG-ANSWER or NONDET was seen. Failing programs are
kept under `$BRIDGE_FUZZ_OUT/fail/` and are reproducible from their seed alone:

    python3 gen.py <seed>

## Verdicts

| verdict | meaning |
| --- | --- |
| `MATCH` | LLVM and trust-cg agree on the exit status |
| `WRONG-ANSWER` | they disagree — **P0**, the program is kept |
| `NONDET` | trust-cg disagrees with ITSELF across two runs — **P0** (this is how an over-read announces itself) |
| `declined` | trust-cg failed closed; tracked, not a defect |

## UB-freedom is the whole game

A generated program that is itself undefined lets the two backends differ
legitimately, so every finding would be a false positive. `gen.py` is UB-free by
CONSTRUCTION, not by inspection:

* all arithmetic is `wrapping_*`;
* shift amounts are masked to the operand width;
* division/remainder go through `checked_div`/`checked_rem` (no `/0`, no
  `INT_MIN / -1`);
* indexing is `arr[i % LEN]` over a non-empty array;
* no floats, no `unsafe`, no uninitialised reads, no I/O, no time, nothing
  address-dependent;
* every input passes through `black_box` so nothing folds to a constant, and the
  result is folded into the exit status.

Before believing any WRONG-ANSWER, re-read the generated program against that
list — the generator is the thing most likely to be wrong.

## The declines (2026-08-25): 28 -> 20

Bucketed over seeds 1-25 at `-O0/-O2/-O3`. Every one is `[TCG-SSA-071]`, the
trust-ir ssa/loop-completeness gate, which makes them look like one thing. They
are not.

### FIXED: a dead `Copy` of a carried-unchanged param (8 declines)

The largest class was **not** a bridge defect, though its message says
`loop-carried value ... is live across back-edge ... but has no loop-header
parameter`, which reads exactly like one. An earlier version of this file
recorded it as "the bridge emitted INCOMPLETE SSA — a real defect in
block-argument construction". That was wrong. The trust-ir was correct and the
CHECKER was over-refuting.

Reduced by hand from seed 4 to:

```rust
let t0 = p2.wrapping_add(p2);
let mut a1 = 0u16;
let mut i1 = 0u16;
while i1 < 4 { a1 = t0; i1 = i1.wrapping_add(1); }
t0.wrapping_sub(p0)            // a1 never read again
```

Dumping the emitted trust-ir settled it: `v9 = p2+p2` is `t0`, `v12` is its
loop-INVARIANT identity param, the body emits `v18 = Copy(v12)` for `a1 := t0`,
and the back-edge re-threads `v12`. All correct. Sub-check (3) ("stale
re-thread") fires on the fingerprint *a dead node using a carried-unchanged
value of the same type* — and a dead `Copy` OF THAT VERY PARAM matches it. But
`d = Copy(p)` means `d == p`, so threading `p` threads `d`. Fixed in
`ssa_loop_complete`, restricted to `Inst::Copy` so a genuine dropped update (an
`add`, an `icmp`, a load) still fires.

**47 MATCH / 28 declined -> 55 MATCH / 20 declined, 0 WRONG-ANSWER.**

### The remaining 20

| count | cause |
| --- | --- |
| 9 | **in-loop diamond**, "set `TCG_P3C_REFINE` to model it" |
| 5 | **REFUTED with a counterexample** — the VC ran and disproved equality. The counterexample environments contain `__tir_v*` OPAQUE values, i.e. the trust-ir side had an instruction the symexec could not model, so equality was unprovable rather than false. |
| 4 | **unmodeled call** `wrapping_shl` / `checked_div` on the loop path |
| 2 | other |

The last three rows share a root: `vc_model_wrapping_call` models
`wrapping_add`/`sub`/`mul` and constant-divisor `wrapping_rem`/`div`, and
nothing else. `wrapping_shl` is not intercepted by the bridge either — it
lowers the real std impl — so the VC sees an opaque result. Modeling it as
`Shl(a, BitAnd(b, bits - 1))` (Rust's own definition) is the obvious next step;
the wrinkle is that the shift amount is `u32` while the value is `uN`, so the
spec has to reproduce the bridge's width handling exactly rather than
approximately.

### `TCG_P3C_REFINE` conflates two things (measured TWICE, both negative)

The diamond cases advise setting `TCG_P3C_REFINE`, but that switch turns on the
threading VC's diamond model AND the per-rvalue refinement lane, and the latter
demands a solver for every >8-bit obligation — so on a solver-less host it just
trades `TCG-SSA-071` for `TCG-REFINE-068 "no solver available"`. The advice is
unusable as written.

Decoupling them was measured twice: once before the `Copy` fix and once after,
in case that defect was masking the benefit. **Identical both times** — 47/28
on/off before, 55/20 on/off after. Enabling the diamond model only moves those
declines to REFUTED or "non-bool discriminant"; it recovers nothing, so it was
not kept. The model itself is sound and pinned in both directions by the
`*_refines_and_swap_refutes` tests in `loop_backedge_symexec`; the blocker is
what comes after it.
