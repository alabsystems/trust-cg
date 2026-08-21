# benchmarks/bridge-fuzz — generative differential gate for the RUSTC BRIDGE

## Why this exists

`scripts/fuzz_campaign.sh` drives trust-ir-gen / csmith / yarpgen, but every one
of those feeds the **trust_ir** and **LLVM-import** frontends. The rustc
**bridge** — the primary user-facing path, the one `-Zcodegen-backend` selects —
had *no generative differential coverage at all*. Its entire correctness net was
41 hand-written programs: 18 in `beat-llvm/progs` and 23 in
`shape-coverage/progs`.

That is thin, and it is demonstrably thin: every one of the 14+ confirmed
wrong-code bugs found on 2026-08-19/20 was caught by differential testing on a
shape those 40 programs did not contain. `18/18 MATCH` is a regression net, not
a correctness argument.

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
