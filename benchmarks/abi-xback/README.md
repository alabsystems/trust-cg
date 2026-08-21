# abi-xback — cross-backend calling-convention differential

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

## Why this gate exists

Whole-program differential tests cannot observe a calling-convention error when
both caller and callee use the same backend: both sides can agree on the same
wrong stack offset. The error appears only when a call crosses a codegen
boundary, as it does against LLVM-compiled libraries, libc, or mixed builds.

That is how the AArch64 stack-argument bug survived: trust-cg classified ELF
targets with DarwinPCS, which packs narrow stack arguments naturally, while
AAPCS64 gives every scalar stack argument an 8-byte slot. For eight leading
GPR arguments followed by `u16, i16, i32`, LLVM uses offsets `0, 8, 16`; the
old trust-cg path used `0, 2, 4`.

## What it checks

For each seed, `gen.py` emits a matched caller/callee signature with 9–20
narrow and mixed-width arguments. Across a seed corpus, these regularly
overflow one of the eight-register argument banks onto the stack.
`run.sh` compares three links:

| build | purpose |
| --- | --- |
| LLVM × LLVM | oracle |
| LLVM caller × trust-cg callee | callee reads the ABI slots correctly |
| trust-cg caller × LLVM callee | caller writes the ABI slots correctly |

Any exit-code difference from the oracle is a definitive ABI mismatch.

## Usage

```sh
./run.sh <first-seed> <count> [opt-levels...] # defaults: 25 seeds, O2
ABI_XBACK_OUT=/tmp/x ./run.sh 1 40 1 2 3
```

The harness exits nonzero on any mismatch and preserves failing sources in
`$ABI_XBACK_OUT/fail/`. Its negative control—forcing Darwin classification on
an AArch64 ELF target—failed 38 of 60 seed/direction combinations at O2; the
target-selected classifier passed 240/240 across O1/O2/O3 for 40 seeds.
