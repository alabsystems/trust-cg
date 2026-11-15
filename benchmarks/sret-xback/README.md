# sret-xback — the indirect-return convention, across a codegen boundary

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

The runner bounds each compiler process to 300 seconds and each binary to 30
seconds through the repository process-group supervisor. It retains artifacts
in the printed temporary directory. A crash/timeout is a failure, not an
oracle; the LLVM/LLVM fixture must return the independently expected 42 before
other cells can be compared. No decline is accepted. The native default
backend suffix is `.so` on Linux and `.dylib` on Darwin. These controls do not
attest tool/source identity or constitute a new native execution result.

## Why this gate exists

Every whole-program differential in this repo — `beat-llvm`, `bridge-fuzz`,
`shape-coverage`, `fmt-selfhost` — builds the caller and the callee with the
**same backend**. A calling-convention disagreement is structurally invisible to
all of them: trust-cg's caller reads the value from wherever trust-cg's callee
left it, so the program agrees with itself and matches LLVM's exit code.

`../abi-xback` makes exactly this argument for **arguments** and links across
backends to test it. It could not make it here when this gate was written: it
then drove a stock upstream `nightly-*` rustc (it has resolved the pinned
Trust compiler since 2026-09-18), and a backend built against the Trust toolchain
(`channel = "trust"`) cannot be loaded into one — `dlopen` fails on
`librustc_driver-*.dylib`. This gate makes the same measurement for the **return**
convention using `trustc` on both sides, which is the compiler this backend is
actually loaded into.

## The shape

`ArgTy` is a 16-byte, niche-encoded, two-variant `BackendRepr::Memory` enum — the
`core::fmt::rt::ArgumentType` layout. rustc's Rust ABI returns it
`PassMode::Indirect`: the **caller** allocates the buffer and passes its address
in `x8` (AAPCS64 §6.9) or `rdi` (System V, as a hidden leading INTEGER argument),
and the callee writes the result through it. The C rule for a 16-byte aggregate
says `x0`/`x1` instead — and for an `extern "C"` function that IS rustc's rule,
which is why the two can only be told apart by reading `FnAbi`.

## What it measures

Four link directions per opt level. `llvm × llvm` runs first and **is** the
oracle, which must itself match the fixture's independently expected exit 42:

| caller | callee | checks |
| --- | --- | --- |
| `llvm × llvm` | | the oracle |
| `llvm × tcg` | LLVM caller → trust-cg callee | does the callee *write* through the buffer |
| `tcg × llvm` | trust-cg caller → LLVM callee | does the caller *allocate* one and pass its address |
| `tcg × tcg` | | self-consistency (always passed, even when both sides were wrong) |

A DECLINE fails this gate as surely as a mismatch: the point is that the
convention is emitted, not refused.

## Negative control

A gate nobody has seen fail is not evidence. Measured 2026-09-11 on
`aarch64-apple-darwin`, against the backend from before the convention was
implemented:

```
$ XXX_NEGATIVE_CONTROL_NO_RET_GATE=1 ./run.sh <pre-change-backend> <trustc> 0 2
ORACLE   caller=llvm callee=llvm O0: exit 42
MISMATCH caller=llvm callee=tcg  O0: want 42 got 0      <- a SILENT WRONG VALUE
MISMATCH caller=tcg  callee=llvm O0: want 42 got 138    <- a crash (Bus error)
MATCH    caller=tcg  callee=tcg  O0: exit 42            <- self-consistent
... identical at O2 ...
sret-xback: 4 failure(s)
```

(That run needs the `[TCG-RET-ABI]` gate bypassed, because the gate REFUSES the
function rather than emit the divergent object. With the gate active and the
convention unimplemented, the same backend fails this gate with four build
declines instead.)

With the convention implemented, all four directions exit 42 at `-Copt-level=0`
and `-Copt-level=2`.

## Running

```sh
./run.sh [backend.dylib] [trustc] [opt-levels...]     # default: 0 2
```

## Linux AArch64 required lane

The program pair also runs in the required Linux cross-backend runner,
[`scripts/check_linux_aarch64_xback.py`](../../scripts/check_linux_aarch64_xback.py),
invoked by the Linux bridge lane on its qualified backend snapshot: four
pairings at O0–O3 with no decline admitted for this suite. On Linux AArch64
all 12 cross cells execute and match
([record](../../reports/perf/2026-10-14-linux-cross-backend-abi/README.md)).
That runner's `abi-families` suite adds the x8 shapes this pair does not
reach (C- and Rust-ABI results over 16 bytes with all eight argument GPRs in
use, a five-`f64` non-HFA, tuples and arrays); an x8 result through a `fn`
pointer is refused by name (`[TCG-SRET-ABI]`) and listed there.

`run.sh` itself passes no backend knob, so its trust-cg halves compile with
proof certificates on. On Linux AArch64 (2026-10-14, Trust `ae9c2c1d`,
backend SHA-256 `d7ca892e…`, O0) both trust-cg halves are then refused at
proof promotion (`[TCG-PROOF-465]`, the L07-P2 opcode-inventory wall) and the
script reports 4 failures with only the oracle built; the required runner
passes the tracked `no-proof-certs`/`refine-solver=0` knobs instead, as
`abi-xback` does.
