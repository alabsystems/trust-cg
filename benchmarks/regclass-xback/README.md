# regclass-xback — which registers a by-value scalar pair rides, across a codegen boundary

`../sret-xback` measures **where** a returned aggregate goes: the return
registers, or the caller-allocated `x8`/`RDI` buffer. That is the only question
the two-variant `ReturnPlacement` of `822fdc69` could ask, and that commit said
so itself:

> a register-CLASS disagreement is still outside this gate's reach — a
> `PassMode::Pair` of floats bound for `d0`/`d1`, or a Pair of 32-bit scalars
> packed into one register, are both "the return REGISTERS" to
> `ReturnPlacement`, so it cannot see them.

This gate asks **which** registers: how many, of which class, carrying which
bytes — in both the RETURN and the ARGUMENT direction.

## The four shapes

| program pair | Rust type | rustc `PassMode` | AAPCS64 registers |
|---|---|---|---|
| `fret_*` | `struct P { a: f64, b: f64 }` returned | `Pair` | `d0`, `d1` (§6.4.2) |
| `farg_*` | the same `P` passed by value | `Pair` | `d0`, `d1` |
| `iret_*` | `struct Q { a: i32, b: i32 }` returned | `Pair` | `w0`, `w1` |
| `iarg_*` | the same `Q` passed by value | `Pair` | `w0`, `w1` |

(Five more ARGUMENT shapes were added on 2026-09-14 — see
[the five ARGUMENT shapes](#the-five-argument-shapes-the-core-census-measured)
below.)

Each callee is `#[inline(never)]` in its own `--crate-type rlib`. Both are
required: without the separate crate the caller inlines the callee, and without
`#[inline(never)]` it does so anyway at `-Copt-level=2`. Either way the two
halves can never disagree, which is exactly why every whole-program differential
in this repo passed on these shapes.

## The defect this measures — CONFIRMED, both opt levels

Measured 2026-09-11 on aarch64-apple-darwin, trustc `8b50cbcc5b`, against the
pre-fix backend. `42` is correct in every cell; the oracle is `llvm x llvm`.

```text
shape                        direction   llvm x tcg   tcg x llvm   oracle
struct P { a: f64, b: f64 }  return          0            0          42
struct Q { a: i32, b: i32 }  return        188 / 28      20          42
struct P (by value)          argument       80          60 / 80      42
struct Q (by value)          argument       20          244 / 4      42
```

Disassembly of the two callees, LLVM against trust-cg, at `-Copt-level=0`:

```text
P   LLVM      fmul d0, d1, d0 ; fmul d1, d1, d2 ; ret          returns in d0/d1
    trust-cg  ldr x0, [x2] ; ldr x1, [x2, #0x8] ; ret          the GPR pair

Q   LLVM      ldr w0, [sp, #0x8] ; ldur w1, [x29, #-0x4] ; ret w0 AND w1
    trust-cg  ldr x0, [x1] ; ret                               ONE register
```

Both backends are internally consistent in both cases: the same bytes, out of
the wrong register file (`P`) or one register short (`Q`).

## What must hold

Every cell that **builds** must match the oracle. Unlike `sret-xback`, a
DECLINE is permitted here and is reported: the register-class gates
(`[TCG-RET-ABI]` / `[TCG-ARG-ABI]`) refuse the shapes trust-cg cannot place
conformantly, and a refusal is always acceptable where a silently divergent ABI
is not. A built binary that disagrees with the oracle is a P0.

The runner now admits a decline only for exit 1 with complete JSON diagnostics
whose errors are explicit `[TCG-RET-ABI]` / `[TCG-ARG-ABI]` refusals. Unrelated
errors, malformed diagnostics, crashes, missing tools and timeouts fail the
campaign. Run `python3 -m unittest discover -s benchmarks/regclass-xback -p
'test_*.py'` from the repository root to test this classification contract;
it does not run a backend.
Compiler processes have a 300-second bound and binaries a 30-second bound,
using the repository process-group supervisor. Logs and binaries are retained
in the printed temporary directory. These are not hermetic source/tool
attestations; actual qualification must additionally freeze their identities.
The LLVM/LLVM cell must complete with the fixture's independently expected
exit 42; no other cell may become a replacement oracle. Built cells must then
match that oracle. The native default suffix is `.so` on Linux and `.dylib`
on Darwin; pass explicit compiler/backend paths for a qualified campaign.

```bash
./run.sh [backend.dylib] [trustc] [opt-levels...]
```

## The five ARGUMENT shapes the `core` census measured

Added 2026-09-14 with the two-value argument lane, because `iarg`'s `{i32,i32}`
is only one of the sub-families the census actually holds. Each row is the
largest shape of its family, and the family sizes are the `[TCG-ARG-ABI]` roots
of the 290-root AArch64 integration census. Every row is passed by value and
rustc classifies every one `PassMode::Pair`:

| program pair | Rust type | rustc lanes | AAPCS64 registers | family |
|---|---|---|---|---|
| `barg_*` | `Option<u8>` | `1 byte @0 ; 1 byte @1`, tag `zeroext` | `w0`, `w1` (x86-64: `edi`, `esi`) | 27 |
| `earg_*` | `Option<u32>` | `4 bytes @0 ; 4 bytes @4`, a TAGGED enum | `w0`, `w1` | 25 |
| `harg_*` | `(i16, i16)` | `2 bytes @0 ; 2 bytes @2` | `w0`, `w1` | 14 |
| `marg_*` | `struct M { a: u32, b: u16 }` | `4 bytes @0 ; 2 bytes @4`, MIXED width | `w0`, `w1` | 6 |
| `qarg_*` | `Option<u128>` | `8 bytes @0/8/16/24` — two register PAIRS | `x0`-`x3` | 2 |

`barg` is the one that decides the extension question: its tag lane carries
rustc's `ArgAttributes { arg_ext: Zext }`, and the caller exercises BOTH
variants (`Some(20)` and `None`), so a tag arriving with dirty upper bits in the
`caller=tcg callee=llvm` cell is a wrong exit code, not a silent pass. `marg`'s
second lane is NARROWER than its first, so a plan that synthesised lane offsets
from the carriers' widths instead of reading rustc's own would place it wrong.

`qarg` is the shape the whole-slot rule gets most wrong: at 32 bytes trust-cg
sends it through a caller-allocated copy addressed by pointer while rustc puts it
in x0-x3, so the two conventions do not even agree on whether a pointer is
involved. It is also the only row whose lanes are register PAIRS rather than
single registers, which is why the AArch64 ARGUMENT carrier table admits an
`i128` lane where the RETURN table refuses one. x86-64 argument lanes use the
RETURN table, so `qarg` keeps its `[TCG-ARG-ABI]` refusal by name there until the
four-INTEGER-lane placement has been measured across the boundary on that target.

## Current state (2026-09-14, after the two-value ARGUMENT lane)

```text
regclass-xback: 0 failure(s), 0 decline(s)
```

72 of 72 cells MATCH on aarch64-apple-darwin. Before the lane, the same tree
reported **24 declines** — the four `iarg` cells plus the twenty belonging to the
five shapes above — every one of them `[TCG-ARG-ABI]`, and every one now a
cross-boundary `exit 42` in both link directions at `-Copt-level=0` and `=2`.

The x86-64 port of the lane (2026-09-22, Darwin x86-64) measured the four
original shapes plus `barg`/`harg`/`earg`/`marg` at 0 failures and 0 declines at
`-Copt-level=0` and `=2`. `qarg` is not part of that measurement; on x86-64 its
refusal is an expected, reported decline. Neither measurement was re-run on the
tree that carries both lanes.

The 2026-09-11 attempt that turned 606 `core` census roots into loud
`Call argument arity mismatch` failures is closed by two properties of
`scalar_pair_param_plan`, not by touching those hand-built argument lists: it is
the ONE decision function the declaration, the callee entry block and every call
site all ask, and it engages ONLY where the whole-slot classification is already
REFUSED — so a `&str` / `&[T]` / `&dyn` fat pointer, whose 16-byte lane tuple
already lands in the x0/x1 pair rustc asks for, keeps the single slot-pointer
argument every one of those lists builds for it. Measured the same day: `core`
290 -> 223 roots, `[TCG-ARG-ABI]` 73 -> 0, **zero** new failed symbols and
**zero** `arity mismatch` lines in the census stderr.

## Linux AArch64 required lane

The nine program pairs here also run in the required Linux cross-backend
runner, [`scripts/check_linux_aarch64_xback.py`](../../scripts/check_linux_aarch64_xback.py),
which the Linux bridge lane invokes on its qualified backend snapshot: all four
caller × callee pairings at O0–O3 (`run.sh` defaults to O0 and O2), the LLVM
oracle held to the fixture's exit 42, every built cell compared with it. That
runner admits a decline only as a row of its committed `EXPECTED_DECLINES`
table, which holds none for this suite: on Linux AArch64 all 108 cross cells
execute and match ([record](../../reports/perf/2026-10-14-linux-cross-backend-abi/README.md)).
It passes the backend's tracked `no-proof-certs`/`refine-solver=0` knobs, as
`abi-xback` does; `run.sh` passes neither, so its trust-cg halves compile
with proof certificates on. Measured on Linux AArch64 on 2026-10-14 (Trust
`ae9c2c1d`, backend SHA-256 `d7ca892e…`, O0): the nine LLVM oracles exit 42
and every trust-cg compile it attempts is refused at proof promotion
(`[TCG-PROOF-465]`, the L07-P2 opcode-inventory wall), so `run.sh` reports 18
failures, 0 declines and no executed cross cell.
