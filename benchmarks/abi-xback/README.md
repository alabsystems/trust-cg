# abi-xback — cross-backend calling-convention differential

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

## Why this gate exists

Every other differential net in this repo compiles a **whole program with one
backend**:

| gate | shape |
| --- | --- |
| `benchmarks/beat-llvm` | whole program, LLVM vs trust-cg |
| `benchmarks/bridge-fuzz` | whole program, LLVM vs trust-cg |
| `benchmarks/shape-coverage` | whole program, LLVM vs trust-cg |

A **calling-convention disagreement is structurally invisible to all of them.**
If trust-cg puts a stack argument at the wrong offset, the trust-cg caller
writes it there and the trust-cg callee reads it from there — both sides are
wrong in the same way, so the program agrees with itself and the exit code
matches LLVM's. The error appears only when a call **crosses a codegen
boundary**: against LLVM-compiled `std` or any other LLVM-built library,
against libc, or in any mixed build.

That is exactly how the AArch64 stack-argument layout bug survived: trust-cg
classified an ELF target with DarwinPCS, which packs narrow stack arguments at
their natural size (`u16` → 2 bytes), while AAPCS64 (IHI 0055 §6.4.2 stage
C.14) gives every scalar stack argument an 8-byte slot. For eight leading GPR
arguments followed by `u16, i16, i32`, LLVM lays the stack tail out at slot
offsets `0, 8, 16`; the old trust-cg path used `0, 2, 4`:

```
LLVM      ldrh  w9, [sp]       ldrsh x8, [sp, #8]    ldrsw x9, [sp, #16]
trust-cg  ldrh  w0, [x29, #16] ldrsh x3, [x29, #18]  ldr   w1, [x29, #20]
                                          ^^^^                     ^^^^
```

## What it checks

For each seed, `gen.py` emits a matched callee/caller pair with 9–20 narrow and
mixed-width arguments. Across a seed corpus these regularly overflow one of the
eight-register argument banks (8 GPR / 8 FPR) onto the stack. `run.sh` then
links three ways and compares exit codes:

| build | direction | checks |
| --- | --- | --- |
| `llvm × llvm` | — | the **oracle** |
| `llvm × tcg` | LLVM caller → trust-cg callee | trust-cg as **callee** — does it *read* args from the right slots |
| `tcg × llvm` | trust-cg caller → LLVM callee | trust-cg as **caller** — does it *write* args to the right slots |

Any exit-code difference from the oracle is a definitive P0 ABI mismatch.

## Usage

```sh
./run.sh <first-seed> <count> [opt-levels...]      # default: 25 seeds at -O2
ABI_XBACK_OUT=/tmp/x ./run.sh 1 40 1 2 3
./run.sh --driver <trust-package>/bin/trustc 1 25  # explicit Trust package
```

The script runs on AArch64 Linux GNU and on `aarch64-apple-darwin`. It loads
the newest bridge backend [`scripts/bridge_backend.py`](../../scripts/bridge_backend.py)
names (or `ABI_XBACK_DYLIB`) and refuses one older than any input of its
build. The linker is resolved from the compiler's own host triple and printed:
on Darwin the host C driver `cc` (xcrun's, else PATH's) is passed as
`-Clinker` to every link, ld64 is named by path and identified by `ld -v`, and
no `gcc-ld` shim is put on PATH; on Linux GNU the Trust sysroot's `gcc-ld`
shim directory goes on PATH, with the same host's rustup `stable` shim as the
marked stock exception when the Trust package ships none. On Darwin one probe
link with the exact link flags runs before the first combination, and the
gate fails unless rustc's printed link line (`--print link-args`) invokes the
resolved `cc`. A trust-cg compile that fails is a backend decline; a link
that fails (the LLVM caller against the trust-cg archive, or rustc's
`error: linking with` for the trust-cg caller) is a skip, and its diagnostic
is kept in `fail/`. The summary adds a
per-direction MATCH line, which the Darwin consumer lane
requires to be 160 in each direction for seeds 1-40 at O0-O3.

Every half is compiled by the Trust compiler that the bridge's
`channel = "trust"` pin requires, resolved by
[`scripts/trust_toolchain.py`](../../scripts/trust_toolchain.py) from the PATH
`trustc`/`targo` package or `--driver`, in Trust's explicit unverified frontend
lane (`-Ztrust-verify=off`, diagnostic, no verified-compilation claim).
Exits non-zero unless every requested caller/callee direction matches: a
mismatch, backend decline, oracle/generator skip, missing backend, or a missing,
stock or retired-nightly compiler all fail the gate. Failing sources are kept in
`$ABI_XBACK_OUT/fail/`. `./run.sh --selftest` pins this result contract with one
positive and four rejection arms.

## The required Linux lane

`run.sh` is the manual, per-seed tool. The REQUIRED Linux AArch64 run is
[`scripts/check_linux_aarch64_xback.py`](../../scripts/check_linux_aarch64_xback.py),
which `scripts/check_linux_aarch64_bridge.py` invokes on the backend snapshot
it has just built and qualified (ledger gap L06-P9; decision record LD-27). It
drives four suites through one engine, each at O0, O1, O2 and O3 and in all
four caller × callee pairings (`llvm×llvm` is the oracle):

| suite | source | cases |
| --- | --- | --- |
| `abi-xback` | `gen.py --emit-group`: seeds 1–40 as ONE callee crate (`xabi_<seed>`) and one caller crate | 40 |
| `abi-families` | [`families.py`](families.py): named AAPCS64 placement families, one crate pair per family and ABI | 346 |
| `regclass-xback` | [its nine program pairs](../regclass-xback/README.md) | 9 |
| `sret-xback` | [its program pair](../sret-xback/README.md) | 1 |

`families.py` names one case per placement rule instead of hoping a random draw
reaches it: integer widths with dirty upper bits and every narrow return
(caller extension), floats, HFAs of every member count as arguments and
returns, the exact-fit and no-back-fill HFA boundaries (C.3), HVAs and bare
64/128-bit vectors, GPR composites at C.10/C.13/C.14 (a 16-byte composite
with one GPR left goes to the stack and NGRN becomes 8), `i128` even-register
rounding (C.8) and 16-aligned stack slots, `x8` results (`sret`) with the GPRs
full, by-reference copies the callee overwrites (B.4: the caller's original
must not change), `&mut` write-back, a fat pointer whole in x6:x7 and one split
across x7 (data) and the stack (length), `bool`, variadic calls into an
LLVM-built `c_variadic` callee (and variadic definitions, which trust-cg
refuses), a direct call and a call through a C-variadic `fn` pointer with no
anonymous argument, over-aligned FIXED arguments of such a callee, directly
and through such a pointer (which trust-cg refuses by name, decision record
LD-29), a pointer call with anonymous arguments (refused by its argument
count), glibc `snprintf` with stack anonymous
arguments, callbacks through `extern "C"` and Rust `fn` pointers, the Rust-ABI
`Cast` aggregates of LIMITATIONS.md "Register exhaustion", twenty-argument
spills, a thirty-two-argument spill of mixed composites and scalars
(`spill_all_exec_c`; its twin `spill_all_c` adds a `float32x4_t`, a two-vector
HVA and `MixF`, is refused on both sides and executes nothing), and 40 seeded
mixed signatures. Since 2026-10-14 five layout families add
`#[repr(align(N))]` composites for N from 2 to 64 under both ABIs (two
16-aligned shapes per ABI whose members are less aligned, at every NGRN 0–7
and on the stack at NSAA 0 and 8; every other shape in registers, on the
stack and as a result; nested both ways), `#[repr(packed)]` and `packed(2)`
composites, unions (integer, mixed integer/float, HFA-shaped, 2 to 24 bytes),
payload enums (Rust layout and the RFC 2195 `repr(u8)` / `repr(C, u32)`
layouts) and niche-carrying scalars (`NonZero*`, `Option<NonZero*>` up to
`u128`, `Option<bool>`, `Option<char>`). Each case is under the C ABI (an
`extern "C"` block, the FFI shape) and/or the Rust ABI (a path call through
`extern crate`). Every case also keeps ten `u64` and eight `f64` live across
its call (`live=`), in callee-saved registers or the caller's frame as each
compiler chooses, so a callee that clobbers either is a wrong value; nothing
forces a value into a particular register.

Every generated case carries the line its generator computed without a
compiler; the oracle must print exactly that line (regclass/sret: exit 42)
before a cross cell is compared with it, byte for byte. Each case runs in its
own process (selected by argument count), so a crash names one case. A trust-cg
refusal (exit 1, every error `[TCG-...]`-tagged, no compiler panic) is a
DECLINE, listed by case, side and level, and must equal the runner's committed
`EXPECTED_DECLINES` table, each declined cell with exactly its row's tag set:
an unlisted decline and a vanished one both fail, and the executed, matched
cross-cell count per suite has a pinned floor. When one function of a group
refuses, that group and level is rebuilt one case per crate pair so the
refusal hides nothing else; the cells the whole-group attempt did execute are
judged too (a wrong value or crash there fails the run), and its refusal must
be reproduced, side and tags, by the per-case rebuild. A wrong value, crash,
timeout, build or link failure, oracle failure or missing cell fails; there is
no skip.

Callers black-box SCALAR leaves only (both modes of `gen.py`): `black_box` is
itself a Rust-ABI call, and `black_box(A16 {..})` put a second, unrelated
Rust-ABI aggregate return in front of the C call under test, which the bridge
refused at O0/O1 (`[TCG-RET-ABI]`) in 25 of the 40 seeds' callers before the
change. The seeds' signatures and values are unchanged (the rng sequence is
the corpus); 157 of seeds 1–200's pair-mode callers differ only in where
`bb(..)` sits.

The trust-cg halves run with proof certificates and the refinement solver off
(`-Ztrust-ir-cg-args=no-proof-certs`, `refine-solver=0`) in Trust's unverified
frontend lane: ABI execution evidence, not proof evidence. The Linux record is
[reports/perf/2026-10-14-linux-cross-backend-abi](../../reports/perf/2026-10-14-linux-cross-backend-abi/README.md).

```sh
python3 scripts/check_linux_aarch64_xback.py --backend <backend.so> --out <new dir> --jobs 4
python3 -m unittest scripts/tests/test_linux_aarch64_xback.py   # runner contract, no backend
```

## Negative control

A gate nobody has seen fail is not evidence. Forcing the pre-fix behaviour
(`isel.set_abi_variant(AArch64AbiVariant::Darwin)` regardless of target — i.e.
Darwin classification on an AArch64 ELF target) makes this gate fail
**38 of 60** seed/direction combinations at `-O2` (seeds 1–30, both
directions) — i.e. 63% of randomly generated many-argument signatures were
miscompiled across a backend boundary. With the fix in place, the
target-selected classifier passes **240/240** MATCH across `-O1/-O2/-O3` for
40 seeds.

### 2026-08-25 — the type table decides which bugs the gate can express

The gate above was green while a second ABI bug of this exact class shipped:
AAPCS64 stage **C.8** (round the GPR index up to an EVEN register before
allocating a pair for any 16-byte-ALIGNED argument) was documented in the
`classify_params` doc comment and never implemented. It could not be caught
here because `gen.py`'s `INT_TYPES` stopped at `u64`/`i64` — no `i128`, no
16-byte-aligned aggregate. **The generator could not emit the shape that
breaks.** A gate is bounded by its input domain, not just by its assertions.

`gen.py` now also emits `u128`/`i128` and two `repr(C)` aggregates: `A16 {
i128 }` (align 16, must skip a register) and `A8 { i64, i64 }` (same 16 bytes,
align 8, must NOT skip) as the negative control — the rule keys off alignment,
so a same-size 8-aligned sibling is what keeps a future rewrite honest. The
checksum folds BOTH halves of every 128-bit value, since one read a register
too low still has a plausible low half.

Negative control for the extended table, measured before the fixes landed —
seeds 1–25 at `-O2`, 50 combinations:

| | result |
| --- | --- |
| C.8 missing, i128 stack paths missing | **14 MATCH, 18 MISMATCH, 18 declined** |
| after both fixes | **50 MATCH, 0 MISMATCH, 0 declined** |

The 18 declines and 18 mismatches were the same shape from two sides: an i128
that lands on the STACK (8 GPRs already consumed, or 7 consumed and C.8
rounding to 8). The callee failed closed — `value Value(8) not defined before
use`, because the incoming path materialised one vreg for a value that needs a
PAIR — while the caller silently stored only the low half. Fail-closed on one
side and a silent wrong answer on the other, from one missing case.

### Return values take three paths; the gate used to exercise one

Every generated program returned `u64`. But a return crosses the same boundary
as an argument and reaches it three different ways: `x0` for a scalar, `x0:x1`
for a 128-bit pair, and an INDIRECT sret buffer whose pointer arrives in `x8`
for anything over 16 bytes. `gen.py` now picks the return type per seed from
`u64`, `i128`, `A16`, `A8` and `A24` (>16B, so sret), and the caller folds the
value back to a `u64` exit code — a return read from the wrong register or the
wrong buffer changes it.

This one found no bugs: all five shapes matched in both directions on the first
run, which is the expected result, since returns start at `x0` and are already
even so C.8 cannot bite. Recording it so nobody re-derives it: **the AArch64
return path is clean; the parameter path was where both bugs lived.**

Current: **160/160** MATCH across `-O0/-O2` for 40 seeds with the extended
table, covering 5 return shapes and both i128 register and stack argument
paths.

### 2026-09-27 — Darwin

The first run on `aarch64-apple-darwin` (Apple M4 Max, macOS 26.6.2) passes
**320/320** MATCH for seeds 1–40 at O0–O3 in both directions, with a
negative control that forces AAPCS64 classification on the Darwin target.
Commands, compiler and backend identities, the generated sources and both
transcripts are in
[reports/perf/2026-09-27-darwin-abi-xback](../../reports/perf/2026-09-27-darwin-abi-xback/README.md).
The generator's domain is unchanged, so the DarwinPCS rules it cannot express
(HFA/HVA, `bool`, variadic, small or packed composites) are checked by the
Apple clang twins `e2e_aarch64_{aggregate_stack,variadic,bool_abi}_darwin`
instead.
