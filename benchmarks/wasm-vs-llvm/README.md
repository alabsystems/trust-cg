# benchmarks/wasm-vs-llvm — the wasm32 output-quality ratchet

The evidence institution for the wasm32 optimization program in
`docs/wasm32_perf_roadmap.md` (its phase
P0). It compares the code the trust-cg wasm32 lane emits for Rust programs with
the code rustc's LLVM backend emits for the same programs, and it records the
comparison in the shared performance ledger under the same rules as the native
`beat-llvm` rows: provenance stamps, evidence eligibility, append-only
machine-generated rows, a versioned contract and named baselines.

## Baselines

| name | lane | definition | role |
|---|---|---|---|
| **B1** | `llvm_o2` | rustc + LLVM, `wasm32-unknown-unknown`, `-C opt-level=2`, the same rustc frontend, sysroot and `wasm-ld` as the trust-cg lane, **no wasm-opt** | the primary bar; every ratio and every ratchet is trust-cg / B1 |
| — | `tcg_o2` | the same rustc with `-Zcodegen-backend=<the bridge dylib>`, `-C opt-level=2`, `-Ztrust-ir-cg-args=no-proof-certs` | the measured lane |
| **B2** | `llvm_o2_wasmopt` | B1's module through binaryen `wasm-opt -O2 -g` (names kept, as in B1) | context only: what a wasm-pack style pipeline ships; never ratcheted or gated |

Both rustc lanes compile with `-Ztrust-verify=off` (the Trust frontend's
explicit unverified lane, as the native harness and the bridge differentials
do), `--edition 2021 --crate-type cdylib -C panic=abort`, and link with the
same `wasm-ld`.

The wasm32 lane emits no per-instruction proof certificates, and the bridge
refuses it under the default proof-certificate gate (`[TCG-PROOF-465]`), so
`no-proof-certs` is part of the lane's definition: the ledger requires it on
every wasm32 row and rejects every other proof-weakening knob or `TCG_*`
environment. **These rows make no proof claim** about the code they measure.

## Corpus

`progs/` holds 144 `#![no_std]` cdylib programs (519 exported functions) from this
project's wasm32 Rust-level differential campaigns, selected because they
agreed with rustc+LLVM at `-C opt-level=2` when the plan was written. The plan's
list named 150 files; six of them (`k18o/drop_*`, `k20cgu/fmt_*`) were
byte-identical copies of others and were dropped so that no program counts
twice. Sources are `trustfmt`-formatted (edition 2021). `progs/manifest.json`
is the source of truth: every program has a row with its `group` (the campaign:
float, int, slice, kernels) and SHA-256, and `run.py` refuses to run when files
and rows disagree. A row may list `soft_signed_zero` exports (below), each
with its reason. A program-set change starts a new lineage (below).

Every export takes and returns only `i32`/`i64`/`f32`/`f64` scalars; loops are
bounded independently of their inputs; a panic traps.

## What a run measures

`run.py` compiles every program in the three lanes and hands the modules to
`wasmtool.mjs` (node, no dependencies):

1. **Correctness first.** Every scalar export is driven over a deterministic
   grid (38 `i32`, 21 `i64`, 17 `f32` and 20 `f64` values; the full cross
   product for one or two parameters, 600 tuples from a fixed LCG for three or
   more, three calls for none) on a fresh instance of each lane, and every
   result is compared with B1, traps included. Each run executes in its own
   worker thread under a time budget. A disagreement, a missing export, a
   differing workload accumulator (below), or a trust-cg module that fails to
   compile or instantiate, or does not return within max(20 s, 50x B1's time),
   where B1's ran, makes the program a **MISMATCH**: stop-the-line, and the
   ledger rejects the whole results file. A `+0`/`-0` difference is a
   disagreement unless the manifest lists the export under `soft_signed_zero`
   (today only `c7_minmax`'s `min32` and `max64`, which call `f32::min` and
   `f64::max`: Rust returns either operand for equal zeros); a listed
   difference is counted and recorded with its export and arguments
   (`soft_signed_zero_total` on the row). NaN payloads are not observable at
   the JavaScript boundary and are not compared.
2. **Workload.** The grid calls on which B1 does not trap, in grid order. Each
   lane gets a loop module: its own module plus one appended function,
   `__wvl_loop(reps)`, that runs the workload `reps` times inside wasm,
   folds every result into an `i64` accumulator (floats by their bits, every
   NaN as one pattern, `-0` as `+0` only for listed `soft_signed_zero`
   exports), and passes its constant arguments
   through mutable zero globals so the engine cannot fold them. The
   accumulator of one pass must be equal in every lane.
3. **Static metrics** from a decoder of each module: file bytes, code-section
   bytes, decoded instructions (`end`/`else` markers excluded), declared
   locals, static loads/stores/bulk-memory operations, `local.*` operations,
   and functions that write `__stack_pointer`.
4. **Dynamic metrics** from one pass of the workload on an instrumented copy
   of each lane's loop module (the appended loop itself is not counted):
   executed instructions, memory operations, calls and loop-header entries,
   counted per straight-line segment (exact for a non-trapping workload), and
   the **stack high-water**: `__stack_pointer`'s initial value minus the
   lowest stack address in use, which is the lower of the smallest value any
   `global.set` wrote to `__stack_pointer` and the smallest effective address
   any load, store or non-empty bulk-memory operation touched below its
   initial value. Writes alone would undercount: LLVM's leaf functions use
   memory below the stack pointer without moving it. The region below the
   initial stack pointer is the stack only in a stack-first layout (rustc
   links wasm32 with `--stack-first`), which the harness checks (one memory,
   every active data segment above it); a module without it gets no stack
   reading. Both components are recorded. The instrumented pass must produce
   the plain loop's accumulator, or the readings are dropped.
5. **Timing** in three node engine modes, one node process per mode:
   default tiering, `--no-liftoff` (TurboFan only) and `--liftoff-only`
   (baseline compiler only). After a warm-up pass, `reps` is calibrated on B1
   until one sample takes at least `--target-ms` (20 ms); then `--n-run` (5)
   samples per lane are taken, interleaved, with the lane order rotated each
   round. The reading is the **min** of the samples; the median is kept as
   context, and so is the first single pass on a fresh instance
   (`first_call_ms`, which includes lazy compilation). In default mode the
   samples follow warm-up and calibration, so hot functions have usually
   tiered up; the Liftoff column shows the baseline-compiler gap.

Programs with an empty workload, or whose B1 loop traps on a fresh instance
(a stateful export), have no dynamic, stack or timing reading; that is decided
by B1 alone and they are listed as `workload_excluded`.

A program that is not measured is **INCOMPLETE** with an `incomplete_kind`:
`refused` (the bridge refused it with a typed `[TCG-*]` diagnostic: a
fail-closed refusal, which lowers coverage), `compile_failed` (the bridge
failed in any other way), `b1_failed` (rustc+LLVM failed, or its module did
not run) or `harness`. Only `refused` is compatible with an evidence row.

## Aggregates

Per-program ratios are trust-cg / B1. Metrics that are positive by
construction (file and code bytes, static and dynamic instructions, time)
aggregate as the **geomean** of the ratios. Counts that can be zero for LLVM
(declared locals, static and dynamic memory operations, calls, stack bytes:
some programs touch no stack memory at all in LLVM's code) aggregate as the
**ratio of corpus totals**, because a per-program ratio with a zero
denominator is undefined. Every aggregate is exact and fail-closed: null unless every program
in its scope has both readings. `contract/wasm_contract.py` is the one
definition; the harness stamps it and the ledger recomputes it and rejects a
stamp that disagrees.

## Running it

```sh
WASM32_SYSROOT=<sysroot from scripts/build_wasm32_sysroot.sh> WASM_LD=<wasm-ld> \
WASM_OPT=<binaryen wasm-opt, optional> \
python3 benchmarks/wasm-vs-llvm/run.py --rustc <trustc> \
    --bridge crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib
```

Every tool comes from an argument or the documented environment
(`--rustc`, default `trustc` on PATH; `--bridge`, required; `--sysroot` or
`WASM32_SYSROOT`; `--wasm-ld` or `WASM_LD`; `--node`, default `node` on PATH;
`--wasm-opt` or `WASM_OPT`, optional). The harness never builds trust-cg or the
bridge. It refuses a LOADED machine unless `--allow-loaded`. `--progs` measures
a subset (never evidence), `--jobs` parallelizes compiling and the
deterministic measurements (timing is always sequential), `--work-dir` places
the per-program build outputs, which are deleted as soon as a program is done.
A full run with `--jobs 4` took about ten minutes on a loaded 14-core Apple M4 Pro.

Results go to `results/<sha12>[-dirty]-<stamp>.json` (gitignored) with a
markdown summary beside it. They enter the ledger only through the checker:

```sh
python3 scripts/check_perf_ratchet.py --append benchmarks/wasm-vs-llvm/results/<file>.json
```

`node wasmtool.mjs selftest` checks the decoder, the loop builder, the
instrumenter (counts and stack readings, leaf frames and bulk memory
included), the isolated runner and the differential on hand-assembled modules
with known answers; `scripts/tests/test_wasm_perf_ratchet.py` runs it and
drives `run.py`'s per-program verdicts through the real `wasmtool.mjs` with
hand-built modules that hang, fail validation, trap at instantiation or
differ only in the sign of zero.

### Where the file bytes go

`sections.py` is a diagnostic beside the harness, not part of it: it
compiles the corpus (or `--progs`) with `run.py`'s own flags in the B1 lane
and in one trust-cg lane per `--bridge NAME=DYLIB`, and splits every linked
module into its sections, each counted with its header so that they sum to
the file bytes, plus what the excess is made of inside them (distinct
types, identical bodies, data images and their zero bytes, export and
import names, and the `name` section's subsections with the bytes of
function names that keep the crate-private mark). It writes
`<out>/sections.json` and prints corpus totals per lane over all programs
and over those larger than B1:

```sh
python3 benchmarks/wasm-vs-llvm/sections.py --rustc <trustc> --sysroot <sysroot> \
    --wasm-ld <wasm-ld> --bridge base=<dylib> --bridge new=<dylib> --out <dir>
```

It is not in `measurement_sha256` and no ledger row is made from it.

## Ledger rows

`scripts/check_perf_ratchet.py` routes a `trust-cg-wasm-bench-v2` results file
to `scripts/wasm_perf_ratchet.py`, which condenses a `row_family: "wasm32"` row
into `ratchet/ledger.jsonl` and renders a wasm32 section into
`benchmarks/LEDGER.md` (machine-generated; never edit it). Native rows and wasm32
rows never see each other.

- **Rejected** (never appended): a MISMATCH, missing mandatory provenance, a
  non-wasm32 target, a proof-weakening knob or environment beyond the lane's
  `no-proof-certs`, a stamped aggregate that disagrees with the per-program
  table, a malformed table (an INCOMPLETE program without its kind, a MATCH
  program whose differential is not clean, a signed-zero allowance the
  manifest does not list).
- **Evidence** (`evidence: true`, a possible baseline) requires, recomputed from
  the results rather than the headline stamp: a QUIET host (1-minute load at
  most ncpu/2 before and after, no threshold override, no runaway process), a
  clean tree, the default environment and exactly the lane's knobs, complete
  provenance, a backend dylib no older than the backend sources, exactly the
  committed corpus, 0 MISMATCH, every INCOMPLETE program a typed refusal, at
  least 5 timing samples, all three engine modes, and every deterministic and
  timing aggregate measured. Other rows are recorded as context
  (`evidence: false`) and are still regression-checked.
- **Ratchet** (thresholds in `ratchet/perf_baseline.json`, `wasm32_thresholds`):
  the deterministic metrics against evidence rows with the same toolchain key
  (target, opt level, rustc, wasm-ld, sysroot digest, grid digest, contract
  version, and `measurement_sha256`, the digest of `run.py`, `wasmtool.mjs`
  and `contract/wasm_contract.py`), with **zero tolerance**: they do not
  depend on the host or engine, and a change to what or how the harness
  counts starts a new key, so under one key any increase is a change in the
  measured code. Timing against evidence rows with the same
  toolchain, host and node/V8, with a 10% floor. A coverage drop is red. Every
  comparison uses the per-program pairs both rows kept, over the programs
  both measured, so a corpus change never hides a regression on the programs
  that stayed; a changed program set is otherwise INCONCLUSIVE until
  `--append --new-lineage '<reason>'` on an eligible evidence row. A program
  subset, fewer than 5 samples or fewer modes is INCONCLUSIVE.
- **GATE-WASM-SB** (contract `gates`) is **PROPOSED**, not owner-approved: file
  bytes and both time geomeans below 1.00x B1 with every program at most 1.50x,
  stack high-water total at most 1.00x, and full coverage. The ledger view
  reports it; the ratchet never reads it.

## What the numbers show, and what they do not

They show, for the stamped bridge dylib, rustc, sysroot, `wasm-ld` and node:

- how the bytes and the static and dynamic wasm instruction counts of the
  trust-cg lane compare with LLVM's on these 144 programs, exactly and
  reproducibly;
- how much shadow-stack memory each lane touches while running the workload;
- how fast V8 runs each lane's code on this host, in each tier;
- that the trust-cg lane computed the same results as LLVM on the grid and on
  the workload, for every program counted, up to the sign of zero on the
  exports the manifest lists (and NaN payloads, which are not observed).

They do **not** show:

- anything about proofs: the lane runs with `no-proof-certs`, and both
  frontends with `-Ztrust-verify=off`;
- correctness beyond the grid: agreement on finitely many inputs is a
  differential test, not a proof, and the corpus was selected from programs
  that already agreed (survivor bias);
- representative application performance: the programs are small
  differential-test kernels with scalar exports, dominated in places by call
  and harness overhead;
- machine-level cost: dynamic counts are wasm instructions, not the native
  instructions V8 emits; the stack high-water counts only the shadow stack in
  linear memory (the lowest address written to `__stack_pointer` or touched
  below its initial value), not the engine's own stack or wasm locals;
- that one host or node version predicts another: timing is compared only
  within one host and engine;
- that wasm-opt-level or LLVM `-O3`/`-Os` comparisons hold: B2 is context, and
  `-O3`/`-Os` are not measured;
- that a stale-looking dylib is wrong, or a fresh-looking one right: the
  staleness check compares file times only.

A LOADED or dirty row is context, never a baseline or a headline. The last
row in `LEDGER.md` describes its stamped revision and host, not the current
checkout.
