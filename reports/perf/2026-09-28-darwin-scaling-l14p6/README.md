# L14-P6: the superlinear compile growth on aarch64-apple-darwin, located and removed

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Ledger row `L14-P6`. The [2026-09-28 Darwin campaign](../2026-09-28-darwin-aarch64-campaign/README.md)
measured `scale_gate.py --rss` at 12.14x LLVM compile time and 25.35x peak RSS
(9,453.7 MiB) on the 33,605-line crate. Tripling the crate multiplied time by 8.6
and memory by 10. This report names the loops that caused the growth, describes the
fixes, and gives the before and after numbers. Every object the fixes touched
compiles to the same bytes.

Host: the campaign's Apple M4 Max (`Mac16,5`, 12 performance and 4 efficiency
cores, 48 GiB), macOS 26.6.2. Driver: Trust package 9192 (`trustc` `321aaeda7`,
explicit unverified frontend lane `-Ztrust-verify=off`). The bridge was built with
the campaign's command ([`commands/build_bridge.sh`](commands/build_bridge.sh),
`targo --unverified build --release --locked`). The CLI was built with stock Rust
1.97.1 (`cargo build --release --locked -p trust-cg-cli`). Every compile below is
`-O3` for `aarch64-apple-darwin` with proof certificates off (`no-proof-certs` in
the bridge; the CLI emits none unless asked). Scaling is still unmeasured with
proofs on, because the production lane refuses the corpus (`L07-P2`).

Other builds ran on this machine throughout, with a 1-minute load of 3 to 15.
Decisions rest on instructions retired and peak RSS from `/usr/bin/time -l`, which
load does not move much. Wall time is reported only with its load.

## Where the growth came from

`scale_gate.py` generates `n` loop functions and a `main` that calls each once:
`let r = f0(s, 0) ^ f1(s, 1) ^ … ;`. That `main` is **one basic block with `n`
calls**. `time`/`time-codegen` phase totals (`TCG_TIME`) put the xlarge compile in
`prepare::optimization`: 26.3 s of CPU against 2.4 s for everything else. A
`sample(1)` stack of the 2,400-function compile showed one worker in
`trust_cg_opt::scheduler::build_dag_for_insts` under
`PressureAwareScheduler`, while the other 15 were idle.

The same crate shape, written as trust-ir and compiled by the CLI with no rustc
frontend ([`commands/gen_tir.py`](commands/gen_tir.py)), grew the same way: 98.0G
instructions and 6,372 MiB at 2,400 functions. So the growth is in the backend.

1. **Pre-RA scheduler, call barriers** (`trust-cg-opt/src/scheduler.rs`,
   `build_dag_for_insts` step 3a). Every call or barrier gets an edge from every
   earlier instruction and to every later one. That gives a `HashSet<(usize, usize)>`
   and `deps`/`rev_deps` vectors of `O(calls * instructions)` edges. The pairwise
   physical-register (1d), fixed-PReg (1e) and memory (2) steps also compared
   instructions across every call. At 2,400 calls the block has about 15,000
   instructions and tens of millions of edges. This one loop was the 9 GiB.
2. **Register allocation, call sites** (`trust-cg-regalloc`). After the scheduler
   fix, CLI modules up to 25,600 functions showed a residual quadratic term of
   about 300 instructions per pair of functions, 30% of the compile at 25,600
   functions (646.5G instructions, then 449.7G once removed). `sample` put it in
   three places that ask every live interval about every call site's reserved
   positions:
   `call_clobber::find_call_crossings_in`, `LinearScan::reserved_interferes[_except]`
   and `regalloc_validator::check_physreg_interference`.

A second shape turned up while bisecting: **one long basic block of memory
accesses**. [`commands/gen_ptr.py`](commands/gen_ptr.py) generates store/load pairs
through a pointer argument, and [`commands/gen_mem2.py`](commands/gen_mem2.py)
generates them into a stack tuple. Per-pass timings (`TRUST_CG_TIME_PASSES`) and
`sample` named four more quadratic loops:

3. **Scheduler memory order** (step 2): every access ordered after every earlier
   access it may alias. A block of `m` stores holds `m(m-1)/2` edges, and the
   scheduler runs three times (pressure-aware twice, then the codegen scheduler).
4. **Frame-index elimination** (`trust-cg-codegen/src/frame.rs`,
   `scratch_live_after`). Every out-of-range frame access proves X16/X17 dead with
   a forward scan, which usually runs to the block end. This took 3.65 s at 4,000
   pairs on a 32 KB frame.
5. **Spill-slot coloring** (`spill_slot_reuse::compute_spill_slot_reuse`).
   First-fit compared each spill against every member of each color.
6. **Post-RA redundant-reload elimination** (`post_ra_opt`). A `retain` over every
   active slot per def, a forward scan per rewrite end, and a whole-range pass per
   rewrite.

## The fixes (emitted bytes unchanged)

| # | Change | Why the output is unchanged | Differential |
| --- | --- | --- | --- |
| 1, 3 | `build_scheduling_dag_for_insts`: split each region at calls, barriers and terminators. Run the edge rules per segment, with step 2 as the chain of total accesses. Chain each barrier to its neighbours. The public `build_dag` keeps the full DAG. | Every dropped edge `u -> w` is implied by a kept path `u -> v -> … -> w`. So the partial order, every critical-path priority, and every readiness step and start cycle are the same. The ready-set keys never read edges. The doc comment gives the argument. | `scheduling_dag_matches_full_dag_schedules`: 900 regions compared on reachability, priorities, and both list schedulers' order and pressure replay. `…_call_chain_is_linear` and `…_store_block_is_linear` check the edge counts. |
| 2 | `LiveInterval::first_live_point`: binary-search each live range into an ascending position list. `find_call_crossings_in` walks the ranges over sorted call positions. | It returns what the literal `find` returns, with the same predicate calls in the same order. It falls back to the scan for an unsorted list or ranges outside the invariant. | `first_live_point_matches_literal_scan` (2,000 cases), `find_call_crossings_matches_per_call_scan` (300 functions against the old per-call scan). |
| 4 | `ScratchLiveness`: the same scan run backward once per block and scratch register. | The elimination loop rewrites only the current position, so later positions are untouched when they are queried. A block with a repeated instruction id keeps the scan. | `scratch_liveness_table_matches_forward_scan`: every position of 400 blocks. |
| 5 | `color_against_range_unions`: one merged range set per color. | With ordered ranges, overlapping some member is the same as overlapping the union. Colors are tried in the same order. | `range_union_coloring_matches_pairwise_first_fit`: 500 spill sets against `color_pairwise`. |
| 6 | Active reloads indexed by def VReg; def and use position indexes per block. | The indexes follow every NOP and rewrite. A repeated instruction id keeps the scans. | `indexed_reload_elimination_matches_retain_scan`: 400 functions against the old implementation. |

## Byte identity

- **Bridge.** The seven crates of [`commands/ladder.sh`](commands/ladder.sh) are
  scale_gate's four plus 100, 400 and 1,600 functions. Their 21 objects
  (`-C save-temps`: the CGU, entry and allocator-shim objects) and 7 linked
  binaries are byte-identical between the baseline backend (`d201fe9e…`, built
  from `e29e8006d`) and the final one (`41d88451…`)
  ([`commands/compare_dirs.sh`](commands/compare_dirs.sh): `compared=28
  differing=0`).
- **CLI.** Every generated trust-ir module compiled with both the baseline and a
  fixed CLI gave identical object hashes. That covers the scale_gate shape at 25,
  100, 400, 800, 1,600 and 2,400 functions, the pointer block at 256, 1,024 and
  4,096 pairs, and the stack block at 500, 2,000 and 8,000 pairs.

After review, the comparison was widened beyond the scaling shapes and repeated
with the final backend of the fix round (bridge `57ee682d…`, CLI built from the
same tree), against a baseline bridge (`662f1a56…`) and a baseline CLI that the
review built with `--locked` from a scratch export of `e29e8006d`:

- **Bridge ladder again.** [`commands/ladder.sh`](commands/ladder.sh) then
  [`commands/compare_dirs.sh`](commands/compare_dirs.sh) against the baseline
  ladder: `compared=28 differing=0`.
- **Bridge corpus.** [`commands/bridge_corpus.sh`](commands/bridge_corpus.sh)
  compiles the repository's 102 Rust benchmark programs (`beat-llvm` 18,
  `shape-coverage` 72, `decline-shapes` 12) with `-C save-temps`, proofs off, at
  `-O3` and again at `-O1`. At each level all 413 objects and binaries are
  identical, and the same two programs (`s27_dyn_box_drop`, `s31_vec_sort_dedup`)
  fail on both backends (`logs/bridge-corpus.log`).
- **CLI corpus.** [`commands/cli_corpus.sh`](commands/cli_corpus.sh) compiles 129
  trust-ir modules (the 122 committed `.tir` fixtures, most of them
  `trust-cg-codegen` test inputs, plus the scaling shapes at small sizes) for
  `aarch64-apple-darwin`, `aarch64-unknown-linux-gnu`, `x86_64-unknown-linux-gnu`
  and `x86_64-apple-darwin` at `-O1` and `-O3`. All 844 emitted objects are
  identical. The other 188 compiles are refused by both CLIs with the same
  message once each build's own `target/release/build/<crate>-<hash>/` path is
  normalized, and no compile succeeds on one side only
  (`logs/cli-corpus.log`). The x86-64 rows matter because
  the register-allocation changes also run there.

Scope of this evidence: most Darwin floor targets build their modules in Rust test
code rather than from files, so their objects are not in either corpus; the floor
checks those by results (native differentials), not by bytes. Certificate bytes
were not compared, since every compile here has proofs off.

## Routes the changes reach

None of the changes adds, removes or reorders a pass, and none is a transform:
each computes the same answer as the code it replaces (the table above gives the
argument and the differential). So each runs wherever the replaced code ran,
including proof-grade AArch64 routes, and the register-allocation changes also run
on x86-64. No pass-schedule policy is involved.

## Before and after

### Bridge ladder (single compile each, `/usr/bin/time -l`)

The full rows and phase breakdowns are in
`logs/bridge-ladder-before.tsv` (load 6.0 to 6.1)
and `logs/bridge-ladder-after.tsv` (load 13.5 to
14.7). Instructions retired include the rustc frontend, about 5.9G at the smallest
size.

| Crate | Functions | Lines | Instructions before | after | Peak RSS before | after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 25 | 355 | 5.93G | 5.97G | 168.7 MiB | 167.3 MiB |
| x100 | 100 | 1,405 | 8.65G | 8.37G | 208.5 MiB | 182.5 MiB |
| medium | 200 | 2,805 | 12.78G | 11.84G | 243.2 MiB | 204.8 MiB |
| x400 | 400 | 5,605 | 22.36G | 18.70G | 427.6 MiB | 238.2 MiB |
| large | 800 | 11,205 | 46.26G | 32.45G | 1,040.5 MiB | 301.4 MiB |
| x1600 | 1,600 | 22,405 | 115.40G | 60.13G | 3,356.4 MiB | 428.3 MiB |
| xlarge | 2,400 | 33,605 | 232.73G | 88.11G | 9,541.1 MiB | 546.9 MiB |

From large to xlarge (3x the functions), instructions grew 5.03x before and
2.72x after, and peak RSS grew 9.17x before and 1.81x after. After the fix the
cost per added function is flat: `(I(n) - I(small)) / (n - 25)` is 34.2M
instructions at 800 functions and 34.6M at 2,400.

### scale_gate.py --rss (min-of-5 wall, min-of-3 RSS, lanes interleaved)

[`commands/scale_gate_pair.sh`](commands/scale_gate_pair.sh) ran both backends back
to back. The raw output is in `logs/scale-gate-pair.log`.

The fixed backend ran first (load 10.8 at the start, 8.4 at the end), then the
baseline (8.4 at the start, 10.4 at the end). Times are LLVM and trust-cg wall
seconds, and RSS is in MiB (the gate's `M`).

| Crate | Lines | LLVM | before | after | Time before | after | LLVM RSS | RSS before | after | Memory before | after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 355 | 0.336 / 0.342 | 0.472 | 0.482 | 1.41x | 1.41x | 137.2 / 137.1 | 168.2 | 167.1 | 1.23x | 1.22x |
| medium | 2,805 | 0.446 / 0.460 | 0.712 | 0.650 | 1.60x | 1.41x | 147.1 / 147.1 | 242.5 | 204.8 | 1.65x | 1.39x |
| large | 11,205 | 0.846 / 0.851 | 2.836 | 1.278 | 3.35x | 1.50x | 202.0 / 200.5 | 915.9 | 301.3 | 4.53x | 1.50x |
| xlarge | 33,605 | 1.938 / 1.933 | 24.756 | 2.891 | 12.77x | 1.50x | 371.5 / 373.1 | 9,368.0 | 541.0 | 25.22x | 1.45x |

The baseline reproduces the campaign's 12.14x and 25.35x. After the fix, time
and memory stay within 1.5x of LLVM from 11,205 to 33,605 lines, where LLVM itself
grows 2.3x in time and 1.9x in memory and trust-cg grows 2.3x and 1.8x. These are
wall ratios under load; the instruction counts above are the load-robust record.

### Backend alone: CLI on generated trust-ir

The baseline CLI was built from `e29e8006d` and the final one from this branch's
head. [`commands/cli_ladder.sh`](commands/cli_ladder.sh),
[`commands/cli_ptr.sh`](commands/cli_ptr.sh) and
[`commands/cli_chain.sh`](commands/cli_chain.sh) ran them, one compile each, at a
load of 4 to 11. The raw numbers are in
`logs/cli-ladders.tsv`. The baseline was not run at 6,400
and 25,600 functions, which would need tens of GiB. `gen_tir.py` is a timing
generator whose rotate amount can reach 64 at function 62, so its objects are for
comparison only. The regression test's generator keeps the amount in 1 to 62.

| Shape | Size | Instructions before | after | Peak RSS before | after |
| --- | ---: | ---: | ---: | ---: | ---: |
| scale_gate shape (functions) | 25 | 0.51G | 0.54G | 19.3 MiB | 18.6 MiB |
| scale_gate shape (functions) | 100 | 1.96G | 1.84G | 41.2 MiB | 27.5 MiB |
| scale_gate shape (functions) | 400 | 8.84G | 7.10G | 244.3 MiB | 54.6 MiB |
| scale_gate shape (functions) | 800 | 20.66G | 14.00G | 838.2 MiB | 88.5 MiB |
| scale_gate shape (functions) | 1,600 | 53.41G | 27.67G | 4,007.1 MiB | 153.8 MiB |
| scale_gate shape (functions) | 2,400 | 97.99G | 41.43G | 6,372.3 MiB | 220.5 MiB |
| scale_gate shape (functions) | 6,400 | not run | 110.17G | not run | 546.7 MiB |
| scale_gate shape (functions) | 25,600 | not run | 446.21G | not run | 2,091.9 MiB |
| pointer store/load block (pairs) | 256 | 0.83G | 0.65G | 33.9 MiB | 22.2 MiB |
| pointer store/load block (pairs) | 1,024 | 5.55G | 3.59G | 242.8 MiB | 47.0 MiB |
| pointer store/load block (pairs) | 4,096 | 138.75G | 18.36G | 3,567.5 MiB | 147.4 MiB |
| stack-tuple store/load block (pairs) | 500 | 1.20G | 1.21G | 27.4 MiB | 27.0 MiB |
| stack-tuple store/load block (pairs) | 2,000 | 17.04G | 8.87G | 849.4 MiB | 81.6 MiB |
| stack-tuple store/load block (pairs) | 8,000 | 469.38G | 44.40G | 13,987.0 MiB | 307.3 MiB |

For the scale_gate shape, the cost per function is flat after the fix: 18.4M
instructions at 100 functions, 17.3M at 2,400 and 17.4M at 25,600, with RSS growing
about 83 KiB per function. Before the fix it grew from 19.6M at 100 functions to 40.8M
at 2,400. Both store/load shapes are near-linear in memory after the fix, but not in
instructions: per 4x step the pointer block grows 5.5x then 5.1x, and the
stack-tuple block 7.3x then 5.0x (see "What is not done").

## Merge with main at `59f72f9d4`

Main moved while this branch was in review, and three of its commits touch the
same loops.

- **`9f0e4a24b` (LinearScan reservation checks).** Main replaced the
  per-position scan with a range-side search over a memoized union of the
  reserved positions per candidate register. That computes the same existential
  this branch computed with `first_live_point` over sorted per-key lists. The
  merge keeps main's form and its oracle test, and charges `scan_work` in the
  range walk and the union build, so `reservation_checks_cost_grows_linearly`
  now guards main's code. Forcing the old position scan reads x16.00; rebuilding
  the union on every check reads x15.95.
- **`f1ae76c31` (scheduling DAG edge set).** Main collects the DAG's edges in a
  `DenseEdges` bit matrix. The merged `dependency_edges` takes the collector as a
  type parameter; the full DAG uses `DenseEdges` as on main, and so does each
  barrier-free segment of the scheduling DAG. At most one matrix (8 MiB at most)
  is live at a time.
- **`becb4b9df` (provenance).** Main removed `ProvenanceMap::record_merge`'s scan
  of the whole trust-ir-to-machine map on every CSE merge, one of the two
  residual terms this report named. The same commit re-derives the reverse
  index after every mutation in debug builds, and `aarch64_compile_scaling`,
  which runs in the test profile, failed after the merge: on the external-call
  block allocated bytes grew 14.5x then 15.6x per 4x step, and instructions
  14.1x then 16.1x. `sample` of the debug CLI put 3,481 of 3,810 samples under
  `record_lowering` -> `debug_assert_mach_index_exact`. The re-derivation now
  runs on an amortized schedule: after every mutation while the map holds at most
  32 instructions, after every `size / 32` mutations above that, and once
  unconditionally in `build_transitive`. Main's oracle test still checks after
  every operation. Release builds compile neither check. The debug CLI
  (`--no-parallel`) on the external-call block read 6.00G and 81.1G
  instructions at 128 and 512 calls before, and 1.71G, 6.14G and 25.08G at 128,
  512 and 2,048 calls after.

**Byte identity against main.** A release `trust-cg` CLI and `compile_corpus`
were built with `--locked` from main at `59f72f9d4` and from the merged head, in
this branch's worktree:

- `benchmarks/compile-corpus` (`run.py measure --reps 2`, then `run.py
  compare`): **Identity: PASS** on all 534 (entry, lane) pairs
  ([`logs/compile-corpus-merge-compare.md`](logs/compile-corpus-merge-compare.md)). That includes
  198 pairs of `rustc-bridge` modules, which are the trust-ir the bridge hands to
  the backend, and their `aot-proofs` refusal texts. Steady-state instructions,
  merged against main: `aot-object` 0.943x (the scale gate's 200-function
  program 7.11G to 5.99G), `aot-proofs` 0.970x, `jit-raw` 0.993x.
- [`commands/cli_corpus.sh`](commands/cli_corpus.sh), main's CLI against the
  merged one, over the same 129 trust-ir modules x 4 targets x `-O1`/`-O3`: all
  844 emitted objects identical, the other 188 compiles refused by both with the
  same message, no compile succeeding on one side only
  (`logs/cli-corpus-merge.log`).
- The seven generated shapes in the table below: identical objects.

The bridge was not rebuilt after the merge. The corpus's `rustc-bridge` origin
covers the backend on bridge-produced trust-ir.

**Cost against main.** Release CLI, one compile each, `-O3`,
`aarch64-apple-darwin`, instructions retired and peak RSS from `/usr/bin/time
-l`, at a load of 16 to 21:

| Shape | Size | Instructions, main | merged | Peak RSS, main | merged |
| --- | ---: | ---: | ---: | ---: | ---: |
| scale_gate shape (functions) | 2,400 | 88.55G | 30.47G | 8,666.8 MiB | 225.5 MiB |
| pointer store/load block (pairs) | 256 | 0.55G | 0.48G | 29.9 MiB | 22.7 MiB |
| pointer store/load block (pairs) | 1,024 | 3.60G | 2.46G | 192.4 MiB | 52.2 MiB |
| pointer store/load block (pairs) | 4,096 | 133.34G | 12.91G | 4,025.6 MiB | 168.0 MiB |
| stack-tuple store/load block (pairs) | 500 | 0.58G | 0.58G | 27.1 MiB | 28.0 MiB |
| stack-tuple store/load block (pairs) | 2,000 | 13.90G | 5.56G | 965.2 MiB | 87.5 MiB |
| stack-tuple store/load block (pairs) | 8,000 | 451.50G | 28.65G | 13,801.3 MiB | 297.4 MiB |

## What is not done

- **Memory-heavy single blocks keep a superlinear CPU term.** After the merge
  with main, instructions grow 5.1x (256 to 1,024 pairs) then 5.2x (1,024 to
  4,096) for store/load pairs through a pointer, and 9.6x (500 to 2,000) then
  5.2x (2,000 to 8,000) for pairs into a stack tuple. Before the merge the same
  steps read 5.5x, 5.1x, 7.3x and 5.0x; main's provenance fix made the small
  sizes cheaper than the large ones. The remaining term is `LinearScan::allocate`.
  On the stack-tuple block the per-pass timings (`TRUST_CG_TIME_PASSES=1`, merged
  CLI, load 16) put the `allocate-core` stage at 3.8 ms, 124 ms and 662 ms at
  500, 2,000 and 8,000 pairs (32x, then 5.3x), while the optimization phase takes
  12 ms, 70 ms and 351 ms (5.6x, then 5.0x). A `sample` of the 8,000-pair
  compile has `LinearScan::allocate` as the top self-time frame (318 samples)
  and `ProvenanceMap::record_merge` nowhere above the sampler's threshold.
  Before the merge, `allocate-core` took 3.8 ms, 122 ms and 647 ms and the
  optimization phase 38 ms, 209 ms and 1,076 ms (fix-round CLI, load 7.3), and
  `sample` put `LinearScan::allocate` at 321 of 572 register-allocation
  samples. Before the merge, this shape's heap bytes and allocations in a debug
  build also grew 4.7x to 4.9x per 4x step, too close to the test's 5x bound for a
  stable probe, so the regression test has no whole-compile probe for it. The fixes for it
  are bounded by the unit work counts below.
- **Proofs on.** The certificates-on lane refuses the corpus on this host
  (`L07-P2`), so there is still no proofs-on scaling curve.
- **Quiet re-measure.** Every number here was taken under concurrent build load.
  The wall-time ratios should be re-read on a quiet machine.

## Regression test

`crates/trust-cg-codegen/tests/aarch64_compile_scaling.rs` is a Darwin floor
target (`scripts/check_darwin_aarch64.py`, minimum 4). It compiles generated
trust-ir modules at 1x, 4x and 16x size through `Compiler::compile` (`-O3`,
Mach-O, proofs off, serial preparation). It fails if heap bytes allocated, heap
allocations, peak live heap (a counting global allocator) or, on macOS,
instructions retired (`proc_pid_rusage`) grow more than 5x across a 4x step. The
probes are an external-call block (128, 512 and 2,048 calls) and the scale_gate
shape (8, 32 and 128 loop functions plus the call block). With the fixes every
step reads 3.8x to 4.1x. With the old scheduler it fails at 13.4x allocated bytes
(and runs 78 s instead of 5 s). With the old register-allocation scans it fails at
5.83x instructions retired. A fourth test links the 48-function module against a
C reference and compares results for five seeds.

Instructions retired are read on macOS only, and the memory-block shape has no
whole-compile probe, so each fix is also bounded in its own crate by a
deterministic work count that runs on every host. `trust-cg-regalloc`'s
`scan_work` module is a per-thread counter that exists only under `cfg(test)`
(elsewhere `charge` compiles to nothing). The new range walks, union probes and
index lookups charge it, and so do the primitive probes the replaced scans were
built from (`LiveInterval::is_live_at`, `LiveInterval::overlaps`, the forward def
scan, the per-position rewrite loop), so a caller routed back through them is
counted. `frame.rs` has the same counter for the IP-scratch scans. Each
`*_cost_grows_linearly` test measures 1x, 4x and 16x inputs and allows 5x per 4x
step:

| Test | Shape | Old scan forced | Step |
| --- | --- | --- | ---: |
| `liveness::first_live_point_cost_grows_linearly` | `n` short intervals against `n` points | literal branch | x16.00 |
| `call_clobber::find_call_crossings_cost_grows_linearly` | block of `c` calls | per-call branch | x16.00 |
| `linear_scan::reservation_checks_cost_grows_linearly` | `n` intervals, one register reserved at `n` points | callers back to `is_live_at` (before the merge) / main's form back to the position scan, or its union rebuilt per check (after) | x15.91 / x16.00, x15.95 |
| `regalloc_validator::physreg_interference_cost_grows_linearly` | same, through the validator | literal branch | x16.00 |
| `spill_slot_reuse::spill_slot_coloring_cost_grows_linearly` | `s` disjoint spills | `color_pairwise` | x16.09 |
| `post_ra_opt::reload_elimination_cost_grows_linearly` | `n` reloads reloaded again | forward def scan / rewrite loop | x14.97 / x15.13 |
| `frame::tests::scratch_liveness_cost_grows_linearly` (codegen) | `n` far-slot stores through `FrameIndexEliminator` | forward scan | x15.82 |

With the fixes every step reads about 4x. The two differentials
`first_live_point_matches_literal_scan` and
`find_call_crossings_matches_per_call_scan` also assert, case by case, that the
charged work stays within the range walk's bound, and count only cases where the
literal scan would exceed it. Reload elimination's `retain` over the active slots
has no fallback left to charge, so its differential checks results only. The
scheduler's reductions are bounded by the edge-count tests
`scheduling_dag_of_a_call_chain_is_linear` and
`scheduling_dag_of_a_store_block_is_linear`.
