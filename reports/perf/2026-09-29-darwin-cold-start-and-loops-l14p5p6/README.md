# L14-P5 and L14-P6 residuals: the Darwin cold start, and the loop and stack-tuple scaling terms

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Ledger rows `L14-P5` (per-compile fixed cost) and `L14-P6` (superlinear compile
growth). This report attributes the cost a cold bridge compile adds to a warm one,
names the parts that changed and the parts that remain, and gives before and after
numbers for the loop and stack-tuple shapes. It is measurement and testing on one
shared host. It is not a ledger row, not proof, and not evidence for a `run.py`
gate. Emitted bytes are unchanged throughout (see [Byte identity](#byte-identity)).

## Setup

| Item | Value |
| --- | --- |
| host | Apple M4 Max (`Mac16,5`, 16 CPUs, 48 GiB), macOS 26.6.2, shared with other agents' builds; 1-minute load 6.7 to 12.8 during the measurements below, recorded before every compile |
| driver | Trust package 9192 `bin/trustc` (`321aaeda7`, sha256 `6c513314…`), explicit unverified frontend lane `-Ztrust-verify=off` |
| base | main `7a713cf6f`: backend sha256 `2e05e484…`, CLI sha256 `a76e1f71…` |
| trace base | `7a713cf6f` plus only the start-path marks of `387e7fcf9` (backend `d411b158…`), for the attribution |
| head (start path, fixed cost) | the branch at `5bd422379`, before its merge of main: backend `b7fde329…` |
| final (scaling, byte identity) | the branch at `f07978702`, merged with main `5ff639bc2`: backend `74e9f783…`, CLI `c0d0b73d…` |
| builds | [`commands/build.sh`](commands/build.sh): `targo --unverified build --release --locked` through `scripts/trust_cargo.sh` (no proof claim for the build) |

Decisions rest on instructions retired and peak RSS from `/usr/bin/time -l` and on
the in-process heap counters of `aarch64_compile_scaling`. Wall time is reported
only with its load. Every bridge compile below has proof certificates off
(`no-proof-certs`), because the production lane refuses the corpus (`L07-P2`).

## 1. What a cold compile adds (L14-P5)

A cold compile populates a fresh private cache root (`XDG_CACHE_HOME`, mode 0700),
as `run.py --cold` does. It admits the AY build, writes and verifies a new private
copy of it, starts that copy for the first time, and discharges every obligation
live because the certificate store is empty. A warm compile replays stored
certificates.

The backend's `time` knob now prints a start-path trace: the milliseconds from
process start (macOS `proc_pidinfo`, Linux procfs) at which each step began or
ended. [`commands/startpath.py`](commands/startpath.py) runs five interleaved cold
and warm compiles per program and backend.

### Attribution, before (`p3_gcd`, one cold sample of the trace base)

| ms after process start | Step |
| ---: | --- |
| 9.3 | backend `init` |
| 9.7 to 30.9 | the Clean checker's two control-proof probes |
| 70.7 | AY admission digest of the 91 MB source done |
| 81.5 | DRAT checker digest done |
| 136.8 / 154.5 | private copy streamed / published |
| 195.1 | copy re-digested before use (custody check) |
| 195.2 | first start of the copy (`ay --version`) begins |
| 271.3 | `codegen_crate`: the front end is done |
| 277.2 | the first solve starts waiting for the first start |
| 900.6 | first start ends |
| 912 to 1,257.5 | nine live discharges: a fresh `ay solve --proof` (22 to 51 ms) then a Clean check (4 to 11 ms) each |
| 1,268.2 | `join_codegen` ends |

The warm compile of the same program ends `join_codegen` at 404.3 ms: its nine
certificate replays take 4 to 14 ms each. Of the 864 ms difference, about 620 ms is
the first solve waiting for the first start of the new copy and about 250 ms is live
discharges in place of replays. Everything before the first start runs on the
identity warm-up thread while the front end runs. It delays the compile only by
delaying the first start.

The first start is slow because macOS assesses a new executable before it first
runs it (a syspolicyd/XProtect scan of the whole 91 MB file). In the 40 cold samples
below, the time from the start of that assessment to the end of the first start is
681 to 749 ms in 22 samples and 781 to 921 ms in five. The other 13 (5 before, 8
after) took 1.0 to 3.2 s. The host was shared with other agents' builds (load 10.7
to 12.4), whose new executables the same host service assesses; the trace does not
record what delayed any one sample.

### What changed

1. **One read admits AY and writes the copy.** When this process has not digested
   the AY's file state and no copy is published (every cold compile), one read of
   the source streams the private copy and is the admission digest. The source's
   stamp is checked before the open and after the read, before the streamed digest
   is compared, as the separate digest checks it, and the published copy is still
   digested before it is used. Cold compiles digest three executables (299 MB)
   instead of four (390 MB), and the copy is published at 78 to 89 ms instead of 144
   to 195 ms (medians). A candidate whose bytes are not the admitted identity is
   refused from that same read, with the same `Mismatch` refusal and nothing
   published, but its bytes are first streamed into a temporary under the cache
   root (removed at once), and the empty directory named by the admitted digest
   stays. Before, a mismatch was read once and never written. Unit tests change the
   source during the read and before it, and fail if either stamp check or the
   separate digest's own stamp check is removed.
2. **The assessment starts at publication.** Right after it publishes a copy it
   streamed from bytes that digest to the admitted identity, the backend spawns the
   copy suspended (`POSIX_SPAWN_START_SUSPENDED`), checks that the child is stopped
   (`SSTOP`) with no user time, kills it and reaps it. Not one instruction of the
   copy runs, and the host's assessment begins and continues after the kill. A child
   that fails the check is killed as well, and the process makes no further such
   spawn. A copy another process published first is not spawned before this process
   has re-digested it. The re-digest of the copy and the checker digest now run while
   the host assesses it. An `atexit` hook serializes against a spawn in flight.
   `process_cost` counts these spawns (`assessment_spawns`): one per cold compile,
   none warm. The unit test `beginning_the_host_assessment_never_runs_the_file`
   holds the spawn for 500 ms before the check, long enough for an unsuspended
   child to start `sh` and write its marker: without the suspend flag it fails at
   the check, and with the check also disabled it fails on the marker.
3. **The checker probe runs beside AY admission** on a scoped helper thread. Both
   results are still required before the first start.

No identity, custody or fail-closed check was removed or moved after the point
where its result is used.

### After (medians of 5, ms after process start; load 10.7 to 12.4)

| Program | assessment begins, before / after | first start ends, before median (min) / after median (min) | cold `join_codegen` end, before / after | warm `join_codegen` end, before / after |
| --- | ---: | ---: | ---: | ---: |
| `trivial` (`fn main(){}`) | 238 / 85 | 954 (880) / 972 (786) | 1,021 / 1,053 | 303 / 294 |
| `p3_gcd` | 195 / 92 | 907 (897) / 789 (778) | 1,268 / 1,146 | 385 / 383 |
| `p1_xorshift` | 184 / 81 | 1,243 (907) / 1,302 (867) | 1,593 / 1,581 | 385 / 396 |
| `m1_call_chain` | 197 / 93 | 926 (900) / 986 (800) | 1,342 / 1,393 | 442 / 416 |

"Before" is the trace base's first start, which is when its assessment began. The
assessment now begins 100 to 150 ms earlier, and the earliest first-start end of
each program moves 40 to 120 ms earlier. The medians do not move reliably, because
the assessment queue's outliers land in both lanes. No cold wall-time gain is
claimed beyond that. Raw marks of every sample:
`logs/startpath-results.json`.

### Fixed cost (medians of 5, [`measure.py`](../2026-09-28-darwin-fixed-cost/measure.py))

`base` is `7a713cf6f` and `head` is `5bd422379`. Instructions retired are in
millions, peak RSS (`maximum resident set size`) in MB, and wall in seconds with
load 9.4 to 12.8. Raw samples: `logs/fixed-cost-results.json`.

| Program | Lane | Base instr. | Head instr. | Base RSS | Head RSS | Base wall | Head wall | LLVM instr. / RSS / wall |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `trivial` | warm | 4,626 | 4,617 | 150.1 | 150.0 | 0.35 | 0.35 | 3,946 / 126.1 / 0.33 |
| `trivial` | cold | 4,851 | 4,694 | 151.2 | 151.3 | 1.45 | 1.30 | |
| `p3_gcd` | warm | 4,812 | 4,809 | 170.2 | 170.1 | 0.48 | 0.48 | 4,019 / 143.1 / 0.36 |
| `p3_gcd` | cold | 5,076 | 4,925 | 169.9 | 170.1 | 1.49 | 1.99 | |
| `p1_xorshift` | warm | 4,780 | 4,779 | 170.1 | 170.2 | 0.42 | 0.41 | 4,026 / 142.4 / 0.33 |
| `p1_xorshift` | cold | 5,040 | 4,881 | 169.7 | 170.0 | 1.31 | 1.33 | |
| `m1_call_chain` | warm | 4,807 | 4,811 | 171.2 | 171.2 | 0.41 | 0.42 | 4,014 / 143.0 / 0.33 |
| `m1_call_chain` | cold | 5,078 | 4,927 | 170.9 | 171.0 | 1.54 | 1.55 | |
| `id32` (certificates on) | warm | 4,533 | 4,536 | 141.7 | 141.3 | 0.27 | 0.27 | 3,875 / 121.1 / 0.27 |
| `id32` (certificates on) | cold | 4,755 | 4,598 | 143.2 | 143.3 | 0.28 | 0.28 | |

Every cold compile retires 151 to 159 M fewer instructions (the 91 MB digest that
is no longer read). Warm compiles are unchanged within 10 M. The cold wall medians
are dominated by the assessment queue (single samples range from 0.97 to 4.33 s).

### What remains, and why it stays

- **The host's assessment of the new copy, about 0.7 s.** The AY identity rule runs
  AY only from a private copy under the cache root, so a fresh cache root holds a
  new executable, and macOS assesses a new executable before its first run. The
  wait is paid once per cache root and AY build. Avoiding it would need a copy
  that outlives the cache root (for example one per user and AY digest), which
  moves the custody boundary, so it is not done (OD-48 in the
  decision record, ruled 2026-10-02).
- **Live discharges, about 200 to 260 ms more than replays.** A cold compile has no
  certificates, so each obligation is discharged by a fresh AY proof and checked by
  Clean before its result is used. They run one after another because the bridge
  keeps its recursive proof work on one process-local 32 MiB-stack worker by default
  (`rustc-codegen-trust-cg` `init`): Cargo already runs many rustc processes at once,
  and the policy keeps crate-level and instruction-level parallelism from
  multiplying across them. `max-parallelism` overrides it. Running a cold compile's
  discharges concurrently would change that policy, so it is not attempted here.
  Deliverable (1) of this work is therefore mostly attribution: it removed one
  91 MB read (about 155 M instructions) and began the assessment about 100 ms
  earlier, and claims no cold wall-time gain.
- **Two 91 MB digests per compile**: the source when a copy exists, and the copy
  before use. Both are identity and custody checks, and both run on the identity
  thread, finished at about 92 ms warm while the front end runs until about 278 ms.

## 2. Scaling (L14-P6)

### The stack-tuple block: `LinearScan::allocate`

The [L14-P6 report](../2026-09-28-darwin-scaling-l14p6/README.md) left one term:
on one long block of spilled values, `LinearScan::allocate` was the top self-time
frame and its `allocate-core` stage grew 5.2x per 4x step. Every "does some active
interval hold a register overlapping this one" question walked the active set and
looked each interval's VReg up in the allocation map, and the eviction search asked
it per candidate register per active interval.

When every interval has its own VReg (every production caller), an active
interval's register is `allocation[vreg]` for as long as it is active. The
allocator now records the holdings as intervals enter and leave the active set, and
a question reads the holdings of the registers overlapping its register (memoized
per register over the allocatable registers). A repeated VReg keeps the literal
scans. Free-pool reinsertion reads a precomputed preference rank. The allocation
stage of the 2,000- and 8,000-pair blocks fell from 84.6 to 7.3 ms and from 441.6
to 31.7 ms.

Differential: `indexed_linear_scan_matches_the_reference_allocator` compares the
allocation, spilled-VReg order and free pools against the pre-change allocator,
kept verbatim as `linear_scan_reference.rs` (test only), on 4,000 generated
problems over the AArch64 and x86-64 register files, with and without the index.
`blocked_allocation_cost_grows_linearly` bounds the scan-work units. The generated
problems never give two active intervals overlapping registers, because the allocator
never builds such an active set, so
`blocked_spill_candidate_matches_the_literal_scan_on_overlapping_holdings` compares
the eviction search against the literal scan on 3,000 active sets made by hand that
do (`Xn` beside `Wn`, or one register twice).

### The `loops` shape

compile-scaling's `loops` crate (one function of N independent loops) cost 2.08x
LLVM's CPU at 120 loops. Per-pass timings of its trust-ir, compiled by the CLI,
showed four passes redoing whole-function work once per loop:

| Pass | Per-loop work | Replacement | Differential |
| --- | --- | --- | --- |
| neon-fill | a whole-function `live_def_count` scan per copy strip, and a whole-function clone per applied plan | one `DefIndex` per sweep (built after four literal questions), and every plan applied to one private candidate, published only if all succeed | `def_index_answers_what_the_whole_function_scans_answer`, `a_def_index_asked_few_questions_builds_no_layout_index`, `a_chain_of_fill_loops_applies_as_one_candidate_like_one_at_a_time` |
| loop-unswitch | def sites rebuilt and the function scanned for body live-outs per innermost loop | one `UnswitchIndex` per run, from the second loop that searches | `unswitch_index_matches_the_per_loop_scans` |
| LICM | the constant-chain index dropped and rebuilt after each hoisting loop; the layout walked per fixpoint round, loop-defs build and memory-fact scan | the index refreshed for the blocks a hoist touched (not after the last loop); each loop visits its own blocks in layout order (positions built at the second loop) | `a_refreshed_chain_index_equals_a_rebuild`, `refreshing_the_chain_index_changes_no_hoist`, `body_blocks_in_layout_match_the_layout_filter` |
| post-RA coalescing | the whole function's physical liveness re-solved after each mutating block | strongly connected components numbered topologically; a mutation re-solves only the components it can reach, each from empty sets (the same least fixpoint) | `scc_liveness_matches_the_whole_function_resolve_under_mutation`, plus the existing decision-identity oracles |

At 480 loops, neon-fill fell from 1,169 to 39 ms, LICM from 844 to 35 ms,
loop-unswitch from 407 to under 4 ms and post-RA coalescing from 537 to 6 ms
(`logs/loops-pass-times.txt`).

The first build of these indexes made neon-fill and LICM cost more on a function
that asks few questions. In the bridge, scale_gate's 2,400 one-loop functions read
about 0.2% more instructions (serial, solver off: 69.86 to 69.93 G before, 70.03 to
70.05 G after). A bisection put it in the opt changes, and `f07978702` answers a
small function's first questions with the literal scans, which removed it (69.85
to 69.87 G against 69.88 to 70.02 G for the branch with `7a713cf6f`'s regalloc and
opt sources): `logs/sg-xlarge-serial-probe.txt`.

### Before and after: CLI, trust-ir only (medians of 3, `logs/cli-shapes.log`)

`base` is `7a713cf6f` and `final` is `f07978702`, release CLI, `aarch64-apple-darwin`,
load 7.0 to 10.2. The stack and pointer blocks come from the L14-P6 report's
[`gen_mem2.py`](../2026-09-28-darwin-scaling-l14p6/commands/gen_mem2.py) and
[`gen_ptr.py`](../2026-09-28-darwin-scaling-l14p6/commands/gen_ptr.py), the loops
modules are the bridge's dump of compile-scaling's crates
([`commands/dump_loops.py`](commands/dump_loops.py), `-O2` as that harness), and the
fill chains are [`commands/gen_fill_chain.py`](commands/gen_fill_chain.py).

| Module | Base instr. | Final instr. | Base RSS | Final RSS | Base wall | Final wall |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| stack tuple, 500 pairs | 0.581 G | 0.577 G | 28.0 MiB | 27.5 MiB | 0.037 s | 0.038 s |
| stack tuple, 2,000 pairs | 5.582 G | 3.667 G | 83.2 MiB | 85.5 MiB | 0.288 s | 0.217 s |
| stack tuple, 8,000 pairs | 28.814 G | 18.473 G | 290.7 MiB | 283.0 MiB | 1.480 s | 1.077 s |
| pointer block, 256 pairs | 0.446 G | 0.377 G | 22.7 MiB | 22.7 MiB | 0.029 s | 0.026 s |
| pointer block, 1,024 pairs | 2.474 G | 1.715 G | 52.5 MiB | 51.2 MiB | 0.135 s | 0.103 s |
| pointer block, 4,096 pairs | 12.975 G | 8.369 G | 147.5 MiB | 149.3 MiB | 0.655 s | 0.474 s |
| loops, 15 | 0.402 G | 0.356 G | 23.9 MiB | 23.7 MiB | 0.031 s | 0.028 s |
| loops, 30 | 0.904 G | 0.716 G | 31.3 MiB | 30.4 MiB | 0.062 s | 0.051 s |
| loops, 60 | 2.451 G | 1.697 G | 50.9 MiB | 47.9 MiB | 0.158 s | 0.112 s |
| loops, 120 | 7.745 G | 4.730 G | 100.0 MiB | 97.3 MiB | 0.464 s | 0.314 s |
| loops, 240 | 27.356 G | 15.199 G | 267.6 MiB | 263.8 MiB | 1.623 s | 0.912 s |
| loops, 480 | 101.054 G | 52.787 G | 911.8 MiB | 820.0 MiB | 6.063 s | 3.265 s |
| fill chain, 16 | 0.159 G | 0.142 G | 18.7 MiB | 18.4 MiB | 0.014 s | 0.014 s |
| fill chain, 64 | 0.764 G | 0.530 G | 24.8 MiB | 24.0 MiB | 0.052 s | 0.037 s |
| fill chain, 256 | 7.147 G | 3.340 G | 55.7 MiB | 51.9 MiB | 0.399 s | 0.196 s |
| fill chain, 1,024 | 114.481 G | 51.992 G | 390.2 MiB | 386.5 MiB | 6.134 s | 2.695 s |
| scale_gate medium (bridge dump) | 3.263 G | 3.252 G | 39.7 MiB | 39.9 MiB | 0.097 s | 0.097 s |
| scale_gate xlarge (bridge dump) | 36.969 G | 36.850 G | 263.3 MiB | 267.8 MiB | 0.812 s | 0.845 s |

Per 4x step the stack tuple now grows 6.4x and then 5.0x (was 9.6x and 5.2x); the
first step crosses the 512-field SROA limit, below which the tuple lives in
registers. The pointer block grows 4.5x and 4.9x (was 5.5x and 5.2x). Peak RSS of
the 8,000-pair block is not a stable metric: in an earlier run of the same binaries
(against the `5bd422379` CLI) it read 287 MiB base and 309 to 325 MiB head,
and with `TRUST_CG_MAX_PARALLELISM=1` each of those two binaries produced both
285-to-290 and 317-to-318 MiB runs. The counted heap peak of the in-process probe is identical before and
after (50,132,302 bytes at 2,560 pairs, `logs/in-process-probe.txt`).

### Before and after: bridge ladder (medians of 3, `logs/bridge-ladder.log`)

[`commands/bridge_ladder.py`](commands/bridge_ladder.py): compile-scaling's four
shapes (`-O2`, `no-proof-certs`, `refine-solver=0`, one codegen unit, as its
harness) and scale_gate's four crates (`-O3`, `no-proof-certs`), with the LLVM lane
interleaved. CPU is user plus system time; load 6.7 to 8.0.

| Shape | LLVM instr. / CPU | Base instr. / CPU / RSS | Final instr. / CPU / RSS |
| --- | ---: | ---: | ---: |
| loops 15 | 4.204 G / 0.41 s | 5.092 G / 0.57 s / 157.7 MiB | 5.045 G / 0.56 s / 157.2 MiB |
| loops 30 | 4.432 G / 0.42 s | 5.783 G / 0.61 s / 163.7 MiB | 5.547 G / 0.60 s / 163.3 MiB |
| loops 60 | 4.959 G / 0.47 s | 7.828 G / 0.73 s / 178.2 MiB | 6.874 G / 0.67 s / 178.0 MiB |
| loops 120 | 6.253 G / 0.54 s | 14.724 G / 1.13 s / 214.5 MiB | 10.910 G / 0.91 s / 215.5 MiB |
| blocks 800 | 5.599 G / 0.54 s | 8.770 G / 0.74 s / 192.5 MiB | 8.760 G / 0.73 s / 192.3 MiB |
| funcs 400 | 6.210 G / 0.53 s | 8.731 G / 0.78 s / 187.2 MiB | 8.747 G / 0.77 s / 186.8 MiB |
| arraysize 262,144 | 3.974 G / 0.38 s | 4.669 G / 0.55 s / 152.3 MiB | 4.675 G / 0.54 s / 152.0 MiB |
| scale_gate small | 4.270 G / 0.41 s | 5.482 G / 0.66 s / 168.0 MiB | 5.493 G / 0.64 s / 167.8 MiB |
| scale_gate medium | 6.198 G / 0.54 s | 10.628 G / 0.94 s / 196.9 MiB | 10.573 G / 0.93 s / 196.3 MiB |
| scale_gate large | 12.808 G / 0.94 s | 28.101 G / 1.93 s / 293.8 MiB | 28.036 G / 1.98 s / 293.9 MiB |
| scale_gate xlarge | 30.727 G / 2.12 s | 75.053 G / 4.58 s / 535.2 MiB | 75.120 G / 4.55 s / 535.2 MiB |

The 120-loop crate went from 2.09x to 1.69x LLVM's CPU. The other shapes move by
-0.5% to +0.2% of instructions, within about twice their run-to-run spread. The
linked binaries of all 20 crates are identical.

### What remains superlinear

- **The `loops` shape still grows faster than linearly** (final CLI, per 2x step:
  2.0x, 2.4x, 2.8x, 3.2x and 3.5x from 15 to 480 loops). Two stages carry it:
  `allocate-core` (59, 189 and 630 ms at 120, 240 and 480 loops) and the allocation
  validator's value-flow fixpoint (25, 100 and 380 ms, about 3.8x per 2x), which
  grows with the values live across loops.
- **The fill-loop chain** (a pointer and an accumulator live across N loops) grows
  6.3x from 64 to 256 loops and 15.6x from 256 to 1,024. At 1,024 loops a
  `sample(1)` of the `5bd422379` CLI spreads its self time over per-loop
  whole-function work in several passes: the vectorizer's use scans,
  `loop_latch_layout`'s rebuild after each rewritten loop, dominator-tree
  recomputation, the validator's exit-state fixpoint and the final layout
  cross-check. None is addressed here.

## 3. Guards

`crates/trust-cg-codegen/tests/aarch64_compile_scaling.rs` (Darwin floor minimum
now 7) adds three probes over the production AOT compiler:

- `stack_tuple_block_compile_cost_grows_linearly`: 640 to 2,560 pairs at `-O1`, in
  the spilled regime; heap bytes, allocations, peak live bytes and instructions
  within 5x per 4x step, and on macOS at most 10.5 G and 52 G instructions retired.
  The step bound alone does not guard the linear-scan change: the pre-change
  allocator also passes it (x4.98, 13.92 G to 69.28 G, in
  `logs/in-process-probe.txt`, against x4.89 and 7.88 G
  to 38.53 G after). The ceilings do: with the holdings index disabled the probe
  reads 13.93 G at 640 pairs and fails. On every host,
  `blocked_allocation_cost_grows_linearly` (`trust-cg-regalloc`) bounds the
  holdings search's work units, and it also fails with the index disabled.
- `fill_loop_chain_compile_cost_grows_linearly`: 4, 16 and 64 loops at `-O3`; heap
  metrics within 5x, instructions within 6x per 4x step (the remaining term above;
  before this work the 16-to-64 step read 7.46x allocated bytes and 6.46x
  instructions).
- `a_trivial_compile_stays_within_its_fixed_cost_budget`: one function returning
  its argument, after a warm-up compile, at most 2,100 allocations, 245,000 bytes
  and 11 M instructions (measured 1,391, 163,266 and 5.5 M in the test profile).

The bridge fixture `fixed_cost_budget_aarch64` now bounds a cold compile at 4
executable digests (was 5) and at most one assessment spawn cold and none warm.
Its certificates-on `id32` compile read cold 2 probes, 4 digests, 1 solver start
and 1 assessment spawn, and warm 2, 4, 0 and 0, with the `5bd422379` backend. After
the merge with main the fixture is red on this host for a reason outside this
work: main's `5ff639bc2` keeps a proof-grade Darwin leaf's FP/LR envelope, and the
`id32` compile is then refused with `[TCG-PROOF-465]` (its frame rows need an
independently replayed proof), with main's own sources as well. Until that is
resolved on main, no passing test enforces the fixture's new bounds. A review
reproduced the fixture by hand at the merged head `c93f2cbee` (its source and flags,
a fresh 0700 cache root, cold then warm): cold 4 digests (299.0 MB) and 1
assessment spawn, warm 4 digests and none, against 5 cold digests (390.4 MB) for
main `b522a4a1f`. The same cause ("source-bound frame needs independently
replayed proof", for the `StpPreIndex`/`LdpPostIndex` frame of an inlined leaf)
also fails trust-cg-codegen `--lib`
`compiler::tests::test_compile_module_to_jit_rejects_unproved_calling_frame`, on
main `b522a4a1f` as on this branch (3 of 3 runs each, in that review). The
Darwin bridge gate does not start here at all
(`DARWIN_BRIDGE_TRUST_TOOLCHAINS_DIVERGENT`: the rustup `trust` link names a
different sysroot than the package), so the fixture was run directly with the
package's `trustc` and `targo`.

## Byte identity

- **Bridge corpus** ([`commands/bridge_corpus.py`](commands/bridge_corpus.py)): the
  102 Rust benchmark programs (`beat-llvm`, `shape-coverage`, `decline-shapes`)
  with `-C save-temps`, proofs off, at `-O3` and `-O1`, base against final: all
  413 objects and binaries identical at each level, and the same two programs
  (`s27_dyn_box_drop`, `s31_vec_sort_dedup`) fail on both
  (`logs/bridge-corpus-O3.log`,
  `logs/bridge-corpus-O1.log`).
- **CLI corpus** ([`commands/cli_corpus.py`](commands/cli_corpus.py)): every
  committed `.tir` fixture, the scale_gate, pointer and stack shapes at small
  sizes for four targets at `-O1` and `-O3`, and the dumped `loops` modules at
  `-O1` to `-O3`: 959 objects identical, 104 compiles refused by both with the same
  message, none differing (`logs/cli-corpus.log`).
- **Shapes and ladder**: every module and crate in the tables above.

## Reproducing

```sh
export TRUST_PKG=<trust 9192 package> L14_CHECKOUT=<checkout> L14_WORK=<new private directory>
R=$L14_CHECKOUT/reports/perf/2026-09-29-darwin-cold-start-and-loops-l14p5p6/commands
# Build each side with $R/build.sh and copy the backend and CLI out.
python3 $R/startpath.py out.json 5 <before.dylib> <after.dylib> <programs...>
python3 $R/bridge_corpus.py <base.dylib> <final.dylib> 3 $L14_WORK/bcorpus $L14_CHECKOUT
python3 $R/cli_corpus.py <base-cli> <final-cli> $L14_WORK/corpus
python3 $R/shape_cli.py 3 <base-cli> <final-cli> shapes.json <module[:opt]>...
python3 $R/bridge_ladder.py <base.dylib> <final.dylib> ladder.json --n 3
```

The fixed-cost numbers use the L14-P5 report's
[`measure.py`](../2026-09-28-darwin-fixed-cost/measure.py) with its command line.
