# 2026-09-28 — JIT tier-up: exact across tiers; what a first tier costs

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

Host: M5 Max, macOS 26 (Darwin 25.6.0), aarch64-apple-darwin, shared with
other sessions' builds (load average 16–38 during these runs). trust-cg built
with the repository's pinned stock 1.97.1 (`rust-toolchain.toml`) at
`b48c0be5d` (`lane/jit-tier-up` = main `ec6748a56` + the tier-up commit; the
tier-up code does not touch the compile path). Instruction counts are the
evidence; cycles and wall times were taken on a loaded box and are
indicative only. Design and plan: docs/jit-tier-up.md.

## Answer

1. **Tier-up is exact.** 22 workload cells (the ay watched-literal BCP kernel
   on two DIMACS formulas, nine `scripts/fuzz` kernels; a short and a long run
   each) × 4 arms × 3 interleaved repetitions: **every cell has one checksum**
   across base (O0), top (O2), tier-up (O0 then O2 after it) and concurrent
   tier-up. The service test target additionally shows each tier's payload is
   byte-identical to a plain compile-service compile of the same request.
2. **O0 is not a cheap first tier in this backend.** Over the compile corpus's
   JIT lane (139 compiled entries; `run.py tier-cost`, Consistency PASS),
   compiling at O0 costs **0.966** of the production levels on TY's semantic
   images, **0.902** on the ay kernels, **0.608** on the small fixture kernels,
   and on TY's production batches between **0.89 and 1.50** of their O1
   compile — O0 is the MORE expensive level for four of them. O1 costs 0.967 /
   0.941 / 0.850 of production.
3. **Why:** at O0 the optimizer's share of a TY semantic image compile falls
   from 25% to 2.7%, but register allocation grows to 45% and the frame-net
   verifier to 15% on the larger unoptimized code (sampled profile of
   `ty-semantic/ACP_NB_TLC/0`). The optimization level is a weak compile-cost
   lever; allocation and verification of large unoptimized functions are the
   strong one (plan item P2).
4. **So what tier-up buys here is overlap.** Long runs reach top-tier
   throughput without paying the top compile before the first call (e.g. `pc`
   100,000 calls: base 764 ms, top 39 ms, tier-up 42 ms, concurrent 37 ms;
   BCP 20,000 calls: 155 / 117 / 115 / 113 ms); every run pays one extra
   compile of CPU (whole-process instructions +0.04–0.31 G against the top
   arm: the O0 compile plus the calls made before the swap). With O0 costing
   ~0.9 of O2, the first-result latency gain is within this box's noise.

## Exactness and cost on non-TY programs (`tier_up_bench`)

`tier_up_bench` compiles through `TierUpSession` + `ServiceTierBackend` in
every arm (a one-tier plan is an ordinary compile), calls through a
`TierEntryTable`, and folds every result into one FNV-1a checksum. The `tier`
arms poll the session (non-blocking) before each call and install the top
tier into the table when it arrives. Medians of 3; `first`/`run` are wall ms
from session start, `proc` the whole process under `/usr/bin/time -l`
(instructions, all threads). Full table: [`bench-matrix.md`](bench-matrix.md);
raw: `bench-matrix.json.gz`.

| workload | calls | base run ms / proc Gi | top | tier | tierc | top took over at call |
|---|--:|--:|--:|--:|--:|--|
| bcp rand3sat-225 | 20,000 | 154.7 / 3.284 | 116.8 / 2.204 | 115.3 / 2.505 | 113.2 / 2.395 | 2234–2332 (tierc 56–521) |
| bcp blocks-3-t4 | 20,000 | 131.8 / 2.701 | 96.5 / 1.875 | 106.2 / 2.189 | 111.1 / 2.085 | 2943–3210 (tierc 0–551) |
| fib | 200,000 | 278.7 / 3.936 | 93.2 / 1.220 | 95.9 / 1.279 | 101.5 / 1.261 | 2196–2464 |
| pc | 100,000 | 764.0 / 12.106 | 39.3 / 0.629 | 41.9 / 0.715 | 36.6 / 0.684 | 371–491 |
| abs | 100,000 | 401.5 / 7.221 | 33.6 / 0.584 | 31.9 / 0.688 | 28.9 / 0.647 | 782–907 |
| crcx | 100,000 | 364.6 / 7.304 | 126.1 / 2.435 | 117.7 / 2.521 | 118.5 / 2.537 | 996–1150 |
| mm_ikj (48²) | 2,000 | 192.4 / 3.698 | 37.6 / 0.650 | 39.0 / 0.762 | 42.3 / 0.715 | 43–47 |
| bcp rand3sat-225 | 500 | 29.4 / 0.401 | 23.8 / 0.389 | 28.6 / 0.639 | 24.8 / 0.598 | never / 0–415 |
| fib | 2,000 | 17.9 / 0.146 | 11.4 / 0.113 | 13.5 / 0.185 | 16.8 / 0.166 | never / 0–413 |

Tier-0 compile brackets (instructions, median): BCP O0 266–272 M vs O2
295–299 M; the fuzz kernels O0 57–71 M vs O2 63–86 M (these include the
process's one-time compiler initialisation, which the corpus's steady-state
repetitions exclude). A `tierc` tier-0 bracket also counts the concurrent
worker's instructions (the counters are per process).

## What the first tier costs (`benchmarks/compile-corpus`, `run.py tier-cost`)

Same binary, JIT lane (`jit-raw`), 3 repetitions per entry in one process,
`RAYON_NUM_THREADS=1`, steady state = cheapest of repetitions 2–3; the
rustc-bridge entries have no JIT lane and are not in these runs. Tables:
[`tier-cost-O0-vs-prod.md`](tier-cost-O0-vs-prod.md),
[`tier-cost-O1-vs-prod.md`](tier-cost-O1-vs-prod.md); raw:
`corpus-{O0,O1,prod}.json.gz`.

| origin | entries | O0 / production | O1 / production | production level |
|---|--:|--:|--:|---|
| ty-semantic | 87 | 117,846 M / 121,965 M = **0.966** | 0.967 | O2 |
| ty-prod | 22 | 3,976 M / 3,850 M = **1.033** | 1.032 | O0 (5 downgraded batches) or O1 |
| ay-jit-matrix | 5 | 384 M / 426 M = **0.902** | 0.941 | O2 |
| trust-cg-fixture | 25 | 475 M / 781 M = **0.608** | 0.850 | O2 |

TY's production batches, by entry: the five batches TY downgrades to O0
(`Barriers/0`–`/4`) would cost 1.07–1.09x at O1, so the downgrade still saves
~8% of their compile; but `Barriers/7` costs 659 M at O0 against 440 M at O1
(1.50x), `Barriers/6` 1.16x, `clean/1` 1.10x, `Barriers/9` 1.10x.

Phase brackets, all TY semantic entries (G instructions, O0 / O1 / O2):
adapter 9.26 / 9.25 / 9.25, prepare 85.1 / 90.2 / 95.6, link 22.8 / 17.9 /
16.5 — O0 saves 10.5 G of preparation and spends 6.3 G more linking its
larger code.

Sampled profile of `ty-semantic/ACP_NB_TLC/0` (`run.py profile --opt-level`,
40 s, self samples by innermost phase; `profile-ACP_NB_TLC-O0.txt`,
`-O2.txt`):

| phase | O0 | O2 |
|---|--:|--:|
| regalloc | 44.6% | 37.3% |
| opt | 2.7% | 25.0% |
| verify: frame net | 14.7% | 5.5% |
| verify: other + a64-validate + reaching-def | 13.2% | 10.8% |
| adapter + isel + frame + encode | 15.6% | 12.5% |
| other | 8.9% | 8.8% |

## What this means for consumers

* **TY.** The measured cost that motivated the O1→O0 downgrade is now ~8%
  of the downgraded batches' compile, and O1's ~10% execution win
  (MCLamportMutex, 2026-08-10) is the one tier-up recovers: a `[O0, O1]` plan
  keeps O0's latency and runs O1 once it arrives (`start_concurrent` starts
  it at t=0 on another core). On the semantic lane (O2 images, 88–96% of
  preparation is compile) a lower first tier saves ~3.4% of that compile —
  small; that lane's compile lever is the compile-speed work and warm caches,
  not tiering.
* **ay kernels.** A `[O0, O2]` ladder gets O0's latency (0.90 of O2) and O2's
  code on long solver runs, instead of O1 for both.
* **Everyone.** The general lever for JIT latency is making a low tier
  genuinely cheap — allocation and verification of unoptimized code (plan P2)
  — and `run.py tier-cost` is the gate for it.

## Reproduce

```sh
cargo build --release -p trust-cg-jit-matrix --bin compile_corpus --bin tier_up_bench
cd benchmarks/compile-corpus
python3 run.py measure --bin ../../target/release/compile_corpus --lane jit-raw --opt-level O0 --out O0.json
python3 run.py measure --bin ../../target/release/compile_corpus --lane jit-raw --opt-level O1 --out O1.json
python3 run.py measure --bin ../../target/release/compile_corpus --lane jit-raw --out prod.json
python3 run.py tier-cost O0.json prod.json --table tier-cost-O0-vs-prod.md
python3 run.py profile --bin ../../target/release/compile_corpus --lane jit-raw --opt-level O0 \
    --filter ty-semantic/ACP_NB_TLC/0 --reps 3 --seconds 40 --out prof.txt
cd ../../reports/perf/2026-09-28-jit-tier-up
python3 measure.py --bin ../../../target/release/tier_up_bench --out results.json --reps 3
python3 summarize.py results.json --table bench-matrix.md
cargo test -p trust-cg-codegen --lib tier_up::
cargo test -p trust-cg-codegen --test tier_up
```

## Limits

* One host (AArch64 Darwin). The mechanism is target-neutral; x86-64 and
  Linux runs of the `tier_up` target are plan item P7.
* Wall and cycle columns were taken under load average 16–38 from other
  sessions and are indicative only; instruction counts and checksums are the
  evidence.
* No TY row was run here: TY's pin does not include this commit, and the TY
  adoption (plan item P1) is TY's change.
