# Third wasm32 evidence row — `37be7a759`, 2026-10-07

The ledger row `37be7a759d9d-20261007T080011Z.json` (`row_family: "wasm32"`,
`evidence: true`) in `ratchet/ledger.jsonl`, rendered in
`benchmarks/LEDGER.md`. It is evidence for the stamped revision, bridge and
host only. It is not a measurement of any later checkout.

It is the after-row for wasm32 round 15 (the bridge spells in-bounds place
addresses as GEPs on wasm32 at O1 and above, the irmid rewrite of small C
memory calls, and the unrolling cost model) and for the trust-ir pin move to
`5dbbf177`, which changed no trust-ir source. Its before-rows are the second
wasm32 evidence row, `1fd8eabaa458-20261006T191536Z.json`
([run record](../2026-10-06-wasm32-evidence-1fd8eabaa/README.md)), and the
first, `1deda6c4a117-20261006T062603Z.json`
([run record](../2026-10-06-wasm32-evidence-1deda6c4a/README.md)). All three
rows have the same toolchain key: target, opt level, rustc, `wasm-ld`,
sysroot digest, grid digest, contract version and `measurement_sha256`. The
harness files `run.py`, `wasmtool.mjs` and `contract/`, and
`scripts/wasm_perf_ratchet.py`, `scripts/check_perf_ratchet.py` and
`ratchet/perf_baseline.json`, did not change between `1fd8eabaa` and this
revision. The three rows also have the same host and the same node/V8, so the
ratchet compared the deterministic metrics at its 0% floor and the timing
metrics at its 10% floor against rows 1 and 2. No metric regressed (see
below). The comparison covers all 144 programs, because all three rows
measured the same program set.

## What was measured

- **Revision:** `37be7a759d9d46c6fab4d10af411bd10f1e9ef4a` (main = origin/main
  at measurement time). It was measured in a fresh worktree on branch
  `agents/wasm32-evidence-3`. `git status --porcelain --untracked-files=all`
  was empty (`git_dirty: false`, `untracked_count: 0`). `git_diff_sha256` is
  the digest of the empty diff.
- **Bridge:** `librustc_codegen_trust_cg.dylib`, SHA-256
  `5367917a267cdd3ed58637ee7c521ff52f7975d6e1662efb29140a162dfad8b2`, mtime
  2026-10-07T07:54:24Z. It was built from that tree into a fresh target
  directory (no `target/` existed before), 07:47:27Z to 07:54:24Z (6m56s).
  `dylib_stale_source: null`.
- **rustc:** `rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc 0.1.0)`, commit
  `321aaeda75478038420d97830f14724c33c8dc39` (atpkg store `trust/9192`;
  binary SHA-256 `6c513314d5c99778345a2c2a60feef521b2ece2952149095bc9beded93b1206e`).
- **Lanes:** B1 `llvm_o2`, `tcg_o2` with exactly `-Ztrust-ir-cg-args=no-proof-certs`,
  and B2 `llvm_o2_wasmopt` (`wasm-opt -O2 -g`). All three use
  `-Ztrust-verify=off`.
- **wasm-ld:** `LLD 22.1.2 (alabsystems/trust 59e55fe8e40a)`, SHA-256
  `bacef259c3e44b3cf12e0756a79452e35db484772e58ed6dc6a8adc39a66bae0`.
- **Sysroot** (`scripts/build_wasm32_sysroot.sh` output), target-tree digest:
  `eb3d1911831b88b263f931f7afd1bcaaff03f509fce9495caf08849e2079677b`.
- **wasm-opt (B2, context only):** binaryen `version_133`, SHA-256
  `81041e09f332df94db1c2009a64d8f3b85f0431a2c920ccd014d3ceebb343402`.
- **Engine:** `node v26.3.0 / V8 14.6.202.34-node.20`
  (`/opt/homebrew/Cellar/node/26.3.0/bin/node`), run in three modes: default,
  `--no-liftoff` and `--liftoff-only`.
- **Host:** Apple M4 Pro, arm64, 14 CPUs, Darwin 25.6.0 (the same host as
  rows 1 and 2). The load threshold was 7.0 (ncpu/2) and was not overridden.
  The 1-minute load was 1.32 before the run and 1.16 after it (QUIET).
  `detect_runaways()` found no runaway process, both before the run and as
  stamped. Before timing, no process with ppid 1 was above 50% CPU, so no
  process was killed.
- **Contract and corpus:** contract version 2, with `measurement_sha256`
  `6c8c7619a84bdffc7d7fd2c03d8516a4500b1d980f6dd2350ed13324471a6809`. The
  corpus manifest is `e180e5f6d251f90cfb8eda26adadc783215a5c5ce65eb77d10c27687d600b656`
  (all 144 programs) and the grid is
  `07d156ffc1ea7574dabc5bcae1dbd67783275bf809a15efc5ddeaa69a6ada505`.
- **Timing:** `n_run` 5 and `target_ms` 20. `--jobs 4` parallelized only the
  compile and deterministic phase; timing is always sequential.
- `tcg_env` was `{}`. No `TRUST_*` or `TCG_*` variable was set.

## Commands

The bridge was built from the worktree's bridge directory:

```sh
cd $SCRATCH/wt/ev3/crates/rustc-codegen-trust-cg
CARGO_INCREMENTAL=0 CARGO_PROFILE_RELEASE_DEBUG=0 \
  RUSTC="$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc" \
  targo --unverified build --release --locked
```

The harness was run by a driver script that waits and retries on a LOADED
refusal. The run was QUIET on the first attempt, so it did not retry.

```sh
python3 $SCRATCH/wt/ev3/benchmarks/wasm-vs-llvm/run.py \
  --rustc "$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc" \
  --bridge $SCRATCH/wt/ev3/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib \
  --sysroot $SCRATCH/sysroot_script \
  --wasm-ld $SCRATCH/lld-build/bin/wasm-ld \
  --node /opt/homebrew/bin/node \
  --wasm-opt $SCRATCH/tools/binaryen-version_133/bin/wasm-opt \
  --jobs 4 \
  --out-dir $SCRATCH/ev3/results \
  --work-dir $SCRATCH/ev3/work
```

The ratchet was then run from the worktree root. `<results.json>` stands for
`$SCRATCH/ev3/results/37be7a759d9d-20261007T080011Z.json`.

```sh
python3 scripts/check_perf_ratchet.py <results.json>                           # dry run: OK, evidence=True
python3 scripts/check_perf_ratchet.py --require-current <results.json>         # OK
python3 scripts/check_perf_ratchet.py --require-current --append <results.json>
python3 scripts/check_perf_ratchet.py --check-render                           # matches the renderer
python3 scripts/check_perf_ratchet.py --check-ledger                           # 35 rows, 0 invalid
```

The run used neither `--allow-loaded` nor `--load-threshold`. It took 5m27s
(07:54:44Z to 08:00:11Z). No other build or heavy job ran while it was timing.

## Raw results

The raw results are not committed. This follows the `benchmarks/README.md`
convention (`benchmarks/**/results/` is gitignored) and the records of rows 1
and 2. The files are kept outside the repository in
`~/trust-cg-evidence/wasm32/2026-10-07-37be7a759/`, together with the driver
script, and are identified here by name and SHA-256. The ledger row keeps the
per-program pairs that later rows are compared on.

| File | SHA-256 |
|---|---|
| `37be7a759d9d-20261007T080011Z.json` | `19f2981f595acc1c4a88365725b43e9d6c5aec1e89453b78c7b12844de8e52e6` |
| `37be7a759d9d-20261007T080011Z.md` | `5b346c575b2ded9e9dedb5ea7c0ef9256d53368f79ed997d4816594c4e9de45f` |
| `run_evidence.sh` (driver) | `51f7d2849e5d6d0c64d33c3302ed5807be595c67460a0ddbe2062f66136156f4` |

## Result (trust-cg / B1)

- **Coverage:** 144/144 MATCH, 0 MISMATCH and 0 INCOMPLETE. All 144 programs
  have a workload. There were 2 signed-zero differences, both on exports the
  manifest lists.
- **Size:** file bytes 1.128x, code bytes 1.426x and static instructions
  1.463x (geomeans). Declared locals were 1.610x and static memory operations
  1.389x (corpus totals). trust-cg's file was smaller than B1's on 49 programs.
- **Dynamic:** instructions 1.642x (geomean). Memory operations were 1.498x,
  calls 1.297x and stack high-water 0.982x (totals). The stack was above B1's
  on 40 programs.
- **Time (min of 5):**

  | Mode | Geomean | Worst program |
  |---|---|---|
  | default | 1.180x | `kw_lookup`, 4.26x |
  | TurboFan | 1.184x | `min_zip2`, 5.85x |
  | Liftoff | 1.271x | `kw_lookup`, 4.45x |

  trust-cg was faster than B1 on 37 programs under TurboFan.
- **B2 context:** trust-cg / B2 was 1.339x on file bytes and 1.214x on
  TurboFan time. B2 / B1 file bytes were 0.843x.
- **Compile time:** 1.912x geomean (single sample; context only).
- **GATE-WASM-SB** (PROPOSED, not owner-approved): WSB4 (stack high-water
  total at most 1.00x) and WSB5 (coverage) pass. WSB1–WSB3 fail.

## Delta from rows 2 and 1

All 144 programs are shared with both rows. Ratios are trust-cg / B1 in each
row. Each aggregate is recomputed over the shared programs by the ratchet's
own `shared_value` (`scripts/wasm_perf_ratchet.py`), from the
`program_metrics` of the three rows in `ratchet/ledger.jsonl`.

| Metric | Row 1 (`1deda6c4a`) | Row 2 (`1fd8eabaa`) | This row (`37be7a759`) | Change vs row 2 | Change vs row 1 |
|---|---|---|---|---|---|
| file bytes (geomean) | 1.187 | 1.167 | 1.128 | −3.33% | −4.97% |
| code bytes (geomean) | 1.542 | 1.505 | 1.426 | −5.30% | −7.53% |
| static instructions (geomean) | 1.613 | 1.554 | 1.463 | −5.89% | −9.30% |
| declared locals (total) | 1.662 | 1.632 | 1.610 | −1.36% | −3.17% |
| static memory ops (total) | 1.461 | 1.446 | 1.389 | −3.95% | −4.93% |
| dynamic instructions (geomean) | 2.008 | 1.701 | 1.642 | −3.47% | −18.22% |
| dynamic memory ops (total) | 1.569 | 1.511 | 1.498 | −0.83% | −4.53% |
| dynamic calls (total) | 1.323 | 1.321 | 1.297 | −1.84% | −1.95% |
| stack high-water (total) | 1.003 | 0.983 | 0.982 | −0.09% | −2.10% |
| time, default (geomean) | 1.267 | 1.198 | 1.180 | −1.51% | −6.87% |
| time, TurboFan (geomean) | 1.263 | 1.207 | 1.184 | −1.87% | −6.22% |
| time, Liftoff (geomean) | 1.429 | 1.307 | 1.271 | −2.78% | −11.07% |

The timing deltas compare single runs on one host. They are inside the
ratchet's floor, which permits a 10% regression, and they are not a
noise-bounded measurement of round 15 alone. The TurboFan worst program,
`min_zip2`, read 5.85x here and 5.71x in row 2; per-program timing is
single-run data and the ratchet does not judge it.

The ratchet checks only these aggregates. Per program, the list below compares
this row's `program_metrics` with row 2's (`1fd8eabaa458` in
`ratchet/ledger.jsonl`), which equal `condense()` of each row's raw results.
The B1 reading is identical in both rows for every program and deterministic
metric, so a change in the trust-cg reading is the same as a change in the
ratio.

- **file bytes, code bytes and static instructions** grew on no program. They
  fell on 55 programs each and were unchanged on 89. The largest file-byte
  falls: `pswap_i64` 2538 to 638, `pswap_u32` 2553 to 653, `k19b_ptrswap_ok`
  4011 to 2101, `k15_byval` 7400 to 5462, `rf_small_aggr_abi` 438 to 326,
  `f28b_mem128` 4555 to 3584, `c33_repr__packed_ptr` 613 to 571 and
  `it_range` 2344 to 2221.
- **declared locals** grew on 1 program, `k10_matrix` 146 to 147 (fell on 15).
- **static memory operations** grew on no program (fell on 9):
  `rf_small_aggr_abi` 14 to 0, `pswap_i64` 108 to 14, `pswap_u32` 112 to 18,
  `k19b_ptrswap_ok` 168 to 82, `it_range` 43 to 29, `f28b_mem128` 186 to 138,
  `k15_byval` 464 to 372 and `k21_fsm` 162 to 154, among others.
- **dynamic instructions** grew on 1 program, `f28b_mem128` 2505888 to
  2527938 (+0.88%), and fell on 53. The largest falls: `pswap_i64` 521564 to
  154508, `pswap_u32` 518192 to 179056, `k19b_ptrswap_ok` 2030784 to 816240,
  `rf_small_aggr_abi` 11930 to 9151 and `c33_repr__packed_ptr` 133760 to
  112480.
- **dynamic memory operations, dynamic calls and stack high-water** grew on
  no program. They fell on 7, 4 and 1 programs. Dynamic calls fell on
  `pswap_u32` and `pswap_i64` (8664 to 2888 each), `k19b_ptrswap_ok` (34656
  to 11552) and `k15_byval` (28465 to 25577); the stack high-water fell on
  `rf_small_aggr_abi` (16 to 0 bytes).

Per-program timing is not listed: it is single-run data, and the ratchet
judges timing only as a geomean with a 10% floor.

## What this does not show

The lane runs with `no-proof-certs` and both frontends run with
`-Ztrust-verify=off`, so this row makes no proof claim. Agreement on the grid
and the workload is a differential test, not a proof, and the corpus was
selected from programs that already agreed with LLVM. The timing figures apply
to this host and node/V8 only. The deterministic figures apply to this exact
toolchain key. The deltas from row 2 measure the whole range from `1fd8eabaa`
to `37be7a759` (51 commits, 37 of them non-merge, including merges from
origin/main). They are not attributed to any one round-15 change.
