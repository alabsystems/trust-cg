# Fourth wasm32 evidence row — `7decfad03`, 2026-10-08

The ledger row `7decfad03ddb-20261008T010923Z.json` (`row_family: "wasm32"`,
`evidence: true`) in `ratchet/ledger.jsonl`, rendered in
`benchmarks/LEDGER.md`. It is evidence for the stamped revision, bridge and
host only. It is not a measurement of any later checkout.

It is the after-row for wasm32 round 16 and for the trust-ir pin moves from
`5dbbf177` to `c44f6e94`. Round 16 added the fill-call, byte-copy and
copy-respelling rewrites (`fill_call`, `byte_copy`, `retype_copy`), the
memory cleanup before the inliner, the scalar-replacement reload rule and the
O1+ 128-bit division estimate (stage A). It also emits debug names without
the crate-private mark, shares constant allocations by content and folds
identical bodies into checked forwarders (stage B). Its before-rows are the
third wasm32 evidence row, `37be7a759d9d-20261007T080011Z.json`
([run record](../2026-10-07-wasm32-evidence-37be7a759/README.md)), the
second, `1fd8eabaa458-20261006T191536Z.json`
([run record](../2026-10-06-wasm32-evidence-1fd8eabaa/README.md)), and the
first, `1deda6c4a117-20261006T062603Z.json`
([run record](../2026-10-06-wasm32-evidence-1deda6c4a/README.md)).

All four rows have the same toolchain key: target, opt level, rustc,
`wasm-ld`, sysroot digest, grid digest, contract version and
`measurement_sha256`. The harness files `run.py`, `wasmtool.mjs` and
`contract/`, and `scripts/wasm_perf_ratchet.py`,
`scripts/check_perf_ratchet.py` and `ratchet/perf_baseline.json`, did not
change between `37be7a759` and this revision. Only the harness README and the
new diagnostic `sections.py` changed, and neither is in
`measurement_sha256`. The four rows also have the same host and the same
node/V8. The ratchet therefore compared the deterministic metrics at its 0%
floor and the timing metrics at its 10% floor against rows 1, 2 and 3. No
metric regressed (see below). The comparison covers all 144 programs, because
all four rows measured the same program set.

## What was measured

- **Revision:** `7decfad03ddbc0bf0a5ea9d1380a0b9ef31c93a7` (main = origin/main
  at measurement time). It was measured in a fresh worktree on branch
  `agents/wasm32-evidence-4`. `git status --porcelain --untracked-files=all`
  was empty (`git_dirty: false`, `untracked_count: 0`). `git_diff_sha256` is
  the digest of the empty diff.
- **Bridge:** `librustc_codegen_trust_cg.dylib`, SHA-256
  `db32ab3bd25f07bbe1ce08b5c2f5a2004154394e1dac5b8fa6daaefb7cd54b28`, mtime
  2026-10-08T01:03:49Z. It was built from that tree into a fresh target
  directory (no `target/` existed before), 00:56:43Z to 01:03:49Z (7m06s).
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
  rows 1 to 3). The load threshold was 7.0 (ncpu/2) and was not overridden.
  The 1-minute load was 1.08 before the run and 1.16 after it (QUIET).
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
cd $SCRATCH/wt/ev4/crates/rustc-codegen-trust-cg
CARGO_INCREMENTAL=0 CARGO_PROFILE_RELEASE_DEBUG=0 \
  RUSTC="$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc" \
  targo --unverified build --release --locked
```

The harness was run by a driver script that waits and retries on a LOADED
refusal. It is row 3's driver with the worktree and output directory changed
from `ev3` to `ev4`. The run was QUIET on the first attempt, so it did not
retry.

```sh
python3 $SCRATCH/wt/ev4/benchmarks/wasm-vs-llvm/run.py \
  --rustc "$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc" \
  --bridge $SCRATCH/wt/ev4/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib \
  --sysroot $SCRATCH/sysroot_script \
  --wasm-ld $SCRATCH/lld-build/bin/wasm-ld \
  --node /opt/homebrew/bin/node \
  --wasm-opt $SCRATCH/tools/binaryen-version_133/bin/wasm-opt \
  --jobs 4 \
  --out-dir $SCRATCH/ev4/results \
  --work-dir $SCRATCH/ev4/work
```

The ratchet was then run from the worktree root. `<results.json>` stands for
`$SCRATCH/ev4/results/7decfad03ddb-20261008T010923Z.json`.

```sh
python3 scripts/check_perf_ratchet.py <results.json>                           # dry run: OK, evidence=True
python3 scripts/check_perf_ratchet.py --require-current <results.json>         # OK
python3 scripts/check_perf_ratchet.py --require-current --append <results.json>
python3 scripts/check_perf_ratchet.py --check-render                           # matches the renderer
python3 scripts/check_perf_ratchet.py --check-ledger                           # 36 rows, 0 invalid
```

The run used neither `--allow-loaded` nor `--load-threshold`. It took 5m18s
(01:04:05Z to 01:09:23Z). No other build or heavy job ran while it was timing.

## Raw results

The raw results are not committed. This follows the `benchmarks/README.md`
convention (`benchmarks/**/results/` is gitignored) and the records of rows 1
to 3. The files are kept outside the repository in
`~/trust-cg-evidence/wasm32/2026-10-08-7decfad03/`, together with the driver
script, and are identified here by name and SHA-256. The ledger row keeps the
per-program pairs that later rows are compared on.

| File | SHA-256 |
|---|---|
| `7decfad03ddb-20261008T010923Z.json` | `9f93637d5967d2439e1867a660abc178d92e82e9f46f95a2bfb119b6a797fe69` |
| `7decfad03ddb-20261008T010923Z.md` | `a800c9b0efa3af36512d5ac045a881c78926b3fc8da5155351a3f280196d927d` |
| `run_evidence.sh` (driver) | `ea05f11e94c6e6721a13e97db876ce9259342bef78e25dbd7d59d48042b266ac` |

## Result (trust-cg / B1)

- **Coverage:** 144/144 MATCH, 0 MISMATCH and 0 INCOMPLETE. All 144 programs
  have a workload. There were 2 signed-zero differences, both on exports the
  manifest lists.
- **Size:** file bytes 1.058x, code bytes 1.374x and static instructions
  1.401x (geomeans). Declared locals were 1.594x and static memory operations
  1.351x (corpus totals). trust-cg's file was smaller than B1's on 54
  programs and more than 1.5x B1's on 26.
- **Dynamic:** instructions 1.522x (geomean). Memory operations were 1.453x,
  calls 1.110x and stack high-water 0.970x (totals). The stack was above B1's
  on 35 programs.
- **Time (min of 5):**

  | Mode | Geomean | Worst program | Programs above 1.5x (row 3) | Programs faster than B1 (row 3) |
  |---|---|---|---|---|
  | default | 1.115x | `kw_lookup`, 4.01x | 17 (23) | 48 (33) |
  | TurboFan | 1.124x | `min_zip2`, 4.08x | 15 (23) | 36 (37) |
  | Liftoff | 1.221x | `kw_lookup`, 3.61x | 31 (37) | 28 (30) |

  The per-mode counts are computed from the two rows' raw results files with
  `wasm_contract.program_pairs`.
- **B2 context:** trust-cg / B2 was 1.256x on file bytes and 1.151x on
  TurboFan time. B2 / B1 file bytes were 0.843x.
- **Compile time:** 1.906x geomean (single sample; context only).
- **GATE-WASM-SB** (PROPOSED, not owner-approved): WSB4 (stack high-water
  total at most 1.00x) and WSB5 (coverage) pass. WSB1 (file bytes geomean
  below 1.00x: 1.058x) fails. WSB2 and WSB3 (time geomean below 1.00x and
  every program at most 1.50x) fail on both conditions: TurboFan 1.124x with
  15 programs above 1.5x, and default 1.115x with 17.

## Delta from rows 3, 2 and 1

All 144 programs are shared with all three rows. Ratios are trust-cg / B1 in
each row. Each aggregate is recomputed over the shared programs by the
ratchet's own `shared_value` (`scripts/wasm_perf_ratchet.py`), from the
`program_metrics` of the four rows in `ratchet/ledger.jsonl`. Row 3's
`program_metrics` equal `program_metrics()` of its raw results file
(`37be7a759d9d-20261007T080011Z.json`, SHA-256 `19f2981f…`), which was
checked.

| Metric | Row 1 (`1deda6c4a`) | Row 2 (`1fd8eabaa`) | Row 3 (`37be7a759`) | This row (`7decfad03`) | Change vs row 3 | Change vs row 2 | Change vs row 1 |
|---|---|---|---|---|---|---|---|
| file bytes (geomean) | 1.187 | 1.167 | 1.128 | 1.058 | −6.19% | −9.32% | −10.86% |
| code bytes (geomean) | 1.542 | 1.505 | 1.426 | 1.374 | −3.60% | −8.71% | −10.86% |
| static instructions (geomean) | 1.613 | 1.554 | 1.463 | 1.401 | −4.21% | −9.85% | −13.11% |
| declared locals (total) | 1.662 | 1.632 | 1.610 | 1.594 | −0.97% | −2.32% | −4.11% |
| static memory ops (total) | 1.461 | 1.446 | 1.389 | 1.351 | −2.75% | −6.59% | −7.55% |
| dynamic instructions (geomean) | 2.008 | 1.701 | 1.642 | 1.522 | −7.32% | −10.53% | −24.21% |
| dynamic memory ops (total) | 1.569 | 1.511 | 1.498 | 1.453 | −2.99% | −3.80% | −7.39% |
| dynamic calls (total) | 1.323 | 1.321 | 1.297 | 1.110 | −14.38% | −15.95% | −16.04% |
| stack high-water (total) | 1.003 | 0.983 | 0.982 | 0.970 | −1.21% | −1.31% | −3.29% |
| time, default (geomean) | 1.267 | 1.198 | 1.180 | 1.115 | −5.48% | −6.91% | −11.97% |
| time, TurboFan (geomean) | 1.263 | 1.207 | 1.184 | 1.124 | −5.11% | −6.88% | −11.01% |
| time, Liftoff (geomean) | 1.429 | 1.307 | 1.271 | 1.221 | −3.87% | −6.54% | −14.51% |

The timing deltas compare single runs on one host. They are inside the
ratchet's floor, which permits a 10% regression, and they are not a
noise-bounded measurement of round 16 alone. Decision OD-152 accepted
`f24_calls` becoming slower under Liftoff with the 128-bit division estimate.
In this row it reads 1.305x B1 under Liftoff (0.994x in row 3), 1.367x under
TurboFan (1.415x) and 1.034x under default tiering (1.098x). Per-program
timing is single-run data and the ratchet does not judge it; it judges the
aggregate timing geomeans, which all fell.

The ratchet checks only these aggregates. Per program, the list below compares
this row's `program_metrics` with row 3's (`37be7a759d9d` in
`ratchet/ledger.jsonl`). The B1 reading is identical in both rows for every
program and deterministic metric, so a change in the trust-cg reading is the
same as a change in the ratio.

- **file bytes** grew on 2 programs, `w_div_rem` 2822 to 3003 (+6.41%) and
  `k13_wide` 11947 to 12015 (+0.57%). They fell on 97 and were unchanged on
  45. The largest relative falls: `c33_repr__packed_ptr` 571 to 341,
  `c28_iters__it_zip` 1193 to 725, `c33_repr__packed` 1057 to 718,
  `c33_repr` 2654 to 2021, `slice_swap_f64` 447 to 352, `k04_codec` 12290 to
  9729, `f08_log` 15371 to 12261 and `f19_edges` 19634 to 15847.
- **code bytes and static instructions** grew on 11 programs each (fell on
  31, unchanged on 102): the seven that divide 128-bit integers (`f03b_i128`,
  `f08_log`, `f14b_t128`, `f19_edges`, `f24_calls`, `k13_wide`, `w_div_rem`,
  the helper's wide path; code bytes +2.0% to +12.4%), `f17_conv` (+7.09%),
  and `glob_match`, `k21_fsm` and `utf8_dfa` (+0.14% to +0.41%). The largest
  relative falls in code bytes: `slice_swap_f64` 121 to 26,
  `c33_repr__packed_ptr` 305 to 103, `c33_repr__packed` 724 to 427,
  `c28_iters__it_zip` 498 to 341, `c33_repr` 1840 to 1349 and `min_zip2` 369
  to 271. The largest absolute falls: `f22_sweep` 13111 to 10638 (2473 bytes)
  and `k06_vm` 14816 to 13789 (1027 bytes).
- **declared locals** grew on 18 programs (fell on 20). The largest growths
  are the seven 128-bit dividers (+5 each, `w_div_rem` 33 to 38),
  `f17_conv` 118 to 122 and `c33_repr` 34 to 37; the other nine grew by one
  or two.
- **static memory operations** grew on 3 programs, `k21_fsm` 154 to 156,
  `utf8_dfa` 85 to 87 and `min_refslice_iter` 2 to 3, and fell on 18 (among
  them `slice_swap_f64` 9 to 0, `c28_iters__it_zip` 36 to 9 and `c33_repr`
  194 to 117).
- **dynamic instructions** grew on 2 programs, `f19_edges` 2226569 to
  2227253 (+0.03%) and `f22_sweep` 8036744 to 8036828 (+84), and fell on
  40. The largest relative falls: `slice_swap_f64` 16400 to 2000,
  `c33_repr__packed_ptr` 112480 to 28120, `f03b_i128` 5396437 to 2089255,
  `min_refslice_iter` 2090 to 836, `c33_repr` 923680 to 416000, `bsearch_by`
  2202840 to 1025980 and `partition_pt` 2888912 to 1388596. The largest
  absolute falls: `f14b_t128` 25710965 to 19722052 (5988913), `f03b_i128`
  (3307182) and `k02_heap` 48284222 to 45692309 (2591913).
- **dynamic memory operations** grew on 2 programs, `k21_fsm` 464283 to
  466103 (+0.39%) and `utf8_dfa` 88178 to 89998 (+2.06%), and fell on 23.
- **dynamic calls** grew on 1 program, `f22_sweep` 0 to 42 (the forwarders
  of its folded exports), and fell on 15. The largest relative falls:
  `u16_checksum` 1444 to 0, `c28_iters__it_zip` 4400 to 800, `f17_conv` 42670
  to 10742, `kw_lookup` 253 to 125 and `k04_codec` 124962 to 62806. The
  largest absolute falls: `fmt_ints` 344584 to 257640 (86944), `fmt_str`
  261740 to 187084 (74656) and `k04_codec` (62156).
- **stack high-water** grew on no program and fell on 8, among them
  `slice_swap_f64` 32 to 0 bytes and `c28_iters__it_zip` 176 to 112.

Per-program timing is not listed beyond the table above: it is single-run
data, and the ratchet judges timing only as a geomean with a 10% floor.

## What this does not show

The lane runs with `no-proof-certs` and both frontends run with
`-Ztrust-verify=off`, so this row makes no proof claim. Agreement on the grid
and the workload is a differential test, not a proof, and the corpus was
selected from programs that already agreed with LLVM. The timing figures apply
to this host and node/V8 only. The deterministic figures apply to this exact
toolchain key. The deltas from row 3 measure the whole range from `37be7a759`
to `7decfad03` (204 commits, 132 of them non-merge, including merges from
origin/main and the trust-ir pin moves from `5dbbf177` to `c44f6e94`). They
are not attributed to any one round-16 change, and this run does not check
the statement that the pin moves change nothing the wasm lane reaches.
