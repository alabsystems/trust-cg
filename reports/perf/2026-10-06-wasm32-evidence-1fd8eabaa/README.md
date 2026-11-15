# Second wasm32 evidence row — `1fd8eabaa`, 2026-10-06

The ledger row `1fd8eabaa458-20261006T191536Z.json` (`row_family: "wasm32"`,
`evidence: true`) in `ratchet/ledger.jsonl`, rendered in
`benchmarks/LEDGER.md`. It is evidence for the stamped revision, bridge and
host only. It is not a measurement of any later checkout.

It is the after-row for wasm32 round 14 (full unrolling, induction-variable
strength reduction, LICM tier b, field-access lowering and premised memarg
folds). Its before-row is the first wasm32 evidence row,
`1deda6c4a117-20261006T062603Z.json`
([run record](../2026-10-06-wasm32-evidence-1deda6c4a/README.md)). Both rows
have the same toolchain key: target, opt level, rustc, `wasm-ld`, sysroot
digest, grid digest, contract version and `measurement_sha256`. The harness
files `run.py`, `wasmtool.mjs` and `contract/` did not change between the two
revisions. They also have the same host and the same node/V8, so the ratchet
compared the deterministic metrics at its 0% floor and the timing metrics at
its 10% floor against row 1. No metric regressed (see below). The comparison
covers all 144 programs, because both rows measured the same program set.

## What was measured

- **Revision:** `1fd8eabaa458556fa6a637ceb227da264a1db760` (main = origin/main
  at measurement time). It was measured in a fresh worktree on branch
  `agents/wasm32-evidence-2`. `git status --porcelain --untracked-files=all`
  was empty (`git_dirty: false`, `untracked_count: 0`). `git_diff_sha256` is
  the digest of the empty diff.
- **Bridge:** `librustc_codegen_trust_cg.dylib`, SHA-256
  `add773dcbe8e9f3cdfc74b3e080575d1bf9b92f7b9a19e75fa3a08ae568667a3`, mtime
  2026-10-06T19:09:50Z. It was built from that tree into a fresh target
  directory (no `target/` existed before), 19:02:56Z to 19:09:50Z (6m54s).
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
  row 1). The load threshold was 7.0 (ncpu/2) and was not overridden. The
  1-minute load was 1.27 before the run and 1.27 after it (QUIET).
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
cd $SCRATCH/wt/ev2/crates/rustc-codegen-trust-cg
CARGO_INCREMENTAL=0 CARGO_PROFILE_RELEASE_DEBUG=0 \
  RUSTC="$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc" \
  targo --unverified build --release --locked
```

The harness was run by a driver script that waits and retries on a LOADED
refusal. The run was QUIET on the first attempt, so it did not retry.

```sh
python3 $SCRATCH/wt/ev2/benchmarks/wasm-vs-llvm/run.py \
  --rustc "$HOME/Library/Application Support/aterm/pkg/store/trust/9192/bin/trustc" \
  --bridge $SCRATCH/wt/ev2/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib \
  --sysroot $SCRATCH/sysroot_script \
  --wasm-ld $SCRATCH/lld-build/bin/wasm-ld \
  --node /opt/homebrew/bin/node \
  --wasm-opt $SCRATCH/tools/binaryen-version_133/bin/wasm-opt \
  --jobs 4 \
  --out-dir $SCRATCH/ev2/results \
  --work-dir $SCRATCH/ev2/work
```

The ratchet was then run from the worktree root. `<results.json>` stands for
`$SCRATCH/ev2/results/1fd8eabaa458-20261006T191536Z.json`.

```sh
python3 scripts/check_perf_ratchet.py <results.json>                           # dry run: OK, evidence=True
python3 scripts/check_perf_ratchet.py --require-current <results.json>         # OK
python3 scripts/check_perf_ratchet.py --require-current --append <results.json>
python3 scripts/check_perf_ratchet.py --check-render                           # matches the renderer
python3 scripts/check_perf_ratchet.py --check-ledger                           # 34 rows, 0 invalid
```

The run used neither `--allow-loaded` nor `--load-threshold`. It took 5m29s
(19:10:07Z to 19:15:36Z). No other build or heavy job ran while it was timing.

## Raw results

The raw results are not committed. This follows the `benchmarks/README.md`
convention (`benchmarks/**/results/` is gitignored) and row 1's record. The
files are kept outside the repository in
`~/trust-cg-evidence/wasm32/2026-10-06-1fd8eabaa/`, together with the driver
script, and are identified here by name and SHA-256. The ledger row keeps the
per-program pairs that later rows are compared on.

| File | SHA-256 |
|---|---|
| `1fd8eabaa458-20261006T191536Z.json` | `ee85f11be0a6925fd2981e0c5b0111badd49b73d1e214cad0a09d35953d42b08` |
| `1fd8eabaa458-20261006T191536Z.md` | `345b65b6fae5e97e786548a46abdfe682bfd06e18491a6e9af6d8267980d2a3e` |
| `run_evidence.sh` (driver) | `1f69484d4d68fa0cd7a6a33b0c51d7ce1e032b7dffc5efe2aab3475c73b647ac` |

## Result (trust-cg / B1)

- **Coverage:** 144/144 MATCH, 0 MISMATCH and 0 INCOMPLETE. All 144 programs
  have a workload. There were 2 signed-zero differences, both on exports the
  manifest lists.
- **Size:** file bytes 1.167x, code bytes 1.505x and static instructions
  1.554x (geomeans). Declared locals were 1.632x and static memory operations
  1.446x (corpus totals). trust-cg's file was smaller than B1's on 48 programs.
- **Dynamic:** instructions 1.701x (geomean). Memory operations were 1.511x,
  calls 1.321x and stack high-water 0.983x (totals). The stack was above B1's
  on 41 programs.
- **Time (min of 5):**

  | Mode | Geomean | Worst program |
  |---|---|---|
  | default | 1.198x | `kw_lookup`, 4.28x |
  | TurboFan | 1.207x | `min_zip2`, 5.71x |
  | Liftoff | 1.307x | `kw_lookup`, 4.43x |

  trust-cg was faster than B1 on 37 programs under TurboFan.
- **B2 context:** trust-cg / B2 was 1.385x on file bytes and 1.235x on
  TurboFan time. B2 / B1 file bytes were 0.843x.
- **Compile time:** 1.911x geomean (single sample; context only).
- **GATE-WASM-SB** (PROPOSED, not owner-approved): WSB4 (stack high-water
  total at most 1.00x) and WSB5 (coverage) pass. WSB1–WSB3 fail.

## Delta from row 1

All 144 programs are shared with row 1. Ratios are trust-cg / B1 in each row.
Each aggregate is recomputed over the shared programs by the ratchet's own
`shared_value`.

| Metric | Row 1 (`1deda6c4a`) | This row (`1fd8eabaa`) | Change |
|---|---|---|---|
| file bytes (geomean) | 1.187 | 1.167 | −1.70% |
| code bytes (geomean) | 1.542 | 1.505 | −2.35% |
| static instructions (geomean) | 1.613 | 1.554 | −3.62% |
| declared locals (total) | 1.662 | 1.632 | −1.83% |
| static memory ops (total) | 1.461 | 1.446 | −1.03% |
| dynamic instructions (geomean) | 2.008 | 1.701 | −15.28% |
| dynamic memory ops (total) | 1.569 | 1.511 | −3.73% |
| dynamic calls (total) | 1.323 | 1.321 | −0.11% |
| stack high-water (total) | 1.003 | 0.983 | −2.01% |
| time, default (geomean) | 1.267 | 1.198 | −5.44% |
| time, TurboFan (geomean) | 1.263 | 1.207 | −4.43% |
| time, Liftoff (geomean) | 1.429 | 1.307 | −8.53% |

The timing deltas compare two single runs on one host. They are inside the
ratchet's floor, which permits a 10% regression, and they are not a
noise-bounded measurement of round 14 alone.

The ratchet checks only these aggregates. Per program, the trust-cg reading
grew on some programs while the aggregate fell. These programs are context;
the ratchet does not flag them. The list compares the two rows'
`program_metrics` in `ratchet/ledger.jsonl` (row 1 `1deda6c4a117` against
this row), which equal `condense()` of each row's raw results. The B1 reading
is identical in both rows for every program and deterministic metric, so a
growth in the trust-cg reading is the same as a growth in the ratio.

- **file bytes, code bytes and static instructions** grew on 15 programs
  (fell on 93, 93 and 92; unchanged on the rest). By file bytes:
  `f28b_mem128` 3634 to 4555, `inline_machine` 322 to 847, `f18_mem` 3355 to
  3717, `found_loop` 280 to 616, `result_loop` 350 to 602, `repr_mode` 253 to
  495, `cmp_accum` 442 to 647, `dyn_hash` 5788 to 5972, `nested_enum_loop`
  364 to 482, `c34_phi__condswap` 258 to 339, `sl_ptr` 1850 to 1887,
  `bsearch_by` 1221 to 1252, `k33_robot` 1934 to 1960, `partition_pt` 1350 to
  1370 and `sl_cmp` 10866 to 10878. The same 15 programs grew in code bytes
  and static instructions.
- **declared locals** grew on 20 programs (fell on 39), each by 1 to 6:
  `k02_heap` 132 to 138, `f28b_mem128` 74 to 78, `k24_abi` 114 to 118,
  `bsearch_by` 19 to 22, `dyn_closures` 34 to 37, `c7_minmax` 5 to 7,
  `drop_cond_move` 9 to 11, `isort_f64`, `k31_expr`, `k33_robot`, `c24b_dyn`,
  `c33_repr__packed`, `cmp_accum`, `fmt_str`, `k04_codec`, `k15_byval`,
  `k21_fsm`, `min_bump`, `partition_pt` and `repr_misc`.
- **static memory operations** grew on 12 programs (fell on 26): `k10_matrix`
  344 to 398, `f28b_mem128` 138 to 186, `k15_byval` 416 to 464, `f18_mem` 126
  to 162, `k19b_ptrswap_ok` 152 to 168, `it_sum` 122 to 130, `pswap_u32` 107
  to 112, `c12_fold__prod64` 8 to 12, `pswap_i64` 105 to 108, `c33_repr` 192
  to 194, `labeled` 11 to 13 and `sl_structs` 81 to 83.
- **dynamic instructions** grew on 2 programs (fell on 105): `k33_robot`
  3387466 to 3439298 and `sl_cmp` 3413123 to 3430407.
- **dynamic memory operations, dynamic calls and stack high-water** did not
  grow on any program. They fell on 35, 4 and 10 programs.

Per-program timing is not listed: it is single-run data, and the ratchet
judges timing only as a geomean with a 10% floor.

## What this does not show

The lane runs with `no-proof-certs` and both frontends run with
`-Ztrust-verify=off`, so this row makes no proof claim. Agreement on the grid
and the workload is a differential test, not a proof, and the corpus was
selected from programs that already agreed with LLVM. The timing figures apply
to this host and node/V8 only. The deterministic figures apply to this exact
toolchain key. The deltas from row 1 measure the whole range from `1deda6c4a`
to `1fd8eabaa` (53 commits, including merges from origin/main). They are not
attributed to any one round-14 change.
