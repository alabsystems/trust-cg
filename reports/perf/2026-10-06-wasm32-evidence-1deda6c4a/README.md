# First wasm32 evidence row — `1deda6c4a`, 2026-10-06

The ledger row `1deda6c4a117-20261006T062603Z.json` (`row_family: "wasm32"`,
`evidence: true`) in `ratchet/ledger.jsonl`, rendered in
`benchmarks/LEDGER.md`. It is evidence for the stamped revision, bridge and
host only. It is not a measurement of any later checkout.

It is the first wasm32 row that passes the eligibility rules of
`docs/wasm32_perf_roadmap.md` section 8.2. `scripts/wasm_perf_ratchet.py`
recomputes those rules from the results file. No earlier wasm32 row had an
evidence baseline under the same toolchain key, so the dry run and the append
reported "regression check SKIPPED loudly". This row is now the first baseline
for its toolchain key, and for its host and engine.

## What was measured

- **Revision:** `1deda6c4a117e09e9bb503a3c418a4732032b3c6`, measured in a
  fresh worktree. `git status --porcelain` was empty, with no untracked files
  (`git_dirty: false`, `untracked_count: 0`). `git_diff_sha256` is the digest
  of the empty diff.
- **Bridge:** `librustc_codegen_trust_cg.dylib`, SHA-256
  `b8ad6fcdb8126e980908fb578d024e5fa5d92cd7c2c2dc989d74111b4521099e`, mtime
  2026-10-06T06:19:39Z, built from that tree into a fresh target directory
  with `targo --unverified build --release --locked`
  (`CARGO_INCREMENTAL=0 CARGO_PROFILE_RELEASE_DEBUG=0`,
  `RUSTC=<trust 9192>/bin/trustc`; 6m49s). `dylib_stale_source: null`.
- **rustc:** `rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc 0.1.0)`, commit
  `321aaeda75478038420d97830f14724c33c8dc39` (atpkg store `trust/9192`;
  binary SHA-256 `6c513314d5c99778345a2c2a60feef521b2ece2952149095bc9beded93b1206e`).
- **Lanes:** B1 `llvm_o2`, `tcg_o2` with exactly `-Ztrust-ir-cg-args=no-proof-certs`,
  and B2 `llvm_o2_wasmopt`. All three use `-Ztrust-verify=off`.
- **wasm-ld:** `LLD 22.1.2 (alabsystems/trust 59e55fe8e40a)`, SHA-256
  `bacef259c3e44b3cf12e0756a79452e35db484772e58ed6dc6a8adc39a66bae0`.
- **Sysroot** (`scripts/build_wasm32_sysroot.sh` output), target-tree digest:
  `eb3d1911831b88b263f931f7afd1bcaaff03f509fce9495caf08849e2079677b`.
- **wasm-opt (B2, context only):** binaryen `version_133`, SHA-256
  `81041e09f332df94db1c2009a64d8f3b85f0431a2c920ccd014d3ceebb343402`.
- **Engine:** `node v26.3.0 / V8 14.6.202.34-node.20`, run in three modes:
  default, `--no-liftoff` and `--liftoff-only`.
- **Host:** Apple M4 Pro, arm64, 14 CPUs, Darwin 25.6.0. The load threshold
  was 7.0 (ncpu/2) and was not overridden. The 1-minute load was 1.14 before
  the run and 1.51 after it (QUIET). `detect_runaways()` found no runaway
  process. Before timing, no process with ppid 1 was above 50% CPU.
- **Contract and corpus:** contract version 2, with `measurement_sha256`
  `6c8c7619a84bdffc7d7fd2c03d8516a4500b1d980f6dd2350ed13324471a6809`. The
  corpus manifest is `e180e5f6d251f90cfb8eda26adadc783215a5c5ce65eb77d10c27687d600b656`
  (all 144 programs) and the grid is
  `07d156ffc1ea7574dabc5bcae1dbd67783275bf809a15efc5ddeaa69a6ada505`.
- **Timing:** `n_run` 5 and `target_ms` 20. `--jobs 4` parallelized only the
  compile and deterministic phase; timing is always sequential.
- `tcg_env` was `{}`. No `TRUST_*` or `TCG_*` variable was set.

Command (from the worktree root). Paths outside the repository are
abbreviated: `<trust 9192>` is the atpkg store directory of Trust package 9192,
and `<scratch>` is the measuring session's scratchpad directory (under
`/private/tmp`), the same root everywhere below.

```sh
python3 benchmarks/wasm-vs-llvm/run.py --rustc <trust 9192>/bin/trustc \
  --bridge crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib \
  --sysroot <scratch>/sysroot_script --wasm-ld <scratch>/lld-build/bin/wasm-ld \
  --node /opt/homebrew/bin/node --wasm-opt <scratch>/tools/binaryen-version_133/bin/wasm-opt \
  --jobs 4 --out-dir <scratch>/ev1/results --work-dir <scratch>/ev1/work
python3 scripts/check_perf_ratchet.py <results.json>                           # dry run: OK, evidence=True
python3 scripts/check_perf_ratchet.py --require-current --append <results.json>
```

The run used neither `--allow-loaded` nor `--load-threshold`, and it was not
retried. It took 5m39s (06:20:24Z to 06:26:03Z).

## Raw results

The raw results are not committed, following the `benchmarks/README.md`
convention and the earlier wasm32 record in
`reports/perf/2026-10-01-r7-wasm32-merge/`. They are identified here by name
and SHA-256. The ledger row keeps the per-program pairs that later rows are
compared on.

| File | SHA-256 |
|---|---|
| `1deda6c4a117-20261006T062603Z.json` | `1eb214c098f3482b5c5c8587c5370f37b6d8b28af42dec5472a4d4bf11e94b4d` |
| `1deda6c4a117-20261006T062603Z.md` | `e6b28199fed1f2a258c42398008caba7d258d7eb809bce960a310888f0728bc5` |

## Result (trust-cg / B1)

- **Coverage:** 144/144 MATCH, 0 MISMATCH and 0 INCOMPLETE. All 144 programs
  have a workload. There were 2 signed-zero differences, both on exports the
  manifest lists.
- **Size:** file bytes 1.187x, code bytes 1.542x and static instructions
  1.613x (geomeans). Declared locals were 1.662x and static memory operations
  1.461x (corpus totals). trust-cg's file was smaller than B1's on 49 programs.
- **Dynamic:** instructions 2.008x (geomean). Memory operations were 1.569x,
  calls 1.323x and stack high-water 1.003x (totals). The stack was above B1's
  on 46 programs.
- **Time (min of 5):**

  | Mode | Geomean | Worst program |
  |---|---|---|
  | default | 1.267x | `min_zip2`, 4.94x |
  | TurboFan | 1.263x | `min_zip2`, 12.08x |
  | Liftoff | 1.429x | `min_zip2`, 5.47x |

  trust-cg was faster than B1 on 34 programs under TurboFan.
- **B2 context:** trust-cg / B2 was 1.409x on file bytes and 1.292x on
  TurboFan time. B2 / B1 file bytes were 0.843x.
- **Compile time:** 1.871x geomean (single sample; context only).
- **GATE-WASM-SB** (PROPOSED, not owner-approved): only WSB5 (coverage)
  passes. WSB1–WSB4 fail.

## What this does not show

The lane runs with `no-proof-certs` and both frontends run with
`-Ztrust-verify=off`, so this row makes no proof claim. Agreement on the grid
and the workload is a differential test, not a proof, and the corpus was
selected from programs that already agreed with LLVM. The timing figures apply
to this host and node/V8 only. The deterministic figures apply to this exact
toolchain key.
