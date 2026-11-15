# Darwin arm64 re-measure at `80b0e03aa`: still 0 of 18 with certificates on; the diagnostic lane's two outliers now read about 1.0x and scaling grows like LLVM

Ledger rows `L14-P8` and `X-DARWIN-P8`. This repeats the
[2026-09-28 campaign](../2026-09-28-darwin-aarch64-campaign/README.md) ("the previous
campaign" below) at `main` `80b0e03aa`, with the same driver, harness modes and
flags. It ran on the same host: Apple M4 Max (`Mac16,5`, 12 performance and 4
efficiency cores, 48 GiB), macOS 26.6.2 (`25G83`), AC power, low-power mode off. The
driver is the same Trust package 9192 (`trustc` `321aaeda7`, explicit unverified
frontend lane `-Ztrust-verify=off`). The measured revision is
`80b0e03aa6091fdf517fb3e74940fb3cec799ca3` from a clean tree. It includes the work
recorded in `CHANGELOG.md` since the previous campaign: the `p4_matmul` and
`h1_vec_push_sum` fixes, the L14-P5 fixed-cost changes, the L14-P6 scaling fixes and
the proof-wall census with instruction-derived obligations.

The backend was built from this tree through the repository's Cargo wrapper, with the
same package named explicitly
([`commands/build_bridge.sh`](commands/build_bridge.sh)):
`cd crates/rustc-codegen-trust-cg && CARGO_TARGET_DIR=target-bridge RUSTC=<pkg>/bin/trustc TRUST_TARGO=<pkg>/bin/targo ../../scripts/trust_cargo.sh build --release --locked`.
That is `targo --unverified build --release --locked`, which makes no proof claim
about the build. The dylib's sha256 is `b638dc7adfdc82cb…`
([`logs/00-bridge-build-summary.txt`](logs/00-bridge-build-summary.txt),
[`host.txt`](host.txt)).

**The host was not quiet.** Other agents' builds and test runs kept the 1-minute load
between 2.6 and 30.1 (median 11.8) from 09:19Z to 11:40Z. From 11:40Z to 14:22Z it
ranged from 1.9 to 24.3, with a median of 7.0, against 1.15 to 2.09 for the previous
campaign ([`load-pre-campaign-wait.tsv`](load-pre-campaign-wait.tsv) and
[`load-30s.tsv`](load-30s.tsv), each sampled every 30 s). The harness's quiet
threshold is 8.0 on 16 CPUs. The first attempt was overtaken by load. After that,
each timing step first waited for a lull: a 1-minute load below 4 and a 5-minute
load below 6, or below 5 and 7 for the scaling harnesses (see "Attempts"). The
evidence row comes from the third evidence attempt, which ran QUIET from 3.98 to
3.29. The two earlier attempts ended LOADED and are retained, but they are not
evidence.

## Summary

| What | 2026-09-28 (`01fc13b13`) | This re-measure (`80b0e03aa`) |
| --- | --- | --- |
| Ledger row (evidence mode, `run.py --cold`) | evidence, QUIET, coverage **0.0%** (0 MATCH, 18 INCOMPLETE), all `[TCG-PROOF-465]` | Appended. Evidence, QUIET, clean. Coverage **still 0.0%**: 0 MATCH, 18 INCOMPLETE, 0 MISMATCH, all `[TCG-PROOF-465]` |
| Gates on that row | `G5` fail, ten unmeasured | `G5` fail (0.0% of 80%), ten unmeasured. Unchanged. |
| Diagnostic lane (`no-proof-certs`, never evidence): runtime geomean vs LLVM `-O3` | 1.267x (worst 8.868x `p4_matmul`) | **0.950x** in both runs (worst 1.082x `h1` / 1.113x `h3`) |
| Diagnostic: warm / cold compile vs `-O2` | 1.367x / 4.263x | 1.229x / 3.872x (run A), 1.238x / 3.957x (run B) |
| Diagnostic: linked size / compiler peak RSS vs LLVM | 1.0006x / 1.188x | 1.0006x (each linked file the same size in bytes as before) / 1.196x and 1.197x |
| `scale_gate.py --rss` xlarge (33,605 lines), proofs off | 12.14x time, 25.35x RSS (9,453.7 MB) | **1.26x** time, **1.46x** RSS (546.3 MB); repeat 1.28x and 1.46x |
| `compile-scaling` exponent excess (blocks, loops, funcs, arraysize) | +0.02, +0.28, +0.14, +0.00 | +0.01, +0.18, +0.07, -0.01 (all OK) |
| Compile-time canary | GATE RED (fail-closed) | GATE RED (fail-closed, `[TCG-PROOF-465]`) |
| Determinism sentinel (cold, N=5) | DETERMINISTIC-FAILCLOSED | DETERMINISTIC-FAILCLOSED (5 of 5 attempts, 1.31 to 3.17 s) |

No superiority claim and no gate pass follows from this re-measure. The evidence row
again records that the production lane compiles none of the corpus. The diagnostic
lane measures the code the backend emits with its proof gate off. It is not a ledger
row and not evidence (`benchmarks/beat-llvm/contract`).

## 1. Evidence mode: the ledger row

Command: `python3 benchmarks/beat-llvm/run.py --driver <trust 9192>/bin/trustc --cold --retain-dir <this directory>`

This is the full 18-program contract corpus at the contract N (3 compiles, 5 runs),
with the production backend configuration (no knob, no `TCG_*` variable) and the warm
and true-cold lanes, for `aarch64-apple-darwin` (driver host). The harness retained
the record in [`2026-09-29-80b0e03aa609-141117Z/`](2026-09-29-80b0e03aa609-141117Z/README.md).
`python3 scripts/check_perf_ratchet.py --require-current --append` accepted it as
current, eligible evidence and appended it
([`logs/10-perf-ratchet-require-current-append.log`](logs/10-perf-ratchet-require-current-append.log)).
The ratchet compared it with the previous campaign's row, the first Darwin
baseline for this host, target and program set, and reported no regression. Coverage
is 0.0% in both rows, and every other metric is null in both.

| Field | Value |
| --- | --- |
| results | `80b0e03aa609-20260929T141257Z.json` |
| headline_eligible / ineligible_reasons | true / none |
| load before / after / threshold | 3.98 / 3.29 / 8.0 (QUIET) |
| backend | `target-bridge/release/librustc_codegen_trust_cg.dylib`, sha256 `b638dc7adfdc82cb…`, 114,140,192 bytes |
| driver | Trust package 9192, `trustc` `321aaeda75478038420d97830f14724c33c8dc39` (1.99.0-dev, LLVM 22.1.2), as before |
| independent checker | Managed Clean 8606 (`clean 0.9.0`). The package's own `bin/clean` answers `--version`, and the backend again skips it because it lacks `carcara-verify` (`X-HOST-P8`). |
| certificate store (warm lane) | 1,410 certificates before and after. The previous campaign had 466 before and 479 after. The store is shared host state that other compiles fill, so the count is context, not a result. |
| LLVM compile medians (`-O0`, `-O2`, `-O3`) | 0.305 to 0.360 s. The previous campaign had 0.286 to 0.328 s. |

**Why every program is still INCOMPLETE.** Each refusal is `[TCG-MIR-UNSUPPORTED]`
caused by `[TCG-PROOF-465]`: proof promotion rejects the emitted opcode inventory, and
the bridge then refuses the required functions (`std::rt::lang_start`, `main`, the
`FnOnce` shims, `Termination::report`). The `p3_gcd` probe
([`logs/00-refusal-example-p3_gcd.stderr.txt`](logs/00-refusal-example-p3_gcd.stderr.txt),
same backend and flags, [`commands/probe.sh`](commands/probe.sh)) lists the same 29
distinct AArch64 opcodes as the previous campaign's probe. Its nine refused functions
have the same counts of uncovered opcodes: 10, 17, 7, 45, 6, 13, 2, 14 and 1. What
changed is the reason a
refusal names for `Movz` and `TailCall`. It was "registry name lookup is not proof
credit". It is now "no checked certificate: an instruction-derived obligation is not
proof credit", because the obligation holds but binds no source instruction and
carries no checked certificate. That is the change the
proof-wall census describes,
which added no proof credit. `StpPreIndex` still leads every refusal of `lang_start`
and `main` with "statistical sampling is not proof credit". The sentinel's five
attempts name it first 25 times, and the canary names `Movz` and `TailCall` as
instruction-derived.

## 2. Diagnostic lane: the emitted code with proof certificates off

Command: `run.py --driver … --cold --bridge-cg-arg no-proof-certs --retain-dir diagnostic-no-proof-certs`

The lane ran twice, on the same backend (sha256 `b638dc7a…`). Neither run is a ledger
row, and the ratchet rejects the knob.

- **Run A**, 13:19:35Z to 13:23:50Z, on a clean tree. The load rose from 3.65 to 8.64,
  so the harness also marks it LOADED. Record:
  [`diagnostic-no-proof-certs/2026-09-29-80b0e03aa609/`](diagnostic-no-proof-certs/2026-09-29-80b0e03aa609/README.md).
- **Run B**, 14:17:08Z to 14:21:17Z, QUIET from 3.29 to 2.99. It ran after the ledger
  append, so the harness stamped the tree dirty. The recorded diff hash equals the
  hash of the ledger diff (`ratchet/ledger.jsonl` and `benchmarks/LEDGER.md` only;
  [`logs/12-dirty-tree-is-the-ledger-append.txt`](logs/12-dirty-tree-is-the-ledger-append.txt)).
  Record:
  [`diagnostic-no-proof-certs/2026-09-29-80b0e03aa609-dirty/`](diagnostic-no-proof-certs/2026-09-29-80b0e03aa609-dirty/README.md).

Both runs are 18 of 18 MATCH, with 0 MISMATCH. A MATCH compares exit codes with a
full-width checksum folded in mod 126, so it is probabilistic.

| Axis | vs LLVM | 2026-09-28 | Run A | Run B |
| --- | --- | ---: | ---: | ---: |
| runtime geomean | -O3 | 1.2668x | 0.9498x | 0.9501x |
| runtime, resolvable rows only (10 programs) | -O3 | 0.9692x | 0.9622x | 0.9651x |
| scalar runtime geomean | -O3 | 1.0101x | 1.0054x | 1.0034x |
| worst program | -O3 | 8.868x (`p4_matmul`) | 1.082x (`h1_vec_push_sum`) | 1.113x (`h3_box_leak`) |
| compile, warm | -O2 / -O3 | 1.3674x / 1.3577x | 1.2289x / 1.2210x | 1.2377x / 1.2247x |
| compile, true cold | -O2 | 4.2630x | 3.8718x | 3.9567x |
| linked size geomean (worst) | -O3 | 1.00060x (1.00286x) | 1.00060x (1.00286x) | 1.00060x (1.00286x) |
| program peak-RSS geomean | -O3 | 0.9988x | 0.9990x | 0.9994x |
| compiler peak-RSS geomean | -O2 / -O3 | 1.1876x / 1.1872x | 1.1957x / 1.1957x | 1.1973x / 1.1962x |

The informational gate check is never evidence. It moved in both runs
([`logs/05-check-gates-diagnostic.log`](logs/05-check-gates-diagnostic.log),
[`logs/13-check-gates-diagnostic-repeat.log`](logs/13-check-gates-diagnostic-repeat.log)).
`G1b` (each vectorizable kernel within 2.0x) and `G1c` (geomean below 1.00x, no
program above 1.50x) now pass, where both failed before. `G1a`, `G5` and `S1` pass as
before. `G2-M1` warm and cold, `G2` end-state, `S2` and `R2` fail as before, and `R1`
is unmeasured.

| Category | 2026-09-28 | Run A | Run B |
| --- | ---: | ---: | ---: |
| branch | 1.007 | 1.014 | 1.017 |
| heap | 1.684 | 0.990 | 0.988 |
| multifn | 0.953 | 0.937 | 0.956 |
| scalar | 1.010 | 1.005 | 1.003 |
| vectorizable | 1.553 | 0.852 | 0.849 |

Program by program (runtime and compile ratios vs LLVM; the bridge-lane `rel_spread`
of the five runtime samples in brackets; full tables in [`comparison/`](comparison/)):

| Program | Runtime x -O3: 09-28 | Run A | Run B | Warm x -O2: 09-28 / A / B | Cold x -O2: 09-28 / A / B | Compiler RSS x -O2: 09-28 / A / B |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| b1_mispredict | 1.007 [0.01] | 1.014 [0.01] | 1.017 [0.01] | 1.406 / 1.220 / 1.290 | 4.281 / 4.000 / 4.264 | 1.190 / 1.197 / 1.203 |
| h1_vec_push_sum | **5.100** [0.13] | 1.082 [0.09] | 1.013 [0.05] | 1.356 / 1.259 / 1.237 | 4.184 / 3.929 / 4.015 | 1.185 / 1.189 / 1.191 |
| h2_vec_grow | 1.142 [0.82] | 0.996 [0.02] | 0.996 [0.02] | 1.355 / 1.202 / 1.204 | 4.206 / 3.651 / 3.676 | 1.183 / 1.193 / 1.196 |
| h3_box_leak | 1.412 [0.33] | 1.046 [0.05] | 1.113 [0.11] | 1.350 / 1.180 / 1.223 | 4.210 / 3.554 / 3.783 | 1.183 / 1.189 / 1.190 |
| h4_vec_dropper | 0.977 [0.49] | 0.852 [0.14] | 0.848 [0.02] | 1.371 / 1.165 / 1.391 | 4.261 / 3.653 / 5.424 | 1.182 / 1.187 / 1.188 |
| m1_call_chain | 0.933 [0.01] | 0.930 [0.01] | 0.937 [0.01] | 1.351 / 1.238 / 1.219 | 4.321 / 3.787 / 3.922 | 1.186 / 1.199 / 1.203 |
| m2_call_heavy | 0.973 [0.01] | 0.943 [0.03] | 0.975 [0.01] | 1.380 / 1.223 / 1.241 | 4.303 / 3.810 / 3.771 | 1.186 / 1.196 / 1.196 |
| p1_xorshift | 1.007 [0.01] | 1.005 [0.01] | 0.998 [0.01] | 1.348 / 1.172 / 1.180 | 4.162 / 3.488 / 3.604 | 1.186 / 1.195 / 1.200 |
| p2_collatz | 1.002 [0.01] | 1.006 [0.05] | 0.997 [0.01] | 1.327 / 1.222 / 1.194 | 4.177 / 3.765 / 3.628 | 1.187 / 1.197 / 1.198 |
| p3_gcd | 0.997 [0.01] | 1.000 [0.00] | 0.994 [0.01] | 1.362 / 1.187 / 1.214 | 4.229 / 3.641 / 4.071 | 1.183 / 1.193 / 1.193 |
| p4_matmul | **8.868** [0.11] | 1.004 [0.01] | 1.002 [0.00] | 1.366 / 1.191 / 1.190 | 4.227 / 3.675 / 3.834 | 1.195 / 1.207 / 1.206 |
| p5_struct_acc | 1.001 [0.01] | 0.987 [0.01] | 0.996 [0.00] | 1.348 / 1.166 / 1.184 | 4.159 / 3.624 / 3.771 | 1.190 / 1.197 / 1.196 |
| p6_branch_match | 1.054 [0.02] | 1.038 [0.03] | 1.044 [0.01] | 1.404 / 1.506 / 1.237 | 4.414 / 4.134 / 4.155 | 1.193 / 1.197 / 1.200 |
| p7_sieve | 0.820 [0.50] | 0.797 [0.03] | 0.803 [0.01] | 1.346 / 1.207 / 1.235 | 4.139 / 3.919 / 3.740 | 1.195 / 1.197 / 1.204 |
| p8_closure_nest | 1.001 [0.01] | 0.997 [0.00] | 0.991 [0.01] | 1.355 / 1.229 / 1.229 | 4.179 / 4.030 / 3.803 | 1.188 / 1.192 / 1.196 |
| v1_saxpy | 0.753 [0.03] | 0.740 [0.03] | 0.740 [0.00] | 1.368 / 1.327 / 1.299 | 4.329 / 5.496 / 3.874 | 1.191 / 1.199 / 1.200 |
| v2_memfill | 1.356 [0.69] | 1.012 [0.10] | 0.998 [0.01] | 1.413 / 1.159 / 1.252 | 4.490 / 3.824 / 4.061 | 1.185 / 1.203 / 1.195 |
| v3_popcount | 1.218 [1.31] | 0.747 [1.57] | 0.743 [1.76] | 1.411 / 1.310 / 1.274 | 4.484 / 4.072 / 4.132 | 1.189 / 1.197 / 1.198 |

Linked size is not in the table. Every program's linked file is the same number of
bytes as in the previous campaign, in both runs, including `p4_matmul` and
`h1_vec_push_sum`, whose code changed. The ratios are therefore unchanged: 1.0019x to
1.0029x, and 0.9682x for `p7_sieve`.

Reading the table:

- **Improved, well outside the noise.** `p4_matmul` went from 8.868x to 1.004x and
  1.002x. `h1_vec_push_sum` went from 5.100x to 1.082x and 1.013x. Each has a
  bridge `rel_spread` below 0.1 in both runs. These are the two outliers the previous
  campaign named. `CHANGELOG.md` records the code changes to both programs and their
  instruction counts. This re-measure reads the result through the harness; it does
  not attribute it.
- **Improved, but the previous reading was noisy.** `h3_box_leak` (1.412x to 1.046x
  and 1.113x), `h2_vec_grow` (1.142x to 0.996x), `h4_vec_dropper` (0.977x to 0.852x
  and 0.848x) and `v2_memfill` (1.356x to 1.012x and 0.998x). Their previous bridge
  spreads were 0.33, 0.82, 0.49 and 0.69. `CHANGELOG.md` records code changes for
  `h2` to `h4` and none for `v2`, so `v2`'s change is a noise reading.
- **Not resolvable.** `v3_popcount` runs for about 5 ms, with bridge spreads of 1.57
  and 1.76. Its 0.74x reading is not a result.
- **Unchanged within about 3%.** The branch, scalar and multifn programs, `p7_sieve`
  and `v1_saxpy` moved by at most 0.03 in either direction. `p6_branch_match` is
  still 1.04x and `b1_mispredict` 1.01 to 1.02x.
- **The runtime geomean** fell from 1.267x to 0.950x. Almost all of that is `p4`,
  `h1` and the noisy short programs. The resolvable-rows geomean, the 10 programs
  that run for at least 50 ms with spread at most 0.25, is 0.969x before and 0.962x
  and 0.965x now. That subset contains neither `p4` nor `h1`.
- **The compile ratios fell, but only a third to a half of the fall is the bridge.** Over
  the 18 programs, the geomean of the bridge's warm median went from 0.416 s to
  0.401 s and 0.395 s. The cold median went from 1.297 s to 1.265 s and 1.264 s. The
  LLVM `-O2` median rose from 0.304 s to 0.327 s and 0.319 s, on the same compiler
  under a busier host ([`comparison/absolute-levels.txt`](comparison/absolute-levels.txt)).
  The LLVM `-O3` runtimes of the 10 resolvable programs are also about 11% longer
  than the previous campaign's (geomean 0.220 s to 0.246 s and 0.245 s), and the
  bridge's rose with them. So the absolute level of this host moved between the
  campaigns. Only ratios taken within one run compare. The warm ratio fell 10.1% in
  run A and 9.5% in run B, of which the bridge's own warm time accounts for 3.6% and
  5.0%. Cold minus warm is still about 0.87 s per compile (0.88 s before).
- **Compiler peak RSS** rose slightly. The bridge's geomean went from 171.5 MB to
  172.8 MB, LLVM's stayed at 144.4 MB, and the ratio went from 1.188x to 1.196x.
  Single cold readings vary a lot under load: `v1_saxpy` read 5.496x in run A and
  3.874x in run B, and `h4_vec_dropper` read 5.424x in run B.

## 3. Scaling (proofs off in both harnesses)

Command: `python3 benchmarks/beat-llvm/scale_gate.py --driver … --rss`. Wall time is
min-of-5 and peak RSS min-of-3, with lanes interleaved, at `-O3` for
`aarch64-apple-darwin`. The trust-cg lane passes `no-proof-certs`. The run went from
14:13:00Z to 14:13:40Z at load 3.29 to 4.75, and the repeat of large and xlarge
(`--sizes large xlarge --rss`) at 3.96 to 7.05
([`logs/06-scale-gate-rss.log`](logs/06-scale-gate-rss.log),
[`logs/11-scale-gate-large-xlarge-repeat.log`](logs/11-scale-gate-large-xlarge-repeat.log)).

| Crate | Lines | LLVM | trust-cg | Time: 09-28 -> now (repeat) | trust-cg RSS: 09-28 -> now | Memory: 09-28 -> now (repeat) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 355 | 0.320 s | 0.387 s | 1.38x -> 1.21x | 168.4 -> 168.0 MB | 1.23x -> 1.22x |
| medium | 2,805 | 0.427 s | 0.517 s | 1.57x -> 1.21x | 243.4 -> 204.2 MB | 1.65x -> 1.39x |
| large | 11,205 | 0.794 s | 0.991 s | 3.25x -> 1.25x (1.29x) | 916.9 -> 301.9 MB | 4.57x -> 1.51x (1.51x) |
| xlarge | 33,605 | 1.824 s | 2.293 s | **12.14x -> 1.26x (1.28x)** | **9,453.7 -> 546.3 MB** | **25.35x -> 1.46x (1.46x)** |

From large to xlarge, trust-cg's compile time now grows 2.31x and its peak RSS 1.81x.
LLVM's grow 2.30x and 1.86x. In the previous campaign trust-cg's grew 8.6x and 10.3x.
The trust-cg lane's xlarge compile went from 21.817 s to 2.293 s. The
[L14-P6 report](../2026-09-28-darwin-scaling-l14p6/README.md) read xlarge at 1.50x
time and 1.45x memory, at a load of 8 to 12. The memory ratio agrees with this run.
The time ratio here is lower, at a lower load. The loaded first attempt (load 11.5 to
12.3) read 1.24x and 1.44x ([`attempts/1-loaded-20260929T1140Z/logs/06-scale-gate-rss.log`](attempts/1-loaded-20260929T1140Z/logs/06-scale-gate-rss.log)).

Command: `python3 benchmarks/compile-scaling/run.py --driver … --out-dir <scratch>`.
CPU time, median-of-3, `-O2`, `no-proof-certs` and `refine-solver=0`, at load 4.75
to 5.54 ([`logs/07-compile-scaling.log`](logs/07-compile-scaling.log)).

| Shape | Sizes | LLVM exponent: 09-28 -> now | trust-cg exponent: 09-28 -> now | Excess: 09-28 -> now | Ratio at largest: 09-28 -> now |
| --- | --- | ---: | ---: | ---: | ---: |
| blocks | 100 to 800 | 0.15 -> 0.14 | 0.17 -> 0.15 | +0.02 -> +0.01 | 1.44x -> 1.39x |
| loops | 15 to 120 | 0.15 -> 0.13 | 0.42 -> 0.31 | +0.28 -> +0.18 | 2.66x -> 2.08x |
| funcs | 50 to 400 | 0.14 -> 0.12 | 0.28 -> 0.19 | +0.14 -> +0.07 | 1.91x -> 1.64x |
| arraysize | 4,096 to 262,144 B | 0.01 -> 0.01 | 0.01 -> 0.01 | +0.00 -> -0.01 | 1.43x -> 1.42x |

The verdict is again "OK: no shape grows materially faster than LLVM" (limit 0.6).
`loops` is still the steepest shape: 2.08x LLVM's CPU time at 120 loops, with an
exponent excess of +0.18. The loaded first attempt read +0.01, +0.20, +0.11 and
+0.01.

## 4. Compile-time canary and determinism sentinel

- `scripts/compile_time_canary.sh --driver …` exited 1 with `canary: GATE RED: bridge
  failed to compile the pinned canary program`, and `[TCG-PROOF-465]`. No compile time
  was measured, as before.
- `scripts/compile_determinism_sentinel.sh 5 --driver …` ran cold, each attempt with a
  fresh `XDG_CACHE_HOME`, and exited 2 with DETERMINISTIC-FAILCLOSED. All five attempts
  failed closed at load 5.58 to 6.17, in 1.31 to 3.17 s each. "Not a flap."

## What improved, what did not, and what still separates this backend from LLVM here

Improved:

- `p4_matmul`, 8.9x to 1.00x, and `h1_vec_push_sum`, 5.1x to 1.01 to 1.08x, in the
  diagnostic lane. With them, the diagnostic runtime geomean went from 1.267x to
  0.950x, and `G1b` and `G1c` now pass informationally.
- Crate-size scaling. At 33,605 lines, compile time went from 12.1x to 1.26x to
  1.28x LLVM and peak RSS from 25.4x (9.45 GB) to 1.46x (546 MB). The growth from
  large to xlarge now matches LLVM's. The `compile-scaling` exponent excesses fell
  for `loops` and `funcs`.
- The bridge's absolute compile times are lower: warm by 3.6 to 5.0%, cold by 2.5%.
  The ratios fell further, but part of that fall is LLVM's own lane running slower on
  this busier host.

Did not improve:

- **Coverage of the production lane: 0 of 18, unchanged.** The certificates-on bridge
  refuses every corpus program, the canary and the sentinel program with
  `[TCG-PROOF-465]` (`L07-P2`). Only the reason named for `Movz` and `TailCall`
  changed, from registry-name to instruction-derived-uncertified. The evidence row
  still has no runtime, compile, size or RSS ratio, and ten gates stay unmeasured.
- Linked size: each file is the same size in bytes as before, 1.0006x (`S2`, at
  most 1.00x, fails).
  Compiler peak RSS: 1.19 to 1.20x (`R2` fails), up about 1.3 MB per compile.
- The resolvable scalar, branch and multifn programs: within about 3% of their
  previous ratios.

What still separates trust-cg from LLVM on this host, as measured here:

1. **No certificates-on compile succeeds.** Every number that compares emitted code
   or compile cost comes from the `no-proof-certs` diagnostic lane.
2. **Compile time.** Warm is 1.23 to 1.24x LLVM `-O2`, about 75 ms more per
   compile (geomeans 0.395 and 0.401 s against 0.319 and 0.327 s). True cold is 3.9
   to 4.0x, and the cold lane still costs about 0.87 s more than the warm one.
   `CHANGELOG.md`/`LIMITATIONS.md` (L14-P5) attribute the remaining cold gap to the
   XProtect scan of each fresh private AY copy and to live discharges into an empty
   store. This campaign does not break it down. At 120 loops the `loops` shape costs
   2.08x LLVM's CPU time.
3. **Memory.** Compiler peak RSS is 1.20x LLVM `-O2` on the corpus, and 1.22x to
   1.51x on the scaling crates.
4. **Runtime.** No program is above 1.12x. The ones above 1.02x in either run are
   `h3_box_leak` (1.05x and 1.11x), `h1_vec_push_sum` (1.08x and 1.01x) and
   `p6_branch_match` (1.04x). `b1_mispredict` reads 1.01 to 1.02x. The resolvable
   geomean is 0.96x.

## Attempts, and why the steps are split across invocations

[`commands/campaign.sh`](commands/campaign.sh) is the previous campaign's script, with
three scheduling changes and no change to any measured command. The atpkg launcher
directory is on `PATH`. Each timing step waits for a lull first
([`commands/wait_quiet.py`](commands/wait_quiet.py), logged in `load.tsv`,
`load-wait.tsv` and `logs/quiet-wait.log`). `STEPS` selects a subset of steps.
Attempt 1 ran before the wait and `STEPS` were added, and it started at a 1-minute
load of 2.80, after a manual wait.
[`commands/sequence.sh`](commands/sequence.sh) lists the invocations after the first
full run. `logs/steps.log` has every step's exit code and wall time. `load.tsv` has
the load before and after each step. `load-before.txt` and `load-after.txt` hold one
process, memory, power and thermal snapshot per invocation.

| Step | UTC | 1-min load (harness; range of 30 s samples while waiting) | Outcome |
| --- | --- | --- | --- |
| evidence, attempt 1 | 11:40:15 to 11:42:07 | 2.80 -> 12.16 | LOADED: 11 INCOMPLETE and 7 NONDET-CANDIDATE (refused twice under load). Not evidence. [`attempts/1-loaded-20260929T1140Z/`](attempts/1-loaded-20260929T1140Z/) |
| diagnostic, attempt 1 | 11:42:08 | 11.51 | The harness refused to start (loaded). |
| scaling, canary and sentinel, attempt 1 | 11:42:10 to 11:44:02 | 11.5 -> 19.7 | Ran under load. Context only, in `attempts/1-…/logs/`. |
| waiting before evidence | 11:45:20 to 12:05:51 | 1.9 to 17.0 | |
| evidence, attempt 2 | 12:05:51 to 12:07:33 | 1.69 -> 8.03 | LOADED (8.03 > 8.0). Not evidence. [`attempts/2-loaded-20260929T1205Z/`](attempts/2-loaded-20260929T1205Z/) |
| waiting before diagnostic | 12:07:34 to 13:19:35 | 3.7 to 24.3 | |
| diagnostic run A | 13:19:35 to 13:23:50 | 3.65 -> 8.64 | Ran. LOADED at the end, clean tree. |
| waiting before scaling | 13:23:51 to 13:54:59 | 4.3 to 11.2 | Stopped by the operator. The remaining steps were re-sequenced (`sequence.sh`). |
| waiting before evidence | 13:55:14 to 14:11:15 | 3.9 to 12.0 | |
| **evidence, attempt 3** | 14:11:15 to 14:12:57 | **3.98 -> 3.29** | **QUIET, clean, eligible: the ledger row.** Logs 01 to 03. |
| scale gate, compile-scaling | 14:13:00 to 14:14:17 | 3.29 -> 5.54 | Section 3. |
| canary, sentinel | 14:14:19 to 14:14:32 | 5.54 -> 5.76 | Section 4 (no quiet wait: fail-closed verdicts). |
| scale-gate repeat | 14:15:06 to 14:15:38 | 3.96 -> 7.05 | Section 3. |
| diagnostic run B | 14:17:08 to 14:21:17 | 3.29 -> 2.99 | QUIET. Dirty only by the ledger append. |

## Components that could not run as required, and why

1. **The production (certificates-on) bridge lane.** It refuses every corpus program,
   the canary and the sentinel program (section 1). As before, no evidence-grade
   runtime, compile, size or RSS ratio exists for this host.
2. **A quiet host for the whole campaign.** The host was shared with other agents'
   builds. The evidence row is quiet, but diagnostic run A ended above the threshold,
   and the scaling and repeat steps ran at 1-minute loads of 3.3 to 7.1, above the
   previous campaign's 1.2 to 2.1. Runtime and compile ratios are taken within one
   run and cancel much of this. Absolute times do not (section 2).
3. **The Trust package's own Clean.** `store/trust/9192/bin/clean` still lacks
   `carcara-verify` (`X-HOST-P8`). The backend used managed Clean 8606, and no run was
   marked DEGRADED.
4. **The portable certificate set.** It is still DISABLED. The vendored `drat-trim`
   built by this host's Apple clang 21 / SDK 27.0 hashes to `f075353b…`, while
   `manifest.v1` authorizes `6933827a…`. Live discharge is kept.
5. **Core pinning.** macOS has no `sched_setaffinity`, so the heterogeneous cores are
   not pinned.
6. **Not in this re-measure.** No TY or model-checker workloads (`L14-P4`), no
   proofs-on scaling ladder (the production lane cannot compile the corpus; `L14-P6`),
   and no real-crate denominator (`L14-P7`).

## Files

- `2026-09-29-80b0e03aa609-141117Z/`: the harness record of the eligible evidence run,
  which the ledger row names as `retained_dir`.
- `diagnostic-no-proof-certs/2026-09-29-80b0e03aa609/` (run A) and
  `diagnostic-no-proof-certs/2026-09-29-80b0e03aa609-dirty/` (run B): the harness
  records of the diagnostic lane. Neither is a ledger row.
- `attempts/`: the two LOADED evidence attempts, and the first invocation's logs and
  load record.
- `comparison/`: [`commands/compare.py`](commands/compare.py) output for each of the
  three runs against the previous campaign's file, and
  [`commands/absolutes.py`](commands/absolutes.py) output for the absolute levels.
- `logs/`: every step's output, `steps.log`, the bridge build summary, the `p3_gcd`
  refusal example, the ledger append, and the dirty-tree identity check.
- `load.tsv`, `load-wait.tsv`, `load-30s.tsv`, `load-pre-campaign-wait.tsv`,
  `load-before.txt`, `load-after.txt`: the load record.
- `host.txt`: host identity, Trust package, Clean candidates, C toolchain, linker, SDK,
  Python, and the backend's hash and build command.
- `commands/`: `build_bridge.sh`, `campaign.sh`, `sequence.sh`, `wait_quiet.py`,
  `hostinfo.sh`, `probe.sh`, `compare.py`, `absolutes.py`.
