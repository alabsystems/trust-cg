# Darwin arm64 requalification at current `main` (L14-P1) and the first proofs-on larger corpus (L14-P7): the production lane still compiles nothing

Ledger rows `L14-P1` and `L14-P7` (with `L14-P8`, `X-DARWIN-P8`). This record repeats
the [2026-09-29 re-measure](../2026-09-29-darwin-aarch64-remeasure/README.md) at the
current candidate, with the same driver, harness modes and flags, and adds the
versioned larger corpus of [`benchmarks/real-corpus/`](../../../benchmarks/real-corpus/README.md).

**Measured revision.** `efc47d3bc3e58412eae6c867769c394e65b45d60`, clean tree. It is
`main` `2dde71362` (2026-10-14) plus one commit that adds only
`benchmarks/real-corpus/`, its unit test and the benchmark index row; the
backend's build inputs are those of `2dde71362`, and the backend was built
before that commit (`scripts/bridge_backend.py` finds it current).

**Host.** Apple M4 Max (`Mac16,5`, 12 performance and 4 efficiency cores, 48 GiB),
macOS 26.6.2 (`25G83`), AC power, low-power mode off ([`host.txt`](host.txt)). The
host is shared with other agents' Trust builds. Its 1-minute load ranged from
about 2 to 42 during this session ([`load-wait.tsv`](load-wait.tsv),
[`load.tsv`](load.tsv)); every wall-clock number below is given with its load,
and the load-robust counters (instructions retired, cycles) are reported beside
it.

**Driver and backend.** Trust package 9192 (`trustc` `321aaeda7`, LLVM 22.1.2,
explicit unverified frontend lane `-Ztrust-verify=off`), as in both earlier Darwin
rows. The backend was built from this tree with
[`commands/build_bridge.sh`](commands/build_bridge.sh) (`targo --unverified build
--release --locked` through `scripts/trust_cargo.sh`; no proof claim about the
build): `librustc_codegen_trust_cg.dylib`, 133,004,352 bytes, sha256
`55cc7f2f8bf46d677004b1ba2284733fc6cea2d7ebd0e8b935802c700e0ce395`
([`logs/00-bridge-build-summary.txt`](logs/00-bridge-build-summary.txt)). The
independent checker is managed Clean 8606 (`clean 0.9.0`); the package's own
`bin/clean` is skipped by the backend because it lacks `carcara-verify`
(`X-HOST-P8`).

## Summary

| What | Result |
| --- | --- |
| Ledger row (`run.py --cold`, production lane), `L14-P1` | Appended: the third `aarch64-apple-darwin` evidence row, at `efc47d3bc`, QUIET (1.97 -> 7.64), clean, eligible, accepted by `check_perf_ratchet.py --require-current --append`. **Coverage 0.0%**: 0 of 18 MATCH, 18 INCOMPLETE (`[TCG-PROOF-465]`, 11 of them refused under load and labeled NONDET-CANDIDATE), 0 MISMATCH. `G5` fails; twelve gates unmeasured. Two earlier attempts ended LOADED and are retained. |
| Ratios now vs LLVM, diagnostic lane (`no-proof-certs`, never evidence), 18 programs | Runtime 0.926x `-O3` wall (worst 1.020x, `p6_branch_match`), **0.916x in cycles**; emitted code **1.016x** `-O3` (worst 2.07x, `p4_matmul`), linked file 0.9997x; warm compile **1.030x** `-O2` wall / 1.026x `-O3`, **1.185x in compiler instructions retired**, 1.52x CPU with children; true-cold compile **3.37x** `-O2`; compiler peak RSS **1.218x** `-O2` / 1.217x `-O3`; program peak RSS unresolved (15 of 18 at the sampler floor). |
| Scaling at the same revision (proofs off) | `scale_gate.py --rss` xlarge (33,605 lines) **1.14x** time and **1.23x** peak RSS (was 1.26x and 1.46x at `80b0e03aa`); `compile-scaling` exponent excess at most +0.12 (`loops`), 1.86x LLVM CPU at 120 loops. |
| Canary / sentinel | GATE RED / DETERMINISTIC-FAILCLOSED (`[TCG-PROOF-465]`). |
| Larger corpus (`L14-P7`), 62 rows, production lane | **0 of the 57 rows with code complete.** As run, the harness counted 5 of 62 (8.1%), all vacuous (library crates whose LLVM object holds no code); under the round-1 rule that a library compile writing no object is an ERROR, it is **1 of 62 (1.6%), vacuous** (`unicode-ident`), with 4 ERROR rows. 56 INCOMPLETE (`[TCG-PROOF-465]`), `core` at `-O0` TIMEOUT at 3,600 s. Not evidence: 27 rows ran under load. |
| Larger corpus, diagnostic lane | As run 46 of 62 (74.2%); re-scored **42 of 62 (67.7%)**, 41 with code: every real-program guest and ladder crate MATCHes LLVM, 8 of 27 crates (1 vacuous) and `core` at `-O0` compile; 16 rows refused for lowering gaps, 4 wrote no object. Compile 1.35x LLVM wall and 1.45x instructions (geomean over the 42), up to 30x on `siphasher`; `core` `-O0` 8.4x wall, 2.9x code bytes. |

No superiority claim and no gate pass follows from this record. Every compile-cost,
runtime, size and memory ratio above comes from the `no-proof-certs` diagnostic
lane: the production lane still compiles none of the 18 programs and none of the
57 larger-corpus rows that give it code to compile (`L07-P2`).

## 1. L14-P1: the ledger row (evidence mode)

Command: `python3 benchmarks/beat-llvm/run.py --driver <trust 9192>/bin/trustc --cold --retain-dir <this directory>`
([`commands/campaign.sh`](commands/campaign.sh) step 01): the full 18-program
contract corpus at the contract N (3 compiles, 5 runs, 5 peak-RSS samples), the
production backend configuration (no knob, no `TCG_*` variable), warm and
true-cold lanes, for `aarch64-apple-darwin` (the driver's host).

Three attempts ran, each after a quiet wait
([`commands/evidence_until_quiet.sh`](commands/evidence_until_quiet.sh); its
stopping rule, the first attempt the harness stamps eligible, was fixed before
the first retry). Two ended LOADED and are retained, not evidence:

| attempt | UTC start | 1-min load start -> end | harness verdict | programs refused on a quiet machine / under load (NONDET-CANDIDATE) |
| --- | --- | --- | --- | --- |
| 1 ([`attempts/1-loaded-20261014T1352Z/`](attempts/1-loaded-20261014T1352Z/)) | 13:52:09 | 3.58 -> 10.58 | LOADED, not evidence | 9 / 9 |
| 2 ([`attempts/2-loaded-20261014T1359Z/`](attempts/2-loaded-20261014T1359Z/)) | 14:03:17 | 2.24 -> 8.26 | LOADED, not evidence | 2 / 16 |
| **3** ([`2026-10-14-efc47d3bc3e5/`](2026-10-14-efc47d3bc3e5/README.md)) | 14:15:14 | **1.97 -> 7.64** | **QUIET, clean, eligible** | 7 / 11 |

`python3 scripts/check_perf_ratchet.py --require-current` accepted attempt 3 as
current-source eligible evidence ([`logs/02-perf-ratchet-require-current.log`](logs/02-perf-ratchet-require-current.log))
and `--require-current --append` appended it
([`logs/13-perf-ratchet-require-current-append.log`](logs/13-perf-ratchet-require-current-append.log)):
the third `aarch64-apple-darwin` evidence row, compared like-with-like with the
`01fc13b13` and `80b0e03aa` rows (same host model, target and program set), with
no regression.

| Field | Value |
| --- | --- |
| results | `efc47d3bc3e5-20261014T142054Z.json` (retained with `outcomes.json`, `raw_samples.json` and `inventory.json`) |
| headline_eligible / ineligible_reasons | true / none |
| coverage | **0.0%**: 0 MATCH, 18 INCOMPLETE, 0 MISMATCH |
| gates | `G5` fail (0.0% of 80%); the other twelve unmeasured (every runtime, compile, size and RSS aggregate is null) |
| LLVM compile medians (`-O0`, `-O2`, `-O3`) | 0.302 to 0.352 s |
| certificate store (warm lane) | 11,315 certificates before and after (shared host state; context, not a result) |

**Why every program is INCOMPLETE.** Each is `[TCG-MIR-UNSUPPORTED]` caused by
`[TCG-PROOF-465]`: proof promotion rejects the emitted opcode inventory of the
required functions (`std::rt::lang_start`, `main`, the `FnOnce` shims,
`Termination::report`), `L07-P2`. Seven programs were refused twice on a quiet
machine. Eleven (`p1_xorshift` to `v3_popcount`, the second half of the run)
were refused twice with the first attempt above the 8.0 threshold (1-minute
load 8.13 to 19.49); their retries ran at 7.64 to 19.30, all but
`v3_popcount`'s (7.64) above it. The harness labels them NONDET-CANDIDATE, a
refusal under load that does not by itself establish completeness. For every one of them both
attempts reported the identical error, the harness found no solver timeout in
it (`err_is_solver_timeout: false`), and the refusal is an opcode-inventory
rejection, not a solver deadline. The row stays eligible by the harness's
preregistered start/end load rule, and the labels are in the row.

The `p3_gcd` probe ([`logs/00-refusal-example-p3_gcd.stderr.txt`](logs/00-refusal-example-p3_gcd.stderr.txt),
same backend and flags) shows what moved since `80b0e03aa`: its nine refused
functions now carry 14, 4, 3, 37, 1, 7, 3, 12 and 1 uncovered opcode rows (82,
across 22 distinct opcodes) against 10, 17, 7, 45, 6, 13, 2, 14 and 1 (115,
across 29) then. The frame-pair opcodes (`StpPreIndex`, `LdpPostIndex`) no longer
appear in it. Every refusal now names `AddRI` first (`RECONSTRUCTED Iadd_64 ->
AddRI (real-operand)`: "statistical sampling is not proof credit") or, in one
function, `MovI` ("no checked certificate"). No function of it compiles.

## 2. The diagnostic lane: the emitted code with proof certificates off

Command: `run.py --driver … --cold --bridge-cg-arg no-proof-certs --retain-dir diagnostic-no-proof-certs`
(step 04), on the same backend, from 14:54:42Z after a quiet wait. The load rose
from 3.90 to 12.46 during the run, so the harness also stamps it LOADED. Like
every run with a backend knob it is never evidence and never a ledger row
([`diagnostic-no-proof-certs/2026-10-14-efc47d3bc3e5/`](diagnostic-no-proof-certs/2026-10-14-efc47d3bc3e5/README.md)).
Ratios are taken within one run, so the load moves both lanes; absolute times
are not comparable across sessions ([`comparison/absolute-levels.txt`](comparison/absolute-levels.txt)).

18 of 18 MATCH, 0 MISMATCH (exit statuses with a full-width checksum folded in
mod 126: probabilistic).

| Axis | vs LLVM | 2026-09-29 run B (`80b0e03aa`, QUIET 3.29 -> 2.99) | **now** (`efc47d3bc`, 3.90 -> 12.46) |
| --- | --- | ---: | ---: |
| runtime geomean (wall, median of 5) | `-O3` | 0.950x | **0.926x** |
| runtime, resolvable rows only (9 now, 10 then) | `-O3` | 0.965x | 0.938x |
| scalar runtime geomean | `-O3` | 1.003x | 0.974x |
| worst program | `-O3` | 1.113x (`h3_box_leak`) | **1.020x** (`p6_branch_match`) |
| compile, warm | `-O2` / `-O3` | 1.238x / 1.225x | **1.030x / 1.026x** |
| compile, true cold | `-O2` | 3.957x | **3.366x** |
| emitted-code size geomean (worst) | `-O3` | not measured (results schema v1); 1.020x in the [2026-10-07 per-program record](../2026-10-01-darwin-runtime-per-program/README.md) | **1.016x** (2.072x, `p4_matmul`) |
| linked file size geomean (worst) | `-O3` | 1.0006x (1.0029x) | 0.9997x (1.0028x) |
| program peak RSS geomean | `-O3` | 0.999x | null: 15 of 18 programs peak at or below twice the sampler floor (gates.json version 4) |
| compiler peak RSS geomean | `-O2` / `-O3` | 1.197x / 1.196x | **1.218x / 1.217x** |

The informational gate check ([`logs/05-check-gates-diagnostic.log`](logs/05-check-gates-diagnostic.log),
never evidence): `G1a`, `G1b`, `G1c`, `G5`, `S1`, `S2` and `S3` pass; `G2-M1`
warm (1.030x, bound 1.00x) and cold (3.366x, bound 2.00x), `G2` end-state, `S4`
(1.016x, bound 1.00x) and `R2` (1.218x, bound 1.00x) fail; `R1` is unmeasured.

Program by program ([`comparison/diagnostic-vs-2026-09-29-B.md`](comparison/diagnostic-vs-2026-09-29-B.md)
holds the full table, with LLVM and bridge run medians and spreads):

| Program | runtime x `-O3` (09-29 B -> now) | warm x `-O2` | cold x `-O2` | emitted x `-O3` (bytes LLVM / bridge) | compiler RSS x `-O2` |
| --- | ---: | ---: | ---: | ---: | ---: |
| b1_mispredict | 1.017 -> 0.975 | 1.034 | 3.438 | 1.319 (564 / 744) | 1.226 |
| h1_vec_push_sum | 1.013 -> 0.996 | 1.012 | 3.340 | 0.868 (936 / 812) | 1.210 |
| h2_vec_grow | 0.996 -> 0.916 | 1.027 | 3.316 | 1.086 (940 / 1,021) | 1.210 |
| h3_box_leak | 1.113 -> 0.972 | 1.027 | 3.324 | 0.929 (956 / 888) | 1.208 |
| h4_vec_dropper | 0.848 -> 0.872 | 1.018 | 3.234 | 0.623 (1,412 / 880) | 1.209 |
| m1_call_chain | 0.937 -> 0.932 | 1.044 | 3.394 | 1.152 (396 / 456) | 1.220 |
| m2_call_heavy | 0.975 -> 0.915 | 1.028 | 3.359 | 1.057 (424 / 448) | 1.217 |
| p1_xorshift | 0.998 -> 0.964 | 1.019 | 3.130 | 0.902 (488 / 440) | 1.219 |
| p2_collatz | 0.997 -> 0.995 | 1.038 | 3.432 | 1.177 (384 / 452) | 1.218 |
| p3_gcd | 0.994 -> 1.001 | 1.031 | 3.312 | 1.147 (436 / 500) | 1.217 |
| p4_matmul | 1.002 -> 0.994 | 1.043 | 3.313 | 2.072 (984 / 2,039) | 1.229 |
| p5_struct_acc | 0.996 -> 0.889 | 1.025 | 3.184 | 1.120 (400 / 448) | 1.217 |
| p6_branch_match | 1.044 -> 1.020 | 1.040 | 3.551 | 1.206 (524 / 632) | 1.215 |
| p7_sieve | 0.803 -> 0.782 | 1.027 | 3.231 | 0.126 (9,248 / 1,166) | 1.223 |
| p8_closure_nest | 0.991 -> 0.978 | 1.009 | 3.237 | 1.131 (396 / 448) | 1.213 |
| v1_saxpy | 0.740 -> 0.791 | 1.027 | 3.442 | 1.280 (656 / 840) | 1.224 |
| v2_memfill | 0.998 -> 0.969 | 1.064 | 3.624 | 1.571 (420 / 660) | 1.222 |
| v3_popcount | 0.743 -> 0.773 | 1.029 | 3.796 | 1.549 (568 / 880) | 1.220 |

Reading it: every program's runtime is at or below 1.02x LLVM `-O3`, and the
largest movers since `80b0e03aa` are the ones the 2026-10-07 per-program work
changed (`p5_struct_acc` 0.996x -> 0.889x, `h2_vec_grow` 0.996x -> 0.916x,
`m2_call_heavy` 0.975x -> 0.915x). The warm compile ratio fell from 1.24x to
1.03x: the bridge's warm geomean went from 0.395 s to 0.338 s while LLVM `-O2`
went from 0.319 s to 0.328 s (the warm-path work of 2026-10-01, `L14-P5`).
Cold minus warm is 0.767 s per compile (0.868 s then). Compiler peak RSS rose
from 1.197x to 1.218x `-O2`.

## 3. Load-robust companion (diagnostic lane)

Command: [`commands/loadrobust.py`](commands/loadrobust.py) (step 14), 15:33:00Z
to 15:36:47Z. For each program, after one unmeasured warmup compile per lane,
five interleaved rounds of LLVM `-O2`, LLVM `-O3` and the bridge's
`no-proof-certs` `-O3` compile under `/usr/bin/time -l`, then one warmup run and
eleven interleaved rounds of the LLVM `-O3` and bridge binaries. Instructions
retired and cycles do not move (instructions) or move little (cycles) with load;
the load rose from 3.9 to 25.4 during the step and is listed per program
([`loadrobust.json`](loadrobust.json)). Every exit status equals the manifest's.

| Measure (geomean over 18 programs, bridge diagnostic `-O3`) | vs LLVM `-O2` | vs LLVM `-O3` |
| --- | ---: | ---: |
| compiler instructions retired (the `trustc` process; the bridge runs in it, its AY/Clean children do not count) | **1.185x** | 1.179x |
| compile CPU, user+sys including every child (median) | 1.518x | 1.512x |
| compiler peak RSS (median) | 1.216x | 1.217x |
| compile wall (median; load 3.9 to 25.4) | 1.021x | 1.018x |
| program cycles, minimum / median | | **0.916x** / 0.919x |
| program instructions retired | | 1.086x |
| program wall, minimum (load as above) | | 0.927x |

Per program:

| Program | compiler instructions x `-O2` | CPU x `-O2` | compiler peak RSS x `-O2` | runtime cycles x `-O3` (min / median) | runtime instructions x `-O3` | 1-min load |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| b1_mispredict | 1.189 | 1.564 | 1.225 | 0.972 / 0.972 | 1.185 | 3.9-4.0 |
| h1_vec_push_sum | 1.181 | 1.512 | 1.209 | 0.986 / 0.996 | 1.102 | 3.9-4.0 |
| h2_vec_grow | 1.184 | 1.525 | 1.209 | 0.887 / 0.897 | 0.962 | 3.9-3.9 |
| h3_box_leak | 1.182 | 1.550 | 1.209 | 1.001 / 0.990 | 0.959 | 4.2-4.2 |
| h4_vec_dropper | 1.174 | 1.550 | 1.208 | 0.837 / 0.841 | 0.972 | 4.2-4.4 |
| m1_call_chain | 1.185 | 1.488 | 1.214 | 0.931 / 0.931 | 1.087 | 4.4-4.5 |
| m2_call_heavy | 1.186 | 1.500 | 1.216 | 0.911 / 0.917 | 0.654 | 4.5-4.6 |
| p1_xorshift | 1.172 | 1.439 | 1.217 | 0.963 / 0.965 | 1.992 | 4.6-6.0 |
| p2_collatz | 1.181 | 1.487 | 1.215 | 0.999 / 0.999 | 1.139 | 6.0-6.2 |
| p3_gcd | 1.184 | 1.513 | 1.214 | 1.000 / 1.000 | 1.189 | 6.1-6.4 |
| p4_matmul | 1.192 | 1.500 | 1.223 | 1.005 / 1.004 | 1.076 | 6.5-6.5 |
| p5_struct_acc | 1.180 | 1.487 | 1.214 | 0.889 / 0.888 | 1.099 | 6.5-14.0 |
| p6_branch_match | 1.193 | 1.561 | 1.216 | 1.011 / 1.024 | 1.218 | 15.0-23.9 |
| p7_sieve | 1.176 | 1.500 | 1.223 | 0.782 / 0.793 | 0.977 | 23.9-24.4 |
| p8_closure_nest | 1.178 | 1.475 | 1.213 | 0.999 / 0.999 | 1.197 | 23.1-25.4 |
| v1_saxpy | 1.195 | 1.512 | 1.225 | 0.738 / 0.737 | 1.653 | 21.8-23.1 |
| v2_memfill | 1.198 | 1.564 | 1.222 | 0.987 / 0.988 | 1.140 | 19.7-21.8 |
| v3_popcount | 1.201 | 1.600 | 1.222 | 0.688 / 0.693 | 0.617 | 18.6-19.7 |

In cycles, 11 programs are below 0.99x LLVM `-O3` on both statistics
(`b1`, `h2`, `h4`, `m1`, `m2`, `p1`, `p5`, `p7`, `v1`, `v2`, `v3`); six are
within 1% of parity on at least one (`h1_vec_push_sum` 0.986x / 0.996x,
`h3_box_leak`, `p2_collatz`, `p3_gcd`, `p8_closure_nest`, and `p4_matmul` at
1.005x / 1.004x); `p6_branch_match` is slower (1.011x / 1.024x). That agrees
with the 2026-10-07 record's reading of its branch (0.918x cycles,
`p6_branch_match` slower), which `main` now contains. The compiler
retires 18.5% more instructions than LLVM `-O2` on these 12-to-40-line
programs (4.80 G against 4.05 G per compile, geomean), and the whole tree
uses 1.52x LLVM's CPU because the certificate replays and custody digests run
on other threads and in child processes (`L14-P5`).

## 4. Scaling (proofs off in both harnesses)

`python3 benchmarks/beat-llvm/scale_gate.py --driver … --rss` (step 06,
15:42:48Z to 15:43:28Z, 1-minute load 4.50 to 4.75): wall time min-of-5 and peak
RSS min-of-3, lanes interleaved, `-O3`, the trust-cg lane with `no-proof-certs`
([`logs/06-scale-gate-rss.log`](logs/06-scale-gate-rss.log)).

| Crate | Lines | LLVM | trust-cg | Time: 09-29 -> now | trust-cg RSS: 09-29 -> now | Memory: 09-29 -> now |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 355 | 0.332 s | 0.353 s | 1.21x -> **1.06x** | 168.0 -> 167.4 MiB | 1.22x -> 1.22x |
| medium | 2,805 | 0.444 s | 0.495 s | 1.21x -> **1.11x** | 204.2 -> 179.8 MiB | 1.39x -> 1.22x |
| large | 11,205 | 0.825 s | 0.972 s | 1.25x -> **1.18x** | 301.9 -> 248.6 MiB | 1.51x -> 1.24x |
| xlarge | 33,605 | 1.868 s | 2.128 s | 1.26x -> **1.14x** | 546.3 -> 456.4 MiB | 1.46x -> **1.23x** |

`python3 benchmarks/compile-scaling/run.py --driver … --out-dir <scratch>` (step
07, 15:43:28Z to 15:44:06Z, load 4.46 to 4.75): CPU time, median-of-3, `-O2`,
`no-proof-certs` and `refine-solver=0`
([`logs/07-compile-scaling.log`](logs/07-compile-scaling.log)).

| Shape | Sizes | LLVM exponent | trust-cg exponent | Excess: 09-29 -> now | Ratio at largest: 09-29 -> now |
| --- | --- | ---: | ---: | ---: | ---: |
| blocks | 100 to 800 | 0.13 | 0.12 | +0.01 -> -0.01 | 1.39x -> 1.35x |
| loops | 15 to 120 | 0.13 | 0.25 | +0.18 -> +0.12 | 2.08x -> 1.86x |
| funcs | 50 to 400 | 0.12 | 0.12 | +0.07 -> +0.00 | 1.64x -> 1.42x |
| arraysize | 4,096 to 262,144 B | -0.01 | 0.01 | -0.01 -> +0.01 | 1.42x -> 1.45x |

Verdict "OK: no shape grows materially faster than LLVM" (limit 0.6). `loops` is
still the steepest shape (1.86x LLVM's CPU at 120 loops). Both ladders are
proofs-off: the certificates-on lane refuses their crates too (section 6), so no
proofs-on wall-time or RSS ladder exists (`L14-P6`).

## 5. Compile-time canary and determinism sentinel

- `scripts/compile_time_canary.sh --driver …` (step 08): exit 1, `canary: GATE
  RED: bridge failed to compile the pinned canary program`, `[TCG-PROOF-465]`.
  No compile time was measured.
- `scripts/compile_determinism_sentinel.sh 5 --driver …` (step 09, cold, a fresh
  `XDG_CACHE_HOME` per attempt): exit 2, DETERMINISTIC-FAILCLOSED, 5 of 5
  attempts fail closed (load 4.37 at the end). The sentinel program's `main`
  alone carries 72 uncovered opcode rows across 31 opcodes, led by `AddRI`.

## 6. L14-P7: the larger corpus, proofs-on

Command: `python3 benchmarks/real-corpus/run.py --driver <trust 9192>/bin/trustc --diagnostic-lane --trust-checkout <trust checkout> --work-dir <scratch> --out-dir l14p7-real-corpus/real-corpus`
(campaign step 10, run with [`l14p7-real-corpus/`](l14p7-real-corpus/) as its
campaign directory so the run's own logs touch no tracked file). It measured
`7fe6e3c25` (the ledger-row commit: `efc47d3bc` plus the ledger row and this
record; the same backend, sha256 `55cc7f2f…`) from a clean tree, 15:45:57Z to
18:01:58Z. The corpus is `l14-real-corpus` version 1.0.0 (62 rows, manifest
sha256 `e8883a23acd04082…`), committed in `efc47d3bc` before any of its rows
was measured proofs-on; only a four-row development run on a loaded host
preceded it, outside the tree. The Trust checkout holds the driver's revision
`321aaeda7`, whose `library/` tree is the manifest's `fbda2d97…`, so every input
was available and matched its digest. N = 3 compiles and 5 runs per lane.
The harness that ran is the one at `efc47d3bc`. A later commit (`546bc0e4f`)
makes a harness fault on one row an ERROR row instead of the end of the run, a
path this run never reached. The review round-1 commit (`9723e56c9`) changes
how library rows are scored: a library compile that exits 0 without writing a
readable object is now an ERROR row (the LLVM lane's a BASELINE-FAILED row),
and a library whose LLVM object holds no code is flagged vacuous. This run
counted four such no-object compiles as COMPILED; the re-scored figures below
apply the new rules to its retained samples.

**How the 27 crates were chosen.** They are a convenience sample, hand-picked
from the crates that meet the manifest's rule (in the Trust compiler's
`Cargo.lock` at that version, no build script, no required dependency) before
any proofs-on measurement of them, by no further written criterion: neither
random nor exhaustive. Applying the rule with the harness's own `crate_plan`
([`commands/qualifying_crates.py`](commands/qualifying_crates.py),
[`l14p7-real-corpus/qualifying-crates.tsv`](l14p7-real-corpus/qualifying-crates.tsv))
gives 189 qualifying crates on this host (607 packages checked: 274 need a
dependency, 81 have a build script, 35 are proc-macros, 28 archives are not
cached); all 27 are among them. Every crate-level rate and ratio below
describes these 27 only. Manifest version 1.0.1 states this in its
`selection_rules` and changes no row.

**Not evidence.** The run is clean, current, complete and quiet at its start
(4.21) and end (7.92), but 27 of its 62 rows started or ended above the 8.0
threshold (load up to 41.6 from other agents' builds), and the harness
therefore names it ineligible. While the `core` `-O0` row ran, this session's
`must_refuse_corpus` and `tippy` gates ran at `nice 19`. The proofs-on
outcomes below are refusals whose content did not depend on load in this
run: every one of the 56 refused rows reported the same named codes and the
same first error on both attempts, 33 of them on rows that started and ended
quiet. The compile and runtime ratios are wall time and counters under that
load.

**Production (certificates-on) lane: none of the 57 rows with code completes.**
Five rows (`either`, `fnv`, `rustc-hash`, `scopeguard`, `unicode-ident`) are
vacuous: library crates whose LLVM `-O3` object holds 0 bytes of code. As run,
the harness counted all five as COMPILED (5 of 62, 8.1%), but the production
lane wrote no object for four of them and 16 code bytes for `unicode-ident`.
Under the round-1 rules ([`l14p7-real-corpus/rescored-object-rule.md`](l14p7-real-corpus/rescored-object-rule.md),
from [`commands/rescore_object_rule.py`](commands/rescore_object_rule.py) over
the retained samples) those four are ERROR rows, which leaves **1 of 62 (1.6%),
vacuous, and 0 of the 57 rows with code (every program and every library
whose LLVM object holds code)**. A six-row check with the round-1 harness and
the same backend (sha256 `55cc7f2f…`, [`l14p7-real-corpus/round1-object-rule-check/`](l14p7-real-corpus/round1-object-rule-check/),
a subset on a loaded host, not evidence) reproduces it: both lanes exit 0 and
write no object for the four crates (ERROR, "the compile exited 0 but wrote no
object"), and `unicode-ident` is COMPILED and vacuous.

| kind | rows | production complete: as run / re-scored | diagnostic (`no-proof-certs`) complete: as run / re-scored |
| --- | ---: | ---: | ---: |
| real-program (bridge guests, `-O3`, run) | 13 | 0 / 0 | 13 / 13 (13 MATCH) |
| real-crate (crates.io, `-O3`, compile) | 27 | 5 / 1 (all vacuous) | 12 (5 vacuous) / 8 (1 vacuous) |
| trust-sysroot (`library/core` at `321aaeda7`) | 2 | 0 / 0 | 1 / 1 (`-O0`) |
| scale-ladder (`scale_gate`, `compile-scaling`, run) | 20 | 0 / 0 | 20 / 20 (20 MATCH) |
| **total** | **62** | **5 (8.1%) / 1 (1.6%)** | **46 (74.2%) / 42 (67.7%)** |

Production outcomes (re-scored): 56 INCOMPLETE, every one
`[TCG-MIR-UNSUPPORTED]` with `[TCG-PROOF-465]` among its causes (`L07-P2`),
1 TIMEOUT (`core` at `-O0`, killed at the manifest's 3,600 s; the retained
stderr tail holds only its last "emitted immutable data static" lines and no
rusage, so this record does not show where that time went), 4 ERROR (no
object), 0 MISMATCH, 0 BASELINE-FAILED, 0 UNAVAILABLE. The production lane's
time to refusal ranges from 0.5 s (`arrayvec`) to 549 s (`regex-syntax`,
58,528 lines), against 0.27 to 2.8 s for LLVM's whole compile of the same
crate; this record did not profile how that time divides between the
compiler process and the solver and checker processes it starts.

The diagnostic lane names the refusals that remain once the proof gate is off,
in 16 rows (15 crates and `core` at `-O3`), every one `[TCG-MIR-UNSUPPORTED]`:
typed causes `[TCG-COLLECTION-IMAGE]` (6 rows), `[TCG-POINTEE-LANES]` (5),
`[TCG-OWNING-ITER-METHOD]` (3), `[TCG-ARG-ABI]`, `[TCG-RET-ABI]`,
`[TCG-SRET-ABI]`, `[TCG-FMT-DECLINED]`, `[TCG-IR-LOWER]`, `[TCG-ITER-UNMODELED]`
(2 each), `[TCG-BOX-PAYLOAD-DROP]`, `[TCG-FAT-POINTEE-LANE]` and
`[TCG-STEPBY-OPT-LEVEL]` (1 each), and untyped MIR shapes such as a transmute
into a memory array (`fastrand`), the `simd_extract` intrinsic of a NEON helper
(`hashbrown`), a place projection (`unicode-width`) and an `&raw` of a
dereferenced reference (`core` at `-O3`, `Ipv6Addr`'s `Display`). These are
lowering gaps of real crates (`aho-corasick`, `regex-syntax`, `memchr`, `glob`,
`heck`, `strsim`, `termcolor`, `percent-encoding`, `fastrand`, `foldhash`,
`hashbrown`, `minimal-lexical`, `same-file`, `unicode-segmentation`,
`unicode-width`) that the 18-program corpus never reaches. The production lane
also names `[TCG-REGALLOC-063]` in four rows (`p04_matmul`, `adler2`,
`regex-syntax`, `core` at `-O3`), two of which the diagnostic lane compiles.

**Diagnostic-lane ratios over its completed rows** (never evidence; under the
load stated above). As run, over 46 rows; re-scored, over the 42 that wrote
their object:

| ratio vs LLVM (same opt level) | geomean, as run (46) | geomean, re-scored (42) | worst |
| --- | ---: | ---: | ---: |
| compile wall | 1.314x | 1.352x | 30.1x (`siphasher`) |
| compiler instructions retired | 1.419x | 1.449x | 8.85x (`siphasher`) |
| compile CPU including children | 1.914x | 1.961x | 26.4x (`siphasher`) |
| compiler peak RSS | 1.190x | 1.208x | 1.29x (`scale_gate` large) |
| program cycles (33 run rows) | 1.011x | 1.011x | 1.348x (`scale_gate` xlarge) |
| program instructions retired | 1.008x | 1.008x | 1.177x |
| library code bytes (8 non-vacuous rows) | null (vacuous rows) | 4.902x | 75.8x (`siphasher`) |

- **Compile cost grows with real code.** `library/core` at `-O0` compiles in the
  diagnostic lane at 8.38x LLVM's wall time (43.0 s against 5.14 s),
  4.78x its instructions (336 G against 70 G) and 1.03x its peak RSS, and emits
  2.91x its code bytes (1,141,352 against 391,720). `siphasher` (30.1x wall,
  8.85x instructions, 75.8x code bytes: 10,304 against 136) and `adler2` (10.7x,
  1.67x, 5.19x) show the same pattern: the bridge's library object holds far
  more code than LLVM's `-O3` object of the same crate. The `scale_gate` crates
  read 1.05x to 1.10x wall but 1.26x to 2.23x instructions: the backend spends
  about twice LLVM's instructions on the 33,605-line crate and hides it behind
  parallel codegen units.
- **Runtime ratios here are not code-quality results.** Every one of the 33 run
  rows finishes in 3 to 6 ms, so process start dominates its cycles, far below
  the 50 ms the beat-llvm harness requires before it calls a runtime ratio
  resolvable. `scale_gate` xlarge reads 1.35x cycles (7.0 M against 5.2 M) with a
  larger binary; that is a start-up cost, not attributed here.
- **The library code-size column is a backend difference, not noise:** the
  object sizes are deterministic, and all 8 non-vacuous library rows the
  diagnostic lane compiled (7 crates and `core` at `-O0`) emit 1.4x to 76x
  LLVM's code bytes
  ([`l14p7-real-corpus/tables.md`](l14p7-real-corpus/tables.md)).

Per-row results: [`l14p7-real-corpus/tables.md`](l14p7-real-corpus/tables.md)
(from [`commands/real_corpus_tables.py`](commands/real_corpus_tables.py)) and the
harness's own [`l14p7-real-corpus/real-corpus/7fe6e3c25532-20261014T180158Z.md`](l14p7-real-corpus/real-corpus/7fe6e3c25532-20261014T180158Z.md);
every sample, attempt, first error and stderr tail is in the results JSON beside it.

## Eligibility rules applied

Nothing here is evidence unless every rule of its harness holds; each result
file names the rules a run fails in `ineligible_reasons`.

**The ledger row (`benchmarks/beat-llvm/run.py`, metrics-contract.md "Eligibility",
gates.json version 4).** A row is evidence only when: the tree has no tracked edit
at a full revision (untracked files are recorded, not disqualifying); the backend
is no older than its build inputs; no proof-weakening `TCG_*` variable and no
backend knob; the 1-minute load is at most ncpu/2 = 8.0 at the start and the end
(threshold not overridden); no runaway process; exactly the 18-program contract
corpus at the contract N (3 compiles, 5 runs, 5 peak-RSS samples); 0 MISMATCH;
complete size and RSS readings and a calibrated RSS sampler; an independent proof
checker (Clean) that runs when probed and no DEGRADED bridge compile; complete
provenance. `check_perf_ratchet.py --require-current` additionally requires that
the results were measured at the checkout's HEAD from a tree without tracked
edits and that the checkout still has none, and the append compares the row only
with evidence rows of the same host model, target and program set.

**Comparability.** The two earlier `aarch64-apple-darwin` rows (`01fc13b13`,
`80b0e03aa`) used the same host, the same driver (Trust package 9192, `trustc`
`321aaeda7`, explicit unverified frontend lane), the same harness modes and flags
and the same program set, so this row is like-with-like with them and the
ratchet compared it with them. The 22 `aarch64-unknown-linux-gnu` rows were
measured on another host with the retired stock-nightly driver; they are not
baselines for this row, and whether Trust-driver rows may ever be compared with
that lineage is an open owner decision (`L14-P1` note).

**The diagnostic lane** (`--bridge-cg-arg no-proof-certs`) fails the knob rule by
construction. It is never evidence and never a ledger row. Its ratios describe the
code the backend emits with the proof gate off.

**The larger corpus (`benchmarks/real-corpus/run.py`).** The rules are in
[its README](../../../benchmarks/real-corpus/README.md#measurement-and-eligibility):
the beat-llvm rules above where they apply (clean tree, current backend, no
`TCG_*`, quiet start and end, no runaway, whole manifest, N >= 3 compiles and 5
runs, no MISMATCH, a runnable checker, no DEGRADED compile), plus: every row must
start and end quiet, and every input must be available and match its manifest
digest. Since review round 1 the harness also requires the committed manifest
at HEAD (path and bytes), a backend that loaded in every bridge compile, and a
known outcome for every row, and a library row completes only when every
compile wrote a readable object. An eligible run is evidence for that corpus
only and feeds no ratchet.

## Residuals and what this does not establish

- **No proof-enabled ratio exists on this host.** The ledger row and both corpora
  measure the refusal. Runtime, compile, size and memory superiority claims need a
  certificates-on lane that compiles the corpus (`L07-P2`), then the `G1`/`G2`/
  `S3`/`S4`/`R2` gates on an eligible row.
- **Linux AArch64.** No Linux row was measured at this revision. The Linux host
  (`spark-d5a4`) is not reachable from this Mac: `ssh -o BatchMode=yes` fails host
  key verification, and there is no configured route. The Linux ledger lineage
  (22 rows, last `5bfe67a2f`, stock-nightly driver) stays historical, and its
  comparability with Trust-driver rows is an open owner decision.
- **Proofs-on scaling (`L14-P6`).** Both scaling harnesses run proofs off, and the
  larger corpus's ladder rows show why a proofs-on ladder cannot be read yet:
  every ladder crate is refused (`[TCG-PROOF-465]`), in 1.5 to 10.4 s.
- **The larger corpus feeds no ratchet** and has no preregistered pass predicate.
  Version 1.0.0 fixed its rows and digests, and 1.0.1 only states how its 27
  crates were sampled; a later version adds rows (for example the other 162
  qualifying crates) and keeps these. `core` rows need a Trust checkout at the driver's revision, and the
  crate rows need the crates.io archives in the local Cargo registry cache (the
  harness verifies each digest, so another host either reproduces the input or
  reports it UNAVAILABLE). TY and model-checker workloads are not in it
  (`L14-P4`).
- **Load.** The host was shared throughout; the harness eligibility rules were
  applied as written, and every wall-clock figure is given with its load.
  Instructions retired, cycles and byte counts are the load-robust readings.
- **Core pinning.** macOS offers no `sched_setaffinity`; lanes are unpinned on a
  host with performance and efficiency cores (stamped in provenance).

## Files

- `2026-10-14-efc47d3bc3e5/`: the harness record of the eligible evidence run
  (attempt 3), which the ledger row names as `retained_dir`.
- `attempts/`: the two LOADED evidence attempts, each with its harness record
  and logs.
- `diagnostic-no-proof-certs/2026-10-14-efc47d3bc3e5/`: the harness record of the
  diagnostic lane (not a ledger row).
- `loadrobust.json`: the load-robust companion's samples and summary.
- `l14p7-real-corpus/`: the larger corpus run's campaign directory: the
  results JSON and markdown under `real-corpus/`, `tables.md`, its logs and load
  record; `rescored-object-rule.json`/`.md` (the round-1 rules over the retained
  samples), `round1-object-rule-check/` (the six-row check with the round-1
  harness) and `qualifying-crates.tsv` (the crate population).
- `comparison/`: [`commands/compare.py`](commands/compare.py) and
  [`commands/absolutes.py`](commands/absolutes.py) output against the 2026-09-29
  re-measure's diagnostic run B.
- `logs/`: every step's output, `steps.log`, `evidence-attempts.log`, the bridge
  build summary and the `p3_gcd` refusal example.
- `load.tsv`, `load-wait.tsv`, `load-before.txt`, `load-after.txt`: the load
  record. `host.txt`: host identity, Trust package, Clean candidates, C
  toolchain, linker, SDK, Python, and the backend's hash and build command.
- `commands/`: `build_bridge.sh`, `campaign.sh`, `sequence.sh`, `sequence2.sh`,
  `sequence3.sh`, `evidence_until_quiet.sh`, `wait_quiet.py`, `hostinfo.sh`,
  `probe.sh`, `loadrobust.py`, `real_corpus_tables.py`, `compare.py`,
  `absolutes.py`, `rescore_object_rule.py`, `qualifying_crates.py`, and
  `make_manifest.py`, which generated the corpus manifest's version 1.0.0 (it
  rewrites `efc47d3bc`'s `benchmarks/real-corpus/manifest.json` byte for byte on
  this host; version 1.0.1 was edited from it by hand and changes only
  `selection_rules` and `revisions`).
