# First aarch64-apple-darwin performance campaign: the production bridge refuses 18 of 18

Ledger rows `L14-P8` and `X-DARWIN-P8`. This is the first performance measurement of
the Darwin arm64 target. It ran on an Apple M4 Max (`Mac16,5`, 12 performance and 4
efficiency cores, 48 GiB) under macOS 26.6.2 (`25G83`), on AC power with low-power
mode off. It measured revision `01fc13b13608` from a clean tree. That revision is
`main` `9fc0c2bb4` plus the scaling-gate target commit. Its compiler crates are
identical to `main`'s, and so is the backend they build.

All lanes ran one after another between 13:41:59Z and 13:52:33Z, with nothing else
running. The 1-minute load ranged from 1.15 to 2.09 on 16 CPUs, and the harness's
quiet threshold is 8.0. Per-step load is in [`load.tsv`](load.tsv), with full
snapshots in [`load-before.txt`](load-before.txt) and
[`load-after.txt`](load-after.txt). Host identity and toolchain versions are in
[`host.txt`](host.txt), and every command is in [`commands/`](commands/).

## Summary

| What | Result |
| --- | --- |
| Ledger row (evidence mode, `run.py --cold`) | Appended. `evidence: true`, QUIET, clean. **Coverage 0.0%: 0 of 18 MATCH, 18 INCOMPLETE, 0 MISMATCH.** Every program fails closed with `[TCG-PROOF-465]`. |
| Gates on that row | `G5_coverage_M6` **fail** (0.0% measured, 80% required). The other ten gates are **unmeasured**: with no MATCH row, every runtime, compile, size and RSS aggregate is null. None passes. |
| Diagnostic lane (`--bridge-cg-arg no-proof-certs`, never evidence) | 18 of 18 MATCH. Runtime geomean 1.267x LLVM `-O3` (scalar 1.010x, worst 8.868x `p4_matmul`). Warm compile 1.367x `-O2`, cold 4.263x `-O2`. Linked size 1.0006x. Compiler peak RSS 1.188x `-O2`. |
| Crate-size scaling (`scale_gate.py --rss`, proofs off) | Time 1.38x, 1.57x, 3.25x and **12.14x** LLVM; peak RSS 1.23x, 1.65x, 4.57x and **25.35x** (**9.45 GB** at 33,605 lines). A repeat gave 12.22x and 25.12x. The growth is roughly quadratic. |
| Per-shape exponents (`compile-scaling/run.py`, proofs off) | All four shapes are within the gate's excess limit of 0.6: blocks +0.02, loops +0.28, funcs +0.14, arraysize +0.00. |
| Compile-time canary | **GATE RED** (exit 1). The production bridge fails closed on the pinned program, so no time was measured. |
| Determinism sentinel (cold, N=5) | **DETERMINISTIC-FAILCLOSED** (exit 2): 5 of 5 attempts fail closed, in 1.36 to 1.51 s each. There is no verdict flap. |

No superiority claim and no gate pass follows from this campaign. The one evidence row
records that the production lane compiles none of the corpus on this host at this
revision. The diagnostic numbers describe the code the backend emits with its proof
gate off. They are not a ledger row and they are not evidence, as
`benchmarks/beat-llvm/contract` states for any backend knob.

## 1. Evidence mode: the ledger row

Command: `python3 benchmarks/beat-llvm/run.py --driver <trust 9192>/bin/trustc --cold --retain-dir <this directory>`

This is the harness's evidence mode: the full 18-program contract corpus at the
contract N (3 compiles, 5 runs), the production backend configuration with no knob and
no `TCG_*` variable, and the warm and true-cold lanes. The target is the driver's host,
`aarch64-apple-darwin` (`target_selection: driver host`). The harness retained the raw
evidence in [`2026-09-28-01fc13b13608/`](2026-09-28-01fc13b13608/README.md).
`python3 scripts/check_perf_ratchet.py --require-current --append` accepted the file as
current, eligible evidence. There is no earlier evidence row for this host and target,
so the regression check reported SKIPPED and this row becomes the first baseline.

| Field | Value |
| --- | --- |
| results | `01fc13b13608-20260928T134336Z.json` |
| headline_eligible / ineligible_reasons | true / none |
| load before / after / threshold | 1.29 / 1.66 / 8.0 (QUIET) |
| backend | `target-bridge/release/librustc_codegen_trust_cg.dylib`, sha256 `8fb063d31d9d4261…`, built from this tree by `targo --unverified build --release --locked` (see [`logs/00-bridge-build-summary.txt`](logs/00-bridge-build-summary.txt)) |
| driver | Trust package 9192, `trustc` commit `321aaeda75478038420d97830f14724c33c8dc39` (1.99.0-dev, LLVM 22.1.2), explicit unverified frontend lane `-Ztrust-verify=off` |
| independent checker | managed Clean 8606 (`clean 0.9.0`) ran when probed. The package's own `bin/clean` also runs, but the backend skipped it because it lacks `carcara-verify` (`X-HOST-P8`). No compile printed `verification is DEGRADED`. |
| RSS sampler | `getrusage` wrapper. Its floor is 1,261,568 B, and it agrees with `/usr/bin/time -l` (82,362,368 vs 82,411,520 B). |
| certificate store (warm lane) | 466 certificates before, 479 after |

**Why every program is INCOMPLETE.** Every refusal names `[TCG-PROOF-465]`: proof
promotion rejects the emitted opcode inventory, and the bridge then refuses the required
functions (`std::rt::lang_start`, the program's `main`, the `FnOnce` shims and
`Termination::report`). [`logs/00-refusal-example-p3_gcd.stderr.txt`](logs/00-refusal-example-p3_gcd.stderr.txt)
holds the full stderr for `p3_gcd`, from the same backend and command line as the lane.
It lists 29 distinct AArch64 opcodes, among them `StpPreIndex`, `LdpPostIndex`, `AddRI`,
`Bl`, `Movz`, `Movk`, `Madd`, `UDiv` and `Msub`. Two kinds of evidence are refused as
proof credit:

- "statistical sampling is not proof credit": a reconstructed `StpPreIndex` found no
  counterexample in 100,000 samples, and a test is not a proof;
- "registry name lookup is not proof credit": `Movz` and `TailCall` select a theorem
  by name rather than by an obligation built from the instruction.

This is the refusal class the Linux canary and sentinel reached at `159f53415`
(ledger `L07-P2`). It is a completeness gap in proof evidence, not a load effect: the
machine stayed quiet, the retry after each refusal failed the same way, and the
sentinel's five cold attempts all refused. The load at each refusal was 1.14 to 1.82.

What the row does measure is the LLVM lanes. Every compile median is between 0.286 and
0.328 s at `-O0`, `-O2` and `-O3`, dominated by the link. The raw samples are in
`raw_samples.json`.

## 2. Diagnostic lane: the emitted code with proof certificates off

Command: `run.py --driver … --cold --bridge-cg-arg no-proof-certs --retain-dir diagnostic-no-proof-certs`

The harness marks this run ineligible for one reason: `non-default backend knobs
['no-proof-certs'] (diagnostic lane)`. The ratchet rejects the knob outright, so this
run is **not a ledger row**. Load was 1.66 before and 1.80 after (QUIET), on the same
tree and backend. It is retained in
[`diagnostic-no-proof-certs/2026-09-28-01fc13b13608/`](diagnostic-no-proof-certs/2026-09-28-01fc13b13608/README.md).

Coverage was 100%: 18 MATCH, 0 MISMATCH, 0 NONDET. A MATCH compares exit codes, with a
full-width checksum folded in mod 126, so it is probabilistic.

| Axis | vs LLVM | Value | Gate (informational, never evidence) |
| --- | --- | ---: | --- |
| runtime geomean | -O3 | 1.2668x | G1c needs < 1.00x and worst <= 1.50x: fail |
| runtime, resolvable rows only (10 programs) | -O3 | 0.9692x | not gated |
| scalar runtime geomean | -O3 | 1.0101x | G1a <= 1.30x: pass |
| worst program (`p4_matmul`) | -O3 | 8.868x | G1b <= 2.0x per vectorizable kernel: fail |
| compile, warm | -O2 / -O3 | 1.3674x / 1.3577x | G2-M1 <= 1.00x: fail; end-state < 1.00x: fail |
| compile, true cold | -O2 | 4.2630x | G2-M1 cold <= 2.00x: fail |
| linked size geomean (worst) | -O3 | 1.00060x (1.00286x) | S1 <= 1.10x: pass; S2 <= 1.00x: fail |
| program peak-RSS geomean | -O3 | 0.9988x | R1: unmeasured (15 of 18 programs are floor-bound) |
| compiler peak-RSS geomean | -O2 / -O3 | 1.1876x / 1.1872x | R2 <= 1.00x: fail |

| Category | match/total | runtime geomean x |
| --- | ---: | ---: |
| multifn | 2/2 | 0.953 |
| branch | 1/1 | 1.007 |
| scalar | 6/6 | 1.010 |
| vectorizable | 5/5 | 1.553 |
| heap | 4/4 | 1.684 |

| Program | Category | LLVM -O3 run (s) | Bridge run (s) | Runtime x | Warm x -O2 | Cold x -O2 | Size x | Compiler RSS x -O2 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| b1_mispredict | branch | 0.1811 | 0.1825 | 1.007 | 1.406 | 4.281 | 1.0029 | 1.190 |
| h1_vec_push_sum | heap | 0.0087 | 0.0443 | 5.100 | 1.356 | 4.184 | 1.0020 | 1.185 |
| h2_vec_grow | heap | 0.0126 | 0.0143 | 1.142 | 1.355 | 4.206 | 1.0019 | 1.183 |
| h3_box_leak | heap | 0.0179 | 0.0253 | 1.412 | 1.350 | 4.210 | 1.0019 | 1.183 |
| h4_vec_dropper | heap | 0.0166 | 0.0163 | 0.977 | 1.371 | 4.261 | 1.0020 | 1.182 |
| m1_call_chain | multifn | 0.0887 | 0.0828 | 0.933 | 1.351 | 4.321 | 1.0027 | 1.186 |
| m2_call_heavy | multifn | 0.0583 | 0.0567 | 0.973 | 1.380 | 4.303 | 1.0025 | 1.186 |
| p1_xorshift | scalar | 0.5392 | 0.5429 | 1.007 | 1.348 | 4.162 | 1.0027 | 1.186 |
| p2_collatz | scalar | 0.1936 | 0.1940 | 1.002 | 1.327 | 4.177 | 1.0026 | 1.187 |
| p3_gcd | scalar | 0.3277 | 0.3266 | 0.997 | 1.362 | 4.229 | 1.0026 | 1.183 |
| p4_matmul | vectorizable | 0.0293 | 0.2596 | 8.868 | 1.366 | 4.227 | 1.0028 | 1.195 |
| p5_struct_acc | scalar | 0.6031 | 0.6036 | 1.001 | 1.348 | 4.159 | 1.0027 | 1.190 |
| p6_branch_match | scalar | 1.4533 | 1.5319 | 1.054 | 1.404 | 4.414 | 1.0028 | 1.193 |
| p7_sieve | vectorizable | 0.0197 | 0.0162 | 0.820 | 1.346 | 4.139 | 0.9682 | 1.195 |
| p8_closure_nest | scalar | 0.1817 | 0.1819 | 1.001 | 1.355 | 4.179 | 1.0028 | 1.188 |
| v1_saxpy | vectorizable | 0.0514 | 0.0387 | 0.753 | 1.368 | 4.329 | 1.0027 | 1.191 |
| v2_memfill | vectorizable | 0.0078 | 0.0106 | 1.356 | 1.413 | 4.490 | 1.0027 | 1.185 |
| v3_popcount | vectorizable | 0.0057 | 0.0069 | 1.218 | 1.411 | 4.484 | 1.0028 | 1.189 |

Reading limits:

- Programs that run for a few milliseconds are not resolvable. Their bridge-lane
  `rel_spread` reaches 0.82 (`h2`), 0.69 (`v2`) and 1.31 (`v3`). The harness's
  resolvable subset (LLVM median >= 50 ms, spread <= 0.25) has 10 programs and reads
  0.969x. That subset is reported, not gated.
- The two clear losses are large and stable. `p4_matmul` is 8.9x slower, because the
  LLVM lane vectorizes the kernel and the bridge does not. `h1_vec_push_sum` is 5.1x
  slower. (Follow-up, same day: LLVM does not vectorize `p4_matmul`, whose i64
  multiply has no NEON form. It unrolls the 24-wide inner loop, keeps the `c` row in
  24 registers across the k-loop and elides the bounds checks: 41 instructions per 24
  multiply-adds. The bridge's nest reached `mac-reg-block` but was refused, because
  its bounds checks are `TrapBoundsCheckExact` carriers; see `CHANGELOG.md` and
  `LIMITATIONS.md` for the fix and its measurement.)
- The cores are heterogeneous (12 performance, 4 efficiency) and macOS offers no
  `sched_setaffinity`, so no lane is pinned. The harness warns about this and records
  `affinity: none`.
- The default-CPU field in `cpu_policy` is null. `trustc --print target-cpus` names no
  default for this target, so there is nothing to parse. Both lanes compile with
  `-C target-cpu` and `-C target-feature` left at their defaults, so the lanes match.
- Programs peak below twice the 1.26 MB sampler floor except `h1` (6.2 MB), `h2`
  (51.8 MB) and `h3` (39.9 MB). Those three read equal to LLVM, so R1 stays unmeasured.
- The cold lane costs about 0.9 s more per compile than the warm lane, with
  certificates off. That is the population of a fresh per-user cache root. This run
  does not break the cost down.

## 3. Scaling (proofs off in both harnesses)

Command: `python3 benchmarks/beat-llvm/scale_gate.py --driver … --rss`

Wall time is min-of-5 and peak RSS is min-of-3, with the lanes interleaved rep by rep,
at `-O3` for `aarch64-apple-darwin` (driver host). The trust-cg lane passes
`no-proof-certs`. Log: [`logs/06-scale-gate-rss.log`](logs/06-scale-gate-rss.log).

| Crate | Lines | LLVM | trust-cg | Time | LLVM RSS | trust-cg RSS | Memory |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 355 | 0.313 s | 0.431 s | 1.38x | 137.2 MB | 168.4 MB | 1.23x |
| medium | 2,805 | 0.418 s | 0.657 s | 1.57x | 147.2 MB | 243.4 MB | 1.65x |
| large | 11,205 | 0.782 s | 2.537 s | 3.25x | 200.8 MB | 916.9 MB | 4.57x |
| xlarge | 33,605 | 1.798 s | 21.817 s | **12.14x** | 373.0 MB | 9,453.7 MB | **25.35x** |

Repeat of large and xlarge (min-of-3, load 1.43 before and 1.15 after):
large 3.21x time and 5.15x memory; xlarge 12.22x time and 25.12x memory
([`logs/10-scale-gate-large-xlarge-repeat.log`](logs/10-scale-gate-large-xlarge-repeat.log)).

From large to xlarge, the line and function count grows 3x. The trust-cg compile time
grows 8.6x and its peak RSS 10.3x, which is roughly quadratic. LLVM's grows 2.3x and
1.9x. The gate's docstring records xlarge on `x86_64-apple-darwin` on 2026-08-31 at
2.13x time and 1.39x memory. That measurement is from another target and revision, so
it is context, not a comparison. This campaign does not locate the growth. A crate of
2,400 small functions in one codegen unit is the reproducer:
`scale_gate.py --sizes large xlarge --rss`.

Command: `python3 benchmarks/compile-scaling/run.py --driver … --out-dir <scratch>`

This harness uses CPU time, median-of-3, at `-O2`, with `no-proof-certs` and
`refine-solver=0`. Log: [`logs/07-compile-scaling.log`](logs/07-compile-scaling.log).

| Shape | Sizes | LLVM exponent | trust-cg exponent | Excess | Ratio at largest |
| --- | --- | ---: | ---: | ---: | ---: |
| blocks | 100 to 800 | 0.15 | 0.17 | +0.02 | 1.44x |
| loops | 15 to 120 | 0.15 | 0.42 | +0.28 | 2.66x |
| funcs | 50 to 400 | 0.14 | 0.28 | +0.14 | 1.91x |
| arraysize | 4,096 to 262,144 B | 0.01 | 0.01 | +0.00 | 1.43x |

The verdict is "OK: no shape grows materially faster than LLVM", against the default
`--max-excess 0.6`. These ladders stop at 400 functions. The superlinear growth above
shows only at 800 and 2,400 functions, beyond this gate's `funcs` ladder.

## 4. Compile-time canary and determinism sentinel

- `scripts/compile_time_canary.sh --driver …` exited 1: `canary: GATE RED: bridge failed
  to compile the pinned canary program`. The refusal is `[TCG-PROOF-465]`. The
  stderr tail the canary keeps names a `FnOnce` shim, `__rust_begin_short_backtrace`
  (`TailCall`, `B`) and `Termination::report` (`Movz`). No compile time was measured,
  so the 8 s threshold was not evaluated. It is a cliff alarm, not a Darwin
  calibration.
- `scripts/compile_determinism_sentinel.sh 5 --driver …` ran in cold mode, each attempt
  with a fresh `XDG_CACHE_HOME`, and exited 2. All five attempts gave FAILCLOSED, at a
  load of 1.60 to 1.65. The sentinel reports "Not a flap".

## Components that could not run as required, and why

1. **The production (certificates-on) bridge lane.** It refuses every corpus program,
   the canary and the sentinel program with `[TCG-PROOF-465]` (section 1). No
   runtime, compile, size or RSS ratio exists for it on this host. Only the diagnostic
   lane measures the emitted code, and that lane is never evidence.
2. **The Trust package's own Clean.** `store/trust/9192/bin/clean` lacks
   `carcara-verify` (`X-HOST-P8`). The backend skipped it and used managed Clean 8606.
   That is a working independent checker, and no run was marked DEGRADED.
3. **The portable certificate set.** Every bridge compile printed "portable certificate
   set is DISABLED": the vendored `drat-trim` built by this host's Apple clang 21 /
   SDK 27.0 hashes to `f075353b…`, but `verdict_db/canary_certs/manifest.v1`
   authorizes `6933827a…`. Certificate skipping is declined and live discharge is
   kept. This does not affect eligibility, but the proofs-on compile time here does
   not include certificate skips that a host with the authorized checker would take.
4. **Core pinning.** macOS has no `sched_setaffinity`, so the heterogeneous cores are
   not pinned (section 2).
5. **Not in this campaign.** There are no TY or model-checker workloads (`L14-P4`),
   no proofs-on scaling ladder (the production lane cannot compile the corpus, and
   `L14-P6` stays open), and no real-crate denominator (`L14-P7`).

## Files

- `2026-09-28-01fc13b13608/`: harness retention for the evidence run, which is the
  ledger row's `retained_dir` (results JSON and markdown, outcomes, raw samples,
  inventory).
- `diagnostic-no-proof-certs/2026-09-28-01fc13b13608/`: harness retention for the
  diagnostic lane. It is not a ledger row.
- `logs/`: every step's full output, `steps.log` with exit codes and wall times, the
  bridge build summary, and the `p3_gcd` refusal example.
- `load.tsv`, `load-before.txt`, `load-after.txt`: machine load before and after
  every step, with process and memory snapshots.
- `host.txt`: `hw.model`, CPU, core topology, memory, macOS build, power, the Trust
  package identity, the Clean candidates, the C toolchain, linker and SDK, Python,
  and the backend's hash and build command.
- `commands/`: `campaign.sh` (the sequence above), `build_bridge.sh`, `hostinfo.sh`
  and `probe.sh` (the single-program refusal probe).
