# Fail-closed instruction-cache coherence rows on Linux — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record retains the qualifying run for the Linux half of audit row
**L11-P4**. It ran on clean source `56bb5143f893ebc0d304f7e81096ab274772fac3`
(`records/HEAD.txt`), which is origin/main `dbfc88b79` plus the change.
The Darwin half has no run here, so L11-P4 stays PARTIAL.

## Host

- Linux 6.17.0-1026-nvidia aarch64, Ubuntu 24.04.4 LTS, 4 KiB pages. The
  full record is `records/host.txt`.
- `lscpu` reports two core types. Ten Cortex-A725 cores have MIDR_EL1
  `0x410fd871` (CPUs 0-4 and 10-14). Ten Cortex-X925 cores have
  `0x410fd851` (CPUs 5-9 and 15-19). The host is not a Neoverse V2 part.
- CTR_EL0 reads `0x9444c004`: IminLine and DminLine are both 64 bytes.
  DIC is 0, so `ic ivau` is architecturally required before rewritten
  instructions are fetched. IDC is 1, so instruction fetch already sees the
  data cache and `dc cvau` is not required on this host.
- Stock Rust 1.97.1 (`rust-toolchain.toml`) with the pinned AY/Clean prefix
  on `PATH`. Every Cargo command used `--locked --offline -j 8`.

## What changed

At the base, the floor target `jit_icache_coherence` was positive-only. Its
rows republish into fresh mappings. Fresh pages are maintained by the kernel
when it first maps them executable, so those rows pass without the
`ic ivau` walk (confirmed below). The discriminating same-page test was a
library unit test outside the floor.

`jit::flush_instruction_cache(start, len)` is a new public entry point to
`sys::flush_icache`. That is the walk every publication runs, not a copy.
The target gains two Linux-only rows:

- `in_place::in_place_rewrite_executes_new_code_only_through_the_production_walk_on_one_core`
- `in_place::in_place_rewrite_executes_new_code_only_through_the_production_walk_on_another_core`

Each row uses a page the test owns. It runs 1,024 rounds after the first
image. Every round rewrites 8,229 words on the same physical page, starting
12 bytes into a cache line, through an RX -> RW -> RX cycle that published
buffers never take. Each ADD is `ADD X0, X0, #tag, LSL #12`, and the tag
increases strictly from round to round. A word fetched from any earlier
round therefore lowers the result by a whole number of generations.

- Odd rounds are unmaintained witnesses: `dsb ish; isb`, with no cache
  maintenance.
- Even rounds (512 per placement) run the production walk.

The one-core row writes and executes on one pinned CPU. The cross-core row
writes on CPU 0 and executes on a second pinned thread, which issues `isb`
after it sees the rewrite. Each row runs once for every core type in the
affinity mask:

- one core: CPU 10 (A725) and CPU 15 (X925);
- cross-core: CPU 0 to CPU 14 (A725 to A725) and CPU 0 to CPU 19 (A725 to
  X925).

Every row reads CTR_EL0 itself and requires the library's geometry to match.
At every placement, every production round must return the exact sum. With
DIC 0, at least one witness round at every placement must also return stale
code, so a row that cannot observe the hazard fails instead of passing
vacuously.

## Retained mutation run

`records/harness/mutation_driver.py` builds each variant with one command:
`cargo test -j 8 --locked --offline -p trust-cg-codegen --test
jit_icache_coherence --no-run`. It uses the worktree's single target
directory. The driver then runs the test executable N times with the floor's
arguments, `--nocapture --test-threads=1`, unless the mode is "parallel".
A mutation is a patch to `sys::flush_icache` (`records/mutation/*.patch`). It
is applied with `git apply` for the build only and reverted with
`git apply -R`. The driver checks the `jit.rs` hash before and after, and
records the SHA-256 of the mutated source and of each test executable.

| Variant | Source | Runs | Passing runs | Failing runs, in-place rows (one core / another core) | Failing runs of each other row |
| --- | --- | ---: | ---: | --- | --- |
| real (serial) | `56bb5143f` | 200 | 200 | 0 / 0 | 0 |
| real (parallel, libtest default threads) | `56bb5143f` | 50 | 50 | 0 / 0 | 0 |
| M1: `ic ivau` loop removed | `m1-no-ic-ivau-walk.patch` | 100 | 0 | 100 / 100 | 0 |
| M2: `ic ivau` stride doubled to 128 bytes | `m2-ic-ivau-stride-doubled.patch` | 100 | 0 | 100 / 100 | 0 |
| M3: `dc cvau` loop removed | `m3-no-dc-cvau-walk.patch` | 100 | 100 | 0 / 0 | 0 |
| restored | `56bb5143f` | 100 | 100 | 0 / 0 | 0 |

Stale production rounds per placement, summed over all runs of a variant.
Each run has 512 production rounds per placement:

| Placement | real serial | real parallel | M1 | M2 | M3 | restored |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| one core, CPU 10 (A725) | 0 / 102,400 | 0 / 25,600 | 51,162 / 51,200 | 51,129 / 51,200 | 0 / 51,200 | 0 / 51,200 |
| one core, CPU 15 (X925) | 0 / 102,400 | 0 / 25,600 | 51,133 / 51,200 | 51,129 / 51,200 | 0 / 51,200 | 0 / 51,200 |
| CPU 0 -> CPU 14 (A725 -> A725) | 0 / 102,400 | 0 / 25,600 | 51,187 / 51,200 | 51,184 / 51,200 | 0 / 51,200 | 0 / 51,200 |
| CPU 0 -> CPU 19 (A725 -> X925) | 0 / 102,400 | 0 / 25,600 | 51,130 / 51,200 | 51,106 / 51,200 | 0 / 51,200 | 0 / 51,200 |

Under M1 and M2, every placement had at least 507 of its 512 production
rounds stale in every run (`min_production_stale_rounds_per_run` in
`records/mutation/results.json`). Across all placements that is 204,612 of
204,800 production rounds under M1 (99.91%) and 204,548 of 204,800 under M2
(99.88%). For M1 and for M2, 100 of 100 runs detected the mutation.
Unmaintained witness rounds were stale at every placement in every run of
every variant. The lowest count was 428 of 512, in one real serial run on
CPU 0 -> 19.

M3 is the evidence boundary. It is not detected, because the host's IDC is 1.

The republication rows passed every M1 and M2 run, and every one of those
runs reused all 11 vacated bases. This confirms they are positive-only on
this host as well.

The real and restored builds compile the same `jit.rs` (SHA-256 prefix
`b69fc470d294bd97`) into the same test executable, SHA-256
`0b621677231fbde03d54e150f4b4f0825f6e25e8ca58f7bc802bc4b37cd0e05c`. Each
mutant's source and executable hashes differ from these and are recorded in
`results.json`. The worktree was clean after every variant.

## Independent probe

`records/probe/stale.c` is a C program that shares no code with trust-cg. It
rewrites an executed page in place and counts rounds that execute stale code
for each maintenance mode. `records/probe/probe.log` holds its output on the
same host. Each row has 1,024 rewrites of 8,229 words starting 12 bytes into a
line. Same-thread rows run on CPU 10 (A725) and CPU 15 (X925). Cross-core
rows write on CPU 0 and execute on CPU 14 or CPU 19 after `isb`. The writer
also executes in those rows.

| Mode | Same thread, CPU 10 | Same thread, CPU 15 | Executor on CPU 14 | Executor on CPU 19 |
| --- | ---: | ---: | ---: | ---: |
| 0: `dc cvau` + `ic ivau` at the CTR_EL0 lines | 0 | 0 | 0 | 0 |
| 1: no `ic ivau` | 1,023 | 1,023 | 1,022 | 1,020 |
| 2: `ic ivau` stride 128 | 1,023 | 1,024 | 1,024 | 1,024 |
| 3: no `dc cvau` | 0 | 0 | 0 | 0 |

The table counts stale rewrites out of 1,024. It reproduces the mutation
results without trust-cg, including the IDC=1 boundary.

## Gates at `56bb5143f`

`records/harness/run_gates.sh` ran these gates on the clean checkout.
`records/gates/git-status-before.txt` and `git-status-after.txt` are empty.

- `cargo test -p trust-cg-codegen --test jit_icache_coherence -- --nocapture
  --test-threads=1` (the floor's command shape): `test result: ok. 5 passed;
  0 failed; 0 ignored; 0 measured; 0 filtered out`.
- `cargo test -p trust-cg-codegen --lib`: `test result: ok. 4089 passed; 0
  failed; 1 ignored; 0 measured; 0 filtered out`. The ignored test is the
  existing real-tool campaign `raw_machir_request_cache_real_exhaustive_campaign`.
  The library's CTR_EL0 decode, host-geometry and in-place rewrite tests
  pass.
- `cargo check -p trust-cg-codegen` with default features (which include
  `verify`), with `--features verify`, and with `--no-default-features` (the
  rustc bridge's configuration).
- `cargo clippy -p trust-cg-codegen --test jit_icache_coherence --no-deps --
  --cap-lints warn`: no finding in `jit_icache_coherence.rs` or the new code.
  The library's two existing lints (`data_image.rs:426`, `jit.rs:8176`) are
  unchanged.
- `scripts/check_fmt.sh`; the gate script tests (94 tests, 1 skipped);
  `native_test_host_matrix.py --check`; `check_documentation.py --check`;
  `check_evidence_archive.py --plan`.

The full 147-target Linux floor was not rerun. The library change adds one
public function that no existing path calls, plus comments.
`jit_icache_coherence` is the only floor target whose code changed.

## Evidence boundary

- This is execution evidence from one host, not a proof of coherence. The
  real build passed 350 runs across the two modes, which is a pass rate,
  not a guarantee.
- The rows cover the `ic ivau` walk, its stride and its reach to other
  cores. On this host they cannot detect a missing `dc cvau` walk (M3).
  Where CTR_EL0.DIC is 1 the rows are positive-only and say so.
- The rows exercise the walk on a test-owned page through
  `jit::flush_instruction_cache`. They pin the walk's contents, not that
  publication calls it. A later review removed the publisher's only call to
  the walk (`sys::flush_icache(self.ptr, expected_image_len)` in
  `MappedRegion::seal_rx_and_verify`) at this revision and every row passed
  20 of 20 runs, because the kernel maintains the fresh pages publication
  maps. That mutation (M4) is undetected by this record, like M3. The
  follow-up structural row that detects it is retained in
  `reports/perf/2026-09-23-linux-icache-publisher-walk-control`. The
  publisher's hash check and read-execute seal are covered by other targets;
  its call to the walk is covered by none of the rows in this record.
- A kernel that reports DIC 0 on coherent hardware, or maintains a page on
  every execute-permission change, hides the hazard; the rows then fail
  their non-vacuity check instead of passing.
- Only the widening to 128 bytes (twice the minimum line) was measured. A
  wider power-of-two stride visits a subset of those addresses, so it leaves
  at least the same lines unmaintained. That is an inference; it was not run.
- Preliminary development runs are not retained: 20 runs per mutant on the
  first revision of the rows and 10 per mutant on this revision, each with
  the same outcome as the table above.
- The Darwin half of L11-P4 is not addressed. There is no retained Darwin
  run of `jit_wx_refusal` or `jit_icache_coherence`, and the in-place rows
  are compiled out on Darwin.

## Files

| Path | Content |
| --- | --- |
| `records/HEAD.txt` | the qualifying source revision |
| `records/host.txt` | uname, lscpu, cpuinfo, page size, toolchain, per-CPU MIDR_EL1 |
| `records/mutation/*.patch` | the three source mutations of `sys::flush_icache` |
| `records/mutation/results.json` | per-variant summary: runs, per-test failures, per-placement round counts, hashes, load averages |
| `records/runs/*.runs.log.gz` | the complete output of every run, one file per variant and mode |
| `records/runs/*.build.log.gz` | the Cargo build output of each variant |
| `records/gates/*.log.gz` | the gate logs listed above |
| `records/gates/git-status-*.txt` | `git status --porcelain` before and after the gates (empty) |
| `records/probe/` | the independent C probe and its output |
| `records/harness/` | the driver, mutation generator, gate runner, host and inventory helpers |
