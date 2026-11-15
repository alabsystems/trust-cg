# Publisher maintenance-walk control for `jit_icache_coherence` — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This record retains the qualifying run for the repair of audit row
**L11-P4** (Linux half). It ran on clean source
`4774c3fc8ad82bc600d531385bf680b8e0887ee3` (`records/HEAD.txt`), which is
the first L11-P4 increment (`56bb5143f`, retained in
`reports/perf/2026-09-23-linux-icache-in-place-control`) plus the repair.
The Darwin half has no run here, so L11-P4 stays PARTIAL.

## What the review found

The in-place rows of `jit_icache_coherence` call the walk directly through
`jit::flush_instruction_cache`. They pin what `sys::flush_icache` does, not
that publication calls it. A reviewer removed the publisher's only call,
`sys::flush_icache(self.ptr, expected_image_len)` in
`MappedRegion::seal_rx_and_verify`, at `56bb5143f` and all five rows passed
20 of 20 floor-shaped runs. The republication rows pass without the call
because the kernel maintains the fresh pages publication maps. That run is
the reviewer's and is not retained here. Mutation M4 below repeats it at the
repaired revision, where the other six rows again pass.

The review also found that `flush_instruction_cache(start, 0)` walked the
line containing `start`, so an empty range at `NonNull::dangling()` (0x1)
maintained the line at address 0 and faulted, although the documented
precondition held.

## What changed

- `sys::flush_icache` records each completed walk (a count and the last
  range) in a thread-local log, read through the new public
  `jit::instruction_cache_walks_on_current_thread()`.
- `every_publication_walks_its_published_image` (both hosts) publishes four
  images. Around each, it requires a completed walk on the publishing thread
  whose range starts at the mapping's first byte and covers the whole
  image. Both publication paths call the walk from
  `MappedRegion::seal_rx_and_verify`; the row drives the serialized-buffer
  path.
- `flush_instruction_cache` returns before the walk when `len` is 0.
  `an_empty_range_is_not_walked_even_at_a_dangling_address` (both hosts)
  calls it at `NonNull::dangling()`, `Vec::<u8>::new().as_ptr()` and
  `usize::MAX` with `len` 0 and requires that no walk is recorded.
- The Darwin floor minimum for the target rises from 3 to 5.

## Host

The Linux AArch64 host of the first record: Linux 6.17.0-1026-nvidia
aarch64, ten Cortex-A725 cores (MIDR_EL1 `0x410fd871`, CPUs 0-4 and 10-14)
and ten Cortex-X925 cores (`0x410fd851`, CPUs 5-9 and 15-19), CTR_EL0
`0x9444c004` (64-byte minimum lines, IDC 1, DIC 0). The full record is
`records/host.txt`. Stock Rust 1.97.1 with the pinned AY/Clean prefix on
`PATH`; every Cargo command used `--locked --offline -j 8`.

## Retained mutation run

`records/harness/mutation_driver.py` is the first record's driver with the
two new rows added to its test list and with crash and panic-message
tallies. Each variant is built once with `cargo test -j 8 --locked
--offline -p trust-cg-codegen --test jit_icache_coherence --no-run` in the
worktree's single target directory and run N times with the floor's
arguments, `--nocapture --test-threads=1`, unless the mode is "parallel". A
mutation (`records/mutation/*.patch`, written by
`records/harness/make_mutants.py`) is applied with `git apply` for the build
only and reverted with `git apply -R`; the driver checks the `jit.rs` hash
before and after.

| Variant | Runs | Passing runs | Failing runs by row | How it failed |
| --- | ---: | ---: | --- | --- |
| real (serial) | 100 | 100 | none | |
| real (parallel, libtest default threads) | 20 | 20 | none | |
| M4: publisher's call to the walk removed | 50 | 0 | publisher row 50; every other row 0 | the named assertion "publication at ... completed no instruction-cache maintenance walk on the publishing thread", 50 of 50 |
| M6: publisher walks half the image | 50 | 0 | publisher row 50; every other row 0 | "the last maintenance walk ... len: 24650 does not cover the 49300-byte image", 50 of 50 |
| M5: empty-range return removed | 50 | 0 | empty-range row 50 | SIGSEGV inside `an_empty_range_is_not_walked_even_at_a_dangling_address`, 50 of 50; the process dies, so later rows do not run |
| M1: `ic ivau` loop removed | 20 | 0 | both in-place rows 20; every other row 0 | the in-place rows' named assertion "the production maintenance walk left stale instructions" |
| restored | 50 | 50 | none | |

Under M4 and M6 the four in-place placements had 0 stale production rounds
in every run, and the republication rows reused all 11 vacated bases in
every run. That repeats the review's finding: without the publisher row, no
row of this target detects a publisher that skips or shortens its walk on
this host.

Under M1 the in-place rows still detect the removed walk at this revision:
40,421 of 40,960 production rounds were stale across the four placements,
and at least 481 of 512 per placement in every run.

In the real serial runs, unmaintained witness rounds were stale at every
placement in every run. The lowest count was 146 of 512 (CPU 0 -> 14); the
machine was shared with other builds (load averages are in
`results.json`). The first record's lowest count was 428.

The real and restored builds compile the same `jit.rs` (SHA-256
`f53759f18ab1c43669c8c619ddd242289664f3a833f13fec72f450dc379c1880`) into
the same test executable, SHA-256
`b2de4b1a5ced40f1c3e87da1ea6f3c668441a47c1fdd99e4a3c5489728b30868`. Each
mutant's source and executable hashes differ and are in
`records/mutation/results.json`. The worktree was clean after every variant.

## Gates at `4774c3fc8`

`records/harness/run_gates.sh` ran these gates on the clean checkout.
`records/gates/git-status-before.txt` and `git-status-after.txt` are empty.

- `cargo test -p trust-cg-codegen --test jit_icache_coherence -- --nocapture
  --test-threads=1`: `test result: ok. 7 passed; 0 failed; 0 ignored; 0
  measured; 0 filtered out`.
- `cargo test -p trust-cg-codegen --lib`: `test result: ok. 4089 passed; 0
  failed; 1 ignored; 0 measured; 0 filtered out` (the ignored test is the
  existing real-tool campaign `raw_machir_request_cache_real_exhaustive_campaign`).
- `cargo check -p trust-cg-codegen` with default features (which include
  `verify`), with `--features verify`, and with `--no-default-features`.
- `cargo clippy -p trust-cg-codegen --test jit_icache_coherence --no-deps --
  --cap-lints warn`: only the library's two existing lints.
- `scripts/check_fmt.sh`; the gate script tests (94 tests, 1 skipped);
  `native_test_host_matrix.py --check`; `check_documentation.py --check`;
  `check_evidence_archive.py --plan`.

The full 147-target Linux floor was not rerun. The library change records a
thread-local walk log in `sys::flush_icache` and adds an empty-range return
to a function no production path calls; `jit_icache_coherence` is the only
floor target whose code changed.

## Evidence boundary

- The publisher row is structural. It shows that publication completed a
  call to the walk over the image on the publishing thread. It does not
  show the call's cache effect (the in-place rows cover the walk's contents)
  or its order relative to the read-execute seal.
- The execution rows still pin only the walk's contents. Removing the
  publisher's call passes every execution row on Linux, because the kernel
  maintains the fresh pages publication maps; only the structural row
  detects it.
- A mutation that keeps the record but skips the walk inside
  `sys::flush_icache` is the in-place rows' job (M1 here and M1/M2 in the
  first record). A missing `dc cvau` walk is still undetected on this host
  (IDC 1, M3 in the first record).
- The two new rows are host-neutral, but they ran only on this host. The
  Darwin minimum of 5 is counted from the cfg gates, not from a Darwin run.
- This is execution evidence from one host, not a proof of coherence.

## Files

| Path | Content |
| --- | --- |
| `records/HEAD.txt` | the qualifying source revision |
| `records/host.txt` | uname, lscpu, cpuinfo, page size, toolchain, per-CPU MIDR_EL1 |
| `records/mutation/*.patch` | the four source mutations of `jit.rs` |
| `records/mutation/results.json` | per-variant summary: runs, per-row failures, crashes, panic messages, per-placement round counts, hashes, load averages |
| `records/runs/*.runs.log.gz` | the complete output of every run, one file per variant and mode |
| `records/runs/*.build.log.gz` | the Cargo build output of each variant |
| `records/gates/*.log.gz` | the gate logs listed above |
| `records/gates/git-status-*.txt` | `git status --porcelain` before and after the gates (empty) |
| `records/harness/` | the driver, mutation generator, gate runner, host and inventory helpers |
