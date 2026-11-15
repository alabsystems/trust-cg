# Linux x86-64: the integrated wave-1 measurement (2026-09-21)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Six independently developed items were merged into `main` and then measured
together, because each item's own numbers were taken on its own worktree
dylib and do not compose by arithmetic. Everything below was produced from the
merged tree with a clean working tree, and every artifact it cites is retained
beside this file.

Host: `x86_64-unknown-linux-gnu`, Ryzen 9 9900X3D, 24 cores, 61 GiB. Root
workspace built with the pinned stock Rust 1.97.1 (`rust-toolchain.toml`);
the bridge built with the tree-built stage2 `trustc` (`rustc 1.99.0-dev
(3a3e781fe 2026-09-14)`) through `targo --unverified build --release
--locked`. Backend SHA-256 in
`census/core-x86_64-linux-O0/backend.sha256`.

This is a regression and refusal measurement in the explicit unverified
frontend lane. It is not a proof claim, and it does not establish compiler
completion or release readiness.

## What was merged

| Item | What it changed |
| --- | --- |
| floor fixes | Darwin-residue fixtures, GNU-objdump frame decoding, host symbol spelling, successor edges on two ISel fixtures, instruction-boundary VEX assertions, the CHC SSE4 fixture's type, a decided-absent lane for swiftcc (XD-03) |
| certificate path | `call_only_body` certificate category for bodies with no value-semantics row, the x86 statistical-row trace, and the corrected XD-01 diagnosis |
| partial eightbyte | 3/5/6/7-byte SysV INTEGER eightbyte lanes composed from exact-width accesses, with TV-5 widths and the pipeline mirror |
| pair arguments | Two-carrier `PassMode::Pair` arguments on x86-64 (XD-05), behind one per-argument marshaller every hand-built list now routes through |
| vectorization | Carrier-guard arms in the saxpy-Q recognizers, one shared pure-trap predicate, a `memset` route for large byte-uniform fills |
| Clean and TY | Host-target loading for the frozen Clean fixtures and the TY reducer lanes |

## `library/core` refusal census, O0, certificates on

`scripts/trust_ir_cg_census.py` from the Trust checkout against the merged
bridge. Retained in `census/core-x86_64-linux-O0/`.

| Measurement | Failed roots | Distinct reasons | Objects emitted |
| --- | ---: | ---: | ---: |
| 2026-09-20 baseline, as found | 726 | 28 | 2,706 |
| 2026-09-21 clean HEAD before this wave | 335 | 28 | 3,097 |
| **2026-09-21 merged wave 1** | **183** | **27** | **3,249** |

The three largest classes of the pre-wave census are gone: `[TCG-ARG-ABI]`
74 → 2 (both `Option<u128>`, a 128-bit lane the pair plan declines),
`[TCG-PROOF-465]` 46 → 0, and the `Array(I8/I16, N)` partial-eightbyte
aggregates 38 → 0 (`[TCG-REGALLOC-063]` 46 → 8, the remainder being 7 post-RA
tied-operand roots and one ambiguous symbol, neither an ABI refusal).

The largest remaining classes, in order: `[TCG-POINTEE-DYN-VALUE]` 30,
`[TCG-PASSVAL-067]` 27 (the popcount SWAR obligation the local solver answers
`unknown`), `[TCG-POINTEE-LANES]` 21, fat-pointer union fields 21,
`[TCG-POINTEE-UNSIZED-TAIL]` 16, memory-backed slice `Rvalue::Cast` 11,
`[TCG-REGALLOC-063]` 8, `[TCG-RET-REGCLASS]` 6, then a tail of 21 classes at
five roots or fewer.

## Linux x86-64 regression floor

`scripts/check_linux_x86_64.py --trust-driver <stage2>/bin/trustc`, every
per-target log retained in `floor/`. The bridge lane fails closed without an
explicitly named Trust package, which is why the driver is passed.

| Run | Targets | Pass | Fail |
| --- | ---: | ---: | ---: |
| 2026-09-21 clean HEAD before this wave | 66 | 50 | 16 |
| **2026-09-21 merged wave 1** | **68** | **57** | **11** |

Both added targets pass: the bridge vector-tier trace
(`m143_x86_vectorize_trace`, 2 tests) and the TY BFS kernel through the
x86-64 AOT path (`ty_bfs_minimal`, 9 tests). `e2e_x86_64_swiftcc` is recorded
as decided absent under XD-03 and printed in every report, so the omission
stays visible.

Every one of the 11 remaining failures falls into exactly two open items:

* **XD-01, proof promotion on a formal-capable host (8 targets).**
  `jit_cert_cache_identity_x86_64`, `jit_sysv_x86_64_spill_replay`,
  `jit_validation_modes_x86_64`, `jit_x86_64_aggregate_abi_fail_closed`,
  `jit_x86_64_profile_modes`, `x86_64_constant_pool`, `x86_64_sysv_ay_abi`,
  and one test in `x86_64_target_features`. All report
  `ProofPromotionRejected … validated only by bounded statistical sampling`.
  The corrected diagnosis and the measured per-opcode residual are in the
  [cert-path report](../2026-09-21-linux-x86-64-cert-path/README.md).
* **X03, ELF exception handling (3 targets).** `e2e_x86_64_eh_catch`,
  `e2e_x86_64_eh_invoke_trust_ir_run` and `e2e_x86_64_eh_resume_trust_ir`
  still print a Darwin host SKIP: the x86-64 ELF path emits no LSDA or
  personality wiring, so the tests are compile-time guarded to Mach-O hosts.

## Root workspace unit tests

`cargo test -p trust-cg-codegen --lib` on the merged tree: 3,917 passed, 16
failed. The failing set is byte-identical to the one retained from the
pre-wave run of 2026-09-20 (`codegen-lib-failures.txt`), which had 3,911
passing and the same 16 failures, so the merge introduced no regression and
added six passing tests. Fifteen are `compile_service` tests and one is
`test_aarch64_parallel_and_serial_multi_function_byte_identical`; all sixteen
fail with `ProofPromotionRejected`, the same XD-01 class as the floor's eight.
`cargo test -p trust-cg-lower --lib` passes 1,864 tests.

`cargo test -p trust-cg-verify --lib` is NOT a clean measurement on this host
and is recorded here as an open question rather than a result. Two runs of the
same merged tree disagreed: 4,059 passed with 19 failures, then 4,034 passed
with 25 failures (`verify-lib-failures-loaded-host.txt`), while three other
workflows were building. Every failing test invokes an external solver or
checker — `ay_bridge`, `cegis`, `canary_cert`, `checked_overflow_proofs`'s Z3
CLI test, `fsym_summary`, `lowering_proof`'s registry sweeps, and the popcount
SWAR validators — and the suite takes about 30 minutes, so the variation is
consistent with wall-clock solver deadlines under load, not with a code change.
One of them, `udiv_portable_theorem_cannot_formally_self_attest_sdiv_source`,
is confirmed pre-existing: it fails in the retained 2026-09-20 `lib-synthesis`
shard. The rest are unclassified until the suite is run on a quiet host, and
that run is owed before any claim about this crate's state.

## After reconciling with upstream

Upstream had independently implemented the same partial-eightbyte SysV INTEGER
lane while this wave was in flight, in the same files. The two implementations
were reconciled on `integrate/upstream-2026-09-21` by keeping upstream's lane
(it carries its own tiling proof and is the line everyone else builds on) and
carrying this wave's unique contributions onto it, then re-measuring everything
from scratch. Retained in `reconciled-census/`, `reconciled-floor/` and
`reconciled-codegen-lib-failures.txt`; backend SHA-256 `e938969d…`.

| Measurement | Pre-merge wave 1 | After reconciling with upstream |
| --- | ---: | ---: |
| `library/core` failed roots at O0 | 183 over 27 reasons, 3,249 objects | **183 over 27 reasons, 3,249 objects** |
| Linux x86-64 floor | 57 of 68 pass | **57 of 68 pass** |
| `trust-cg-codegen --lib` | 3,917 pass / 16 fail | **3,917 pass / 16 fail, the identical set** |
| `trust-cg-lower --lib` | 1,864 pass | **1,868 pass** |

The census class ordering is unchanged, the 183 failed roots are byte-identical
between the two runs (`failed_roots.jsonl.gz` compared line by line), and the 11
floor failures are the same targets with the same per-target pass/fail counts —
so upstream's lane and this wave's lane refuse and admit exactly the same shapes.
The collision area was tested directly and passes whole: the aggregate ABI suites
(`e2e_x86_64_aggregate_abi` 30 tests, `e2e_x86_64_aggregate_byval_arg` 8), the
coverage gate (`coverage_gate_tests` 47), the meta theorems (8), the soundness
manifest (10), the addressing gate (`x86_addressing_gate` 10), upstream's new
volatile access-trace gate (`x86_volatile_trace_gate` 8), and this wave's TV-5
dataflow (`post_ra_dataflow` 74) and x86 lowering proofs (176).

Two notes on the identity of these artifacts, so the next re-measurement is not
read as a regression:

* The bridge dylib is rebuilt for each measurement and a release rebuild of
  identical sources does not reproduce its SHA-256 on this host — the pre-merge
  run names `2d6b86a3…` and this one `e938969d…` for the same lowering. Each
  census therefore names its own dylib rather than inheriting one.
* An earlier attempt at the reconciled floor was taken while three other
  workflows were building and testing in sibling worktrees. It recorded
  `rustc-codegen-trust-cg/m143_x86_vectorize_trace` as FAILING and never wrote
  its summary (`report.json` said `incomplete`). Re-run to completion on the same
  commit, that lane passes, and `reconciled-floor/report.json` is the completed
  run. The runner shells out to `cargo`, so a loaded host can starve a lane past
  its deadline; an `incomplete` report is not a result.

## What this does not measure

No `alloc` or `std` census, no performance run (the beat-llvm ledger row is
still owed and no runtime number here is evidence), no Trust-verified
compilation of trust-cg itself, no bridge-corpus floor, and no re-measurement
of the full test matrix.
