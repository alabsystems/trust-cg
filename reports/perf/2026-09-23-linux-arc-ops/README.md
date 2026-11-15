# TrustIR ARC operations on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This run qualifies the ledger L05-P3 increment. It is the first native
execution of `Inst::Retain`, `Inst::Release` and `Inst::IsUnique`. The run
used clean source `91265a106054b4bf8fadb2fd81f7a7f7cd5a9654` (tree
`c3679a6bdbfb5a04134f2d4e54de4274dba92997`, trust-ir pin `7b9146ba`).
`git status --porcelain --untracked-files=all` was empty before and after the
runs (`records/source.json`). The harness that ran everything and built this
directory is `harnesses/qualify-arc-ops-20260923.py`, stored verbatim.

## Host

The host is Linux `6.17.0-1026-nvidia` on NVIDIA Grace (aarch64), with glibc
2.39. `cc` is Ubuntu gcc 13.3.0 (`/usr/bin/aarch64-linux-gnu-gcc-13`), GNU ld
and readelf are 2.42, `llvm-objdump` is LLVM 18.1.3, and rustc and cargo are
1.97.1 through the rustup proxies. `records/tools.json` gives each resolved
path, its SHA-256 and its version line. Cargo ran with `--locked --offline`
and PATH led by the pinned AY/Clean package directory. Ambient `TCG_*` and
`TRUST_CG_*` variables were removed.

## Results

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_arc_ops_linux -- --nocapture --test-threads=1` with `ARC_OPS_LINUX_RETAIN_DIR` set | `test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 2.25s` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_heap_dealloc_linux -- --nocapture --test-threads=1` | `test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.83s` (`PASS 138 heap checks` at O0-O3) |
| `cargo test -p trust-cg-lower --test trust_ir_construct_inventory -- --test-threads=1` | `test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.49s` |

The heap-deallocation twin is re-run here at the current trust-ir pin. The
2026-09-20 Linux floor record at source `86857ff3` used pin `25422eb`.

Every command has a `records/commands/<name>.capture.json` with its argv,
working directory, relevant environment, UTC start and end times, return code
and log hash. `records/results.json` collects the summaries below.

## ARC-op run, per level

| Level | `module.o` SHA-256 | Bytes | CALL26 `clean_inc`/`clean_dec`/`clean_is_exclusive` | CALL26 `malloc`/`free`/`__rust_alloc`/`__rust_dealloc` | Driver |
| --- | --- | ---: | --- | --- | --- |
| O0 | `dcb61fc269adc678…` | 3,760 | 7 / 10 / 12 | 6 / 1 / 1 / 1 | `PASS 95 arc checks` |
| O1 | `62085c387b61ca17…` | 3,624 | 7 / 10 / 12 | 6 / 1 / 1 / 1 | `PASS 95 arc checks` |
| O2 | `9409ae95e34328b3…` | 3,696 | 7 / 10 / 12 | 6 / 1 / 1 / 1 | `PASS 95 arc checks` |
| O3 | `9409ae95e34328b3…` | 3,696 | 7 / 10 / 12 | 6 / 1 / 1 / 1 | `PASS 95 arc checks` |

The O2 and O3 objects are byte-identical. The CALL26 columns are counted from
`readelf -rW` (`records/commands/readelf-rW-O*.log`). They agree with the
test's own ELF reader, which also requires each site to be a `BL` against an
undefined global. The objects are stored as
`records/objects/arc-ops-O*/module.o.gz`. `records/objects/driver.c` is the
driver source, which was identical at every level (SHA-256 `e8e2cefa…`). The
linked binaries are not archived; `results.json` (`levels.*.binaries`)
records the SHA-256 and size of each positive and self-check binary.

- **Interpreter agreement.** The test's four "results equal the interpreter"
  lines report 10 results per level. The interpreter values are
  `arc_share_cycle(7)=241`, `arc_share_cycle(1000)=32017`,
  `arc_dealloc_at_one(5)=186`, `arc_is_unique_after(0|1|3)=1|0|0`,
  `arc_branch_share(0,9)=19`, `arc_branch_share(1,9)=18`,
  `arc_retain_leak(4)=0` and `arc_release_past_zero(0)=0`. The interpreter
  refuses `arc_release_past_zero(1)` with `Release: pointer references a
  freed allocation`.
- **Driver traces.** `records/commands/driver-O*.log` holds each retained
  positive binary, re-run on its own. Every call's per-step trace equals the
  driver's constant. For example, `arc_share_cycle` gives
  `cQ1 cI2 cQ0 cI3 cQ0 cD2 cQ0 cD1 cQ1 cD0F`: unique, shared at 2 and 3, back
  to unique, freed at zero. The leak control gives `cI2 cQ0` with one live
  cell at count 2, and the past-zero control gives `cD0F ?D`: the second
  release is refused and not forwarded. These counts and frees are driver
  observations, not interpreter values.
- **Harness self-checks.** Every inverted-polarity build prints
  `FAILED 18 of 95 arc checks`. Every never-free build prints
  `FAILED 32 of 95 arc checks`. See
  `records/commands/driver-inverted-O*.log` and `driver-never-free-O*.log`.
- **Result normalization.** `records/commands/objdump-dr-O*.log.gz` shows
  that after each `clean_is_exclusive` call the returned byte is
  zero-extended with `uxtb` before the `cmp #0`/`cset`. That masks the
  bits 8-63 the driver's `clean_is_exclusive` deliberately sets. `results.json` counts 11 of 12 O0
  sites with `uxtb wN, w0` within four instructions. The twelfth, in
  `arc_is_unique_after`, first moves `w0` to `w1` and then runs
  `uxtb w0, w1`.

## Inventory disposition correction (2fd201f11)

The construct-inventory row in the Results table ran at `91265a106`. That
source counted `Inst::Retain`/`Release`/`IsUnique` as executed (94 / 37 / 20),
naming the native row of this target as evidence. The inventory's emitted
definition of executed is native execution on aarch64-apple-darwin, and that
row is compiled out on Darwin, so the flip was wrong. No other executed row
rests on a Linux-only native test. Commit `2fd201f11` restores the three rows
to model-only. Their notes cite the Linux-only native row, and they stay in
`no_native_execution`, the Darwin D05 work queue.

`harnesses/rerun-inventory-correction-20260923.py` re-ran the gate and this
target on clean source `2fd201f11eb088a2ab45a878b20c52a3d95ea369` (tree
`e8323c9ad2478190d4295d014182274dfc54f966`; porcelain empty before and
after, `records/inventory-correction/source.json`), with the same pinned
PATH:

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-lower --test trust_ir_construct_inventory -- --test-threads=1` | `test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.51s` |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_arc_ops_linux -- --test-threads=1` | `test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 2.04s` |

`records/inventory-correction/summary.json` records the committed inventory
at that source: 91 executed / 40 model-only / 20 refused (`Inst` 33 / 14 /
11), 60 `no_native_execution` entries including all three ARC instructions,
and the unchanged Darwin-only executed definition. The ARC-op objects,
traces and self-checks above were not re-archived. `2fd201f11` changes
no code that this target compiles.

## Boundary

This is execution and ELF-structure evidence at O0-O3 against a C stand-in
runtime and the pinned trust-ir reference interpreter. It is not proof.

- The driver is the counting runtime. Its side table, seeded at count 1 by
  the wrapped allocators, is not the Clean runtime, whose Perceus cells come
  from the still-refused `CleanHeap`. The correctness of the
  `clean_inc`/`clean_dec`/`clean_is_exclusive` calls rests on the linked
  runtime.
- The native rows ran only on this Linux host. The four host-neutral rows are
  registered on the Darwin floor but did not run on Darwin in this record.
- The `Ty::Rc` ABI, `SwiftHeap`/`CleanHeap` cells with a Swift/Clean release
  ABI, and cross-function `Dealloc` stay refused by name. L05-P3 stays
  **PARTIAL**.
