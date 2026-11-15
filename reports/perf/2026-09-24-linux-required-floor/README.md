# Complete Linux AArch64 regression floor — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**PASS: all 167 required integration targets and 1078 Rust tests** on clean
source `744303be4ddcc6d8872412047665bb71a3b839d2`. Zero tests failed, were ignored,
or were filtered. Every required target ran, including its declared features,
with offline locked dependencies and the recorded AY/Clean proof tools.

The run includes native multi-index GEP semantics, the GEP evidence inventory,
entry-backedge and probed-frame native controls, and source-attributed arithmetic
JIT execution and authority controls. The focused JIT run immediately before
this full suite also passes all 160 proof-required compilations, 23,040 native
calls, 84 emitted-ADD mutations and 84 explicit-LSL mutations. The full run
executes that two-test target again as part of the unchanged required floor.

The preceding complete run at `56d875196` had one failing target because its
tests required a doubling rewrite the source-proof-class guard deliberately
suppresses. Its complete failure, the repair and passing focused controls remain
in [the JIT report](../2026-09-24-jit-proof-class/README.md). The earlier GEP
inventory failure and repair are also retained in their dated reports. No
compiler refusal, proof grade, target denominator or native assertion was
weakened to obtain this result.

The inventory retains all per-target logs, complete gate and
supervisor records, dependency/tool identities, runner scripts and source inputs
with compressed and decoded SHA-256/lengths. The maintained archive checker
validates the entire inventory. Stock Rust 1.97.1, one Cargo job and one test
thread were used under an 8 GiB process-group RSS limit with zero grace; every
target retained its 1,200-second timeout. Per-target elapsed times total
1062.52 seconds. These times are scheduling observations on a shared host,
not comparative performance measurements. The source path owns its Cargo
cache; no cache was shared across different source worktrees.

Reproduce on Linux AArch64 with the recorded dependencies and proof tools:

```sh
python3 scripts/check_linux_aarch64.py --out /path/outside/source \
  --require-clean --require-offline-deps --require-proof-tools \
  --max-rss-gib 8 --jobs 1 --timeout-seconds 1200
```

This is the maintained root-workspace integration floor. It does not qualify
all workspace tests, the separate rustc-private bridge, Trust frontend,
self-hosting, a release package, or the complete L01-L14/G1-G8 goals. In
particular, the source-bound calling-frame proof for opaque external callbacks
remains open. The installed machine toolchain is not changed by this run.
