# Maintained arithmetic AOT matrix at current source — 2026-09-22

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The unchanged `scripts/check_aarch64_aot_arithmetic.py` passes its complete
Linux AArch64 denominator on clean source
`4ded2b97c4d21fd21bc1b16fe9c1334fa4a1da81` (origin/main at the time of the run,
source fingerprint `323eda3d5d23afefb729f619b6574def77912ba7d9ed3587e2d53eeb48b8217a`,
identical before and after): **48/48 cases, 6,912/6,912 native calls, nine
distinct exported queries independently re-solved and their original
certificates accepted, and all 27 corruption controls rejected**. Status
`pass`, no errors, no refusals. The run took 56 seconds
(2026-09-22T17:12:06Z to 17:13:02Z).

This refreshes the [2026-09-20 record](../2026-09-20-maintained-arithmetic-aot/README.md)
(source `c45c4d3f`) at the current source, which has since taken the trust-ir
`7b9146ba` cohort, the i128, closure, direct-tag enum, sret and construct
inventory work merged from the owner's workstation. It is bounded leaf
arithmetic evidence (I32/U32/I64/U64 × ADD/SUB/doubling × O0–O3) on this host.
It closes no L01–L14 row; L09-P12 was already closed by the 2026-09-20 run and
this record only shows the maintained lane still passes at `4ded2b97c`.

## Host, tools and identities

- Host: `aarch64-unknown-linux-gnu`, Ubuntu 24.04.4, Linux `6.17.0-1026-nvidia`,
  NVIDIA Grace (Cortex-X925/A725, 20 cores, LSE/FP16/SVE2 present).
- CLI: `target/release/trust-cg` built in a detached git worktree at the same
  commit `4ded2b97c` with `cargo build --release --locked --offline -j 12 -p trust-cg-cli`
  under stock Rust 1.97.1 (build log retained as `records/release-cli-build.log.gz`);
  SHA-256 `1bb411757cd034cf2285564a4e13b9b7d864916cc83ad78bda0e3489f825d38e`;
  `trust-cg` release 0.6.0. The runner records the binary hash but cannot itself prove
  the binary was built from the fingerprinted source (owner decision OD-13);
  the worktree HEAD and build log are the retained build receipt.
- AY `ec2bf181c384bff0453487b47781fb6d40b959a72c1236bdc760ccc1feee4830` and
  Clean `8d819378eb80696a6a753980bb1722de676f283c4219887f769ac70868f0fff8`,
  both from the installed development package
  `~/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23` (install-prefix
  identity only; executables are not archived), passed through the pinned
  `env-override` routes `AY_SOLVER_PATH` / `TCG_EXTERNAL_CLEAN_CHECKER` because
  this host has no aterm-managed package store. All other `TCG_*`, `TRUST_CG_*`
  and `AY_*` variables were absent or removed by the runner.
- Host C compiler `/usr/bin/cc` (gcc 13.3.0),
  SHA-256 `a20520ee21543f243d40636a9181a142c45ecd989de31ab86b99a8ea5ada870d`.
- Controls: `--require-clean`, `--max-rss-gib 16` (Linux `/proc` supervision),
  default per-command timeouts (120 s compile/link/native, 180 s solver/checker),
  solver memory 8,192 MB.

The run executed concurrently with the maintained Linux regression floor on
the same host (separate output directory, no shared Cargo invocation); the
per-command deadlines were not approached.

## Retained files

`records/` is the complete runner output directory: `report.json`, every case's
compile/link/native logs, objects, C oracle sources and executables, exported
proof sidecars and SMT queries, and the replay directory with each original
Alethe proof, its three corruptions and the checker outcomes. `records/launch.json`
is the exact invocation and pinned environment. `runner-source/` copies the
maintained runner and its shared helpers at this commit.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-22-maintained-arithmetic-aot
python3 scripts/check_aarch64_aot_arithmetic.py --trust-cg /path/to/trust-cg --require-clean --max-rss-gib 16 --out /path/outside/source
```

Other instruction families, linked-image proof binding, signed publication,
verified frontend/self-hosting and complete source-to-native composition remain
open. All fourteen platform completion rows remain OPEN.
