# Complete Linux AArch64 regression floor — 2026-09-25

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

All 167 required integration targets pass: 1,078 Rust tests, zero failed,
ignored or filtered. The exact clean source is
`443ed769f6ba67036e50b219561423dbc8a94ec0`. This repeats the entire maintained
floor after the current verifier sampling/FP changes, x86 conditional-move
repair and AArch64 canonical reconstruction repair.

Every declared target and feature ran with locked offline dependencies,
recorded AY/Clean proof tools, one Cargo job, one test thread, an 8 GiB
process-group RSS ceiling and the unchanged 1,200-second per-target timeout.
The whole supervisor finished successfully and the source stayed unchanged.
All logs, source-bound reports, identities, supervisor results and exact runner
inputs are retained in the inventory.

The [preceding focused qualification](../2026-09-25-main-verifier-qualification/README.md)
separately covers 899 Rust tests, 60 Python tests and affected all-target builds.
The [canonical reconstruction regression](../2026-09-25-aarch64-canonical-reconstruction/README.md)
retains its failing baseline and repaired controls. These populations overlap;
they are not added to this floor's count. The older complete 744303be4 result
remains in the [September 24 archive](../2026-09-24-linux-required-floor/README.md).

Reproduce at the named source with the recorded tools:

```sh
python3 scripts/check_linux_aarch64.py --out /path/outside/source \
  --require-clean --require-offline-deps --require-proof-tools \
  --max-rss-gib 8 --jobs 1 --timeout-seconds 1200
```

Later main changes add report accounting and archived evidence. This record
qualifies the exact captured source and harness. It does not qualify the
separate rustc-private bridge, rebuilt Trust compiler, global installation,
release package, all workspace tests, or the complete L01–L14/G1–G8 contract.
Opaque-callback calling-frame and frontend proof gaps remain open.
