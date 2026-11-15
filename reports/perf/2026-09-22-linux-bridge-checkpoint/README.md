# Linux private ABI bridge lane at current source — 2026-09-22

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The maintained `scripts/check_linux_aarch64_bridge.py` gate ran on clean
source `60b1f73fa48e5357fcb195f54b28b04b880e46dc` (the `linux-aarch64-20260922`
branch: production crates identical to origin/main `4ded2b97c`, plus retained
reports, the runner's `proof_tools` record and documentation) with the
coherent sealed Trust `a62ae50d` package. Result: **FAIL**. The fresh release
backend build (617 s) and the complete native-test build (528 s) pass; the
native target reports **0 passed, 1 failed** in 70 s, without ignored,
filtered, timed-out or resource-limited execution.

This is the current-source reproduction of ledger gap **L06-P1** with the
proof tools pinned and recorded for the first time: the runner's new
`proof_tools`/`final_proof_tools` block names AY
`ec2bf181c384bff0453487b47781fb6d40b959a72c1236bdc760ccc1feee4830` and Clean
`8d819378eb80696a6a753980bb1722de676f283c4219887f769ac70868f0fff8` through the
`aterm-packaged` route, unchanged across the run, so the refusal below cannot
be attributed to a missing checker.

The first scalar-cell fixture, `aliased_f32_read` at O0, still refuses object
emission with `[TCG-PROOF-465]`: the emitted opcode inventory carries
`StpPreIndex`, `StpRI`, `LdpRI` and `LdpPostIndex` for the calling frame with no
bound proof, and proof promotion rejects the function. The LLVM twin is not
reached in this ordering; later positive cells, higher optimization levels and
the HFA corpus receive no credit. This is the same compile-time proof refusal
the [2026-09-20 checkpoint](../2026-09-20-linux-bridge-checkpoint/README.md)
recorded at `cc2d64164`; the merged wave branches did not change it. The
frontend is explicitly unverified (`-Ztrust-verify=off`); backend proof
enforcement is on.

`records/run1-unpinned/` retains the same day's first launch of the same gate
at `4ded2b97c` without a pinned checker prefix on PATH (backend
`52113177dc4237ce5a2f57a5893e08895e9c1749d07bbae66984711a2c5f6189`); it fails
identically at the same site, which shows this refusal is not the provisioning
defect the floor's negative control exposed.

## Identities and controls

- Host `aarch64-unknown-linux-gnu`; `trustc`/`targo` 1.99.0-dev (`a62ae50d8`,
  2026-09-16) from `~/toolchains/trust-a62ae50d`, first on PATH with the installed
  AY/Clean package prefix second, `RUSTC` pinned to that `trustc` for `targo --unverified`.
- Backend SHA-256 `8ffdb7f5c39031ca4eaecf23c984046dc3cd57671252125c5e84a8eb04a99ef7`
  (fresh build in a run-local cache, snapshotted read-only and passed to the
  test by path and hash; identical before and after the test). The snapshot and
  the cache are hash-identified, not archived.
- `--require-proof-tools`, `--jobs 2`, `--timeout-seconds 7200`, run-local
  `XDG_CACHE_HOME`; every `TCG_*`/`RUSTC*`/`RUSTFLAGS` ambient override absent.
- Source fingerprint `e998e358…` identical before the build, after the build,
  after the test build and after the test.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-22-linux-bridge-checkpoint
PATH="$HOME/toolchains/trust-a62ae50d/bin:$PKG/bin:$HOME/.cargo/bin:$PATH" \
  python3 scripts/check_linux_aarch64_bridge.py --require-proof-tools --out /path/outside/source \
    --target-dir /path/outside/source/cache --jobs 2 --timeout-seconds 7200
```

L06-P1, L07-P2 and all L01–L14 completion rows remain OPEN. No gate, positive
case or proof requirement was weakened to obtain this checkpoint. Closing this
lane needs bound proofs for pair memory opcodes in calling frames, which is
the calling-frame memory-algebra work the plan tracks, not a runner change.
