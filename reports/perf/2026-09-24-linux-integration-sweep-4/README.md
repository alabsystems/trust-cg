# Integration-test sweep of the root workspace on Linux AArch64 — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The maintained Linux floor runs a required subset of 166 targets. This
record runs every other root-workspace integration test target too, on the
same host, so tests outside the gate cannot rot unnoticed. It follows the
[2026-09-23 sweep](../2026-09-23-linux-integration-sweep/README.md).

The sweep ran at clean `aceeb3bb67b4a48b4f544caa78bd7666132af1d5`
(origin/main after the twentieth push), in a dedicated worktree with a
separate target directory. Debug info was off, and the package prefix
pinned AY and Clean.

`sweep.sh` builds its target list from `cargo metadata` (`plan.txt`). So no
target name can be stale, and a target with `required-features` runs in a
second pass with those features. For each crate it first ran
`cargo test --no-run`, then
`cargo test --no-fail-fast -p <crate> --test <each target> -- --test-threads=4`.
The `trust-cg-llvm-import` tests are gated in their source, not by
`required-features`, so they compile to 3 tests without the `driver`
feature. They ran again as
`cargo test -p trust-cg-llvm-import --features driver --tests` after the
main loop. `git status --porcelain` was empty before and after.

## Results

| Crate | Test targets | Passed | Failed | Ignored |
| --- | ---: | ---: | ---: | ---: |
| `trust-cg-cli` | 15 | 128 | 0 | 0 |
| `trust-cg-codegen` | 412 | 3052 | 2 | 0 |
| `trust-cg-dialect` | 4 | 61 | 0 | 0 |
| `trust-cg-fuzz` | 28 | 198 | 0 | 0 |
| `trust-cg-gpu` | 3 | 18 | 0 | 0 |
| `trust-cg-ir` | 1 | 25 | 0 | 0 |
| `trust-cg-jit-matrix` | 10 | 91 | 0 | 0 |
| `trust-cg-lift` | 4 | 389 | 0 | 0 |
| `trust-cg-llvm-import` (plain) | 13 | 3 | 0 | 0 |
| `trust-cg-llvm-import` (`--features driver`, with the library) | 15 | 266 | 0 | 0 |
| `trust-cg-lower` | 37 | 634 | 0 | 0 |
| `trust-cg-onnx-import` | 1 | 35 | 0 | 0 |
| `trust-cg-opt` | 7 | 59 | 0 | 0 |
| `trust-cg-regalloc` | 2 | 16 | 0 | 0 |
| `trust-cg-sat-host` | 4 | 23 | 0 | 0 |
| `trust-cg-test` | 5 | 49 | 0 | 0 |
| `trust-cg-verify` | 66 | 873 | 0 | 1 |
| `trust-cg-verify` `core_byte_store` (`core-byte-replay`) | 1 | 6 | 0 | 0 |
| `trust-cg-verify` `core_byte_writer` (`core-byte-replay`) | 1 | 9 | 0 | 0 |

**5,935 passed, 2 failed, 1 ignored.**

The two failures are the known L07-P2 proof wall: `sat_bcp_executable_artifact_installs_only_after_manifest_gate_and_runs_via_bound_contract`
and `sat_bcp_gate_fails_closed_for_missing_wrong_and_unrunnable_artifact_routes`
in `ay_sat_bcp_install_gate`. They are refused with `[TCG-PROOF-465]` for
AArch64 pair opcodes that have no checker-accepted certificate. The
2026-09-23 sweep's other failures are gone. Of the three residuals it
recorded (the `ty_mcl` callback race, the `full_proof_suite` Comparison
pin, the slow `core_byte_writer`), all pass here, and `core_byte_writer`
took 9 minutes 16 seconds.

This is regression evidence for tests outside the floor, not
qualification. The bridge workspace's own targets are not part of the
root workspace and did not run.
