# Integration-test sweep of the root workspace on Linux AArch64 — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The maintained Linux floor runs a required subset of about 150 targets. This
record runs every other root-workspace integration test target too, on the
same host, so tests outside the gate cannot rot unnoticed.

The sweep ran at clean `977de52caf256e7d3712b074886cdc76b92acae5`
(origin/main after the fifteenth push), in a dedicated worktree with a
separate target directory. Debug info was off
(`CARGO_PROFILE_DEV_DEBUG=0`) to keep the test binaries small, and the
package prefix pinned AY and Clean.

Each crate first built its tests with `cargo test --no-run`, then ran
`cargo test --no-fail-fast -p <crate> --test '*' -- --test-threads=4`.
Two crates needed a different invocation:

- **trust-cg-verify** ran with an explicit target list, because
  `--test '*'` includes a target that requires the `core-byte-replay`
  feature. That target ran separately with the feature enabled.
- **trust-cg-llvm-import** ran twice: once plain, where its test files
  compile to zero tests without the `driver` feature, and once with
  `--features driver`.

`git status --porcelain` was empty before and after the run.
`sweep.sh` is the script that ran it.

## Results

| Crate | Test targets | Passed | Failed |
| --- | ---: | ---: | ---: |
| `trust-cg-cli` | 15 | 119 | 0 |
| `trust-cg-codegen` | 412 | 3047 | 2 |
| `trust-cg-dialect` | 4 | 61 | 0 |
| `trust-cg-fuzz` | 28 | 198 | 0 |
| `trust-cg-gpu` | 3 | 18 | 0 |
| `trust-cg-ir` | 1 | 25 | 0 |
| `trust-cg-jit-matrix` | 10 | 91 | 0 |
| `trust-cg-lift` | 4 | 389 | 0 |
| `trust-cg-llvm-import-driver` | 13 | 33 | 2 |
| `trust-cg-llvm-import` | 13 | 3 | 0 |
| `trust-cg-lower` | 37 | 634 | 0 |
| `trust-cg-onnx-import` | 1 | 35 | 0 |
| `trust-cg-opt` | 7 | 59 | 0 |
| `trust-cg-regalloc` | 2 | 16 | 0 |
| `trust-cg-sat-host` | 4 | 23 | 0 |
| `trust-cg-test` | 5 | 49 | 0 |
| `trust-cg-verify.feat-core-byte-replay` | 2 | 15 | 0 |
| `trust-cg-verify` | 66 | 873 | 0 |

**627 target runs, 5,688 tests passed, 4 failed.**

## The four failures

- **`ay_sat_bcp_install_gate` (2 tests).** These fail at the known
  PROOF-465 proof wall (L07-P2): proof promotion refuses
  `StpPreIndex`/`LdpPostIndex`, which have no proof mapping. This
  predates the sweep.
- **Two `trust-cg-llvm-import` driver tests.** Both expected Apple
  behaviour from a host-derived target:
  - `fp_e2e` assumed FEAT_FP16, which Apple's baseline has and the generic
    Linux baseline refuses by name.
  - `ws2_stack_protector_target` expected an old refusal message.

  Both are fixed in the push this record accompanies. So is a product
  defect the investigation found: an explicit `x86_64-unknown-unknown`
  target took its object format from the host.

## Earlier sweeps

An unarchived first sweep ran at `7cacebb13` and found 63 failures outside
every gate. The repairs were archived with the tenth push
([gates-9](../2026-09-23-linux-integrated-gates-9/README.md)). They were:

- 48 x86-64 tests behind a false-positive host probe;
- stale Darwin-pinned host expectations;
- stale trust-ir fixtures;
- a real O2/O3 compile refusal in if-conversion;
- the rustc bridge silently accepting `-Zcodegen-emit-retag`.

A second sweep, at `4d7e2409a`, found the CEGIS wrong-code, budget and
cache defects fixed in the eleventh push.

This is regression evidence for these targets on one host. It is not
proof, not a gate, and not release readiness.
