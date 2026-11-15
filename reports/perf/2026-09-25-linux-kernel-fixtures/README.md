# Linux kernel fixture qualification, 2026-09-25

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The exact Trust compiler `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`
on `aarch64-unknown-linux-gnu` now has regenerated inputs for ten
layout-sensitive kernel integration targets. All 52 listed tests pass in
separate processes: 45 kernel differential, structural and negative-control
cases, plus seven compiler/target selector tests. None of these selected
cases was ignored. This is development testing, not proof-required compiler
acceptance or qualification of the separate rustc-private ABI bridge.

## Defect found and repaired

The first native qualification executed all 52 cases: 34 passed and 18 failed.
Some closures contained duplicate string-global names; other closures returned
`a` where the native oracle returned `u` or `v`, including incorrect cached
name hashes. Module validation and successful text re-parsing had not detected
the latter semantic error.

TrustIR's closure frontend created a fresh lowering context for each member
but shared one module builder. Each context assigned global IDs from zero,
so later functions could reference an earlier function's constant instead of
their own. TrustIR commit `e75f566c26149f3fe2659aedbaab0ff55b1f467d`
carries the constant and vtable interning state across closure members,
assigns absolute module global IDs, compares full string bytes when interning,
and makes literal symbols unique by global ordinal. Its two new regressions
exercise real MIR emission, parsing and validation; the string case also
interprets the emitted closure. The mixed-vtable case checks distinct 8/4-byte
entries after an earlier string constant and reuse of the same vtable.

All 21 Linux closures, including both prior TC stitching inputs, were emitted
twice with that repaired generator. Every pair is byte-identical, carries the
Linux target, validates with zero errors, and re-parses successfully. The
second native qualification passes all 52 cases with the original test bodies
and ABI shims. The two TC fixture files remain byte-identical to their prior
versions; their provenance records the repeated generation.

## Results and boundaries

| Target | Executed tests | Result |
| --- | ---: | --- |
| `fixture_toolchain_selection` | 7 | PASS |
| `e2e_tc_stitching` | 5 | PASS |
| `e2e_defeq_cache` | 8 | PASS |
| `e2e_ctx_whnf_defeq` | 5 | PASS |
| `e2e_lazy_delta` | 5 | PASS |
| `e2e_universe_integration` | 1 | PASS |
| `e2e_eta_struct_ext` | 3 | PASS |
| `e2e_fvar_opening` | 4 | PASS |
| `e2e_binding_defeq` | 5 | PASS |
| `e2e_phase_completion` | 4 | PASS |
| `e2e_universe_realnames` | 5 | PASS |

The broader `trust-cg-codegen --all-targets` check remains a separate diagnostic.
It exited 101 after 492.82 seconds at the retained unknown-compiler guard.
Its actual result is retained with this report. `e2e_frontend_roundtrip`, which
contains 72 tests, has not been migrated or qualified for this compiler. Its
unknown-compiler refusal remains active. The earlier required regression
floor keeps its own source revision; these results do not restamp that floor.

The root consumer still pins TrustIR
`be4018498bc33a9416c4e9ebec317b762f0d7751` and Clean
`6a1050f3d9692a3740c345c41484bd8fa7857447`. The **generator** was built
from TrustIR `14b37845e84b3dfd3cbfa3284e4f3b9a7d0dc3ab` plus the
recorded repair, subsequently published as `e75f566c`. Its binary SHA-256 is
`004b3aea7827bc051ab319beb09140e29d7b5d34656f0404a8b333f88f77a7f1`.
The final additional vtable test did not change the generator's production
source or binary hash. This is not a dependency-pin transaction.

## Reproduction and retained records

The [fixture directory](../../../crates/trust-cg-codegen/tests/fixtures/ae9-linux/README.md)
contains both provenance documents and the inputs. The compressed generation
plans and runners record exact source roots, compiler-private metadata, LLVM
SDK, build profiles and commands. Build and test commands use genuine Targo's
explicit `--unverified` development lane. Every listed test runs with
`--exact --test-threads=1` in a separate process; intentional JIT-side leaks
therefore do not accumulate across cases.

manifest.json binds each losslessly compressed record to its
original SHA-256 and byte length. It includes the failed first native run,
the repaired run, both original and repaired generation records, the TrustIR
regressions and publication, formatting attempts, and the all-targets
diagnostic. Decompress a record with `gzip -dc <path>`. Failed attempts retain
their original outcomes; an expected diagnostic refusal is not a passing gate.

Qualification bound the dirty candidate over trust-cg `b581796e`. After all
owners exited, the stale duplicate `frontend_sha256` field in
`kernel-provenance.json` was corrected to match its already-correct
`generator_sha256`. The metadata-only correction receipt binds both file
versions. No Rust source or fixture bytes changed after native qualification.
