# Scoped proof-LET TrustIR adoption — 2026-09-16

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Qualification, evidence archival and independent audits are complete.
This is not a public release or a whole-toolchain proof.

TrustCG adopted TrustIR `98532215bcaadb1ef29da6471b925a6e6a3c3b95`.
Four dependency-adoption guards and 48 distinct development compiler tests
passed: 46 component tests and two native controls with ten generated-code
calls. The component and native observations have separate terminal receipts.
No proof-required native execution, verified compiler build, complete TY
source-to-native result, target-portability or performance claim is made.

## Source and dependency identities

The qualification subject is CG
`8209c81f1a206aa2774d629d3e52d87ee2e7db5c`, tree
`1200228f5426992c11f8cbf769b1fa3c78e1d5c9`.
That adoption commit changes six files, with 13 inserted and 13 removed lines:
the root and rustc-bridge manifests, all three lockfiles, and the unchecked
compile-cache dependency identity. It moves TrustIR from
`d5ef779d02ea3fa35b9198154857c56382d23eea` to
`98532215bcaadb1ef29da6471b925a6e6a3c3b95`.
Clean remains `68ad1b2027460864ac394be0356f3a5eddce1054`; AY remains
`849c19fa0382085174a6a4827739681f059b4615`.
This report's later documentation commit is not the source revision compiled.

Original local records are under
`/private/tmp/trust-cg-scoped-proof-lets-20260916.amDfaF`:

- adopt-9853/result.json, SHA-256
  `86ae08246b7a03baa77229aa46ee41e02bc1f846683da0ef3638ee2b53adc531`.
- checks-scoped-lets/result.json, SHA-256
  `b54be3d00710642577f6aeb88d26d651f4b52b9b9a94d39e93ed74aef7fab28b`.
- checks-scoped-lets/runner.py, SHA-256
  `e47396887ef4e698f66b8cf8888c6b510f4c75c0238cbbaf24834ae08ffcd749`.
- retained-checks-scoped-lets/result.json, SHA-256
  `f4071d7db9129d6a9aa786b0873a392db6f319156893e0e4a44123772332ceb9`.
- native-smoke-scoped-lets/result.json, SHA-256
  `b2e73f81ab67bf5c76bf3effdb8f8ec3e1d274286e01e755123576182704f2cd`.
- native-smoke-scoped-lets/runner.py, SHA-256
  `24acc35bda7493826e3aca1e34fe9041e5f979a6cb7ca65184c88c9b372135ca`.

These absolute paths identify the original observation, not a portable rerun
package. The relative links identify archived copies. Raw commands, logs,
results and bookends are preserved without rewriting their verdicts; the
archival inventory and local-artifact boundary are described below.

## Dependency-adoption guards

The actual production bumper exited 0. Its raw log records four passed,
zero failed, zero ignored and zero filtered tests:

- `committed_lockfiles_bind_cross_repo_sources_exactly`
- `committed_manifests_bind_cross_repo_sources_exactly`
- `compile_artifact_cache_defaults_bind_dependency_authorities`
- `local_source_redirect_is_explicit_and_uncommitted`

The observer's terminal status is
`transaction-passed-review-required`, not a proof verdict. It records
`inputs_unchanged: true` for its protected inputs and no bookend errors.
Its declared index comparison is `canonical-ls-files-stage-and-flags`;
`raw_index_unchanged` is **false**. Do not call that transaction's physical
Git index byte-identical. The earlier v42 observer's raw-index validation
failure remains failed and unchanged; this successful transaction does not
rewrite that historical result.

These four guards are distinct from the following 46 compiler tests.

## Fresh component qualification: 46 / 46

The six selections below matched source declarations, executable `--list`
output and actual named libtest results. Every selected test passed; none was
failed or ignored. Unselected tests in the larger images are not qualified by
this run.

| Selection | Passed | Scope |
| --- | ---: | --- |
| `lower` | 16 | `trust-cg-lower` integration target `v41_contract_surface` |
| `wasm-v41` | 5 | `wasm::lower::tests::v41_` |
| `wasm-v42` | 1 | `wasm::lower::tests::v42_` |
| `generated-diamond` | 1 | `compiler::affine_bytes::tests::generated_diamond_leaf_frames_bind_both_source_arms` |
| `source-bound-frame` | 22 | 16 existing frame tests plus six diamond/CSET tests |
| `instruction-tombstone` | 1 | `cmp_branch_fusion::tests::test_cset_bool_branch_fuses_to_original_condition` |
| Total distinct selected tests | 46 | Zero failed or ignored |

The observer recorded `status: tests-passed`, `development_only: true`,
`verified_compiler: false`, `inputs_unchanged: true`, and no bookend errors.
An independent read-only audit reauthenticated the raw records and current
inputs rather than relying on that summary alone.

Five primary compilation phases were fresh (`fresh: false`): ordinary codegen
metadata check, lower integration-test image, codegen library-test image,
verify library-test image and optimizer library-test image. The audit checked
actual compiler commands, emitted artifact identities and compiler environment
overlays against the recorded source/target. Compilation used the pinned
Trust compiler in its explicit **unverified development lane**, not stock Rust
and not authenticated `targo trust` verification.

All 17 supervised phases completed with exit 0: five builds, six list probes
and six selected-test executions. Their log hashes matched exit receipts;
phase intervals were sequential. At the independent audit, all 17 recorded
phase PIDs were absent and no related source/target/controller workload remained.
No timeout, compiler error, build refusal or unexpected selected-test failure
was observed in this run.

### Intentional refusal coverage

A passing negative test is evidence that the named boundary refuses its
unsupported or mutated input. It is not successful compilation of that input.
For example, v41/v42 tests cover unsupported metadata and malformed/unused
declared tuple layouts; source-bound frame/diamond tests reject malformed
ownership, source/CFG/operand mutations and unbound machine bodies.

`source_bound_frame_verifier_requires_independent_discharge` intentionally
requires the report to remain `Unverified` with
`source-bound frame needs independently replayed proof`, and requires the
opcode inventory to remain non-promotable. The related diagnostic-mode test
likewise requires refusal. These passes must not be counted as completed
independent proof discharge or proof-required native execution.

## Environment, tools and bookends

The host/compile target was macOS ARM64 (`aarch64-apple-darwin`). The exact
reused source and build target were:

- `/private/tmp/trust-cg-input-domain-build-xFHuDsWm/source-host`
- `/private/tmp/trust-cg-input-domain-build-xFHuDsWm/target-host`

The fixed compiler environment's SHA-256 is
`36ffa687a7d5f513171f05650cdb2535127851cb638377339aa0ac667af43f3b`.
It retains one build job, one test thread, a 64 MiB Rust test stack and
incremental compilation disabled. The commands use process-local
`-Zchecksum-freshness`, `--unverified`, `--locked`, and the existing target.
No target/cache clearing or forced-rebuild invalidation was used.
Each phase acquired the existing 16 GB scheduling reservation, **not a hard
memory cap**. Budgets remain 7,200 seconds per build, 60 per list probe and
300 per selected component-test group, with five seconds' termination grace.

Pinned tool identities include:

| Tool | SHA-256 |
| --- | --- |
| Targo | `e972a5739a9793249b2bbf38d8102d2d32c06131f6e02bcf15bc19916b3f839a` |
| Trust compiler | `b5aeb6a6742cb19c30feacf7d8e2eb4c1585331e0e5a02ddb45be4def1ca0f3d` |
| Trust compiler driver | `f69935c7f6d1a82c84e6c265623bb2788a98c892e94ec818c22475c986508705` |
| AY | `eaeb6ecdec16702f1e312a7825b488dd948efd229d4e5964bef1b6ce1ecc0cc2` |
| Development Clean checker | `d967ca586211da38c981969c2fb40a49420090f0c9a7fca7cbb6351f25dd6869` |

The 22-test verifier group alone used a runtime PATH prepended with the
task-private `proof-packages/bin`; compilation and the other groups used the
unchanged compiler environment. There were no ambient `TCG_*`, `TRUST_CG_*`
or `AY_SOLVER_PATH` policy overrides in that base environment.

The prior proof prefix and its historical receipt were preserved. AY's old
`$HOME/ay/target/release/ay` path now traverses the explicit
`target -> target.noindex` directory alias. The new private prefix points to
`$HOME/ay/target.noindex/release/ay`, with identical AY bytes and mode.
Before/after migration receipts bind both paths and the alias; this is path
provenance, not a newly earned proof-pair canary result.

The component before/after source books are byte-identical (SHA-256
`2c077a70d4693b7b4d205f2dbda2008f5688d7d25844d4ddf3e910e943eb8b14`).
Independent audit found the then-current snapshot equal to both: 9,037 source
entries including three pinned empty gitlinks, 25 tool/control records,
71 sysroot entries and 15 configuration paths. Source HEAD/tree, clean detached
worktree, logical index entries and recorded physical index bytes matched.
Private and historical proof-prefix/path books also matched.

The six output artifacts were unchanged at that audit:

| Artifact filename | Bytes | SHA-256 |
| --- | ---: | --- |
| `libtrust_cg_codegen-fa847f4433be2f87.rmeta` | 11,866,505 | `97a0981c84eb4da230b5e2cad0703461b9c0d08c5a1fce0343578748db888a1c` |
| `v41_contract_surface-fb42e34930a74225` | 39,273,304 | `4aa7a5bba5357209b13aa162402d7690b07f0bf0582c0f5c3c5d9ffab4794f92` |
| `trust_cg_codegen-a558072e02facb74` | 185,174,064 | `c5b3a48ddef832886f559ba535b85255c98fb9fe48eac588e596a8fd7345cbfd` |
| `trust_cg_verify-863b20b4724a9dff` | 142,089,536 | `f38d8bd0ca2e03244656718547dee0a0f09826c26ce01f6b434323958ffd4560` |
| `trust_cg_opt-9860c54fb5771e9c` | 53,958,864 | `4226858e58b5fe6dca17c47c87bb19e9b59e657d594d138202ba60d2393b0c27` |
| Bundled `drat-trim` | 70,120 | `6933827a98fcb21685fe2b4535cced9ee541eb2038e1ecac9297d229e9e39aa1` |

Before shared-target reuse, a separate retention operation copied all six
artifacts (432,432,393 bytes) to `retained-checks-scoped-lets/`. Its receipt
records distinct original/copy inodes and byte/mode equality. Retention's full
before/after books match, including all 78 original component evidence files.
The native controller binds that receipt and validates its six copies before
and after compilation. The independent native audit rechecked all six retained
identities and their distinct inodes; no historical output was overwritten in
place as a means of preservation.

## Development-native gate: 2 / 2, ten calls

Both exact tests passed with zero failed or ignored:

- `test_jit_trust_ir_forward_direct_call_patches_regalloc_preserved_symbol`
- `test_jit_ty_icmp_eq_select_returns_old_vs_appended`

The first checks the actual AArch64 BL target after register allocation and
calls the generated O1 forward-call function twice: `(13,29) -> 42` and
`(-7,7) -> 0`. The second performs four generated select calls at each of O1
and O3: equal/unequal sender-receiver pairs select old/appended values, including
negative payloads. That is **two tests, three JIT compilations and ten native
function invocations**, not ten distinct tests. Source is
`crates/trust-cg-codegen/tests/jit_integration.rs`, SHA-256
`aba290348fff66997295be8bfe50bc99d7d44710dad01f3ba0279d3706b4def6`.
The test functions are at lines 733 and 2865 in the qualified revision.

The common helper explicitly sets `verify: false` and dispatch verification
off in both Pipeline and JIT configurations (lines 2577-2596). Its inputs are
hand-built TrustIR modules, not parsed TLA+ programs. These executions do not
prove an arbitrary TrustIR function or compose TY's frontend proof with native
code. The Cargo feature named `verify` does not override those runtime choices.

The fresh `jit_integration` build and exact named executions used the unchanged
development compiler environment and existing target, with one build job,
the same 16 GB scheduling reservation, and the existing 7,200-second build,
60-second list and 120-second native-test budgets. All five supervised phases
exited 0; both executable list probes matched their exact named selections.
The independent audit authenticated the actual fresh compiler command/artifact
and the raw named results. No native timeout, skip, failure or ignored test
was observed.

The actual image `jit_integration-dae0c3566b12ff64` is 145,092,336 bytes, mode
0755, SHA-256
`eb5f4b2240c52276fdeed7905f0c42a5eced948b5f170915a559b40bee588fe8`.
Its local `retained-jit_integration` copy has identical bytes/mode and a
distinct inode. Native before/after books are byte-identical, SHA-256
`0b07d3eec5c96fafe1ef0b48a1a0632ff44635cde38ec22576e3d1df764eb55b`.
The independently sampled current books matched them: the same 9,037 source
entries, 71 sysroot entries and 15 configuration paths, with 28 tool/control
records after adding the native runner, prior result and retention receipt.
All prior component tool records are preserved as a subset. Both proof-prefix
and path-migration books remain unchanged.

At the terminal native audit all 22 recorded component/native phase PIDs were
absent, with no related source/target/controller workload remaining. The native
result declares `development_native_only: true`, `verified_compiler: false`,
`proof_required: false`, `performance_claim: false`, `inputs_unchanged: true`
and no bookend errors. The total qualified compiler census is **48 distinct
tests**; the four adoption guards remain separate.

No TY/TLC benchmark was run. No claim of superiority, general target execution,
proof-required publication or whole-toolchain verification follows from this
pin adoption and component qualification.

## Archive and local resource release

inventory.json, SHA-256
`5b3900b6b4b073d2930c65f5815ab8f8c327cd21f4472b8b2b151ce0df249e70`,
records **139 files, 21,268,648 original bytes and 3,695,417 stored bytes**,
excluding this README and the inventory itself. The census is 17 adoption
records, 78 component records, four retention metadata records, 29 native
records and 11 controller/helper files. Fourteen records of at least 100,000
bytes use deterministic gzip (level 9, mtime zero, no stored filename); all
others are exact copies. Original/stored SHA-256, byte lengths and modes are
recorded for every file.

The archive controller binds
a frozen 138-input book, SHA-256
`1a023d47ef8d9bdd5a4c9c98e8fcd9be8d31f539862381d31ac8aff216df3a32`;
its own activated source is the 139th archived record. Root activation changed
only its two explicit review/enable flags. Independent read-only audit checked
the exact archive inventory, every decoded byte/hash/mode against the current
original, deterministic gzip reproduction, the unchanged frozen input book and
the absence of unexpected files or symlinks. Original manifest/lock bytes are
stored under inert `Cargo.toml.txt`/`Cargo.lock.txt` names, preventing archived
manifests from becoming new dependency-discovery candidates.

No executable, full source checkout or target/cache was copied into the report.
The six component images and one native image remain independently retained at
the local paths named in the inventory, with byte/mode identities audited after
archival. The inventory is not a substitute for those images, and this archive
is not a hermetic rerun package. Archival performed zero builds and zero test
executions; it does not create new qualification or proof authority.

The independent final audit again found the qualified source/tool/sysroot and
proof-path books equal to the native terminal bookend, all 22 recorded phase
PIDs absent, and no related workload running. On that basis, the qualification
hold on
`/private/tmp/trust-cg-input-domain-build-xFHuDsWm/source-host` and
`/private/tmp/trust-cg-input-domain-build-xFHuDsWm/target-host` is released for
coordinated source/target/cache reuse. This releases local build resources,
not a product or a proof-policy exception. Preserve the original evidence
directories and all seven independent retained artifacts. Any later source or
cache mutation is outside the recorded unchanged-bookend interval and must not
be presented as part of this run.
