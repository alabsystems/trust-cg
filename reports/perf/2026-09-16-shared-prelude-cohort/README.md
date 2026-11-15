# Shared-prelude compiler cohort qualification — 2026-09-16

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

TrustCG adopted IR `d41fa3f8b7d8e2dba3f6e5b5a0b6217194e2a9f5` and Clean
`61c10a6795bc342a7a582adae25962bbb28cfbe2`. **82 distinct development controls
passed: four normal-adoption guards, 76 component tests and two native tests.**
Root and a separate reviewer completed terminal audits before this report.
This is not proof-required native admission, connected TY execution, verification
of the Rust implementation, full-workspace qualification or a performance claim.

## Exact subject and adoption

The compiled subject is CG `c1b22c9b7ced09ad5285a5f3c8e0e153439b0f06`, tree
`59becfad97be0ae00da95f3e14f07ec1a394d87c`. Its detached source is
`/private/tmp/trust-cg-prelude-cohort-20260916.8Xzp4n/qualification-source`.
AY remains `849c19fa0382085174a6a4827739681f059b4615`; package versions,
features and unrelated resolution remain unchanged. The normal bumper changed
six files within its seven-file authority scope: two manifests, three lockfiles
and the compile-cache dependency identity. The AY-only regalloc manifest did not
change. Qualification is about this exact source, not the report's later commit.

The mutable reporting worktree subsequently merged peer documentation at
`2ae7ed20ed1870e80feb64c6abefb2ecb55f828e`. Relative to the qualified commit,
that merge changes only two documentation files, not crates/manifests/config.
It does not extend the qualification to other tests or proof claims.

The normal transaction result, SHA-256
`3721203d58eb3e23a276a76db68a8ea596d625c1c517b517bd9ee00cf23758b6`,
records exit 0, unchanged protected inputs/index and no bookend errors. Its
raw log has exactly these four passed tests:

- `committed_lockfiles_bind_cross_repo_sources_exactly`
- `committed_manifests_bind_cross_repo_sources_exactly`
- `compile_artifact_cache_defaults_bind_dependency_authorities`
- `local_source_redirect_is_explicit_and_uncommitted`

## Selected component and native results

The qualification result, SHA-256
`679e6c92e82896f48cb48606b0565a9ce4509184a370b5d8fdc1ff2818d8d0d2`,
records 78 distinct named passes across 15 selections, zero failed/ignored tests,
and 39 supervised phases with exit 0. Executable listings, raw named results,
source-derived selection and log/exit receipts agree. The four bumper tests are
separate; they are not silently counted again in the 78.

| Selection | Passed |
| --- | ---: |
| Lower v41 contract surface | 16 |
| WASM v41 / v42 | 5 / 1 |
| Generated diamond / instruction tombstone | 1 / 1 |
| Source-bound frame, including three cell guards | 25 |
| Existing codegen handle controls | 5 |
| Lower recursive-handle diagnostic | 1 |
| Opaque-handle integration | 21 |
| ARM64 native controls | 2 |
| Total, excluding four adoption guards | 78 |

The 25 frame tests include diagnostic recognition, query construction and
deliberate refusals. In particular, the new scalar-cell tests do not authorize
a frame proof merely because diagnostic recognition succeeds. Tests requiring
independent discharge retain their unverified/refused verdict. Passing these
negative controls must not be reported as successful proof-required compilation.

The actual native tests are
`test_jit_trust_ir_forward_direct_call_patches_regalloc_preserved_symbol` and
`test_jit_ty_icmp_eq_select_returns_old_vs_appended`. The former executes two
forward-call inputs at O1; the latter executes four select inputs each at O1 and
O3: two tests, three JIT compilations and ten generated-code calls. Their source
is `crates/trust-cg-codegen/tests/jit_integration.rs` at lines 733 and 2865,
SHA-256 `aba290348fff66997295be8bfe50bc99d7d44710dad01f3ba0279d3706b4def6`.
The shared helper explicitly uses `verify: false` in Pipeline and JIT settings.
These are hand-built TrustIR modules, not compiled TLA+ model runs. A Cargo
feature named `verify` does not change that runtime evidence boundary.

## Build, environment and terminal bookends

Nine fresh primaries were authenticated from compiler invocations and emitted
artifact records (`fresh: false`): codegen ordinary/libtest, lower ordinary/
libtest, v41 integration, opaque-handle integration, verify libtest, optimizer
libtest and native `jit_integration`. Codegen images were shared across component
selections, not rebuilt per test. The two ordinary checks produce metadata;
they are not native runtime qualification. The 64 unchanged output records cover
nine primaries, 54 direct externs and bundled `drat-trim`.

This ARM64/macOS run used the explicitly pinned September 10 Trust development compiler
through `targo --unverified`, not a verified Rust compilation or an automatic
managed-package switch. The environment SHA-256 is
`36ffa687a7d5f513171f05650cdb2535127851cb638377339aa0ac667af43f3b`.
One build job, one test thread, 64 MiB stack, incremental off, opt-level 0,
debug-info 2, assertions and overflow checks were retained. No cache clearing,
source touching or forced-rebuild invalidation was introduced.

Budgets were 7200 s/build, 60 s/list, 300 s/component group and 120 s/native group.
The frozen resource algorithm retained its 12 GB unmeasured fallback with the
canonical historical state directory; 12 GB is a scheduling reservation, not
measured RSS or a hard cap. Its only admitted policy delta was the documented
help-text literal. Compiler/list commands use the unchanged base environment;
only the 25 frame executions receive the retained proof-tool PATH. Those AY and
development Clean checker binaries are distinct from the newly pinned Clean
source libraries. No new proof-pair canary qualification is implied.

Source books cover 9,394 CG entries, 31 tool/control records, 71 sysroot entries
and 15 configuration paths. Locked upstream books cover 1,578 IR and 28,435 Clean
files. Before/after source, upstream, prefix, path-migration, resource, owner
and output identities agree. The terminal process receipt preserves four
short-lived heavy-gate sampler sleeps and their natural disappearance during
a 4.266 s passive drain, within the existing 5 s grace. No additional signals or
test-deadline extension were used. Root and independent terminal audits found
no remaining owned workload; this is not complete escaped-descendant containment.

## Retained records and archive boundary

Original evidence remains under
`/private/tmp/trust-cg-prelude-cohort-20260916.8Xzp4n`. The archive covers exactly
the 16 adoption files, 173 qualification files and five controllers/plans/history
files: 194 input records. inventory.json binds every original
absolute path, SHA-256, byte count and mode. It also lists the 64 local output
identities and distinguishes primaries, direct externs and the bundled checker.

179 raw files (3,264,350 bytes) are copied byte-for-byte with their modes, including
both result files, every small command/list/test/exit/process record, child
observations, both controllers and original plans. The plans preserve their
pre-activation wording as history; they are not current launch instructions.
The qualification result's 2,133,890 bytes are retained unmodified.

Fifteen larger files (25,823,904 bytes) stay local and are hash-inventoried:
six complete before/after input books and nine compiler logs. Their original
bytes have not been deleted, rewritten or relabelled. The archive is therefore
not a self-contained replay bundle or a portable substitute for those books.
The [small copier](archive_records.py) checks exact raw membership/hashes,
terminal named census, phase exits and current output identities before copying,
then rechecks inputs and outputs. It does not build or alter the source/cache.

Earlier scoped-LET/native/handle records and twelve independently retained
artifacts remain bound by the original history and retention receipts; their
failures or diagnostic results are not upgraded. **This report archive does
not independently retain the nine newly built primaries or release their target.**
Preserve those artifacts and obtain explicit next-owner authorization before
cache reuse. Nothing here establishes connected TY source-to-native acceptance,
x86-64/WASM runtime qualification or speed/memory superiority over TLC.
