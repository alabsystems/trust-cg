# Cycle-safe opaque-handle diagnostics — 2026-09-16

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The scoped development qualification passed **27 tests**, including both new
recursive-type regressions. Five primary artifacts were freshly compiled.
An independent read-only audit authenticated the actual compiler invocations,
named results, source/tool/artifact bookends and process cleanup. No native-code
execution, proof-required compilation, verified compiler, portability, or
performance claim is made.

## Change and qualified revision

Source revision: `e25e8a04ca8e196c6833ed53b74616416e8c505f`; tree:
`070890100930ea51cc0345f561814ca53ebf645a`. The later report commit is not the
revision compiled. Relative to main `17f1780fa4c9f9dfc1833dfe040477bf45644d03`,
the changes are the lowerer's diagnostic traversal, two regressions, and the
test inventory. No dependency pin or admission rule changes. TrustIR remains
`b094459bbe4decfa424e257e7bb9e288114f6990`.

`reachable_handle_identities` already tracked type and function-signature IDs,
but recursively expandable struct, record, enum and closure IDs were untracked.
A recursive named type could therefore make refusal diagnostics fail to finish.
Four separately typed visited sets now expand each such ID once. Duplicate
definitions still contribute all matching fields, and handle identity collection
remains conservative; this does not make unsupported recursive values admissible.
It is a termination/sharing fix, not evidence of whole-pass linear complexity.

## Tests and compilation

| Selection | Passed | What it covers |
| --- | ---: | --- |
| Lowerer unit | 1 | Self/mutual recursion across all expandable graph tables; distinct typed IDs, duplicate definitions, complete four-handle census, handle-free control |
| Full `v43_opaque_handle` integration target | 21 | Existing positive/refusal boundaries plus good → recursive named-handle refusal → good across adapter entry points |
| Exact codegen controls | 5 | Unused/inline handle gates, precise returned owners, nominal remapping, malformed identity and exported ABI refusal |

There were zero failed or ignored selected tests. All seven native list probes
matched the source-derived selection, and all seven executions matched the
listed names and summaries. The macOS ARM64 host executed Rust test binaries;
cross-adapter lowering tests do not establish generated ARM/x86/WASM execution.

Five fresh primaries (`fresh: false`) were authenticated: ordinary lowerer and
codegen metadata checks; lowerer libtest; opaque-handle integration libtest;
codegen libtest. Their exact compiler argv, generated environment, features,
profiles, paths and byte/mode/SHA identities are in audit.json.
Compilation used pinned Trust tools in the explicit `--unverified` development
lane, default debug profile, one build job, and unchanged process environment.
The codegen feature named `verify` is not proof-required compilation.

All **19 supervised phases** exited 0: five builds, seven lists, seven test
executions. Exit receipts match raw log hashes; intervals were sequential.
Budgets stayed 7200 seconds per build, 60 per list, and 300 per test group.
The unchanged resource algorithm selected its unmeasured **12-GB scheduling
reservation**, not a hard memory cap or an observed peak. No forced rebuild,
cache clearing, policy override or test waiver was used.

## Evidence and preservation

Original records remain under
`/private/tmp/trust-cg-handle-cycle-20260916.FFcKMQ/checks-e25e`:

- Terminal result SHA: `1a4815dff96976520bea262b4bba90c8e448cd4223d88aa580e394127b646ecb`.
- Enabled controller SHA: `e55b6e0da19304c07f537d00125437e72406c3a01de4ed867cf6cf9940def8f3`.
- Byte-identical before/after source books SHA: `2b9a8f744bbd5dcc3efc67b7c5aa77e90d6299e78b279b148366e33bd9e10839`.

The audit rechecked all 9,192 source entries, 31 tool/control records, 71
sysroot entries and 15 configuration paths against the then-current detached
qualification worktree. All 44 primary/direct-extern records matched, as did
the seven previously retained artifacts (577,524,729 bytes). All 19 owned
PID/PPID/process-group identities were absent; no source/target workload remained.

Before any later target reuse, a separate authorized operation retained all five
new primaries (301,120,363 bytes) under `retained-e25e/`. Copies have distinct
inodes and identical bytes, modes and hashes; originals, copies, source/tool
books, prior evidence and process absence were checked before and after.
Retention receipt SHA:
`6db0016a1ae6505f18313fae7271b269f70e99ea535f531403be692c0bc8cc0e`.
That operation did **not** release ownership of the shared cache.

The 77 small files in `records/` are exact copies of commands, process/exit
receipts, selected list/test logs, controller/environment/resource records and
retention evidence. audit.json is the derived independent audit
and inventory: it binds these copies and all original private records by hash.
Full build logs, the 1.1-MB terminal result, full source/retention snapshots and
binary copies remain private; they are not included or presented as a portable
reproduction bundle. Existing failed qualifications and unrelated evidence were
not rewritten.
