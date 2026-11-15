# Linux AArch64 terminate edges and C boundary aborts

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Linux AArch64 now activates exception handling for terminate edges even when a
function has no MIR cleanup blocks. Direct and closure calls, mutable argument
reloads, aggregate returns, and intercepted iterator payloads preserve those
edges. A panic crossing a C boundary reaches the panic runtime's abort routine.
**Full std, mandatory machine proof, self-hosting, and strict compile/runtime
wins over LLVM and Clang remain open.**

## Repairs and native evidence

The baseline scalar reproducer compiles and returns correct normal results at
O0–O3, but its panic escapes an `extern "C"` function and reaches the driver's
catch handler at every level. LLVM aborts instead. The separate aggregate
reproducer passes with LLVM and is rejected by CG because its terminate pad is
requested while exception handling is inactive.

The bridge now seeds EH for Linux AArch64 `UnwindAction::Terminate` edges, routes
calls through normal continuations, and gives intercepted payload calls the
terminate pad. The existing reason-specific lang items distinguish an ABI
boundary from a panic during cleanup. MIR `UnwindTerminate` blocks also call
the correct runtime entry; a plain trap previously produced SIGTRAP instead of
SIGABRT. The call-lane check treats termination as an observable cleanup effect
and rejects a dropped terminate edge. Indirect calls still require an indirect
Invoke implementation and are explicitly refused for these edges.

The iterator test exposed a separate O1 shape: constant folding supplies a
literal range directly to `map`. Map/filter construction can now materialize
that constant's rustc memory image at the inner iterator field offset, using
the existing aggregate constant writer. It retains the existing byte-copy path
for local iterator state.

The permanent LLVM/CG O0–O3 unwind/abort matrix passes **16 normal executions and
81,920 checks**, plus **80 SIGABRT subprocess checks**. Ten cases cover scalar
and aliased destinations, mutable argument reloads, direct and closure aggregate
returns, a mutable closure environment, destruction at a C boundary, iterator
payload calls, and double panic during cleanup. The panic subprocesses check
the signal, callback events, reason-specific panic text, and runtime termination
message. The driver imports
the boundary functions with an unwind-permitting ABI so an incorrectly escaping
panic is observable. Abort builds run only normal paths.

Four refusal controls pass: disabling unwind lowering and using an indirect
terminate-edged call, each at O0/O2. Eight existing regression tests pass
**1,255,572 checks**, including the previous unwind call matrix. These use the
first test executable; their modules are unchanged in the second executable,
which adds the reason-specific panic assertions to the new matrix. The all-target
check, formatting, documentation and diagnostic inventories pass.

The first candidate removed the seven core activation failures, but native
testing found the cleanup trap and O1 constant-range gaps. Those results remain
archived as failures. Final qualification uses `build-third.log`, the frozen
`third-backend.so`, `test-build-second.log`, `second.test`, and `runtime-sealed.log`.
An intermediate backend build overlapped a subsequent source edit and is not
used as source-matched evidence. Initial graph/test launches that failed before
execution because copied files lacked executable permission are retained
separately from the completed retries.

## Std graph and remaining work

Against the same frozen source graph as the preceding report, CG attempts
19 dependencies: **7 pass and 12 fail**, with **108 failing roots, down from
135**. No newly failing root symbols or compiler crashes appear in this
comparison. Compiler_builtins now passes; Cargo still cannot build std through
the remaining dependency failures. The previous LLVM build of all 20 target
crates is retained as the baseline, with its invocation and artifact identities.

| Changed dependency | Before | After |
| --- | ---: | ---: |
| compiler_builtins | 18 | 0 |
| core | 11 | 4 |
| alloc | 5 | 4 |
| object | 23 | 22 |

The other dependency root counts are unchanged. Core's remaining failures are
one cleanup SSA argument mismatch in `try_from_fn_erased` and three loop
path-consensus cases in overflowing powers and maximal-suffix search. These
checks remain active; none is bypassed to make a build pass.

Isolated std O0 completes with **348 failing roots, down from 352**, without
compiler crashes. Four old failures disappear; there are no newly failing symbols
or changed diagnostics for retained roots. This probe uses LLVM-built dependency
artifacts and does not qualify a CG sysroot. O1/O2/O3 std and other sysroot
members remain unqualified. The preceding
O2 probe timed out at 900 seconds; it was not rerun here because these repairs
do not address its compile-time cost.

Strict bridge probes pass at O0/O2: **28/21 functions**, **8/9 pushed refinement
obligations**, zero unmodeled shapes and no skipped obligations. Mandatory
machine proof still rejects uncovered instructions with `TCG-PROOF-465`.
All compiler diagnostics disable Trust frontend verification. Development
backend timings collected during concurrent work are diagnostic profiles,
not performance comparisons.

## Reproduction and identities

The archive retains exact commands, logs, source snapshots, patches, native
objects and executables, artifact hashes, and the same 3,044 frozen std/registry
source inputs. Backend and test binaries are identified by hash; rebuild them
from the archived sources in the recorded environment. Run the permanent
matrix and regression controls, proof probes, dependency graph, and isolated
std probe with its recorded deadline.

Backend SHA-256: `07fb0154cc49c50d8baf4ec8fa5d1c228670a49af47ffa4673b5b0f1490018db`.

Test executable SHA-256:
`4ff61b8940c2936e2ba1b6b4e0ddf0006ab2ab2171ca557696b1514e8c2b9570`.

The archive contains 20,406 independently rehashed files, including 281 current
backend/test source and documentation files and 3,044 frozen std/registry inputs.
Archive SHA-256: `a71e2e3cfe390e6fd48c59d969e058b933b7a9355767901135779ac28d45ca67`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
