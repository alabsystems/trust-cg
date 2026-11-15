# Linux AArch64 unwind call continuations

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Calls can now reload mutable arguments and store returned values on their normal
edge while preserving the panic cleanup edge. Closure aggregate returns use the
same continuation. Cleanup suffixes that need no incoming SSA values no longer
receive artificial block parameters. **Full std, mandatory machine proof,
self-hosting, and strict compile/runtime wins over LLVM and Clang remain open.**

## Changes and native checks

Linux AArch64 calls that require work after returning now invoke a fresh normal
continuation. That continuation reloads mutable arguments before assigning the
return value, then branches to the original MIR successor. Unwinding bypasses
those operations. Closure returns preserve rustc's existing scalar-pair or
hidden-return-buffer ABI. Pure SSA result bindings keep their existing direct
normal edge; other targets retain their existing behavior.

A reverse CFG analysis identifies cleanup suffixes ending in resume, terminate,
or unreachable whose statements are only storage markers or no-ops. It can
follow gotos, monomorphized destructor-free drops, and bool switches that read
stable scalar cells. Every successor must qualify. It excludes real drops,
calls, assignments, other value reads, and cycles without a qualifying terminal.
These suffixes retain their actual instructions and edges, but require no
incoming scalar, projected, or borrowed-scalar SSA joins. The SSA and unwind
checks remain enabled.

The permanent matrix passes **16 executions and 73,728 checks**: LLVM and CG,
O0–O3, with unwind and abort builds. Eleven cases cover cells, memory-backed and
scalarized projected destinations, mutable argument reloads, closure scalar,
pair and large aggregate returns, repeated calls in a loop, and a generic
comparison with drop flags. The aliasing case assigns a call's return value to
the same variable the callee mutates. Its destructor sees the mutation on panic
and the assigned result on normal return. The LLVM-built driver checks exact
return values and event order, including each possible panic point. Abort builds
run only the normal paths. Two `disable-unwind` controls still reject observable
cleanup, at O0/O2.

Archived baseline fixtures pass with LLVM and fail with the baseline backend at
all four optimization levels. Intermediate candidates separately demonstrate
the call-continuation repair and removal of the remaining artificial cleanup
parameters. The final eleven-case matrix is identified by `test-build-fourth.log`,
`final.test`, and `runtime-final.log`. Earlier fixture versions and a rejected
test invocation with a duplicate edition argument are retained as development
records, not counted as final validation.

Seven existing regressions pass **1,181,844 checks**, covering associated drops,
closure wrappers, foreign statics, aggregate returns, residual conversion,
scalar-cell returns, and try-fold unwinding. They use the final backend and the
earlier test executable; those seven test modules are unchanged. The final
all-target check, formatting, documentation and diagnostic inventory checks pass.

## Broader std census

This reruns the preceding std census against the same frozen library and registry
inputs, with unwind and backtrace enabled. The previous LLVM graph built all
20 target crates. The current CG graph still attempts 19 dependencies: **6 pass,
13 fail**, with **135 failed roots, down from 182**. There are no compiler crashes
and no newly failing root symbols in that comparison. Cargo still cannot reach
std through these dependency failures.

| Dependency | Before | After |
| --- | ---: | ---: |
| core | 46 | 11 |
| gimli | 37 | 36 |
| object | 25 | 23 |
| compiler_builtins | 19 | 18 |
| rustc_demangle | 16 | 15 |
| addr2line | 9 | 5 |
| alloc | 7 | 5 |
| std_detect | 7 | 7 |
| libc | 5 | 5 |
| miniz_oxide | 5 | 4 |
| hashbrown | 4 | 4 |
| adler2 | 1 | 1 |
| panic_unwind | 1 | 1 |

Isolated std O0, using the successful LLVM dependency artifacts, completes with
**352 failed roots, down from 426**: 74 previously failing symbols disappear and
none are added. Fifteen retained symbols reach different diagnostics. This is a
complete diagnostic census, not a successful CG sysroot build. The isolated O2
run again reaches its **900-second resource limit** and exits by SIGTERM. It has
no complete root census; its empty aggregate root list is not a passing result.
O1/O3 and the other sysroot members remain unqualified.

Core's remaining eleven failures comprise seven inactive terminate-pad cases,
one cleanup SSA case, and three loop path-consensus cases. These remain explicit
failures. Broader dependencies also retain layout, projected-memory, SIMD and
other lowering gaps. The archived deltas retain both old and new diagnostics.

Timing marks show substantial completed work in predecessor analysis,
memory-backed-local analysis, and block lowering, with individual completed MIR
lowerings taking roughly ten seconds in this development build. These profiles
guide further investigation. They omit unfinished stages, use truncated symbol
prefixes, and were collected during concurrent diagnostic work; they establish
no compile-time or runtime advantage.

## Proof boundary and reproduction

Strict bridge probes pass at O0/O2 with **36/34 functions**, **27/26 pushed
refinement obligations**, zero unmodeled shapes and no skipped obligations.
Mandatory machine proof still rejects uncovered AArch64 instructions with
`TCG-PROOF-465`. All compiler/native diagnostics here disable Trust frontend
verification. Native correctness and bridge coverage do not establish full
machine proof or completion of the Linux plan.

The evidence freezes commands, logs, source snapshots, full and incremental
patches, native objects/executables, source input manifests and artifact hashes.
It includes the same 3,044 frozen std/registry source files and the prior LLVM
invocation records needed to reconstruct the isolated probes. Backend and test
binaries are identified by hash; rebuild them from the archived sources in the
recorded environment. Run the permanent matrix, regression controls, strict and
mandatory-proof probes, then the dependency graph and isolated std probes with
their recorded resource limits.

Backend SHA-256: `8f014110ad4d365f82cecb03ce0360e23aa46c23e0d9e8a3045f1d203f01231d`.

Final test executable SHA-256:
`7ad40f599399743271e6f3dcaaf0dd26942d478a0a25e7018f4d1b99b3293299`.

The archive contains 38,044 independently rehashed files and 278 backend/test
source and documentation files, plus the 3,044 frozen std/registry source files.
Archive SHA-256: `8f426992df0563bafc40e58b357e3162d93b7212a3dad7636e0bd166213ee26f`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
