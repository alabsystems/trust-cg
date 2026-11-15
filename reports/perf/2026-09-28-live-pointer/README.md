# Linux AArch64 live pointer reads after alias mutation

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Thin raw reborrows and nested array copies now load an address-taken pointer's
current value. This fixes an observed stale-address miscompile at O0 and O2 and
lets the main `Ipv6Addr::fmt` body compile at O2/O3. Optimized core improves from
23 to 22 failing functions. **Full Linux completion and strict compile/runtime
wins over LLVM and Clang remain open.**

## Cause and repair

A function takes a reference parameter, passes its address to a call that
replaces it, then returns `p as *const T` or `&raw const p.field`. The old raw
reborrow lowering read the original entry-parameter register. Its guard admitted
entry parameters even when their actual current value lived in a scalar cell.
An independent C driver observes the old address in four baseline executions
(two cases, O0/O2), while LLVM returns the replacement address in every case.

Both raw reborrow paths now use `value_for_runtime_scalar_local`, which loads a
cell when one exists and retains ordinary SSA handling otherwise. Their admission
includes scalar cells and checks that the source is a thin pointer. The existing
placeholder-borrow refusal remains active. Two nested aggregate/array copy paths
also admit and load pointer cells instead of using the SSA-only reader. Their
layout, projection, aggregate and pointer-type restrictions remain active.

The optimized-core diagnostic names `nested_field_deref_source_addr` as the
missing live read in `Ipv6Addr::fmt`. A separate mutation fixture also exposes
the sibling scalarized-array path. The first repaired candidate passes every
small probe; the final candidate only reformats that production change and adds
the permanent regression matrix.

## Validation

The permanent test passes **1,310,720 checks in 16 native executions**, comparing
CG and LLVM at O0–O3 under abort and unwind policies. A C caller replaces pointer
storage through opaque calls and checks whole/field addresses, nested array
returns and stores, surrounding canaries, non-parameter locals, and unchanged
versus replaced control-flow branches. Both the alias writes and expected
addresses/bytes are supplied by C.

Seventeen broader tests pass **16,645,940 checks**, 104 SIGABRT cases and eight
expected refusals. They cover earlier pointer, borrowed-storage, scalar-cell,
enum, panic, unwind, ownership, caller-location, foreign-static, private-linkage
and Linux relocation cases. The all-targets build, formatting, documentation,
diagnostic inventory and diff checks pass.

Core still builds at O0/O1. O2/O3 each remove the `Ipv6Addr::fmt` refusal, leaving
**22 failing functions**, with no added or changed failures. The full CG graph
attempts 19 crates: eight pass, eleven fail, and its **103 failing functions** and
diagnostics are unchanged, with no compiler crashes. Isolated O0 std, built
against frozen LLVM dependencies, retains the same **314 failing functions** and
diagnostics. Every final census finishes without a timeout.

Two coherent graphs rebuild core at O0/O1 with CG and all other std dependencies
with LLVM. Actual std-dylib consumers pass **324,388 UTF-8 checks**, plus **224
caught panics and 224 destructor executions**. Loader traces identify the rebuilt
libraries, and symbol checks trace the exercised routines to their CG core
objects. This is mixed-codegen integration evidence; full CG-built std remains
unfinished. The initial graph-launch attempts never executed a compiler because
the copied harness wrappers were missing or not executable. Those failures are
retained separately, and all three graphs were run after correcting the harness.

Strict bridge probes pass for six functions at each of O0/O2, with **2/0 scalar
refinement obligations**, zero unmodeled shapes and zero skipped obligations.
They generate **no memory-refinement obligations** for this fixture. Mandatory
machine proof still refuses with `TCG-PROOF-465`. These checks do not establish a
complete proof of the aliasing behavior. Development builds disable Trust frontend
verification, and concurrent development timings are not performance measurements.

## Remaining work and reproduction

Read-only follow-up probes reproduce another optimized-core boundary: stores of
fully initialized `MaybeUninit<u8>` and `MaybeUninit<u64>` constants pass LLVM at
O0/O2 and CG at O0, but CG at O2 refuses `ConstValue::Indirect`. The retained core
MIR shows the same form in several numeric-formatting failures. That repair is
not included here. A smaller formatter-only probe compiles at both levels and
does not reproduce the remaining core raw-borrow refusals.

`build-second.py` builds the immutable final backend and `first.test` executable.
`qualify-second.py`, `retry-graphs.py`, `dynamic-consumers.py`, `check-dynamic.py`
and `compare.py` retain commands, results and independent comparisons. Records
include baseline failures, both backend source snapshots, native objects and
executables, MIR, shared libraries, loader traces, and artifact identities.
The 295 current source files, prior 292-file snapshot, frozen 3,044 std sources,
registry inputs and compiler identities are rehashed. Large backend, test and
library archives are identified alongside their build commands and inputs.
This is development evidence, not the consolidated anonymous-clone acceptance
report required by the completion plan.

Backend SHA-256:
`159ec2bdca45ec619d6ac4ee23ee04ac8f696377739351f28b71e86caf4bff0f`.

Native test executable SHA-256:
`1de56466e2f21a4bc0dc4ce5ef4231d026d03c4de7fe9ee401cc8223377103b1`.

The evidence archive contains 23,888 files and is 205,528,897 compressed bytes.
Every member was independently rehashed against `assets.json`.
Archive SHA-256:
`074ba8ddf96de8f1f6c326422ab5a40930a3d8a1d78837a41d6db2741a0cbcab`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
