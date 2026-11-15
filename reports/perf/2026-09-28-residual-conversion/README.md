# Result residual conversions and aggregate cleanup — Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This diagnostic increment reduces `alloc` from **28 to 25 failing functions**.
It removes `RawVecInner::grow_exact`, `shrink_unchecked`, and `grow_amortized`:
all three convert `TryReserveErrorKind` into `TryReserveError`. No roots are
added and no remaining failure reasons change. Full alloc/std, self-hosting,
mandatory proofs, and strict compile/runtime wins over LLVM and Clang remain
unqualified.

The frozen backend is `5ae2e8862b5826da911f60770dfe8a8670f00c2ac63fc615ea2f6d8c45e7b870`
(`target/residual-conversion-investigation/second-backend.so`). The harness is
`second.test`. Commands and artifact hashes are archived. The compiler remains
Trust 1.99.0-dev `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, with LLVM 22.1.2.
The baseline is the [associated-drop increment](../2026-09-28-associated-drop/README.md).

## Change

On Linux AArch64, an inhabited non-identity `Result` residual takes the ordinary
call path. That compiles the actual `FromResidual` MIR, including its call to
`From::from`, concrete layouts, and hidden caller location. The identity
`Result`/`Option` interception remains bounded as before. Other targets retain
their existing policy; this record does not qualify them.

Panic testing exposed a second boundary: direct aggregate-returning calls with
live cleanup emitted a plain call and were correctly refused by the unwind
edge audit. Such Linux AArch64 calls now end with `Invoke` and a fresh normal
continuation. Return stores and mutable-argument reloads occur only there. The
existing ABI plans still govern indirect return buffers, scalar pairs, and
aggregate/HFA carriers. A callee can write an indirect return buffer before it
panics; this change makes no claim that such bytes remain untouched.

The helper retains the existing cleanup audit, invokes existing terminate pads
when EH is active, and refuses a terminate-pad request when EH is inactive.
A standalone LLVM-positive/CG-negative probe confirms the inactive-EH
refusal for a sole-terminate aggregate call. Sole-terminate functions and
double-panic abort semantics are not newly qualified by this matrix. Indirect calls and other return lanes retain their
existing boundaries.

The initial scalar-conversion probe fails on the baseline at O0/O1; O2/O3
already fold the conversion sufficiently to compile. The new backend accepts
all four. Its first candidate passed the normal matrix and removed the three
alloc roots but failed the unwind fixture with `TCG-EH-CALL-EDGE`. That record
is retained. An initial build of the cleanup fix had a target-OS enum type
error; only the successful retry produced the frozen second backend.

## Validation

LLVM-compiled drivers call LLVM and CG corpus objects at O0–O3 and check
independent expected values and event traces. The normal matrix passes
**163,840 checks** across scalar, narrow/niche, aggregate, enum, zero-sized,
owned and chained conversions, identity controls, explicit `FromResidual`,
and a reified function pointer. The allocation registry checks **8,192
allocation/free pairs** for consumed owned errors.

The residual-conversion unwind matrix passes **8,192 checks**: normal return,
conversion panic, consumed-input destruction, and inner/outer guard order. A
separate return-ABI matrix passes **16,384 checks** for Rust scalar-pair returns,
C integer aggregates, indirect return buffers, and three-member floating-point
aggregates. It verifies a callee's mutable argument update on both normal and
panic paths, normal-only post-call events, and guard cleanup. Total new native
checks: **188,416**. The collection-image negative control remains
LLVM-positive and CG-negative. The new test group has four passing tests and
zero failures or ignored tests.

Existing associated-drop, caller-location, ControlFlow residual, and
uninhabited-argument controls pass **172,768 checks**. Their collection refusal
also remains intact. The selected control harness has six passing tests, one
required machine-proof failure, and zero ignored tests.

Fresh core and both compiler-builtins configurations compile diagnostically.
Core retains 44 ELF64 AArch64 objects and 1,281 hidden private functions. LLVM
and CG consumers both link the new core and matching CG builtins and pass
81,097 UTF-8 checks each. Builtins retain 11 AArch64 objects per configuration
and all six weak floating-point exports. `check --all-targets`, documentation,
diagnostic inventory, differential formatting, fixture formatting, and
`git diff --check` pass.

The isolated seven-function conversion probe passes strict bridge coverage
with zero unmodeled shapes, two scalar op-selection refinements, and bounded
field-load refinements. Those do not prove conversion semantics, ownership,
control flow, or unwinding. Mandatory machine-proof promotion still fails. The
required ABI control reports 14 uncovered instructions across 12 opcode kinds,
beginning with `aliased_f32_read[13]` (`StpPreIndex`). Diagnostic runs use
`-Ztrust-verify=off` and CG's `no-proof-certs` where applicable. No performance
qualification is claimed; the separate C linker is GCC, not Clang.

## Durable record

results.json records the matrix and all 25 remaining roots.
assets.json inventories archive members; archive.json
identifies the compressed bytes. The archive includes current and baseline
source, frozen library source, incremental and worktree patches, commands,
complete logs, objects, native executables, and artifact identities. Large
backend, harness, and rlib files are represented by hashes and build records.

Sealed archive: `0f7a6f9f58e6bf695b89441f35d3cb51e344f2a45aa5087e598dab18fbf3c251`, 2,820 members,
98,611,878 compressed bytes. All 228 source hashes match the working tree;
independent member rehashing and the standard archive check pass.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
