# Structural drop glue — Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This diagnostic increment reduces `alloc` from **40 to 31 failing functions**.
Nine roots disappear, with no new roots or changed reasons among the remaining
failures. Full alloc/std builds, self-hosting, mandatory proofs, and strict
compile/runtime wins over LLVM and Clang remain open. No performance
qualification is claimed.

The frozen backend is `f83ee39028e565c466066c2dc1538ef2bdef89972139036ca94bf6ae300988d5`
(`target/structural-drop-investigation/final-backend.so`). It uses the pinned
Trust 1.99.0-dev `ae9c2c1daa0fc80afbfd380e493f5581ac714acb` and LLVM 22.1.2.
The baseline is the [projected-aggregate increment](../2026-09-28-projected-aggregate/README.md).

## Changes

The bridge now invokes rustc's real drop glue for supported sized structs,
enums, tuples and arrays with droppable fields. Aggregate locals, partial-move
sources and drop temporaries use actual rustc memory layouts. Copies connected
to such a temporary retain that representation. Pointer-led drops use the
original allocation and rustc's field offsets, preserving destructor-visible
addresses. Scalar cells and zero-sized borrow/drop addresses retain their
identity. Cleanup and terminate destinations still use the existing Invoke
path.

Consumer-side collection models remain excluded from the new structural
admission path. Local `alloc` definitions keep their real layouts and ordinary
MIR bodies. The established custom-destructor path remains available for
structs whose fields need no destruction, including iterator storage containing
`MaybeUninit`. The address walker refuses an additional dereference that would
require another pointer load. Unsized pointees remain outside this increment.

The removed roots include String's drop glue, `from_utf16`,
`from_utf8_lossy_owned`, both UTF-16 `try_process` instantiations,
`FromUtf8Error::into_utf8_lossy`, the NulError conversion, the Box/Custom glue,
and `RawVec<u8>::into_box`. The remaining roots are recorded verbatim in
results.json.

## Evidence

The independently LLVM-compiled driver checks LLVM and CG corpus objects at
O0 through O3. The normal matrix passes **131,072 checks** across eight
executions. Cases cover nested destructors, parent-destructor mutation before
field drops, declaration order, partial moves in both branches, tuples, enum
variants, niche options, arrays, replacement, zero-sized fields, and pointer
identity. An LLVM allocation registry checks **32,768 allocation/free pairs**
across these runs for exactly-once release and correct payload values.

The unwind matrix passes **6,144 checks** across eight executions. It checks
normal destruction, an external panic with live aggregate locals, and panics
in the parent, either child, and outer destructor. Every case records the
expected destruction order and reaches the LLVM driver's `catch_unwind`.
This matrix does not separately test double-panic abort behavior.

Two LLVM-positive/CG-negative controls retain named refusals for a leading-ZST
tuple borrow and an aggregate owning a consumer-modeled Vec. The initial
collection fixture failed earlier at a different unsupported path; that
counterexample is retained, and the final fixture isolates the collection-image
boundary. Earlier candidates and failures are retained as diagnostic records,
including the optimized drop-temporary copy refusal and the intermediate
iterator regression. They are not qualification artifacts.

The existing pointer-image, wide-owner, projected-aggregate, static-alignment,
function-linkage and zero-sized-drop controls pass **8,956,556 checks**.
Their harness reports eight passing tests, one still-required machine-proof
failure and zero ignored tests. `check --all-targets`, documentation inventory
and diagnostic census checks, differential formatting, new-fixture formatting
and `git diff --check` pass. The new matrix uses the immutable `third.test`
harness; the existing controls use `second.test`. Both pin the same backend.

Fresh core, isolated compiler-builtins, and compiler-builtins linked against
the new core compile in the diagnostic lane. Core retains 44 ELF64 AArch64
objects and 1,281 hidden private functions. Both LLVM and CG consumers link the
new core and matching builtins and pass 81,097 UTF-8 checks each. Builtins retain
11 AArch64 objects per build and all six weak floating-point exports.

The isolated seven-function drop probe passes strict bridge coverage with no
unmodeled shapes;
its refinement evidence covers one scalar XOR selection, not destructor order,
allocation ownership, drop addressing, or unwind behavior. Mandatory machine
proof promotion still fails. The required ABI proof control still reports
14 uncovered instructions across 12 opcode kinds, beginning with
`aliased_f32_read[13]` (`StpPreIndex`). Diagnostic execution is not proof-enabled
admission.

All diagnostic builds use `-Ztrust-verify=off` and CG's `no-proof-certs` where
applicable. Source checks, existing regression results, exact commands, compiler
and artifact identities, and failed candidates are retained in the archive.
The core-consumer C linker is GCC, not Clang.

## Durable record

results.json records the measured matrix and remaining roots.
assets.json inventories the archive members, and
archive.json identifies the compressed evidence. The archive
contains source snapshots, incremental and worktree patches, frozen library
source, complete logs, commands, objects, and native executables. Large backend,
harness and rlib files are represented by hashes and build records. Every
member is rehashed independently before the standard evidence-archive check.

Sealed archive: `fc99126d840d0218be2a0c6b6fc94206d7f3aec8ef163d9f656a13cb306aa242`, 3,377 members,
118,675,227 compressed bytes. All 214 source hashes match the working tree;
independent member rehashing and the standard archive check pass.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
