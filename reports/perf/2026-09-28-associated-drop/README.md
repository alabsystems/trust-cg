# Associated owned fields in structural drop — Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This diagnostic increment reduces `alloc` from **31 to 28 failing functions**.
It removes all three remaining `Cow<str>` drop failures: `to_mut` and both
`AddAssign` implementations. No roots are added and no remaining failure reasons
change. Full alloc/std builds, self-hosting, mandatory proofs, and strict
compile/runtime wins over LLVM and Clang remain unqualified.

The frozen backend is `6414c25049f925bea41e5ee8077a68015a3752d2501a614caf1528b6600730ae`
(`target/associated-drop-investigation/first-backend.so`). The test harness is
`third.test`. Commands and artifact hashes are archived. The compiler remains
Trust 1.99.0-dev `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, with LLVM 22.1.2.
The baseline is the [structural-drop increment](../2026-09-28-structural-drop/README.md).

## Change

An instantiated ADT field can still contain an associated-type projection.
`Cow::Owned`, for example, contains `<B as ToOwned>::Owned`. Structural drop
admission previously classified the unresolved projection and refused it.
It now asks rustc to normalize the field in the fully monomorphized environment
before inspecting the concrete type. Collection exclusions and recursive
ownership checks therefore examine the same concrete type used by layout and
drop-glue queries. The production change is confined to that field classifier;
it adds no machine instructions or alternate collection representation.

The initial associated-type probe is accepted by LLVM and refused by the
baseline CG backend at O0, O1, O2 and O3. The new backend accepts all four.
A separate negative control hides a consumer-modeled Vec behind an associated
owned type; it remains an LLVM-positive/CG-negative collection-image refusal.

## Validation

An independently LLVM-compiled driver calls LLVM and CG corpus objects at
O0–O3. The normal matrix passes **131,072 checks** over eight executions.
Associated payloads cover a leaf destructor, an array, a tuple, nested generic
fields, an optional payload, a zero-sized destructor, replacement, and a
slice-borrowed/owned-buffer enum. The driver's allocation registry verifies
**8,192 allocation/free pairs** for exactly-once release and correct values.

The associated-field unwind matrix passes **6,144 checks** over eight
executions. It tests normal destruction, an external panic, and panics in a
parent destructor, either child, and the outer destructor. The expected order
is checked after LLVM `catch_unwind`. Double-panic abort behavior is not
separately qualified here.

The previous structural-drop and zero-sized-drop controls pass **138,488
checks**, with their collection/ZST refusal controls intact. The selected
control harness has five passing tests, one required machine-proof failure,
and zero ignored tests. The initial standalone driver had a Rust temporary
lifetime error; its source and failing compiler logs are retained, and it is
not counted as native evidence.

Fresh core and both compiler-builtins configurations compile in the diagnostic
lane. Core retains 44 ELF64 AArch64 objects and 1,281 hidden private functions.
The LLVM and CG consumers both link the new core and matching CG builtins and
pass 81,097 UTF-8 checks each. Builtins retain 11 AArch64 objects per build and
all six weak floating-point exports. `check --all-targets`, documentation and
diagnostic inventory checks, differential formatting, fixture formatting and
`git diff --check` pass.

The isolated four-function probe passes strict bridge coverage with zero
unmodeled shapes and zero refinement obligations. This records classifier
coverage; it does not prove drop semantics, ownership or unwind behavior.
Mandatory machine-proof promotion still fails. The required ABI control still
reports 14 uncovered instructions across 12 opcode kinds, beginning with
`aliased_f32_read[13]` (`StpPreIndex`). Diagnostic runs use
`-Ztrust-verify=off` and CG's `no-proof-certs` where applicable. No performance
qualification is claimed; the separate C linker is GCC, not Clang.

## Durable record

results.json records the matrix and all 28 remaining roots.
assets.json inventories archive members; archive.json
identifies the compressed bytes. The archive includes current and baseline
source, frozen library source, incremental and worktree patches, commands,
complete logs, objects, native executables, and artifact identities. Large
backend, harness and rlib files are represented by hashes and build records.

Sealed archive: `0b10a9f5946f50cf3c20bbca0e2e72453d34f36748d044df13d41d41fb3ce5b8`, 2,326 members,
57,170,446 compressed bytes. All 220 source hashes match the working tree;
independent member rehashing and the standard archive check pass.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
