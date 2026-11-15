# Linux AArch64 projected wide pointers and owned drop — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Diagnostic `alloc` failures fall from **19 to 17**. `CStr::clone_into` and
`drop_glue::<Box<dyn Error + Send + Sync>>` now lower. No new roots appear,
and the remaining reasons are unchanged after normalizing source locations.
Full alloc/std, self-hosting, mandatory proofs, and strict compile/runtime
wins over LLVM and Clang remain unqualified.

## Implementation

`wide_projection.rs` reads and writes complete two-word pointer-wrapper
images through fixed fields/downcasts. It checks the wrapper layout,
metadata kind, containing image, projected Rust type, and byte extent.
Rustc supplies the field offsets. Both source words are loaded before either
destination word is stored, preserving self-copies. Slice-wrapper reads
through thin pointers receive complete intermediate slots. Actual collection
image validation and shared-reference mutation restrictions remain intact.

The Linux AArch64 owned-Box drop-glue path is admitted only when its checked
wrapper pointee matches the dynamic place being destroyed. The existing
virtual-drop routine recovers the data/vtable pair from the representation
actually present, tests the drop slot for null, and dispatches the payload
destructor. Rustc's glue then runs the owner's destructor. Indirect drops
requiring cleanup or termination under unwinding still fail closed.

Scalar fields in over-aligned, sized struct/tuple images can be addressed
through an already-bound thin reference using rustc offsets. This does not
allocate an over-aligned stack slot; borrowed scalar aliases and spilled
pointers retain their existing paths.

## Differential execution

The final LLVM/CG O0–O3 matrices pass **1,769,488 checks**:

- **1,204,224** projected-image checks: 49 checks × 3 metadata families ×
  1,024 seeds × 8 executions. A shared LLVM type crate fixes the layouts.
  Cases cover slices, strings, and trait objects in ordinary/C-layout
  structs, nested structs and enum payloads, plus by-value transport,
  replacement, raw self-copy, empty variants, field guards, and changed
  lengths/vtables.
- **565,264** ownership checks: 70,658 per execution × 8. A crate-local
  `owned_box` lang item exercises the real compiler-generated glue without
  the imported alloc Box interception. C callbacks validate destructor
  order/count, release address/size/alignment and allocation guards.
  Cases include ordinary, 64-byte-aligned, no-drop and zero-sized dynamic
  payloads, plus nonempty and empty boxed slices. The runs perform **32,768
  allocation/free pairs** and **24,576 payload destructor callbacks**.

Both negative controls compile with LLVM and retain named CG refusals:
inline collection images and indirect virtual-drop cleanup under unwinding.
The panic runtime used by the C driver is the selected compiler's real
runtime, with its abort control checked; no panic stubs replace core/std.

The second candidate passed the pointer matrix but rejected scalar field
reads in the aligned payload. The third passed the expanded ownership
matrix; the final candidate additionally excludes spilled references from
the new aligned-reference admission. Earlier logs are retained.

Eleven surrounding regression tests pass **4,212,936 checks**, including
structural and associated-type destruction/unwinding, pointer coercions,
wide owners, dynamic tails, and pointer images. No test is ignored.
The separate required ABI proof test still fails on its existing 14
uncovered instructions across 12 opcode kinds, first at
`aliased_f32_read[13]` (`StpPreIndex`).

Fresh core and isolated/matching compiler-builtins builds pass. Core has
44 AArch64 objects and 1,281 hidden private definitions. Both builtin
variants have 11 objects. LLVM and CG consumers linked against fresh CG
core and matching CG builtins each pass 81,097 checks.

The strict bridge probe covers three functions with zero unmodeled shapes
and zero pushed refinement obligations. Mandatory machine proof still
fails on missing emitted-opcode mappings. Shape coverage is not a formal
machine-proof result.

## Identities

- Backend: `8cfa95653d83520a0b0f8d05d858e53b8b7582a73ca088be9886a6a1a94577df`
- Harness: `03e152ba56224a6321f2ba06297f2ff147c8e829e28a7776ac4cb10c3d34b874`
- Investigation: `target/wide-projection-investigation`
- Baseline: `reports/perf/2026-09-28-pointer-coercions`

All-target checking, generated documentation and diagnostic inventories,
incremental and new-file formatting, and `git diff --check` pass. The receipt
seals 250 source files and preserves module registration order. Compiler,
core-source, and library-source identities match the prior manifests.

The archive contains 3,957 independently rehashed members and is 115,369,450
compressed bytes. Its SHA-256 is
`a6b64b8d39b6f49dcd7d92bb10004a5e124a08a5714cb33fa83c01f6b0a982f8`.
It includes source snapshots and patches, command transcripts, the alloc MIR
trace, native objects/executables and identities, negative controls, rejected
candidate logs, fresh core/builtins evidence, and proof-gate results.
The repository archive validator passes; the final source recheck matches all
250 sealed files, and the final generated-documentation check passes.

- Results
- Evidence archive
- Member hashes
- Archive identity
- Top-level inventory

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
