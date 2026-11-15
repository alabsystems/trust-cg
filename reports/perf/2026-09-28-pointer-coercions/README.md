# Linux AArch64 pointer-wrapper coercions — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Diagnostic `alloc` failures fall from **22 to 19**, with no added roots.
`Box<[u8]>::default` and both `From<String>` conversions to boxed error
trait objects now lower. `CStr::clone_into` gets through its coercion and
stops at a separate projected-assignment refusal. The other remaining
reasons are unchanged after normalizing source locations.

This does **not** qualify full alloc/std, self-hosting, mandatory proofs,
or a compile-time/runtime advantage over LLVM or Clang.

## Change and boundaries

`src/pointer_coercions.rs` checks matching wrapper ADTs, exactly one non-ZST
payload at offset zero, and equal size/alignment/backend representation at
every level. Its terminal pointer layouts must match the checked AArch64
one-word or two-word image. Array lengths and trait vtables come from
rustc's monomorphic types; trait upcasts use rustc's supertrait-vtable query.
The data address remains the allocation address, including for `Rc`/`Arc`
headers and custom structs with unsized tails.

Intermediate wide-slice coercions receive complete two-word slots. When
constant propagation replaces a coercion, initialized constant wrapper
images load through the emitted allocation, retaining pointer relocations
and dangling pointer address bits. The new path is restricted to Linux
AArch64. It leaves the collection representation guards intact and rejects
wrappers with additional nonzero-sized state. Projected wide sources and
coercion destinations, unsupported metadata transformations, and creation
of auto-trait-only objects remain outside this increment.

## Native evidence

The final LLVM/CG O0–O3 matrix passes **417,792 checks** (51 checks × 1,024
seeds × 8 executions). A shared LLVM-built type crate pins the ABI layouts;
the LLVM driver checks data addresses, metadata, contents, dynamic dispatch,
and ownership effects. Cases cover transparent and ordinary wrappers,
`NonNull`, `Box`, `Rc`, `Arc`, empty and zero-sized arrays, structs with
unsized tails, auto-trait removal, a non-prefix supertrait upcast,
intermediate calls, and constant pointers with and without relocations.
The driver checks destruction of 24,576 heap-owned values and retention by
cloned `Rc`/`Arc` owners. This count is not an allocator/free counter.

Two LLVM-positive controls remain named CG refusals: additional wrapper
state (`TCG-POINTER-COERCION-IMAGE`) and collection images
(`TCG-COLLECTION-IMAGE`). Neither is ignored.

The first candidate passed the initial 368,640-check matrix. The expanded
second candidate exposed a constant-folded empty wrapper failure at O2.
The final candidate fixes that path and adds a relocated static-pointer
control; the earlier results and failure are retained.

Fresh diagnostic core and compiler-builtins builds pass. Core has 44
AArch64 objects and 1,281 hidden private definitions; both builtin variants
have 11 objects. The LLVM and CG consumers linked against the fresh CG
core and matching CG builtins each pass 81,097 checks.

Seven surrounding regression tests pass **4,948,632 checks** across whole
aggregate stores, pointer images, wide owners, slice tails, and dynamic
tails. The separate required ABI proof test still fails on the existing
14 uncovered instructions across 12 opcode kinds, starting at
`aliased_f32_read[13]` with `StpPreIndex`; no test is ignored.

The strict bridge probe reports three functions with zero unmodeled shapes
and zero pushed refinement obligations. Mandatory machine proof still
rejects emitted AArch64 opcodes, beginning with `StpPreIndex`; bridge shape
coverage is not a machine-proof result.

## Identities

- Backend: `38c5a728115a1768c35a771c687648fb3a66f6b0dcac3d0b547f947c7c6b8327`
- Harness: `17da81acd2fa6e7e7d6ec3f8bf268fc0cadabab440c64e747f380db68a9af8da`
- Investigation: `target/pointer-coercion-investigation`
- Baseline: `reports/perf/2026-09-28-aggregate-store`

All-target checking, generated documentation/diagnostic inventories,
incremental formatting, new-file formatting, and `git diff --check` pass.
The repository evidence-archive validator passes. All 242 sealed source
files match the receipt. Compiler and frozen-library
identities are checked against the prior evidence.

The archive contains 3,047 independently rehashed members and is 120,842,887
compressed bytes. Its SHA-256 is
`7e4e384a0e1722944c88b89a2fa4fa5c92b756df012148f703eb7f570c3d73a5`.
The record set includes the final source receipt, incremental and full
working-tree patches, commands, logs, MIR, object/executable identities,
and the rejected intermediate candidate's results.

- Results
- Evidence archive
- Member hashes
- Archive identity
- Top-level inventory

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
