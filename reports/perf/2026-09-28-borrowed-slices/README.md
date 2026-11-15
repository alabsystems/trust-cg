# Linux AArch64 slice element borrows

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The alloc diagnostic census drops from **17 to 15 failed roots**. Both
`String::from_utf16le_lossy` and `String::from_utf16be_lossy` now lower their
slice-pattern borrow. There are no added failures or changed surviving failures.
Full alloc/std, mandatory machine proof, self-hosting, and the compile-time and
runtime performance objective remain unfinished.

## Change

A slice extracted from a nested tuple may carry data and length as two bound
values instead of a memory slot. Element borrows previously required a slot;
pattern subslices and some metadata reads had the same restriction. The bridge
now recovers the complete pair through the existing resolver, which follows
only unique, unmodified identity definitions. It uses the selected slice's
runtime length for indices counted from the end. The pattern's minimum length
is not used as the slice length.

Reference and raw-pointer borrows, scalar reads, and element stores use the same
address calculation. Raw borrows and direct loads/stores matter because MIR
optimization can replace a reference borrow with them. Existing scalar and
aggregate store checks still apply, including rejection of incomplete wide
values. Slice-element zero-sized borrows preserve the caller's address and
alignment; they no longer request an unnecessary stack placeholder. New
admission is scoped to Linux AArch64.

## Native evidence

The matrix passes **7,974,912 checks** across LLVM and CG at O0, O1, O2, and O3:
996,864 checks per execution. A separately compiled shared type crate pins
layouts, and an LLVM driver calls each generated implementation.

Each execution varies 256 seeds, slice lengths 0 through 32, and eight starting
offsets. It checks first, second, last, penultimate and single-element patterns;
failed boolean/prefix pattern guards; runtime indices; mutable borrows; middle
subslice pointers and lengths; mutation of both ends with surrounding elements
unchanged; and a branch selecting slices of different lengths. Element shapes
are bytes, u64, a 16-byte-aligned two-word aggregate, and a 32-byte-aligned ZST.

The full fixture fails with the baseline CG backend at all four optimization
levels; LLVM accepts it at all four. The initial candidate cleared the two alloc
roots but refused optimized raw borrows and metadata reads. Those candidate
logs are retained. The final focused probe compiles in all eight configurations.
An independent stack-ZST control still compiles with LLVM and receives the named
32-byte stack-alignment refusal with CG at O0 through O3.

## Validation

Six surrounding regression tests pass **5,933,672 checks**, including two
existing negative controls. Fresh core has 44 AArch64 objects and 1,281 private
function definitions; isolated and matching-core builtins builds succeed.
LLVM and CG consumers linked against fresh CG core and matching CG builtins
each pass 81,097 checks. All-target checking, generated documentation and
diagnostic inventories, new-file and differential formatting, and whitespace
checking pass.

The strict bridge probe covers three functions with zero unmodeled shapes and
three pushed refinement obligations. Detailed results are in `results.json`.
Diagnostic codegen uses `no-proof-certs` and compiler verification
is disabled for this investigation. A strict bridge shape-coverage result is
not mandatory machine proof. The machine-proof probe remains refused on a
missing operand-exact emitted-opcode mapping.

## Identities

- Backend: `b31ea927483c01686d6090de27b034fcbb5663e2b04ad9223224014f9f128b6f`
- Harness: `e6dbd5300f2da47a5411dd5ecfc79597344edb41a75850ac4916c6546d90d718`
- Investigation: `target/borrowed-subarray-investigation`
- Baseline: `reports/perf/2026-09-28-wide-projections`

The evidence seals 254 source files and preserves module registration order.
The archive contains 3,313 independently rehashed members and is
71,284,438 compressed bytes. Its SHA-256 is
`270db1ecc3242195452325576aa62a61d6f0abffdb9c6587a8df9843e32847b5`.
The repository archive validator passes. All 254 sealed source files still
match, and the final generated-documentation check passes.

- Results
- Evidence archive
- Member hashes
- Archive identity
- Top-level inventory

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
