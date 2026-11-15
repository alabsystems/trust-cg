# Projected aggregate arguments and Rust pair boundaries — Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This diagnostic increment removes five `alloc` compilation failures, reducing
the census from **45 to 40 failing functions**, with no new roots or changed
reasons among the remaining failures. It also fixes two native ABI
counterexamples discovered by the new argument matrix. Full alloc/std builds,
self-hosting, mandatory proofs, and strict compile/runtime wins over LLVM and
Clang remain open. No performance qualification is claimed.

The tested backend is `09970e46d1bf4686bfc70e579d41f9308df67099c79d90b885ae4b1f2e915e19`
(`target/projected-aggregate-investigation/zst-backend.so`). The file named
`final-backend.so` in that investigation is an earlier, rejected candidate;
its optimized leading-ZST tuple-copy failure is retained. The harness is
`eighth.test`; exact identities and commands are in results.json
and the archived source receipt. The compiler is the same pinned Trust
1.99.0-dev `ae9c2c1daa0fc80afbfd380e493f5581ac714acb` with LLVM 22.1.2 as the
[static-alignment baseline](../2026-09-28-static-alignment/README.md).

## Changes

- `const_eval_select` remaps its argument tuple to projected operands. The
  bridge now assembles scalarized source bytes when necessary and copies an
  aggregate field at rustc's actual byte offset into a fresh argument slot.
  Type equality, source bounds, and load alignment are checked. Scalar siblings
  such as the bool in `(Layout, bool)` use the construction's flattened leaf
  index instead of the MIR field number.
- An optimized copy of a flat nested struct into a scalarized temporary retains
  its MIR field indices, including holes for zero-sized fields. Nested aggregate
  constructions retain their existing flattened indices.
- Qualifying Rust `PassMode::Pair` arguments on Linux AArch64 use independent
  scalar lanes at definitions and calls. With seven preceding integers, LLVM
  puts the first integer lane in `x7` and the next on the stack. The previous
  whole-aggregate path shifted values at that boundary. Rustc's FnAbi checks,
  float-carrier handling, and closure exclusions remain in place.
- Indirect AArch64 calls store both halves of a stack-passed `i128`. The old
  path stored only the low half. Narrow scalar stack stores now use the same
  width-specific instructions as direct calls.

No machine encoding was added. The production edits are in the MIR bridge
and the existing AArch64 indirect-call selector. The incremental patch is
separate from the complete pre-existing dirty-worktree patch in the archive.

## Native evidence

An independently LLVM-compiled driver calls LLVM and CG objects at O0, O1,
O2, and O3, and receives callbacks from each. All eight executions pass
**99,588 checks each: 796,704 checks total**. Both implementations share the
same LLVM-built type metadata, while the driver supplies and checks values
independently of the CG corpus.

Twelve types cover `Layout`, integer pairs/triples, narrow and packed structs,
floating bit patterns, a slice-containing record, a tagged enum, a record
containing `u128`, leading/interior zero-sized fields, and nested structs.
Cases cover selected tuple fields, tuple parameters, multiple aggregate
arguments, repeated calls, mutation before passing, and seven-integer
register pressure in both cross-backend directions. There are 258 input seeds
per type, plus 516 bool-sibling cases. The leading-ZST mutable-reference case
remains a named refusal and is excluded from the positive mutation form only;
its by-value forms run at every optimization level.

Four LLVM-positive/CG-negative controls retain named refusals for leading-ZST
borrows, a tuple containing an array-bearing union, indirect large aggregate
returns, and the unsupported four-float Rust return convention. No test is
ignored. Downcast-specific call projections and reduced-alignment enclosing
packed containers are not separately qualified by this matrix.

The archive preserves the failing initial fixtures and native counterexamples:
ordinary two-integer argument forwarding fails with both the baseline and the
first projected-argument implementation; the independent-lane repair fixes it.
The full matrix then exposes the indirect `u128` high-half loss, followed by
the optimized ZST temporary-binding refusal. Neither failed candidate is used
for the final totals.

The current backend also passes the pointer-image, wide-owner, static-alignment
and function-linkage controls: **8,158,580 existing checks**. Their selected
harness result is four passing diagnostic tests and one required machine-proof
failure, with zero ignored tests. `check --all-targets`, documentation checks,
differential formatting checks, new-fixture formatting and `git diff --check`
pass.

## Build and proof limits

The five removed roots are `Global::alloc_impl`, `deallocate_impl`, `grow_impl`,
`shrink_impl`, and `handle_alloc_error`. The remaining 40 are listed verbatim in
results.json. They are still compilation failures; this is not
an alloc or std build success.

Fresh core and compiler-builtins compile in the explicit diagnostic lane.
Core contains 44 ELF64 AArch64 objects and 1,281 hidden private functions.
Both independently compiled consumer lanes link this core and matching CG
compiler-builtins and pass 81,097 UTF-8 checks each. The two builtins builds
contain 11 AArch64 objects each and retain all six weak FP exports.
The isolated four-function proof probe passes strict bridge coverage with no
unmodeled shapes: it discharges two scalar operation-selection obligations
and four fixed-offset field-load obligations. These do not prove aggregate
argument copying, ABI placement, or the new indirect stack stores. All four
functions still fail mandatory machine-proof promotion with `TCG-PROOF-465`.
The standard mandatory ABI proof test remains required and failing; it is not
counted as a passing diagnostic test.

The reported build and native-pass totals use `-Ztrust-verify=off` and CG's
`no-proof-certs` diagnostic lane where applicable. It supplies correctness
regression evidence within the tested domain, not proof-enabled admission or
performance evidence. `cc` in the separate core-consumer link is GCC, not Clang.

## Durable evidence

results.json records the measured matrix and remaining roots.
assets.json inventories the evidence archive's members, and
archive.json identifies its compressed bytes. The archive
contains current source, incremental and worktree patches, source manifests,
commands, complete logs, object files, native executables and counterexamples.
Large backend/harness/rlib artifacts are represented by their identities and
build records. The archive is independently rehashed member by member and
checked with `scripts/check_evidence_archive.py` before this record is sealed.

Archive SHA-256: `b261c3d9390274aec74038ac337f21f2d9dac9b652126611a2b56bb4765f0e52` (5,604 files; 136,928,047 compressed bytes). The source receipt covers 207 files.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
