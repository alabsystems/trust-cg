# Whole aggregate stores — Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This diagnostic increment reduces `alloc` from **25 to 22 failing functions**.
It removes `mem::replace::<String>`, `Box::<core::io::error::Custom>::new`, and
`Box::<StringError>::new`. No roots are added and no remaining failure reasons
change. Full alloc/std, self-hosting, mandatory proofs, and strict
compile/runtime wins over LLVM and Clang remain unqualified.

The frozen backend is `372354a67ea2b4a7ad1a53a2365f7253ab16957d0f8dab62b173de2ca939d2a1`
(`target/aggregate-store-investigation/second-backend.so`). The harness is
`first.test`, with the backend path and hash supplied explicitly. Commands and
artifact identities are archived. The compiler remains Trust 1.99.0-dev
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, with LLVM 22.1.2. The baseline is the
[residual-conversion increment](../2026-09-28-residual-conversion/README.md).

## Change

A nested value's pointer carrier can describe flattened scalar leaves or
uniform storage lanes. Those indices do not name Rust's top-level fields.
Whole copy/move stores from a memory-backed local previously used carrier
indices to look up field offsets, refusing nested values. On Linux AArch64 they now require matching normalized Rust types,
check the slot size and alignment against rustc, and copy the complete image
with the existing aggregate-buffer copier.

A scalarized source needs the same byte layout. Its SSA fields now pass through
the existing checked materializer, which maps flat or MIR field indices to
rustc offsets, including zero-sized fields. A source that cannot be
materialized remains refused. Nested single-variant enum pointees also use the
checked memory layout when flat pointee classification cannot represent them.
This adds a pointer shell; it does not invent offsets or bypass leaf validation.

Collection-image exclusions remain in place. The local `String` and `Vec`
definitions in an `alloc` build use their real layout; intercepted collections
in a consumer retain their separate guards. The production change does not
admit arbitrary aggregate constructors, projected source forms, or other
architectures beyond their existing paths.

The original nested-store reproducer fails on the baseline at O0–O3 and
compiles on the final backend at all four levels. The first candidate removed
the three alloc roots and passed owned replacement/cleanup, but the full matrix
exposed scalarized-store carrier mismatches and the single-variant enum
pointee gap. Those failures and that candidate's records are retained; the
final matrix includes the same cases.

## Validation

LLVM-compiled drivers call LLVM and CG objects at O0–O3. The copy matrix passes
**491,520 checks** across twelve layouts and five store forms: an out-of-line
assignment, direct pointer assignment, `mem::replace`, self-assignment, and
`ptr::read`/`ptr::write` replacement. Types cover C padding, nested C/Rust
structs, tuples, nested arrays, packed storage, 16-byte alignment and `u128`,
tagged/niche enums, fat references, zero-sized fields, and a nested
single-variant enum. Shared type metadata fixes both compilers' Rust layout.
Each run checks destination and returned values, source preservation, and
surrounding canaries; it does not compare uninitialized padding bytes.

The owned matrix passes **20,480 checks**, including **81,920 allocation/free
pairs**. It checks assignment and replacement of nested owners, exact release
values/counts, and cleanup order when either old or new field destructor
panics. Panics are caught by an LLVM driver; no double-panic abort claim is
made. Total new native checks: **512,000**. The collection-image negative
control remains LLVM-positive/CG-negative. All three new tests pass, with
zero ignored tests.

Existing projected-aggregate and residual-conversion controls pass **985,120
checks**, including aggregate-return unwinding and five refusal cases. The
selected control harness has six passing tests, one required machine-proof
failure, and zero ignored tests.

Fresh core and both compiler-builtins configurations compile diagnostically.
Core retains 44 ELF64 AArch64 objects and 1,281 hidden private functions. LLVM
and CG consumers link the new core and matching CG builtins and pass 81,097
UTF-8 checks each. Builtins retain 11 AArch64 objects per configuration and all
six weak floating-point exports. `check --all-targets`, documentation,
diagnostic inventory, differential formatting, fixture formatting, and
`git diff --check` pass.

The isolated two-function probe passes strict bridge coverage with zero
unmodeled shapes and zero refinement obligations. That records shape coverage,
not a proof of byte movement, layout, ownership or unwinding. Mandatory
machine-proof promotion still fails. The required ABI control reports 14
uncovered instructions across 12 opcode kinds, beginning with
`aliased_f32_read[13]` (`StpPreIndex`). Diagnostic runs use
`-Ztrust-verify=off` and CG's `no-proof-certs` where applicable. No performance
qualification is claimed; the separate C linker is GCC, not Clang.

## Durable record

results.json records the matrix and all 22 remaining roots.
assets.json inventories archive members; archive.json
identifies the compressed bytes. The archive includes current and baseline
source, frozen library source, incremental and worktree patches, commands,
complete logs, objects, native executables, and artifact identities. Large
backend, harness, and rlib files are represented by hashes and build records.

Sealed archive: `70f763c7c55beac910651cb47a2fdb72ff77418dbbf57a90c5ae98e3040b2ce6`, 2,950 members,
96,641,730 compressed bytes. All 235 source hashes match the working tree;
independent member rehashing and the standard archive check pass.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
