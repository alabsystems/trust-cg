# Linux AArch64 pointer images — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Alloc now has 46 failing diagnostic roots, down from 63. Explicit wide-to-thin
casts and projected pointer-image copies pass 1,742,336 native LLVM/CG checks.
Fresh core and matching compiler-builtins compile and link in both independent
consumer lanes. Complete alloc/std, proof, self-hosting and strict compile-time
and runtime wins over LLVM and Clang remain unqualified.

## Change

An explicit `PtrToPtr` cast from a length-metadata pointer to a thin raw pointer
now recovers the complete source pair and selects its data address. CStr and
structs with slice tails use this path without pretending the whole wide value
is a scalar. Wide destinations and transmutes retain both words.

A transmute from a fixed projected wide field loads both words at the actual
rustc field offset. The destination slot classifier recognizes those sources.
A bare pointer held in two projected SSA bindings can also be transmuted into
a wide slot; a missing metadata lane still fails. Checked carrier reads through
a thin reference admit the same validated full-size, offset-zero field chain
as carrier transport. This supports optimized Box, Rc and Arc field projections.
The slot-based pair recovery helper now requires only Field/Downcast projections;
a dereference must use a path that loads the base pointer explicitly.

The existing layout, FnAbi and single-scalar truncation guards remain active.
No machine opcode or instruction encoding changed.

## Evidence

| Check | Result |
| --- | --- |
| New native O0–O3 × LLVM/CG matrix | 8 executions, 1,742,336 checks |
| Existing dyn-tail, slice-tail, layout, wide argument and owner controls | 3,102,200 checks |
| Alloc diagnostic census | 63 → 46 roots; 17 removed, none added |
| Fresh CG core and matching CG compiler-builtins | Compile and link |
| LLVM/CG consumers using both CG libraries | 81,097 UTF-8 checks each |
| All-targets, formatting and documentation checks | Pass |
| Mandatory ABI machine-proof control | Expected TCG-PROOF-465 refusal |

The independent LLVM driver checks seven pointer kinds: byte/word slices, str,
CStr, and headers with byte/word/string tails. It covers data extraction,
NonNull construction and raw-pointer recovery, nested fields at nonzero offsets,
borrowed carrier fields, and wide casts that preserve metadata without rescaling.
Raw pointer checks use lengths 0–257, `usize::MAX`, `usize::MAX-1`, 2^32 and 2^63,
eight aligned address offsets, and null data pointers for data-only casts.
These artificial large lengths are never dereferenced.

Real Box values cover byte/word slices, str and CStr. Rc and Arc checks cover
byte/word slices and str, including payload addresses beyond their allocation
headers, contents, reference counts and release. CString checks compare the
borrowed pointer and bytes including the terminator. Allocation, reference-count
operations and final destruction are LLVM-compiled; CG compiles the exercised
pointer operations. This is not qualification of complete CG allocation/drop
or concurrency. Each native execution performs 217,792 checks.

The remaining census has 45 functions and one static. One remaining root changes
reason; all root identities and diagnostics are archived. Census compilation
uses the frozen source and the existing isolated LLVM-core dependency. Separate
consumers use newly CG-compiled core and matching CG compiler-builtins. Core has
44 AArch64 objects and 1,281 hidden private functions; the two builtins archives
have 11 AArch64 objects each and six weak FP exports.

## Proof and limitations

These are diagnostic codegen runs with Trust verification and mandatory machine
certificates disabled. The isolated five-entry pointer probe emits nine functions
including callees. Refinement and strict bridge coverage accept it with zero
refinement obligations and zero unmodeled shapes. That is not pointer-operation
or ABI proof. Mandatory machine certificates reject the probe and the existing
ABI control; the latter still reports 14 uncovered instructions / 12 opcode
kinds, first `aliased_f32_read[13] = StpPreIndex`. No completion gate is promoted.

The first broader native fixture caught missing scalarized-pair transmute
handling. An earlier fixture also had an LLVM driver type-inference error.
A premature `second-backend.so` copy duplicated the first backend; its repeated
failed run and census are retained and excluded from final qualification.
The completed second build is frozen as `pair-backend.so`. Nothing loaded by
a running test was overwritten.

## Reproduction and identity

Compiler: frozen Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, LLVM 22.1.2,
on native Linux AArch64. The C consumer uses system `cc` (GCC), not Clang.

- Backend: `24d93770d5cd07a865979c249c721faf173b0509d5fdceece37016482ec53f0e`.
- Native harness: `62555932a92b9014695d4f5b8bd4525cf3633c0209796f7b30fafa7f30d44027`.
- Harness selection: `pointer_image::no_proof_pointer_image_matches_llvm`.
- Working evidence: `target/pointer-image-investigation`.
- Results, archive identity,
  member hashes, evidence archive,
  inventory.

The archive includes frozen source, the incremental patch, source and compiler
receipts, exact commands, native objects/executables, census diagnostics,
proof logs, consumer evidence and failed/superseded attempts. Large backend and
harness binaries are recorded by hash. Verify with
`python3 scripts/check_evidence_archive.py reports/perf/2026-09-28-pointer-image`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
