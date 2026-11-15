# Linux AArch64 static alignment — 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The remaining alloc static refusal is removed: the diagnostic census now has
45 failing functions, down from 45 functions plus one static. Default-section
statics, nested immutable allocations and pointer-free TLS templates can retain
allocation alignment above eight bytes on Linux AArch64. The native LLVM/CG
matrix passes 560,352 checks, with independent ELF placement and relocation
audits. Complete alloc/std, proof, self-hosting and strict compile-time/runtime
wins over LLVM and Clang remain unqualified.

## Change

Three bridge admission guards still assumed an eight-byte data-section limit.
The existing typed allocation image already carries rustc's allocation alignment
separately from its packed byte/relocation fields. The existing ELF writer aligns
each global's section offset and raises the section alignment to the strictest
member; TLS alignment is propagated through the linker to `PT_TLS`.

The bridge now admits these existing paths for Linux AArch64. Other targets
retain their admission bound. Custom sections and pointer-bearing TLS templates
still refuse; LLVM-positive/CG-negative probes retain both refusals. This change
does not alter the object writer, ABI classification or any machine encoding.

## Evidence

| Check | Result |
| --- | --- |
| New native O0–O3 × LLVM/CG matrix | 8 executions, 560,352 checks |
| ELF audits | 28 named definitions in objects and executable per run |
| Alignments tested | 16, 64, 256 and 4096 bytes |
| Existing pointer, owner and cross-crate linkage controls | 7,598,228 checks |
| Alloc diagnostic census | 46 → 45 roots; exactly one static removed |
| Fresh CG core and matching CG compiler-builtins | Compile and link |
| LLVM/CG consumers using both CG libraries | 81,097 UTF-8 checks each |
| Mandatory ABI machine-proof control | Expected TCG-PROOF-465 refusal |

The native fixture covers read-only data, initialized writable data, zero-fill
storage, initialized and zero-fill TLS, pointer-bearing aligned statics with
two distinct nested aligned allocations, and an interior-pointer relocation to
a canonical exported static. Independent LLVM code compares exported addresses,
reads every payload word and observes CG stores. Eight simultaneously live
worker threads check fresh TLS initialization, alignment, stable addresses,
independent writes and separation from the main thread. Each execution performs
70,044 checks.

A small independent ELF64 parser checks symbol types, sizes, offsets, section
alignment and storage flags, `.bss`/`.tbss` zero-fill placement, absolute pointer
relocations, the interior-pointer addend, nested target bytes and alignment,
and a `PT_TLS` segment aligned to at least 4096 bytes. The new admission is
validated through actual object files, the final linked image and native loads
and stores.

The census removes `alloc::sync::STATIC_INNER_SLICE` and adds no roots or changed
failure reasons. It remains a failed, incomplete alloc compilation. Census
compilation uses the frozen source and isolated LLVM-core dependency; separate
consumers use fresh CG-compiled core and matching CG compiler-builtins. Core has
44 AArch64 objects and 1,281 hidden private functions. Each builtins archive has
11 AArch64 objects and six weak FP exports. System `cc` is GCC, not Clang.

## Proof and retained failures

This is diagnostic codegen with Trust verification and mandatory machine
certificates disabled. The three-entry alignment probe emits five bridge
functions including callees. Refinement and strict bridge coverage accept it
with zero refinement obligations and zero unmodeled shapes. These results do
not prove data placement, alignment or TLS behavior. Mandatory certificates
reject the three entry functions. The existing ABI control still reports
14 uncovered instructions / 12 opcode kinds, first
`aliased_f32_read[13] = StpPreIndex`. No completion gate is promoted.

The first fixture used volatile operations and exposed existing unsupported
`volatile_load`/`volatile_store` intrinsics. That failure remains archived and
unfixed; the alignment fixture uses ordinary CG stores and independent LLVM
volatile readers. The initial ELF checker also matched generated nested symbols
as public statics; the corrected checker selects the exact exported names and
continues to audit nested storage through its relocations. Failed attempts are
retained. A final build updates two stale comments; final qualification uses
that separately frozen backend.

## Reproduction and identity

Frozen Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, LLVM 22.1.2,
on native Linux AArch64.

- Final backend: `40e2956e17a3a0ce1e1ebd694169312d523b57f077ced78a8b170e0669d91993`.
- Native harness: `dc4c2310e2ad814c184336f2b2ca10e42fcf011aa7205cf6fc2c198649c119a2`.
- Harness selection: `static_alignment::no_proof_static_alignment_matches_llvm`.
- Working evidence: `target/static-alignment-investigation`.
- Results, archive identity,
  member hashes, evidence archive,
  inventory.

The archive retains exact commands, frozen source and receipts, the incremental
patch, object files and native executables, ELF audits, census diagnostics,
proof and consumer logs, and failed attempts. Large backend and harness binaries
are recorded by hash. Verify with
`python3 scripts/check_evidence_archive.py reports/perf/2026-09-28-static-alignment`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
