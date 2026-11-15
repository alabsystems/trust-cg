# Trait-object parent-table lowering on Linux AArch64

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now lowers Rust trait-object upcasts using the compiler's
`supertrait_vtable_slot` query. It preserves the data pointer and either retains
the original vtable or loads the required parent table. Vtable emission follows
`TraitVPtr` entries recursively and records real symbol relocations. Removing
an auto trait or the principal trait preserves the existing metadata.

The native corpus exercises prefix, diamond and nested parent relationships,
shared/mutable/raw pointers, indirect calls, loop selection between different
implementors, pointer identity, dynamic size/alignment and mutation sentinels.
The layouts are 8-byte size/alignment and 32-byte size with 16-byte alignment.
Its independent C model checks all 16 modes. The genuine LLVM IR shows secondary
table loads at offsets 56, 80 and 96; the prefix conversion has no table load.
The same source exposes a constant closure receiver at O1. The bridge now lowers
that shared reference through its ordinary constant-allocation path, preserving
the actual environment instead of requiring a local place operand.

The final genuine Trust/Targo private all-targets check, exact six-test
inventory and fresh backend build pass. The maintained upcast regression passes
all eight LLVM/CG O0–O3 executions: 230,400 checks each, 1,843,200 total. The
unchanged 14-mode trait-pointer regression also passes 1,612,800 checks. Both
link the actual Rust runtime and observe its panic control terminate with SIGABRT.

The original full-core diagnostic falls from 47 failed roots to 46, removing
`core::io::error::Custom`'s Error-to-Debug upcast refusal with zero new roots.
The full compile still fails. The unchanged mandatory C FnABI proof gate was
actually rerun and still fails TCG-PROOF-465 at `aliased_f32_read`: 14 uncovered
instructions across 12 AArch64 opcode kinds. No proof checks were disabled in
that test.

Qualification base: `0fbb4630b4702c91d8238b8c8644326e0c026953`, with all five
changed source/test files hashed in `trait-upcasts-repair-second/results.json`.
Final backend SHA256: `7f465183ac9caf1788e4c64d454f6a3f7ce675a9ad566e12090a8a05026e4c22`.
Root formatting passes; private formatting has the same 61 preexisting edits
and zero new differences, with changed test/fixture sources checked in full.
The main-alignment receipt records normal fetch, pull, push and actual remote
checks for all three repositories before this publication.

The original published backend refuses 12 corpus roots. The first repair passes
LLVM/CG O0 and LLVM O1 native execution, then preserves the CG O1 failure on two
constant closure receivers. No mode, data value, expected result or resource
limit was removed in the final repair.

All native comparisons explicitly disable frontend verification and codegen
certificates. They establish regression evidence only. The unchanged mandatory
proof-required ABI test, full core compilation, current whole-workspace floor,
self-hosting and whole-system acceptance remain separate requirements. No
installed toolchain was changed. All G1–G8 and L01–L14 remain open.

The compressed records retain the exact source snapshots, compiler/backend
identities, commands, complete logs, object files, native executables and test
results. `assets.json` inventories every archived asset; `excluded.json` names
large rebuildable runtime archives/backend libraries with their exact digests.
The archived runners bind the immutable genuine Trust compiler `ae9c2c1da`,
private SDK and source files. Stock Rust is used only by the root formatter.
