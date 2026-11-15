# Returning scalar cells — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A scalar return place that lives in a stack cell now uses the existing typed
operand-load path at return. Previously, MIR could construct its result before
borrowing it, write the cell, and return an undefined SSA value instead. The SSA
validator correctly refused that function. This change reads the value from
its actual storage; it does not relax SSA validation or proof requirements.
Zero-sized, indirect, scalar-pair and aggregate returns retain their existing
ABI paths.

The frozen Linux AArch64 core build now has **five failing roots, down from
six** after the [captured-aggregate repair](../2026-09-27-borrowed-aggregate-captures/README.md).
Only `Repr::new_custom` disappears. All five remaining messages are unchanged,
and both runs emit 44 partial objects. The baseline diagnosis retains the
actual optimized MIR and refused TrustIR: `_0` is stored through a cell in
bb9, but the old bb16 return uses never-defined `ValueId(0)`.

The native regression has nine entry points. Eight shared-borrow return roots
fail on the baseline backend, all with the undefined SSA value; LLVM accepts
the same source. A ninth entry is an existing working control that mutates a
`Cell<u64>` through a shared reference before returning it. Mutable local
prototypes that retain a separate return assignment also compile on the old
backend and are retained as diagnosis, not counted as repaired failures.

**589,824 checks pass across LLVM and CG at O0–O3.** The driver executes 4,096
inputs with both branch choices per binary. It checks u64, i32, u128, bool,
char, pointer identity, exact f32/f64 bits (including signed zero, infinities,
subnormals and NaN payloads), and the value after a shared-reference mutation.
The existing borrowed-aggregate regression also passes on this backend.

All-targets checking passes. The selected related regression run has **nine
passes, one failure and zero ignored tests**. The sole failure is the mandatory
proof ABI test: `TCG-PROOF-465` reports 14 uncovered emitted instructions across
12 opcodes, beginning with `StpPreIndex`. It uses a private AY cache and reaches
the proof gate. No proof policy changed. Native reference-cell, scalar-union,
try-fold, wide-newtype and zero-sized-drop controls pass, including their
expected-refusal checks. This is a selected run, not the entire test suite.

New test files pass formatting, and formatting the baseline and repaired
library leaves only the ten-line repair as their code difference. Existing
unrelated library-format differences remain. Documentation inventory, links
and diagnostic census checks pass.

The repaired backend SHA-256 is
`081e9cbdee90a86a667dbde89fbafa1fa8a023dd50ea4c8dfbf2d1126b5c7cf9`.
The compiler remains Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, with
the unchanged committed dependency cohort. Targo/compiler verification is
explicitly disabled in this development lane, and diagnostic native codegen
uses `no-proof-certs`. These results provide no formal proof credit.

Remaining core roots are `Location::caller`, the u64/u128 `overflowing_pow`
implementations, `TwoWaySearcher::maximal_suffix`, and `Request::fmt`. Full
Linux completion, the proof gate, and compile/runtime dominance over LLVM and
Clang remain open. No qualifying performance comparison was made.

Results, artifact identities, and the
evidence archive retain source snapshots, the incremental
repair, baseline failures and MIR, full command logs, native regression
executables and objects, partial core objects, and compiler/backend identities.
Rebuildable backend libraries and other controls' binaries are not duplicated.
All 815 archived files were independently rehashed against the inventory.
The archive SHA-256 is
`6f72d73457499d6e4ac11fc28bbd3b15fbc0d963ee8fb1cc29ab56d220baab93`.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
