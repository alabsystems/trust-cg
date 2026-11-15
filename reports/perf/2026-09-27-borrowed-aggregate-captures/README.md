# Stable storage for captured aggregates — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

On Linux AArch64, references to memory-eligible aggregate locals stored in
closure environments or other aggregates now point to the original local's
rustc-layout storage. The address analysis retains every possible referent
across reference copies and branch joins. Borrowed arrays also keep their
storage when MIR inlining eliminates the capturing closure. Scalar referents
continue through the scalar-cell analysis; unsupported layouts and all proof
validators retain their existing admission boundaries.

The baseline at `e0ac540a363e36c0f28bea7a4831aca10345c313` refuses all three
new fixture roots. LLVM accepts the same source. The first repair passed O0/O1
but exposed an additional O2 refusal after closure inlining; that failed run
is retained. The final regression passes LLVM and CG at O0–O3, with **327,680
checks** over 4,096 input values per execution. It covers Some/None, mutable
array writes, shared array reads, structs, tuples, branch-selected references,
repeated FnMut calls, caller-visible storage after calls, and surrounding guard
values. The driver computes expected values independently of the fixture.

A fresh baseline and repaired compilation use the identical frozen full-core
source and Trust compiler. Failed roots fall from **7 to 6**, with 44 emitted
objects in both runs. Only `core::wtf8::EncodeWide::next` disappears; every
remaining failure message is byte-identical. A final-source rebuild repeats
the six-root result. This is partial compilation, not a completed core library
or a self-hosted toolchain. Remaining roots are `Repr::new_custom`,
`Location::caller`, two `overflowing_pow` implementations,
`TwoWaySearcher::maximal_suffix`, and `Request::fmt`.

The final backend SHA-256 is
`0d1b2493918f6f4ccd8de1038655a9cbe6a65c9480f7e9174f556f347582ae94`.
The toolchain is Trust `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, with the
committed TrustIR/Clean dependency cohort. Compilation explicitly uses
`--unverified` / `-Ztrust-verify=off`; native diagnostic codegen explicitly uses
`no-proof-certs`. No formal or Trust-verified compilation claim follows.

All-targets checking passes. New test files pass formatting. The qualified
library source and final source are byte-identical after rustfmt; the only
post-qualification edits fix two added formatting hunks. The final backend and
new native/core regression were rebuilt and rerun after those edits. Existing
unrelated library-format differences remain. Documentation inventory, links,
and diagnostic census checks pass.

All 30 existing tests in the Linux bridge target were executed: **29 passed,
one failed, zero ignored**. The sole failure is the mandatory proof ABI test
below. Their native correctness, cleanup/unwind and expected-refusal controls
are unchanged. These executions use the qualified backend before the two
formatting edits; its digest and source equivalence are retained separately.
The final new fixture also selects between two flat structs through a copied
reference, exercising the referent analysis independently of array slotting.

The mandatory proof ABI test still fails with `TCG-PROOF-465`. Its first run
also refused AY's group-writable default cache. A separate final-backend run
uses a private cache; the uncovered emitted instructions still prevent proof
promotion. Neither run changes proof policy or counts as a proof success.

Full Linux completion, the other core roots, instruction proofs, and strict
compile-time/runtime dominance over LLVM and Clang remain open. These are
correctness measurements; the observed compile durations are not a qualified
performance comparison.

Results, artifact identities, and
evidence archive retain the baseline and intermediate failures,
final native executables/objects, partial core objects, commands, compiler and
backend identities, source snapshots, and complete test logs. The 721 frozen
core source files match their original manifest. Rebuildable backend/test
libraries and the other controls' binaries are not duplicated into the archive.
Its SHA-256 is
`2f653405f603a20cf597c0545bb218479443b8475f73b516fc5b066652ea5447`;
all 1,359 archived files were independently rehashed against the inventory.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
