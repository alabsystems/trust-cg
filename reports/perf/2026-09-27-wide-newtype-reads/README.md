# Transparent wide-pointer reads — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Reading `NonNull<str>` or `NonNull<[T]>` through a pointer must preserve both the
data address and length. The bridge now gives these read destinations a memory
slot and loads the validated two-lane image. Optimized MIR may project through
transparent wrapper fields: each accepted field retains that same image at
rustc's checked byte offset zero. Stores keep their existing refusal boundary.

Inlined construction can transmute an already memory-backed slice pointer into
a newtype before borrowing it. The destination now keeps the complete image,
using the existing two-lane transmute lowering. Scalarized construction paths
are excluded from this promotion.

The candidate was integrated with current main `9dd72f594fb1f8019ad4415fe4db1da57a8791c3` before maintained
qualification, including the incoming closure argument-index repair and TrustIR
`dcc5b9a3ce02827dca6c3b0ae556d09ca338fdad`. The prototype was measured separately
on `7b0e0c2a4e7d56ef6d9c459d4f7ba04516cd2bf5`. Genuine Trust `ae9c2c1da`
compiles both lanes. Maintained backend SHA-256: `f47e7820f3d86dd0eadfef9f1b8bcfa57ed7496afb7e869ec8fcd02e23ff74c4`.
Native diagnostics disable frontend verification and codegen proof certificates;
the proof-required ABI test remains a separate unchanged measurement.

## Validation

- Genuine Targo all-targets check and backend build pass. The test target lists
  exactly 21 tests; both new maintained tests execute and pass.
- The positive corpus passes 48,840 native checks across LLVM/CG O0–O3, covering
  the original borrowed `NonNull<str>`, caller-owned string and u32 slice pointer
  slots, a transparent wrapper, empty slices, data, length and buffer guards.
  The original 8,448 checks are included in that expanded total.
- Whole-newtype dereference stores remain specifically refused at all four CG
  optimization levels. LLVM executes the same store input with 272 checks.
- Seventeen unchanged regressions pass 4,966,324 native checks, including 48
  LLVM-only checks for the unsupported aggregate-return cleanup case. The
  over-aligned zero-sized Drop and aggregate cleanup refusal controls remain.
  New and unchanged suites total 5,015,436 native checks.
- Root formatting passes. Private formatting adds zero differences beyond the
  59 pre-existing library blocks; all changed
  test and fixture files pass in full.
- Prototype full core has 17 failed roots. Maintained
  full core on the combined revision has 17, actual exit
  1. Compared with the published
  18-root census, the count falls by 1, with no new roots
  or changed remaining failure messages. Both measurements retain the entire
  original source denominator. This is a lowering measurement, not execution
  or formal qualification of core.
- The unchanged proof-required C ABI gate exits 101,
  passed=false, TCG-PROOF-465=true.
  It uses the existing private mode0700 cache. Native checks do not satisfy
  missing instruction proof requirements.

## Retained failures and scope

The first maintained run stopped before compiling: offline Targo did not have
the dependency revision newly pinned by main. A locked fetch retrieved that
exact revision without changing manifests or source; the full qualification
was then repeated. The initial fetch command used a compilation-only flag and was rejected before
fetching; the corrected fetch and all failed attempts are retained.

Published code refuses the original and expanded read cases. The first prototype
compiled successfully through O2 but produced an incorrect length at O2:
the caller borrowed a scalar-sized newtype image. The actual failed native run,
optimized MIR and trace are retained. The second prototype preserves the caller's
image and passes the original corpus, but the expanded test refuses the projected
wrapper read at O2. That failure and its MIR/trace are retained too. The final
repair runs the expanded corpus unchanged; no test input was removed to pass.

The new read predicate validates the transparent chain, the 16-byte/8-aligned
scalar-pair layout and every projected field offset. It does not widen the store
predicate or manufacture metadata for scalarized sources. Full core, instruction
proof coverage and all compiler completion gates remain open. No installed
compiler or channel is promoted by this report.

## Reproduction

The maintained `wide_newtype_reads::` tests live in
`aarch64_c_fnabi_aggregate_linux`, using the support module and four fixtures.
Archived commands bind compiler, backend, source and test identities; exact
inventory and native markers reject early skips. Manifests retain original
failures, integration, source snapshots, commands, logs, objects and executables.
Rebuildable backend/runtime archives are excluded with exact hashes. The full-core
source inventory and actual nonzero proof/core outcomes remain in the record.
