# Tuple memory elements and cleanup flags — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

A tupled closure argument containing a supported memory aggregate, such as a
character escape iterator with an inline array, must preserve that element's
representation. The bridge now admits these tuples after validating every field,
using the existing slot packing and ABI checks. Scalar-only tuples keep their
existing path.

The first prototype exposed a second failure: cleanup landing pads needed Boolean
drop flags as ordinary SSA parameters, but the unwinder cannot supply those
arguments. Constant-assigned Boolean locals live into cleanup pads now use the
existing scalar-cell load/store path. Entry arguments, call destinations and
locals with nonconstant definitions are excluded from this promotion. Existing
unwind edges and validation remain active.

Qualification uses base `54bb0980bd1086cbee2851171f77bc8f204d5d61` and seven
exact maintained source hashes, genuine Trust `ae9c2c1da`, and TrustIR `794227ad`.
Backend SHA-256: `e07c0a7167e7e968df7536e17130e1e43ed0e424ce5d98c362db02629225635f`. The native diagnostic lanes disable
frontend verification and codegen proof certificates; the unchanged proof-required
test is measured separately. No installed toolchain is promoted.

## Validation

- Genuine Targo all-targets check and backend build pass. The ABI test target lists
  exactly 19 tests; both new maintained tests execute and pass.
- Character escape default/debug/unicode through a generic map/fold closure passes
  38,736 checks across LLVM/CG O0–O3. The corpus covers 269 scalar inputs, invalid
  Unicode, usize and unit accumulators, exact output, lengths and buffer guards.
  The original narrower reproducer also passes; its checks are included in the
  expanded total, not added again.
- A conditional move/drop before a real direct C-unwind callback passes 2,560
  checks across LLVM/CG O0–O3. Normal returns and caught panic payloads, exactly one
  destructor, callback count, destructor payload and event order all match LLVM.
- Fifteen unchanged regressions pass, including 4,925,028 native checks, four
  over-aligned zero-sized Drop refusals and four aggregate-return cleanup refusals.
  This total includes 48 LLVM-only checks for the unsupported aggregate-return
  cleanup case. The new and existing suites total 4,966,324 native checks.
- Both unchanged Linux unwind tests pass with their exact execution marker:
  eight lanes, 24 native runs, 120 calls, 72 caught panics, 240 destructor events,
  missing-landing-pad controls and four unwind-disabled refusals.
- Root formatting passes. Private formatting adds no differences beyond the 59
  pre-existing library blocks, and all changed fixture files pass in full.
- The full original core diagnostic has 18 failed roots,
  actual exit 1. Compared with the
  published 22-root census, 4 roots disappear;
  no new roots or changed remaining failure messages appear. Prototype and
  maintained measurements are retained. Full core remains incomplete.
- The unchanged proof-required C ABI gate exits 101,
  passed=false, TCG-PROOF-465=true.
  It uses the existing mode0700 private cache. Native success does not close
  missing instruction proofs.

## Retained failures

The original map/fold baseline refuses the array element at O0 and O3. A complete
trace is retained alongside the earlier trace that exceeded its capture limit.
The tuple-only prototype builds but fails SSA validation because of the cleanup
Boolean argument. Its IR dump is retained; the combined repair runs the original
input unchanged.

An initial cleanup reproducer used an indirect callback and exposed the existing
unsupported indirect-call cleanup boundary. The direct-callback reproducer keeps
the same panic, destructor and ordering checks and isolates the Boolean flag
failure: published code refuses it with TCG-SSA-071 at O0 and O3, repaired code
executes it at all four optimization levels. Indirect cleanup remains open.

Direct character escaping already passed before the repair. An additional real
str-formatting baseline still exposes a separate O3 pointer-cast type mismatch.
Neither result is hidden or credited as repaired here. All product completion
gates and the remaining full-core/proof failures remain open.

## Reproduction and records

The two maintained tests are `tuple_memory_elements::` in
`aarch64_c_fnabi_aggregate_linux`, backed by
`crates/rustc-codegen-trust-cg/tests/support/tuple_memory_elements.rs` and four
fixtures. Archived scripts bind compiler, source, backend and test identities;
exact test inventory and native markers prevent an early skip from passing.
The manifest, asset, exclusion and inventory files bind retained sources, logs,
objects and executables. Rebuildable backend/runtime archives are excluded with
hashes. Original full-core denominator identity and actual nonzero exits remain
part of the record.
